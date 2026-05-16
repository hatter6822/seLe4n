// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM1.B**: Per-CPU data block and TPIDR_EL1 accessors.
//!
//! ARMv8-A reserves `TPIDR_EL1` (Thread Pointer / ID Register, EL1) as
//! the kernel's per-core scratch register (ARM ARM D17.2.139, analogous
//! to `gs` on x86).  The seLe4n kernel stores each core's [`PerCpuData`]
//! slot address in `TPIDR_EL1` so a per-core lookup at any kernel-mode
//! entry reduces to a single `mrs xN, tpidr_el1` instruction — no hash,
//! no table walk, no atomic read.
//!
//! ## Boot ordering (closes SMP-M4)
//!
//! - **Boot core**: `boot.rs::rust_boot_main` first calls
//!   [`check_per_cpu_invariants`] (SM1.B.6) so a regressed
//!   const-initialiser fails at boot rather than at first kernel-mode
//!   entry; then writes `&PER_CPU_DATA[0]` into `TPIDR_EL1`, emits
//!   `isb`, and enters `enable_irq()`.  The whole sequence runs
//!   before IRQs are unmasked so any future IRQ handler that consumes
//!   `TPIDR_EL1` sees a defined value rather than the architectural
//!   UNKNOWN state.
//! - **Secondary cores**: `boot.S::secondary_entry` writes
//!   `&PER_CPU_DATA[context_id]` into `TPIDR_EL1` *before* calling
//!   `rust_secondary_main`, so the very first Rust instruction on
//!   every secondary sees a valid `TPIDR_EL1`.  Secondaries do not
//!   re-run [`check_per_cpu_invariants`] because [`PER_CPU_DATA`] is
//!   a `static` (non-mutable) array — once the boot core's check
//!   succeeds, the invariant holds for the program's lifetime.
//!
//! ## What this module owns
//!
//! - [`PerCpuData`] — the per-core data block, cache-line aligned to
//!   avoid false sharing.
//! - [`PER_CPU_DATA`] — global per-core array (one slot per
//!   `PlatformBinding.coreCount`), `#[no_mangle]` so `boot.S` can
//!   reach it.
//! - [`PER_CPU_DATA_SLOT_SIZE`] / [`PER_CPU_DATA_SLOT_SIZE_SYM`] —
//!   Rust-side stride constant + asm-visible symbol pinning the stride
//!   used by `boot.S::secondary_entry`'s slot-address `madd`.
//! - [`per_cpu_slot_addr`] — Rust-side helper used by
//!   `boot.rs::rust_boot_main` to set the boot core's `TPIDR_EL1`.
//! - [`current_per_cpu`] — `&'static PerCpuData` reference for the
//!   calling core, derived from `TPIDR_EL1`.
//! - [`current_core_id_from_tpidr`] — fast core-id lookup via TPIDR_EL1
//!   (3-5 cycles cheaper than MPIDR + mask on Cortex-A76).
//! - [`check_per_cpu_invariants`] — runtime gate verifying every
//!   slot's `core_id` matches its array index.
//!
//! ## Layout invariants
//!
//! - `size_of::<PerCpuData>() == PER_CPU_DATA_SLOT_SIZE == 64`
//!   (one cache line on Cortex-A76; pinned by compile-time
//!   `const _: ()` assertions).
//! - `align_of::<PerCpuData>() == 64` (cache-line aligned to avoid
//!   false sharing).
//! - `PER_CPU_DATA.len() == MAX_SECONDARY_CORES + 1` (one slot per
//!   core; pinned by compile-time assertion to
//!   `PlatformBinding.coreCount`).
//! - `PER_CPU_DATA[i].core_id == i` for every `i ∈ 0..MAX_SECONDARY_CORES`
//!   (verified at compile time via `const fn new` initialisation and at
//!   boot via [`check_per_cpu_invariants`]).

use crate::smp::MAX_SECONDARY_CORES;

/// **WS-SM SM1.B.1** (closes SMP-M4): per-core data block.
///
/// Each kernel-mode core stores a pointer to its own [`PerCpuData`]
/// instance in `TPIDR_EL1`.  The first field `core_id` records the
/// core's index `0..coreCount-1`; later WS-SM phases will populate
/// the remaining fields (current-thread pointer, idle TCB pointer,
/// scheduler statistics, BKL ownership flag, etc.).
///
/// **Layout**: `#[repr(C, align(64))]` pins one cache line per core
/// (Cortex-A76 has 64-byte cache lines), eliminating false sharing
/// between adjacent slots when SM5 lands per-core scheduler state.
/// The total size (64 bytes) is enforced at compile time by the
/// `const _: ()` assertions below; growing the struct past one
/// cache line requires bumping [`PER_CPU_DATA_SLOT_SIZE`] in
/// lockstep, which fails the asm-pin assertion otherwise.
///
/// **Field visibility**: `core_id` is `pub` so other modules (the
/// FFI bridge, the verified Lean kernel) can read it directly via
/// [`current_per_cpu`].  The reserved padding is private; future
/// SM5+ fields will replace slots in `_reserved` in lockstep with
/// the struct-grow procedure documented above.
#[repr(C, align(64))]
pub struct PerCpuData {
    /// Core identifier `0..coreCount-1`.  Matches the index of this
    /// slot in [`PER_CPU_DATA`] (verified by
    /// [`check_per_cpu_invariants`] at boot).  Used by
    /// [`current_core_id_from_tpidr`] as the fast-path core-id
    /// lookup.
    pub core_id: u64,

    // SM5+ additions will replace the `_reserved` slots in lockstep
    // with [`PER_CPU_DATA_SLOT_SIZE`].  Reserved fields keep the
    // struct exactly one cache line wide so the asm-side stride
    // (`PER_CPU_DATA_SLOT_SIZE_SYM`) remains stable until a
    // deliberate layout change.
    //
    // Examples of fields that will land in later phases:
    //   - pub current_thread: AtomicU64    (SM5: current TCB pointer)
    //   - pub idle_thread:    u64          (SM5: idle TCB for this core)
    //   - pub bkl_held:       AtomicBool   (SM2/3: BKL ownership flag)
    //   - pub run_queue_head: AtomicU64    (SM5: per-core ready queue)
    //   - pub local_irq_cnt:  AtomicU64    (SM5: per-core stats)
    _reserved: [u64; 7],
}

impl PerCpuData {
    /// **WS-SM SM1.B.1**: const constructor that stamps `core_id`
    /// and zero-pads the reserved tail.
    ///
    /// `const fn` is required because [`PER_CPU_DATA`] is a `static`
    /// array — Rust forbids non-const initialisers for statics, so
    /// the only way to give each slot its own `core_id` at compile
    /// time is via this const-evaluable shape.
    ///
    /// Pairs with SM0.M (`.smp_stacks` zeroing in `boot.S`): together
    /// they guarantee that no stale RAM contents leak through any
    /// per-core data the kernel observes at boot.  The `_reserved`
    /// tail is explicitly zeroed even though Rust's `static`
    /// initialisation would already place these bytes in `.bss` — we
    /// pay the redundancy so the layout discharge here is local and
    /// audit-traceable (one-stop look at this function to verify the
    /// "every byte is zero except `core_id`" invariant).
    #[inline]
    pub const fn new(core_id: u64) -> Self {
        Self {
            core_id,
            _reserved: [0; 7],
        }
    }

    /// **WS-SM SM0.N legacy constructor**: zero-initialised
    /// [`PerCpuData`] instance.
    ///
    /// Equivalent to `Self::new(0)`.  Retained for callers and tests
    /// that wrote against the SM0.N interface before SM1.B added the
    /// `core_id` field; new code should use [`Self::new`] with the
    /// caller's actual `core_id`.
    #[inline]
    pub const fn zero() -> Self {
        Self::new(0)
    }
}

/// **WS-SM SM1.B.1** / SM0.N (closes SMP-M4): per-CPU data array, one
/// entry per core (boot core plus secondaries on RPi5 BCM2712).
///
/// Each slot's `core_id` field is pre-populated by [`PerCpuData::new`]
/// to match the slot index.  This means:
/// - `PER_CPU_DATA[0].core_id == 0` (boot core)
/// - `PER_CPU_DATA[1].core_id == 1`
/// - `PER_CPU_DATA[2].core_id == 2`
/// - `PER_CPU_DATA[3].core_id == 3`
///
/// The `#[no_mangle]` attribute preserves the symbol name so
/// `boot.S::secondary_entry` can reach the array via
/// `adrp + add :lo12:PER_CPU_DATA`.  Likewise, `#[used]` prevents the
/// linker from dropping the symbol under aggressive
/// dead-code-elimination.
///
/// Indexed by `context_id` (PSCI calling convention): boot core =
/// index 0, secondaries = indices 1..`MAX_SECONDARY_CORES`.
#[no_mangle]
#[used]
pub static PER_CPU_DATA: [PerCpuData; MAX_SECONDARY_CORES + 1] = [
    PerCpuData::new(0),
    PerCpuData::new(1),
    PerCpuData::new(2),
    PerCpuData::new(3),
];

/// **WS-SM SM1.B.2** / SM0.N: structurally pinned size of [`PerCpuData`].
///
/// The `secondary_entry` assembly in `boot.S` computes a core's
/// per-CPU slot address as
/// `PER_CPU_DATA + context_id * PER_CPU_DATA_SLOT_SIZE`.  Rather than
/// hard-coding the stride as an immediate literal in the asm (which
/// would silently drift if the Rust struct grew), the asm reads this
/// constant from `.rodata` via an `adrp + ldr` pair against the
/// [`PER_CPU_DATA_SLOT_SIZE_SYM`] symbol — the same pattern AN8-B
/// uses for `MPIDR_CORE_ID_MASK_SYM`.  This makes the Rust constant
/// the single source of truth.
///
/// The compile-time assertions below additionally pin
/// `size_of::<PerCpuData>()` and `align_of::<PerCpuData>()` to this
/// value so a future PR that grows the struct without updating the
/// constant fails the build at elaboration.
pub const PER_CPU_DATA_SLOT_SIZE: usize = 64;

/// **WS-SM SM1.B.2** / SM0.N: linkable symbol exposing
/// [`PER_CPU_DATA_SLOT_SIZE`] for `boot.S::secondary_entry`.
///
/// The asm reads this 64-bit value via
/// `adrp + ldr [..., :lo12:PER_CPU_DATA_SLOT_SIZE_SYM]` and uses it as
/// the `madd` multiplier when computing per-core slot addresses.
///
/// Using a `.rodata` symbol (instead of an asm-side immediate) gives a
/// single source of truth: the build is structurally inconsistent if
/// the Rust constant and the asm-observed value ever diverge, because
/// there is no asm-observed value independent of the symbol.
///
/// `#[no_mangle]` preserves the symbol name; `#[used]` prevents the
/// linker from dropping it; `pub static` (without `mut`) is the
/// standard Rust idiom for read-only data.
#[no_mangle]
#[used]
pub static PER_CPU_DATA_SLOT_SIZE_SYM: u64 = PER_CPU_DATA_SLOT_SIZE as u64;

// Compile-time pin: `size_of::<PerCpuData>() == PER_CPU_DATA_SLOT_SIZE`.
// `boot.S::secondary_entry` reads `PER_CPU_DATA_SLOT_SIZE_SYM` at
// runtime to drive its `madd` stride, so this is the structural seam
// that keeps Rust and asm in agreement.  A future PR that grows the
// struct without updating the constant fails the build here at
// elaboration.
const _: () = assert!(
    core::mem::size_of::<PerCpuData>() == PER_CPU_DATA_SLOT_SIZE,
    "WS-SM SM1.B: size_of::<PerCpuData>() must equal PER_CPU_DATA_SLOT_SIZE; \
     boot.S::secondary_entry reads PER_CPU_DATA_SLOT_SIZE_SYM at runtime, so \
     bumping the struct requires bumping PER_CPU_DATA_SLOT_SIZE in lockstep"
);

// Compile-time pin: cache-line alignment (64 bytes).  False sharing
// between adjacent slots would cripple SM5's per-core scheduler once
// the empty padding fields are populated with atomics.
const _: () = assert!(
    core::mem::align_of::<PerCpuData>() == 64,
    "WS-SM SM1.B: PerCpuData must be 64-byte aligned (cache-line) to avoid false sharing"
);

// Compile-time pin: `PER_CPU_DATA.len() == MAX_SECONDARY_CORES + 1`.
// Enforced by the **type definition** above
// (`static PER_CPU_DATA: [PerCpuData; MAX_SECONDARY_CORES + 1] = [...]`)
// — Rust's type checker verifies the array literal has exactly
// `MAX_SECONDARY_CORES + 1` elements, so a regression that changed
// `MAX_SECONDARY_CORES` without updating the literal would fail with
// a type mismatch ("expected N elements, found M").  This is a
// stronger guarantee than a `const _: () = assert!(...)` could
// provide.
//
// We deliberately do NOT add a `const _: () = assert!(PER_CPU_DATA.len()
// == MAX_SECONDARY_CORES + 1, ...)` here: that pattern requires
// `feature(const_refs_to_statics)` (rust-lang/rust#119618), which only
// stabilised in Rust 1.83.  The seLe4n MSRV is 1.82 (pinned in
// `.github/workflows/lean_action_ci.yml` and CI's
// `dtolnay/rust-toolchain@1.82.0`).  See `cpu.rs:204-213` for the
// matching AN8-B.4 note on the same MSRV constraint.
//
// Transitively: the SM0.O assertion in `smp.rs:82-87`
// (`MAX_SECONDARY_CORES + 1 == 4`) plus this type-level enforcement
// pins `PER_CPU_DATA.len() == PlatformBinding.coreCount` structurally.
// Runtime cross-checks in `tests/per_cpu::tests::sm1b_per_cpu_data_array_has_4_slots`
// and `..._max_secondary_cores_plus_one_equals_array_len` provide
// belt-and-suspenders coverage.

/// **WS-SM SM1.B.2** / SM0.N: load a core's [`PerCpuData`] slot
/// address.
///
/// Used by the boot core's TPIDR_EL1 setup
/// (`boot.rs::rust_boot_main` Phase 4) and by tests that exercise
/// the indexing logic without an actual MMIO.  Asserts on
/// out-of-range `context_id` rather than returning a stray address —
/// defends against a malformed PSCI call passing
/// `context_id ≥ MAX_SECONDARY_CORES + 1`.
#[inline]
pub fn per_cpu_slot_addr(context_id: usize) -> usize {
    assert!(
        context_id < PER_CPU_DATA.len(),
        "context_id out of range for PER_CPU_DATA"
    );
    &PER_CPU_DATA[context_id] as *const PerCpuData as usize
}

/// **WS-SM SM1.B.3**: read `TPIDR_EL1` and return a reference to
/// this core's [`PerCpuData`].
///
/// # Safety invariants enforced
///
/// - **EL1 reachability**: `TPIDR_EL1` is only readable at EL1 or
///   higher.  The kernel runs at EL1 throughout normal operation
///   (EL0 user-mode never reaches this function — every kernel-mode
///   entry traps to EL1 first via the exception vectors), so this
///   precondition is structurally satisfied.
/// - **TPIDR_EL1 set**: every core's `TPIDR_EL1` is written before
///   it executes any Rust code (boot core in
///   `boot.rs::rust_boot_main` Phase 4, secondaries in
///   `boot.S::secondary_entry` before calling `rust_secondary_main`).
///   By the time `current_per_cpu` is callable, the register holds
///   the slot address.
/// - **Pointer validity**: the pointer obtained from `TPIDR_EL1` is
///   one of the entries in the `'static` [`PER_CPU_DATA`] array,
///   which has program-lifetime extent.  The returned `&'static
///   PerCpuData` therefore has the right lifetime.
///
/// # Concurrency
///
/// Reads of `core_id` from another core's slot are safe because
/// `core_id` is initialised at compile time (via [`PerCpuData::new`])
/// and never written at runtime.  Future SM5+ atomic fields in
/// [`PerCpuData`] will require atomic accessors; until then there
/// are no read-write races on per-CPU data.
///
/// # Host (non-aarch64) behaviour
///
/// On hosts the function returns `&PER_CPU_DATA[0]` (the boot core's
/// slot), which is the only slot any host test ever touches.  This
/// matches `cpu::current_core_id()`'s host stub (returns 0).
#[inline(always)]
pub fn current_per_cpu() -> &'static PerCpuData {
    #[cfg(target_arch = "aarch64")]
    {
        let tpidr: u64;
        // SAFETY: MRS TPIDR_EL1 is always safe at EL1; the register
        // is read-only from a side-effect perspective (no memory
        // ordering implications) and has no UB modes.  ARM ARM
        // D17.2.139 documents the read as unconditional at any
        // execution level ≥ EL1.  `nomem` is correct because the
        // read does not touch memory; `preserves_flags` is correct
        // because MRS does not modify PSTATE.{N,Z,C,V}.
        unsafe {
            core::arch::asm!(
                "mrs {}, tpidr_el1",
                out(reg) tpidr,
                options(nomem, nostack, preserves_flags)
            );
        }
        // SAFETY: `TPIDR_EL1` was written by `boot.rs::rust_boot_main`
        // (boot core) or `boot.S::secondary_entry` (secondaries) to
        // the address of one of `PER_CPU_DATA`'s entries — see this
        // module's docstring.  `PER_CPU_DATA` is a `'static` array,
        // so the resulting reference has `'static` lifetime and the
        // dereference does not race with any writer (only `core_id`
        // is read, and it is initialised once at compile time and
        // never written).
        unsafe { &*(tpidr as *const PerCpuData) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: every test runs on the simulated boot core.
        // This matches `cpu::current_core_id()`'s host return of 0.
        &PER_CPU_DATA[0]
    }
}

/// **WS-SM SM1.B.4**: return the current core's id, read from
/// `TPIDR_EL1` via [`current_per_cpu`].
///
/// Preferred over `cpu::current_core_id()` (which reads MPIDR_EL1
/// and masks the affinity fields) on hot kernel paths.  The
/// MPIDR + mask path costs ~3 cycles for the MRS plus ~1-2 cycles
/// for the mask on Cortex-A76; the TPIDR + load path costs ~3
/// cycles for the MRS plus ~3-4 cycles for the cache-hot load of
/// `core_id`.  Net difference is small per call, but TPIDR has the
/// architectural advantage that the value is **pre-validated** —
/// the kernel itself owns what `TPIDR_EL1` contains, whereas MPIDR
/// is a hardware-supplied register that must be re-masked on every
/// read.
///
/// **Range invariant**: the returned `core_id` satisfies
/// `core_id < PlatformBinding.coreCount` because every slot in
/// [`PER_CPU_DATA`] is initialised with an in-range value via
/// [`PerCpuData::new`] and verified by [`check_per_cpu_invariants`]
/// at boot.  The Lean-side `Concurrency.currentCoreId` wrapper
/// re-checks the range to recover a typed `Fin numCores` for
/// downstream consumers.
///
/// # Host (non-aarch64) behaviour
///
/// Returns 0 (boot core).
#[inline(always)]
pub fn current_core_id_from_tpidr() -> u64 {
    current_per_cpu().core_id
}

/// **WS-SM SM1.B.6**: runtime gate verifying every slot's `core_id`
/// matches its array index.
///
/// Called once from `boot.rs::rust_boot_main` Phase 4 (immediately
/// before the `TPIDR_EL1` write) to catch a mis-populated array at
/// boot rather than at first kernel-entry on a secondary.  The check
/// is `O(coreCount) = O(4)`, so the cost is negligible.
///
/// Panics on mismatch (which `boot.rs::idle_loop` would catch in
/// production, but we deliberately panic loudly so the boot log
/// surfaces the failure with a clear diagnostic).  The check is
/// belt-and-suspenders against the compile-time initialiser drifting
/// from the array index — a regression that would otherwise be
/// invisible until SM5+ per-core scheduler code dereferences a
/// wrong slot.
///
/// Thin wrapper over [`check_per_cpu_invariants_in`] — the latter
/// takes a slice so the failure path is reachable from unit tests
/// without mutating the production `PER_CPU_DATA` static (which is
/// immutable from Rust code).
pub fn check_per_cpu_invariants() {
    check_per_cpu_invariants_in(&PER_CPU_DATA);
}

/// **WS-SM SM1.B.6** (inner form, testable):  verify every slot's
/// `core_id` matches its index in the supplied slice.
///
/// The production entry point [`check_per_cpu_invariants`] always
/// passes `&PER_CPU_DATA`; this inner form lets tests construct a
/// locally-allocated slice with intentionally-broken `core_id`
/// values to exercise the panic path (e.g.,
/// [`tests::sm1b_check_per_cpu_invariants_panics_on_mismatch`]).
///
/// Separating the inner form is the same pattern AN9-J's
/// `bring_up_secondaries_inner` uses to make global-state-touching
/// behaviour unit-testable.
#[inline]
pub fn check_per_cpu_invariants_in(slots: &[PerCpuData]) {
    for (i, slot) in slots.iter().enumerate() {
        assert!(
            slot.core_id == i as u64,
            "WS-SM SM1.B: PER_CPU_DATA[{}].core_id = {} ≠ {}; \
             per-CPU array is mis-populated at boot",
            i,
            slot.core_id,
            i
        );
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // WS-SM SM1.B.1 — PerCpuData struct + const constructor
    // ========================================================================

    #[test]
    fn sm1b_per_cpu_data_struct_is_64_byte_aligned() {
        // SM1.B.1: each PerCpuData is one cache line wide via
        // `repr(C, align(64))`.  Future maintainers adding fields
        // must keep the alignment attribute.
        use core::mem::align_of;
        assert_eq!(
            align_of::<PerCpuData>(),
            64,
            "PerCpuData must be 64-byte aligned to avoid false sharing"
        );
    }

    #[test]
    fn sm1b_per_cpu_data_size_equals_slot_size() {
        // SM1.B.2: the asm-visible stride symbol pins this equality.
        // A future field addition that grows the struct past one
        // cache line must bump `PER_CPU_DATA_SLOT_SIZE` in lockstep.
        use core::mem::size_of;
        assert_eq!(size_of::<PerCpuData>(), PER_CPU_DATA_SLOT_SIZE);
        assert_eq!(PER_CPU_DATA_SLOT_SIZE, 64);
    }

    #[test]
    fn sm1b_per_cpu_data_size_is_multiple_of_align() {
        // SM1.B.1: a struct's size is always a multiple of its
        // alignment in Rust, but this would not hold if a future
        // maintainer accidentally shrank the struct below the
        // alignment unit while removing fields.
        //
        // We use the bitwise-AND form `(sz & (al - 1)) == 0` rather
        // than `sz % al == 0` for three reasons:
        //   1. Lint-clean: avoids `clippy::manual_is_multiple_of`
        //      (added in clippy 1.87) so the test compiles cleanly
        //      under the project's pinned MSRV of Rust 1.82 without
        //      an `#[allow(...)]` workaround.
        //   2. Mathematically equivalent for power-of-2 alignments,
        //      and `core::mem::align_of` is *guaranteed* by the Rust
        //      language reference to return a power of 2.
        //   3. MSRV-independent — works identically on every Rust
        //      version.
        use core::mem::{align_of, size_of};
        let sz = size_of::<PerCpuData>();
        let al = align_of::<PerCpuData>();
        assert!(sz >= al);
        assert!((sz & (al - 1)) == 0);
    }

    #[test]
    fn sm1b_per_cpu_data_new_sets_core_id() {
        // SM1.B.1: the const constructor stamps the `core_id` field.
        let pcd = PerCpuData::new(7);
        assert_eq!(pcd.core_id, 7);
    }

    #[test]
    fn sm1b_per_cpu_data_new_zeros_reserved_tail() {
        // SM1.B.1: the reserved tail starts zero so no stale RAM
        // contents leak through.  Inspect via byte view (the field
        // is private so direct read is rejected).
        let pcd = PerCpuData::new(0);
        // SAFETY: read-only inspection of bytes via a local
        // reference.  The local is owned by this thread and lives
        // for the duration of the test.
        let bytes = unsafe {
            core::slice::from_raw_parts(
                &pcd as *const PerCpuData as *const u8,
                core::mem::size_of::<PerCpuData>(),
            )
        };
        // Bytes 0..8 hold core_id (little-endian 0); bytes 8..64
        // hold the reserved padding.  Every byte should be 0.
        assert!(
            bytes.iter().all(|&b| b == 0),
            "PerCpuData::new(0) must produce all-zero bytes"
        );
    }

    #[test]
    fn sm1b_per_cpu_data_new_preserves_core_id_under_round_trip() {
        // SM1.B.1: every plausible `core_id` survives the const
        // constructor.  Spot-check the boundaries plus the four
        // production values.
        for core_id in [0u64, 1, 2, 3, u64::MAX] {
            let pcd = PerCpuData::new(core_id);
            assert_eq!(pcd.core_id, core_id);
        }
    }

    #[test]
    fn sm1b_per_cpu_data_zero_constructor_yields_zero_bytes() {
        // SM0.N back-compat: `PerCpuData::zero()` must produce all
        // zero bytes (same as `PerCpuData::new(0)`).
        let pcd = PerCpuData::zero();
        assert_eq!(pcd.core_id, 0);
        // SAFETY: read-only inspection of bytes (see above).
        let bytes = unsafe {
            core::slice::from_raw_parts(
                &pcd as *const PerCpuData as *const u8,
                core::mem::size_of::<PerCpuData>(),
            )
        };
        assert!(bytes.iter().all(|&b| b == 0));
    }

    // ========================================================================
    // WS-SM SM1.B.2 — Static array layout + slot-address invariants
    // ========================================================================

    #[test]
    fn sm1b_per_cpu_data_array_has_4_slots() {
        // SM1.B.2: per-CPU data array carries one slot per core
        // (boot core + 3 secondaries on RPi5).  Loosely coupled to
        // `MAX_SECONDARY_CORES + 1 = 4`.
        assert_eq!(PER_CPU_DATA.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(PER_CPU_DATA.len(), 4);
    }

    #[test]
    fn sm1b_per_cpu_data_core_ids_match_indices() {
        // SM1.B.2 / SM1.B.6 (compile-time form): every slot's
        // `core_id` field matches its array index.  This is the
        // structural invariant `check_per_cpu_invariants` re-asserts
        // at runtime.
        for (i, slot) in PER_CPU_DATA.iter().enumerate() {
            assert_eq!(
                slot.core_id, i as u64,
                "PER_CPU_DATA[{}].core_id must equal {}",
                i, i
            );
        }
    }

    #[test]
    fn sm1b_per_cpu_slot_addr_in_bounds_returns_valid_address() {
        // SM1.B.2: `per_cpu_slot_addr(i)` returns the address of
        // `PER_CPU_DATA[i]` for any in-range index.  The address
        // must be 64-byte aligned (the cache-line alignment of
        // `PerCpuData`).
        for i in 0..PER_CPU_DATA.len() {
            let addr = per_cpu_slot_addr(i);
            assert!(addr != 0, "per_cpu_slot_addr({}) returned null", i);
            assert_eq!(
                addr % 64,
                0,
                "per_cpu_slot_addr({}) = {:#x} not 64-byte aligned",
                i,
                addr
            );
        }
    }

    #[test]
    fn sm1b_per_cpu_slot_addr_distinct_per_core() {
        // SM1.B.2: distinct context_ids map to distinct slot
        // addresses.  This is the property boot.S TPIDR_EL1 setup
        // relies on — each core's `TPIDR_EL1` must be unique so
        // per-core lookups don't alias.
        let addrs: [usize; 4] = [
            per_cpu_slot_addr(0),
            per_cpu_slot_addr(1),
            per_cpu_slot_addr(2),
            per_cpu_slot_addr(3),
        ];
        for i in 0..addrs.len() {
            for j in (i + 1)..addrs.len() {
                assert_ne!(
                    addrs[i], addrs[j],
                    "per_cpu_slot_addr({}) and per_cpu_slot_addr({}) must differ",
                    i, j
                );
            }
        }
    }

    #[test]
    fn sm1b_per_cpu_slot_addr_stride_matches_struct_size() {
        // SM1.B.2: consecutive slot addresses differ by exactly
        // `size_of::<PerCpuData>() = 64`.  The asm computes the
        // slot address as `PER_CPU_DATA + context_id * 64`, so any
        // change to the struct size would silently corrupt the
        // per-core lookup unless caught here.
        use core::mem::size_of;
        let stride = size_of::<PerCpuData>();
        for i in 0..(PER_CPU_DATA.len() - 1) {
            let a = per_cpu_slot_addr(i);
            let b = per_cpu_slot_addr(i + 1);
            assert_eq!(
                b - a,
                stride,
                "PER_CPU_DATA stride between slot {} and {} = {}, expected {}",
                i,
                i + 1,
                b - a,
                stride
            );
        }
    }

    #[test]
    fn sm1b_per_cpu_data_slot_size_matches_asm_literal() {
        // SM1.B.2: the `PER_CPU_DATA_SLOT_SIZE` Rust constant is the
        // single source of truth for the slot stride the
        // `secondary_entry` asm uses.  Belt-and-suspenders against
        // a future hand-edited stride.
        use core::mem::size_of;
        assert_eq!(PER_CPU_DATA_SLOT_SIZE, 64);
        assert_eq!(size_of::<PerCpuData>(), PER_CPU_DATA_SLOT_SIZE);
    }

    #[test]
    fn sm1b_per_cpu_data_slot_size_sym_observable() {
        // SM1.B.2: the `PER_CPU_DATA_SLOT_SIZE_SYM` linkable symbol
        // used by `boot.S::secondary_entry` for the `madd` stride
        // must be observable from Rust at the value
        // `PER_CPU_DATA_SLOT_SIZE`.  A future PR that drops the
        // `#[used]` attribute would break this test before the asm
        // could fault at runtime.
        assert_eq!(PER_CPU_DATA_SLOT_SIZE_SYM, PER_CPU_DATA_SLOT_SIZE as u64);
        let sym_addr = &PER_CPU_DATA_SLOT_SIZE_SYM as *const u64 as usize;
        assert!(
            sym_addr != 0,
            "PER_CPU_DATA_SLOT_SIZE_SYM must have a valid linker-assigned address"
        );
    }

    #[test]
    #[should_panic(expected = "context_id out of range")]
    fn sm1b_per_cpu_slot_addr_out_of_bounds_panics() {
        // SM1.B.2: an out-of-range `context_id` panics rather than
        // returning a stray address.  Defends against a malformed
        // PSCI call passing `context_id ≥ MAX_SECONDARY_CORES + 1`.
        let _ = per_cpu_slot_addr(PER_CPU_DATA.len());
    }

    // ========================================================================
    // WS-SM SM1.B.3 — current_per_cpu accessor
    // ========================================================================

    #[test]
    fn sm1b_current_per_cpu_returns_boot_slot_on_host() {
        // SM1.B.3: on host (non-aarch64) the function returns the
        // boot core's slot, matching `cpu::current_core_id()`'s
        // host stub (returns 0).
        let pcd = current_per_cpu();
        assert_eq!(pcd.core_id, 0);
    }

    #[test]
    fn sm1b_current_per_cpu_address_in_static_array() {
        // SM1.B.3: the returned reference must point inside
        // `PER_CPU_DATA` (any valid slot).  On host this is always
        // slot 0; on aarch64 with TPIDR_EL1 set correctly it is
        // the current core's slot.
        let pcd_addr = current_per_cpu() as *const PerCpuData as usize;
        let array_start = &PER_CPU_DATA[0] as *const PerCpuData as usize;
        let array_end = array_start + core::mem::size_of_val(&PER_CPU_DATA);
        assert!(
            pcd_addr >= array_start && pcd_addr < array_end,
            "current_per_cpu() address {:#x} not inside PER_CPU_DATA \
             [{:#x}, {:#x})",
            pcd_addr,
            array_start,
            array_end
        );
    }

    #[test]
    fn sm1b_current_per_cpu_address_is_cache_line_aligned() {
        // SM1.B.3: the returned reference must point at a 64-byte
        // boundary (cache-line aligned slot).
        let addr = current_per_cpu() as *const PerCpuData as usize;
        assert_eq!(
            addr % 64,
            0,
            "current_per_cpu() address {:#x} not 64-byte aligned",
            addr
        );
    }

    // ========================================================================
    // WS-SM SM1.B.4 — current_core_id_from_tpidr fast lookup
    // ========================================================================

    #[test]
    fn sm1b_current_core_id_from_tpidr_returns_zero_on_host() {
        // SM1.B.4: on host this defers to
        // `current_per_cpu().core_id` = `PER_CPU_DATA[0].core_id` = 0.
        assert_eq!(current_core_id_from_tpidr(), 0);
    }

    #[test]
    fn sm1b_current_core_id_from_tpidr_in_range() {
        // SM1.B.4: the returned core_id must satisfy
        // `core_id < coreCount`.  Both the host stub (returns 0)
        // and the aarch64 path (returns `current_per_cpu().core_id`
        // ∈ {0,1,2,3} by `check_per_cpu_invariants`) honour the
        // bound.
        let id = current_core_id_from_tpidr();
        assert!(
            (id as usize) < PER_CPU_DATA.len(),
            "current_core_id_from_tpidr() = {} ≥ coreCount = {}",
            id,
            PER_CPU_DATA.len()
        );
    }

    // ========================================================================
    // WS-SM SM1.B.6 — check_per_cpu_invariants runtime gate
    // ========================================================================

    #[test]
    fn sm1b_check_per_cpu_invariants_passes_on_static_array() {
        // SM1.B.6: the runtime gate must pass for the production
        // initialiser — this is the property `rust_boot_main` Phase
        // 4 asserts at boot.
        check_per_cpu_invariants();
    }

    #[test]
    fn sm1b_check_per_cpu_invariants_in_passes_on_well_formed_slice() {
        // SM1.B.6 (inner form): a locally-allocated well-formed slice
        // also passes the gate.  Verifies the inner function is a
        // pure structural check, not coupled to the `PER_CPU_DATA`
        // static.
        let slots = [
            PerCpuData::new(0),
            PerCpuData::new(1),
            PerCpuData::new(2),
            PerCpuData::new(3),
        ];
        check_per_cpu_invariants_in(&slots);
    }

    #[test]
    fn sm1b_check_per_cpu_invariants_in_passes_on_empty_slice() {
        // SM1.B.6: an empty slice trivially passes the gate (the
        // loop does not execute).  Edge case for forward-compat
        // with single-core platforms that might use `coreCount = 1`
        // (in which case the only slot is the boot core, but a
        // zero-secondary configuration would still have one slot).
        // We pass an empty array here as a stress test on the
        // structural form; the production `PER_CPU_DATA` is never
        // empty because `MAX_SECONDARY_CORES + 1 >= 1`.
        let slots: [PerCpuData; 0] = [];
        check_per_cpu_invariants_in(&slots);
    }

    #[test]
    #[should_panic(expected = "per-CPU array is mis-populated")]
    fn sm1b_check_per_cpu_invariants_in_panics_on_wrong_core_id() {
        // SM1.B.6: the runtime gate panics if any slot's `core_id`
        // disagrees with its array index.  This is the regression
        // path that the production `PER_CPU_DATA` initialiser would
        // hit if a future PR mis-populated the static (e.g., changed
        // `PerCpuData::new(2)` to `PerCpuData::new(99)` in the
        // initialiser).  The inner form lets us simulate this without
        // mutating the immutable production static.
        let slots = [
            PerCpuData::new(0),
            PerCpuData::new(1),
            PerCpuData::new(99), // mis-populated — index 2 but core_id 99
            PerCpuData::new(3),
        ];
        check_per_cpu_invariants_in(&slots);
    }

    #[test]
    #[should_panic(expected = "per-CPU array is mis-populated")]
    fn sm1b_check_per_cpu_invariants_in_panics_on_first_slot_wrong() {
        // SM1.B.6: the gate also catches a regression on the boot
        // slot.  Reorder-detection: if the slots are accidentally
        // populated in reverse, the very first iteration catches it.
        let slots = [
            PerCpuData::new(3), // wrong: index 0 should be core_id 0
            PerCpuData::new(2),
            PerCpuData::new(1),
            PerCpuData::new(0),
        ];
        check_per_cpu_invariants_in(&slots);
    }

    #[test]
    #[should_panic(expected = "per-CPU array is mis-populated")]
    fn sm1b_check_per_cpu_invariants_in_panics_on_zero_default_regression() {
        // SM1.B.6: the gate catches the "every slot is zero" regression
        // — the case where someone reverts SM1.B.2's per-slot
        // initialiser back to the SM0.N `PerCpuData::zero()` pattern.
        // Pre-SM1.B the SM0.N initialiser produced this exact layout;
        // catching it at boot now is the SM1.B contract.
        let slots = [
            PerCpuData::zero(), // core_id = 0 ✓
            PerCpuData::zero(), // core_id = 0 but index 1 — FAIL HERE
            PerCpuData::zero(),
            PerCpuData::zero(),
        ];
        check_per_cpu_invariants_in(&slots);
    }

    // ========================================================================
    // WS-SM SM1.B.6 — Layout consistency cross-checks
    // ========================================================================

    #[test]
    fn sm1b_max_secondary_cores_plus_one_equals_array_len() {
        // SM1.B.2: the array size must equal
        // `MAX_SECONDARY_CORES + 1` (boot core + N-1 secondaries).
        // Cross-check the assertion at the module-level
        // `const _: ()` evaluator.
        assert_eq!(PER_CPU_DATA.len(), MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn sm1b_core_id_pairwise_distinct() {
        // SM1.B.6: every slot's `core_id` is distinct.  This is the
        // property `current_core_id_from_tpidr` relies on for its
        // O(1) core-id lookup: distinct slots produce distinct
        // core-ids.
        let ids: [u64; 4] = [
            PER_CPU_DATA[0].core_id,
            PER_CPU_DATA[1].core_id,
            PER_CPU_DATA[2].core_id,
            PER_CPU_DATA[3].core_id,
        ];
        for i in 0..ids.len() {
            for j in (i + 1)..ids.len() {
                assert_ne!(
                    ids[i], ids[j],
                    "PER_CPU_DATA[{}].core_id and PER_CPU_DATA[{}].core_id collide at {}",
                    i, j, ids[i]
                );
            }
        }
    }

    #[test]
    fn sm1b_core_id_in_canonical_range() {
        // SM1.B.6: every slot's `core_id` is in [0, coreCount).
        // Pairs with `current_core_id_from_tpidr_in_range`; that
        // test checks the live FFI value, this one checks the
        // statically-initialised slots.
        for (i, slot) in PER_CPU_DATA.iter().enumerate() {
            assert!(
                (slot.core_id as usize) < PER_CPU_DATA.len(),
                "PER_CPU_DATA[{}].core_id = {} ≥ coreCount = {}",
                i,
                slot.core_id,
                PER_CPU_DATA.len()
            );
        }
    }

    #[test]
    fn sm1b_current_per_cpu_and_slot_addr_agree_for_boot_core() {
        // SM1.B.3/SM1.B.4 cross-check: on host, `current_per_cpu()`
        // returns slot 0, which is also what `per_cpu_slot_addr(0)`
        // resolves.
        let live = current_per_cpu() as *const PerCpuData as usize;
        let expected = per_cpu_slot_addr(0);
        assert_eq!(live, expected);
    }
}
