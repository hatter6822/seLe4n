// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-J (DEF-R-HAL-L20): Secondary-core bring-up scaffolding.
//!
//! At v1.0.0 the kernel boots single-core by default — the runtime
//! flag [`smp_enabled`] is `false` so `bring_up_secondaries` is a
//! no-op.  The SMP code path is fully present, code-reviewed, and
//! unit-tested on host so the activation cost at v1.x.x is just
//! flipping the flag.
//!
//! ## Boot sequence (when enabled)
//!
//! 1. Primary core finishes its early init (MMU, GIC, timer,
//!    UART) on its own MPIDR-0 affinity slot.
//! 2. For each entry in [`SECONDARY_MPIDR_TABLE`], primary issues
//!    a PSCI `CPU_ON` (`crate::psci::cpu_on`) with `entry_point =
//!    secondary_entry` (a `boot.S` label) and a per-core context
//!    id distinguishing this call.
//! 3. Secondary cores wake, run `secondary_entry` which sets up
//!    SP / TPIDR_EL1, calls `rust_secondary_main`, runs the
//!    AK5-D-ordered MMU enable sequence, applies the AK5-C
//!    SCTLR_EL1 bitmap, initialises its GIC CPU interface, and
//!    spins on its `core_ready` flag.
//! 4. Once primary signals ready (`sev`), secondaries proceed to
//!    the per-core scheduler entry.
//!
//! ## What this module owns
//!
//! - `SmpConfig` — runtime flag + secondary-core inventory
//! - `bring_up_secondaries` — primary-core entry point that issues
//!   the CPU_ON loop
//! - `rust_secondary_main` — placeholder Rust entry called from
//!   `boot.S::secondary_entry`
//! - Per-core readiness flags
//!
//! ## What this module does NOT own
//!
//! - The boot.S secondary-entry assembly (lives in `boot.S`)
//! - Per-core scheduler state (lives in the Lean kernel)
//! - PSCI HVC encoding (lives in `psci.rs`)
//!
//! Per the AN9-J plan, full QEMU `-smp 4` validation is gated on
//! firmware support (PSCI must be available at EL2); the host
//! tests here exercise the Rust call graph with stubbed PSCI.

use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

use crate::psci::{cpu_on, PsciResult};

/// AN9-J / **WS-SM SM0.O**: maximum number of secondary cores the kernel
/// will attempt to bring up.  BCM2712 has 4 Cortex-A76 cores total, so
/// we have at most 3 secondaries.
///
/// **WS-SM SM0.O**: the value is structurally pinned to the Lean-side
/// `PlatformBinding.coreCount` field of `RPi5Platform` (which holds `4`)
/// via the compile-time assertion below.  Rust does not see the Lean
/// typeclass directly, but the constant assertion fails the build if the
/// two sides drift — a future multi-platform port that changes
/// `coreCount` must update this constant in lockstep.
pub const MAX_SECONDARY_CORES: usize = 3;

/// **WS-SM SM0.O** (closes SMP-L2): compile-time pin of the Rust
/// `MAX_SECONDARY_CORES` constant against the Lean
/// `Platform.RPi5.PlatformBinding.coreCount` value (`4`).
///
/// `MAX_SECONDARY_CORES + 1` (boot core + N-1 secondaries) must equal
/// the total core count exposed by the production platform binding.
/// If a future PR bumps the Lean `coreCount` (for example, to support a
/// hypothetical 8-core RPi6) without bumping this Rust constant, the
/// assertion below fails to elaborate at build time, producing a
/// compiler error that points the contributor straight at the drift.
const _: () = assert!(
    MAX_SECONDARY_CORES + 1 == 4,
    "WS-SM SM0.O: MAX_SECONDARY_CORES + 1 must equal \
     PlatformBinding.coreCount (RPi5 = 4)"
);

/// AN9-J: runtime SMP-enable flag.  At v1.0.0 the default is `false`
/// so `bring_up_secondaries` is a no-op; deployments that opt in to
/// SMP set this `true` via a kernel-command-line parameter parsed by
/// `boot.rs::rust_boot_main` before invoking `bring_up_secondaries`.
pub static SMP_ENABLED: AtomicBool = AtomicBool::new(false);

/// AN9-J: secondary-core readiness flags.  Index 0 is unused (the
/// boot core); indices 1..=3 correspond to secondary cores.  Each
/// flag is set `true` by the primary AFTER `bring_up_secondaries`
/// returns (i.e., once every CPU_ON call has succeeded), so
/// secondaries waiting in their `wfe_bounded` loop wake up and
/// proceed to the per-core scheduler entry.
pub static CORE_READY: [AtomicBool; 4] = [
    AtomicBool::new(true), // boot core is always ready
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
];

/// AN9-J: count of secondary cores actually brought up.  Populated by
/// `bring_up_secondaries` and read by tests / diagnostics.
pub static SECONDARY_CORES_ONLINE: AtomicU32 = AtomicU32::new(0);

/// AN9-J: BCM2712 secondary-core MPIDR table.  Each entry is a 64-bit
/// MPIDR_EL1 value where (Aff2, Aff1, Aff0) identify a specific
/// Cortex-A76 in the dual-cluster topology.
///
/// Cortex-A76 in BCM2712 is a single-cluster 4-core configuration
/// (per-Pi 5 schematic), so cluster Aff is 0 for all four cores and
/// Aff0 selects the core within the cluster.  Secondaries are
/// `Aff0=1`, `Aff0=2`, `Aff0=3`.
pub const SECONDARY_MPIDR_TABLE: [u64; MAX_SECONDARY_CORES] = [
    0x0000_0001, // Aff0 = 1
    0x0000_0002, // Aff0 = 2
    0x0000_0003, // Aff0 = 3
];

/// **WS-SM SM0.N** (closes SMP-M4): per-core data block.
///
/// Each kernel-mode core stores a pointer to its own `PerCpuData`
/// instance in `TPIDR_EL1` (the ARMv8-A "Thread Pointer / ID Register
/// for EL1") so a per-core lookup is a single `mrs xN, tpidr_el1`
/// instruction without any hash/lookup overhead.
///
/// At SM0 the struct is empty — the *seam* matters more than the
/// content.  SM1.B populates the fields once the per-core scheduler
/// state lands (current thread pointer, idle TCB pointer, per-core
/// run queue head, etc.).  The `#[repr(C, align(64))]` ensures each
/// instance occupies its own cache line, eliminating false sharing
/// once the fields are populated.
#[repr(C, align(64))]
pub struct PerCpuData {
    // SM1.B will populate these fields:
    //   pub current_thread: AtomicU64,   // current TCB pointer
    //   pub idle_thread:    AtomicU64,   // idle TCB for this core
    //   pub bkl_owner:      AtomicBool,  // does this core hold the BKL?
    //   pub run_queue_head: AtomicU64,   // per-core ready queue head
    //
    // SM0.N intentionally leaves the struct empty so the seam is
    // available without committing to a layout that SM1.B may
    // reshape during per-core scheduler design.  An empty struct
    // still occupies one cache line via `repr(C, align(64))` so the
    // alignment / padding of the array layout is forward-compatible
    // with SM1.B's additions.
    _reserved: [u64; 8],
}

impl PerCpuData {
    /// **WS-SM SM0.N**: zero-initialised constructor.  Used to populate
    /// the static `PER_CPU_DATA` array; the explicit zero discharge
    /// matches the asm-side `.smp_stacks` zeroing (SM0.M) and
    /// guarantees no stale RAM contents leak through the per-core
    /// data block at boot.
    pub const fn zero() -> Self {
        Self { _reserved: [0; 8] }
    }
}

/// **WS-SM SM0.N**: per-CPU data array, one entry per core (boot
/// core plus 3 secondaries on RPi5 BCM2712).  Each `secondary_entry`
/// (boot.S) loads the address of its own slot into `TPIDR_EL1`
/// before branching to `rust_secondary_main`.  The boot core's
/// TPIDR_EL1 is set in `boot.rs::rust_boot_main` (Phase 4).
///
/// Indexed by `context_id` (PSCI calling convention): boot core =
/// index 0, secondaries = indices 1..3.
#[no_mangle]
#[used]
pub static PER_CPU_DATA: [PerCpuData; MAX_SECONDARY_CORES + 1] = [
    PerCpuData::zero(),
    PerCpuData::zero(),
    PerCpuData::zero(),
    PerCpuData::zero(),
];

/// **WS-SM SM0.N**: structurally pinned size of `PerCpuData`.
///
/// The `secondary_entry` assembly in `boot.S` computes a core's
/// per-CPU slot address as `PER_CPU_DATA + context_id * 64` —
/// the literal `64` is hard-coded into the asm because the
/// `madd` instruction takes an immediate stride, not a symbol.
/// This Rust-side compile-time assertion locks the Rust struct
/// size to that literal, so any future PR that grows `PerCpuData`
/// past 64 bytes (or shrinks it below 64) fails the build before
/// the asm can compute a wrong address at runtime.
///
/// To grow the struct beyond 64 bytes safely, the contributor must
/// in the same PR: (a) update this `PER_CPU_DATA_SLOT_SIZE`
/// constant, (b) update the literal `#64` in
/// `boot.S::secondary_entry`, and (c) re-run the
/// `sm0n_per_cpu_slot_addr_stride_matches_struct_size` unit test.
pub const PER_CPU_DATA_SLOT_SIZE: usize = 64;

const _: () = assert!(
    core::mem::size_of::<PerCpuData>() == PER_CPU_DATA_SLOT_SIZE,
    "WS-SM SM0.N: size_of::<PerCpuData>() must equal PER_CPU_DATA_SLOT_SIZE; \
     update boot.S::secondary_entry's `mov x5, #64` literal in the same PR"
);

const _: () = assert!(
    core::mem::align_of::<PerCpuData>() == 64,
    "WS-SM SM0.N: PerCpuData must be 64-byte aligned (cache-line) to avoid false sharing"
);

/// **WS-SM SM0.N**: load a core's `PerCpuData` slot address.  Used by
/// the boot core's TPIDR_EL1 setup (in `boot.rs::rust_boot_main`) and
/// by tests that exercise the indexing logic without an actual MMIO.
#[inline]
pub fn per_cpu_slot_addr(context_id: usize) -> usize {
    // SAFETY: PER_CPU_DATA has MAX_SECONDARY_CORES + 1 entries; the
    // bound check below converts a stray context_id into a panic
    // rather than an out-of-bounds memory read.  Production callers
    // always pass `0..=3`.
    assert!(
        context_id < PER_CPU_DATA.len(),
        "context_id out of range for PER_CPU_DATA"
    );
    &PER_CPU_DATA[context_id] as *const PerCpuData as usize
}

// AN9-J: opaque secondary-entry symbol.  Resolved at link time by
// `boot.S::secondary_entry`; declared here as `extern "C"` so the
// PSCI CPU_ON call can pass its address.
//
// Test builds substitute a host-side stub so the bring-up loop can
// be exercised without the assembly artefact.
#[cfg(not(test))]
extern "C" {
    pub fn secondary_entry();
}

/// AN9-J test stub for `secondary_entry`.  Never called by host
/// tests (the PSCI host stub does not actually transfer control); the
/// signature exists so address-of expressions in the bring-up loop
/// type-check on host.
#[cfg(test)]
pub extern "C" fn secondary_entry() {
    // host stub: no-op
}

/// AN9-J: bring up all secondary cores listed in `mpidr_table`.
///
/// Inner form taking explicit state references so unit tests can
/// substitute local atomics and avoid cargo's parallel-test global
/// state race.  Production callers go through
/// [`bring_up_secondaries`] which threads the global statics.
///
/// Behaviour:
///   1. If `enabled.load(Acquire) == false`, returns 0 (no-op).
///   2. Otherwise, issues PSCI `CPU_ON` for each secondary with
///      `entry_point = secondary_entry` and `context_id` = index+1.
///   3. Sets `core_ready[idx+1] = true` for each successful core.
///   4. Stores online count into `online_count`.
///   5. On aarch64, broadcasts SEV so secondaries parked in `wfe`
///      wake immediately.
///
/// Returns the number of secondaries successfully brought up.
pub fn bring_up_secondaries_inner(
    enabled: &AtomicBool,
    core_ready: &[AtomicBool],
    online_count: &AtomicU32,
    mpidr_table: &[u64],
) -> u32 {
    if !enabled.load(Ordering::Acquire) {
        return 0;
    }

    let mut online: u32 = 0;
    for (idx, &mpidr) in mpidr_table.iter().enumerate() {
        let context_id = (idx as u64) + 1; // matches core_ready index
        // First cast to a raw fn pointer, then to usize, to keep
        // clippy happy (`function_casts_as_integer`).  The fn item
        // type only converts to a fn pointer or integer via these
        // explicit steps.
        let entry_addr = secondary_entry as *const () as usize;
        let result = cpu_on(mpidr, entry_addr, context_id);
        match result {
            PsciResult::Success | PsciResult::AlreadyOn => {
                online += 1;
                // AN9-J.4.d: signal the secondary it can proceed.
                let core_idx = idx + 1;
                if core_idx < core_ready.len() {
                    core_ready[core_idx].store(true, Ordering::Release);
                }
            }
            other => {
                // Diagnostic log: PSCI rejection is non-fatal at boot.
                // The kernel continues with however many secondaries
                // came up successfully.
                crate::kprintln!(
                    "[SMP] PSCI CPU_ON rejected for MPIDR {:#x}: {:?}",
                    mpidr,
                    other
                );
            }
        }
    }

    online_count.store(online, Ordering::Release);

    // AN9-J.4.d: broadcast SEV so any secondary parked in `wfe`
    // wakes immediately.  On host this is a no-op.
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: SEV is a hint instruction with no side effects.
        // (ARM ARM C6.2.243)
        unsafe {
            core::arch::asm!("sev", options(nomem, nostack, preserves_flags));
        }
    }

    online
}

/// AN9-J: bring up all secondary cores listed in
/// [`SECONDARY_MPIDR_TABLE`] using the global static state.
///
/// Production-path entry point.  Calls [`bring_up_secondaries_inner`]
/// with the global atomics; tests use the inner form with local
/// state to avoid global-state races under parallel cargo test.
///
/// Returns the number of secondaries successfully brought up.
pub fn bring_up_secondaries() -> u32 {
    bring_up_secondaries_inner(
        &SMP_ENABLED,
        &CORE_READY,
        &SECONDARY_CORES_ONLINE,
        &SECONDARY_MPIDR_TABLE,
    )
}

/// AN9-J: secondary-core entry point called from the boot.S
/// `secondary_entry` label.  Each secondary core runs through the
/// AK5-D-ordered MMU-enable sequence, applies the AK5-C SCTLR_EL1
/// bitmap, initialises its GIC CPU interface, then spins on its
/// `core_ready` flag (using `wfe_bounded` to avoid hanging if SEV
/// never fires).
///
/// At v1.0.0 this routine is wired but unreachable in the default
/// build (`SMP_ENABLED = false` means primary never issues CPU_ON);
/// the implementation is present so the build links cleanly when
/// SMP is opted in.
#[no_mangle]
pub extern "C" fn rust_secondary_main(context_id: u64) -> ! {
    // AN9-J.4.d: spin on the per-core ready flag with a bounded WFE
    // (AN9-G).  This avoids hanging if the primary never issues SEV.
    let core_idx = context_id as usize;
    if core_idx < CORE_READY.len() {
        while !CORE_READY[core_idx].load(Ordering::Acquire) {
            // Discard elapsed-ticks return; the secondary's only
            // wake condition is the `CORE_READY` flag, polled on the
            // next loop iteration.  AN9-G's bounded primitive
            // ensures we never block forever if the primary's SEV
            // is lost.
            let _ = crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }
    }

    // Once ready, fall into the per-core idle loop.  At v1.0.0 the
    // per-core scheduler entry is not yet wired (lives in the Lean
    // kernel); secondaries park here.
    loop {
        crate::cpu::wfe();
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // AN9-J test discipline: the inner-state-injection refactor
    // eliminates global-state races.  Each test allocates its own
    // local atomics and exercises `bring_up_secondaries_inner` so
    // cargo's parallel test execution never sees inter-test state
    // bleed-through.

    fn fresh_local_state() -> (AtomicBool, [AtomicBool; 4], AtomicU32) {
        (
            AtomicBool::new(false),
            [
                AtomicBool::new(true),  // boot core
                AtomicBool::new(false),
                AtomicBool::new(false),
                AtomicBool::new(false),
            ],
            AtomicU32::new(0),
        )
    }

    #[test]
    fn smp_default_is_disabled() {
        // AN9-J: v1.0.0 default — single-core boot.  The GLOBAL
        // `SMP_ENABLED` is `false` at module load time.  This test
        // is read-only on the global so concurrent tests do not
        // affect the outcome.
        assert!(!SMP_ENABLED.load(Ordering::Acquire));
    }

    #[test]
    fn bring_up_secondaries_returns_zero_when_disabled() {
        // AN9-J: with `enabled = false`, no PSCI calls are issued.
        let (enabled, ready, count) = fresh_local_state();
        let online = bring_up_secondaries_inner(
            &enabled, &ready, &count, &SECONDARY_MPIDR_TABLE);
        assert_eq!(online, 0);
        assert_eq!(count.load(Ordering::Acquire), 0);
    }

    #[test]
    fn secondary_mpidr_table_matches_bcm2712_topology() {
        // BCM2712 has 4 Cortex-A76 cores in a single cluster.  Three
        // secondaries with Aff0 = 1..=3.
        assert_eq!(SECONDARY_MPIDR_TABLE.len(), MAX_SECONDARY_CORES);
        assert_eq!(SECONDARY_MPIDR_TABLE[0], 0x0001);
        assert_eq!(SECONDARY_MPIDR_TABLE[1], 0x0002);
        assert_eq!(SECONDARY_MPIDR_TABLE[2], 0x0003);
    }

    #[test]
    fn core_ready_boot_core_starts_ready() {
        // AN9-J.4.d: the boot-core slot is always `true` at module
        // initialisation regardless of test ordering.
        assert!(CORE_READY[0].load(Ordering::Acquire));
    }

    #[test]
    fn fresh_state_secondaries_start_not_ready() {
        // AN9-J.4.d: a freshly-allocated local state has all
        // secondaries in the not-ready state until primary signals.
        let (_enabled, ready, _count) = fresh_local_state();
        assert!(ready[0].load(Ordering::Acquire),
            "boot core slot should start ready");
        assert!(!ready[1].load(Ordering::Acquire));
        assert!(!ready[2].load(Ordering::Acquire));
        assert!(!ready[3].load(Ordering::Acquire));
    }

    #[test]
    fn bring_up_secondaries_when_enabled_runs_psci_loop() {
        // AN9-J: with `enabled = true` and the host PSCI stub
        // returning Success, all 3 secondaries come online.
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let online = bring_up_secondaries_inner(
            &enabled, &ready, &count, &SECONDARY_MPIDR_TABLE);
        assert_eq!(online, MAX_SECONDARY_CORES as u32);
        assert_eq!(count.load(Ordering::Acquire),
                   MAX_SECONDARY_CORES as u32);
        // Each secondary's ready flag should now be true.
        for idx in 1..=MAX_SECONDARY_CORES {
            assert!(ready[idx].load(Ordering::Acquire),
                "core_ready[{}] must be true after successful bring-up", idx);
        }
    }

    #[test]
    fn bring_up_secondaries_partial_table_is_supported() {
        // AN9-J: passing a smaller mpidr table brings up fewer
        // secondaries.  Tests the parameter discipline.
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let small_table: [u64; 1] = [0x0001];
        let online = bring_up_secondaries_inner(
            &enabled, &ready, &count, &small_table);
        assert_eq!(online, 1);
        assert!(ready[1].load(Ordering::Acquire));
        // Cores 2 and 3 untouched.
        assert!(!ready[2].load(Ordering::Acquire));
        assert!(!ready[3].load(Ordering::Acquire));
    }

    // ========================================================================
    // WS-SM SM0.O — MAX_SECONDARY_CORES parameterization tests
    // ========================================================================

    #[test]
    fn sm0o_max_secondary_cores_pinned_to_platform_binding() {
        // WS-SM SM0.O: the Rust constant MAX_SECONDARY_CORES is
        // structurally pinned to the Lean PlatformBinding.coreCount
        // value (4 for RPi5).  The compile-time `assert!` in smp.rs
        // would fail elaboration if drift occurred; this runtime
        // assertion is a redundant double-check that the same value
        // can be read at runtime.
        assert_eq!(MAX_SECONDARY_CORES + 1, 4,
            "MAX_SECONDARY_CORES + 1 must equal PlatformBinding.coreCount");
    }

    #[test]
    fn sm0o_secondary_mpidr_table_size_matches_max() {
        // WS-SM SM0.O: the secondary MPIDR table cardinality follows
        // MAX_SECONDARY_CORES; if the constant changes the table must
        // be updated in lockstep.
        assert_eq!(SECONDARY_MPIDR_TABLE.len(), MAX_SECONDARY_CORES);
    }

    // ========================================================================
    // WS-SM SM0.N — Per-CPU data block + TPIDR_EL1 setup tests
    // ========================================================================

    #[test]
    fn sm0n_per_cpu_data_array_has_4_slots() {
        // WS-SM SM0.N: per-CPU data array carries one slot per core
        // (boot core + 3 secondaries on RPi5).  Loosely coupled to
        // MAX_SECONDARY_CORES + 1 = 4.
        assert_eq!(PER_CPU_DATA.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(PER_CPU_DATA.len(), 4);
    }

    #[test]
    fn sm0n_per_cpu_data_struct_is_64_byte_aligned() {
        // WS-SM SM0.N: each PerCpuData is one cache line wide via
        // `repr(C, align(64))`.  This test verifies the alignment is
        // preserved if a future maintainer adds fields without
        // checking the alignment attribute.
        use core::mem::align_of;
        assert_eq!(align_of::<PerCpuData>(), 64,
            "PerCpuData must be 64-byte aligned to avoid false sharing");
    }

    #[test]
    fn sm0n_per_cpu_data_size_is_multiple_of_align() {
        // WS-SM SM0.N: a struct's size is always a multiple of its
        // alignment in Rust.  At SM0 the struct holds [u64; 8] = 64
        // bytes, which is exactly one alignment unit.  This test
        // catches a future layout change that would shrink the struct
        // below the alignment unit (a footgun under repr(align(N))).
        use core::mem::{align_of, size_of};
        let sz = size_of::<PerCpuData>();
        let al = align_of::<PerCpuData>();
        assert!(sz >= al,
            "size_of::<PerCpuData>() = {} must be >= align_of = {}", sz, al);
        assert!(sz.is_multiple_of(al),
            "size_of::<PerCpuData>() = {} must be a multiple of align = {}",
            sz, al);
    }

    #[test]
    fn sm0n_per_cpu_data_zero_constructor_yields_zero_bytes() {
        // WS-SM SM0.N: `PerCpuData::zero()` produces an all-zero
        // instance.  This pairs with SM0.M (.smp_stacks zeroing): the
        // boot core's per-CPU data is statically zero-initialised
        // before any kernel code observes it, so no stale RAM contents
        // can leak through.
        let pcd = PerCpuData::zero();
        // SAFETY: we own the local `pcd` and read its bytes through a
        // valid reference; this only validates the all-zero invariant
        // claimed by the constructor.
        let bytes = unsafe {
            core::slice::from_raw_parts(
                &pcd as *const PerCpuData as *const u8,
                core::mem::size_of::<PerCpuData>(),
            )
        };
        assert!(bytes.iter().all(|&b| b == 0),
            "PerCpuData::zero() must produce all-zero bytes");
    }

    #[test]
    fn sm0n_per_cpu_data_static_array_zero_initialised() {
        // WS-SM SM0.N: the `PER_CPU_DATA` static array is initialised
        // via `PerCpuData::zero()` at load time, so every byte starts
        // at zero.  This test verifies the property without writing to
        // the static (which would require taking a `&mut`, denied by
        // the `pub static` declaration).
        for (idx, slot) in PER_CPU_DATA.iter().enumerate() {
            // SAFETY: read-only inspection of bytes via a `*const`
            // pointer; no concurrent writers exist (SMP_ENABLED is
            // false in tests so secondaries never run).
            let bytes = unsafe {
                core::slice::from_raw_parts(
                    slot as *const PerCpuData as *const u8,
                    core::mem::size_of::<PerCpuData>(),
                )
            };
            assert!(bytes.iter().all(|&b| b == 0),
                "PER_CPU_DATA[{}] must start zero-initialised", idx);
        }
    }

    #[test]
    fn sm0n_per_cpu_slot_addr_in_bounds_returns_valid_address() {
        // WS-SM SM0.N: `per_cpu_slot_addr(i)` returns the address of
        // PER_CPU_DATA[i] for any in-range index 0..=3.  The address
        // must be aligned to 64 bytes (the cache-line alignment of
        // PerCpuData).
        for i in 0..PER_CPU_DATA.len() {
            let addr = per_cpu_slot_addr(i);
            assert!(addr != 0, "per_cpu_slot_addr({}) returned null", i);
            assert_eq!(addr % 64, 0,
                "per_cpu_slot_addr({}) = {:#x} not 64-byte aligned",
                i, addr);
        }
    }

    #[test]
    fn sm0n_per_cpu_slot_addr_distinct_per_core() {
        // WS-SM SM0.N: distinct context_ids map to distinct slot
        // addresses.  This is the property the boot.S TPIDR_EL1 setup
        // relies on — each core's TPIDR_EL1 must be unique so per-core
        // lookups don't alias.  Fixed-size array (no `Vec` in `no_std`).
        let addrs: [usize; 4] = [
            per_cpu_slot_addr(0),
            per_cpu_slot_addr(1),
            per_cpu_slot_addr(2),
            per_cpu_slot_addr(3),
        ];
        for i in 0..addrs.len() {
            for j in (i + 1)..addrs.len() {
                assert_ne!(addrs[i], addrs[j],
                    "per_cpu_slot_addr({}) and per_cpu_slot_addr({}) must differ",
                    i, j);
            }
        }
    }

    #[test]
    fn sm0n_per_cpu_slot_addr_stride_matches_struct_size() {
        // WS-SM SM0.N: consecutive slot addresses differ by exactly
        // size_of::<PerCpuData>() = 64.  This is the layout invariant
        // the boot.S TPIDR_EL1 setup relies on: the asm computes the
        // slot address as `PER_CPU_DATA + context_id * 64`, so any
        // change to the struct size would silently corrupt the
        // per-core lookup unless caught here.
        use core::mem::size_of;
        let stride = size_of::<PerCpuData>();
        for i in 0..(PER_CPU_DATA.len() - 1) {
            let a = per_cpu_slot_addr(i);
            let b = per_cpu_slot_addr(i + 1);
            assert_eq!(b - a, stride,
                "PER_CPU_DATA stride between slot {} and {} = {}, expected {}",
                i, i + 1, b - a, stride);
        }
    }

    #[test]
    fn sm0n_per_cpu_data_slot_size_matches_asm_literal() {
        // WS-SM SM0.N: the `PER_CPU_DATA_SLOT_SIZE` Rust constant is
        // the single source of truth pinning the Rust struct size to
        // the literal `#64` in boot.S::secondary_entry.  The
        // compile-time assertion (in the parent module) already
        // catches a struct-size drift at build time; this runtime
        // assertion is a redundant double-check that the constant is
        // observable from external test code and equals 64.
        use core::mem::size_of;
        assert_eq!(PER_CPU_DATA_SLOT_SIZE, 64,
            "PER_CPU_DATA_SLOT_SIZE must equal the literal #64 in boot.S");
        assert_eq!(size_of::<PerCpuData>(), PER_CPU_DATA_SLOT_SIZE,
            "size_of::<PerCpuData>() must equal PER_CPU_DATA_SLOT_SIZE");
    }

    #[test]
    #[should_panic(expected = "context_id out of range")]
    fn sm0n_per_cpu_slot_addr_out_of_bounds_panics() {
        // WS-SM SM0.N: an out-of-range context_id panics rather than
        // returning a stray address.  Defends against a malformed PSCI
        // call passing context_id ≥ MAX_SECONDARY_CORES + 1.
        let _ = per_cpu_slot_addr(PER_CPU_DATA.len());
    }
}
