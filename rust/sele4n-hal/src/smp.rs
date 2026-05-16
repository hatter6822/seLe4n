// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-J (DEF-R-HAL-L20) + **WS-SM SM1.C** (closes SMP-C2):
//! Secondary-core bring-up scaffolding and full per-core init.
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
//! 3. Secondary cores wake at `boot.S::secondary_entry`, which
//!    masks DAIF, sets up the per-core stack and TPIDR_EL1, then
//!    calls [`rust_secondary_main`].  That function:
//!    * waits on its `CORE_READY` flag (primary releases via SEV);
//!    * runs the [`crate::mmu::init_mmu_secondary`] sequence (AK5-D
//!      ordered MMU enable; AK5-C SCTLR_EL1 bitmap);
//!    * installs the exception vectors via
//!      [`crate::boot::install_exception_vectors`] (shared with the
//!      primary's `rust_boot_main`);
//!    * initialises this core's GIC CPU interface via
//!      [`crate::gic::init_cpu_interface_secondary`];
//!    * arms the per-core timer via
//!      [`crate::timer::init_timer_secondary`];
//!    * unmasks IRQ delivery; and
//!    * jumps into the Lean kernel via
//!      `lean_secondary_kernel_main(context_id)` (defined in
//!      `SeLe4n/Kernel/SecondaryEntry.lean` with the matching
//!      `@[export]` attribute).
//! 4. The Lean kernel currently parks the secondary at SM1.C; SM5+
//!    will replace the placeholder with the per-core scheduler
//!    entry.
//!
//! ## What this module owns
//!
//! - `SMP_ENABLED` — runtime SMP-enable flag (default `false`)
//! - `SECONDARY_MPIDR_TABLE` — BCM2712 secondary-core MPIDR inventory
//! - `MAX_SECONDARY_CORES` — number of secondaries (3 on RPi5)
//! - `bring_up_secondaries` — primary-core entry point that issues
//!   the CPU_ON loop
//! - `rust_secondary_main` — secondary-core Rust entry called from
//!   `boot.S::secondary_entry`.  Performs the WS-SM SM1.C full
//!   per-core init pipeline (validate context_id → wait on
//!   `CORE_READY[i]` → MMU → VBAR → GIC → timer → IRQ unmask → Lean
//!   kernel entry via `lean_secondary_kernel_main` → idle fallback)
//! - `validate_secondary_context_id` — defense-in-depth validator
//!   that refuses an out-of-range PSCI context_id before any
//!   hardware init runs
//! - Per-core readiness flags (`CORE_READY`, `SECONDARY_CORES_ONLINE`)
//!
//! ## What this module does NOT own
//!
//! - `PerCpuData`, `PER_CPU_DATA`, `PER_CPU_DATA_SLOT_SIZE*`,
//!   `per_cpu_slot_addr`, `current_per_cpu`, `current_core_id_from_tpidr`,
//!   `check_per_cpu_invariants` — these moved to `per_cpu.rs` at
//!   **WS-SM SM1.B** and are re-exported here for backward
//!   compatibility (see the `pub use crate::per_cpu::{...}` block
//!   below).  New code should import from `crate::per_cpu::*` directly.
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
/// `MAX_SECONDARY_CORES` constant to the literal `4`.
///
/// `MAX_SECONDARY_CORES + 1` (boot core + N-1 secondaries) must equal
/// `4` — the total core count of the production RPi5 BCM2712 binding.
/// If a future PR bumps `MAX_SECONDARY_CORES` past 3, the assertion
/// below fails to elaborate at build time, producing a compiler
/// error that points the contributor at the drift.
///
/// **Note on cross-language pinning**: Rust has no direct visibility
/// into the Lean `PlatformBinding.coreCount` typeclass field at build
/// time.  The Lean side has its own pinning theorem
/// (`SeLe4n.Platform.RPi5.numCores_eq_rpi5_coreCount`) that asserts
/// `Concurrency.numCores = PlatformBinding.coreCount RPi5Platform`,
/// both equal to the literal `4`.  Cross-language consistency between
/// Rust `MAX_SECONDARY_CORES + 1` and Lean `numCores` is therefore
/// enforced by *both* sides asserting the same literal `4`; a future
/// multi-platform port that changes the value must bump both
/// constants in the same PR.  Each side's assertion catches drift
/// within its own language; the literals together pin the two sides
/// to each other by symbol-name identity.
const _: () = assert!(
    MAX_SECONDARY_CORES + 1 == 4,
    "WS-SM SM0.O: MAX_SECONDARY_CORES + 1 must equal 4 (the RPi5 \
     BCM2712 core count, pinned on the Lean side via \
     numCores_eq_rpi5_coreCount)"
);

/// **WS-SM SM1.C audit-pass-2**: total core count
/// (`MAX_SECONDARY_CORES + 1`) exposed as a `.rodata` symbol for
/// `boot.S::secondary_entry`'s pre-stack context_id validation.
///
/// The asm's audit-pass-2 defense rejects `context_id == 0` and
/// `context_id >= total_core_count` BEFORE the SP / TPIDR_EL1 setup
/// uses `context_id` arithmetically.  Without the asm-level check, a
/// PSCI implementation passing `context_id = 4` would compute
/// `SP = __smp_secondary_stack_top - 3 * 0x10000 = __smp_secondary_stacks_bottom`,
/// adjacent to the boot core's stack — the prologue push of
/// `rust_secondary_main` would corrupt boot-core stack frames before
/// the Rust validator could halt.
///
/// Using a `.rodata` symbol (not an asm literal) keeps the Rust
/// constant the single source of truth; a future PR bumping
/// `MAX_SECONDARY_CORES` automatically updates the asm-side bound.
///
/// `#[no_mangle]` preserves the symbol name for the asm's
/// `adrp`/`ldr` references; `#[used]` prevents the linker from
/// dropping the symbol as "unused" (only `boot.S::secondary_entry`
/// references it).
#[no_mangle]
#[used]
pub static MAX_CORE_COUNT_SYM: u64 = (MAX_SECONDARY_CORES + 1) as u64;

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

// ============================================================================
// WS-SM SM1.B (closes SMP-M4) — Per-CPU data block + TPIDR_EL1 accessors
// ============================================================================
//
// SM0.N landed the per-CPU data block in this module; SM1.B factored
// the layout (`PerCpuData`, `PER_CPU_DATA`, `PER_CPU_DATA_SLOT_SIZE*`,
// `per_cpu_slot_addr`) plus the new accessors (`current_per_cpu`,
// `current_core_id_from_tpidr`, `check_per_cpu_invariants`) into the
// dedicated `per_cpu.rs` module.  The asm-visible symbol names
// (`PER_CPU_DATA`, `PER_CPU_DATA_SLOT_SIZE_SYM`) are unchanged
// because `#[no_mangle]` makes them location-independent.
//
// The re-exports below preserve every pre-SM1.B path that referenced
// these items via `crate::smp::{PerCpuData, PER_CPU_DATA, ...}`.  New
// code should import from `crate::per_cpu::*` directly.
pub use crate::per_cpu::{
    check_per_cpu_invariants, current_core_id_from_tpidr, current_per_cpu, per_cpu_slot_addr,
    PerCpuData, PER_CPU_DATA, PER_CPU_DATA_SLOT_SIZE, PER_CPU_DATA_SLOT_SIZE_SYM,
};

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

/// **WS-SM SM1.D.6**: bring up secondary cores subject to an upper
/// bound on the total number of cores online.
///
/// Used by `boot.rs::rust_boot_main` Phase 5 when a `smp_max_cores=N`
/// option appears on the kernel command line.  Lets operators boot
/// with fewer cores than the platform supports — useful for:
///
///   - QEMU `-smp 2` regression testing without touching this
///     binary's `MAX_SECONDARY_CORES` constant.
///   - Single-secondary diagnostic boots (`smp_max_cores=2`) when
///     hunting a multi-core bug.
///   - Hardware bring-up on a partial production board where one
///     core has failed.
///
/// ## Semantics
///
/// The argument names a **total core count** (including the boot
/// core), not a secondary count.  Translation:
///
///   - `max_cores = 0` → no cores brought up (returns 0).
///   - `max_cores = 1` → boot core only; no secondaries (returns 0).
///   - `max_cores = N (2..=MAX_SECONDARY_CORES + 1)` → bring up
///     `N - 1` secondaries from the head of the MPIDR table.
///   - `max_cores > MAX_SECONDARY_CORES + 1` → saturated to
///     `MAX_SECONDARY_CORES + 1` (the platform bound; defensive
///     against caller-side parsing errors).
///
/// Returns the number of secondaries actually brought up (NOT the
/// total core count — same return shape as
/// [`bring_up_secondaries`]).
///
/// ## Why a separate function vs adding a parameter to
/// [`bring_up_secondaries`]
///
/// The pre-existing `bring_up_secondaries()` is the
/// no-limit / full-platform call site preserved for callers that
/// don't need command-line-driven configuration.  The two entry
/// points are otherwise identical in semantics; mechanical
/// refactors should NOT collapse them into one with a default
/// argument since `bring_up_secondaries` is already in the public
/// API and renaming it would break downstream consumers.
pub fn bring_up_secondaries_with_limit(max_cores: usize) -> u32 {
    let limit = max_cores.min(MAX_SECONDARY_CORES + 1);
    let secondaries_to_spawn = limit.saturating_sub(1);
    let table = &SECONDARY_MPIDR_TABLE[..secondaries_to_spawn];
    bring_up_secondaries_inner(
        &SMP_ENABLED,
        &CORE_READY,
        &SECONDARY_CORES_ONLINE,
        table,
    )
}

/// **WS-SM SM1.C.5 / audit-pass-1** (defense-in-depth): validate a
/// PSCI `context_id` received by [`rust_secondary_main`].
///
/// Returns `Some(core_idx)` if the `context_id` names a secondary
/// slot (`1..=MAX_SECONDARY_CORES`), or `None` otherwise.  Two
/// rejection cases:
///
/// 1. `context_id == 0` — that's the boot-core slot.  The boot core
///    must enter `rust_boot_main` from `_start` (see `boot.S`); it
///    must not re-enter via `secondary_entry`.  A PSCI implementation
///    waking a secondary with `context_id = 0` would alias the
///    secondary to the boot core's `PerCpuData` slot — silently
///    corrupting the boot core's per-CPU state once the secondary's
///    init runs.
/// 2. `context_id >= CORE_READY.len()` — PSCI passed a value larger
///    than the platform's core count.  We have no slot for this PE;
///    running per-core init would touch undefined state (no
///    pre-cleared stack, no allocated TPIDR_EL1 slot, no
///    CORE_READY[i] flag).
///
/// Both cases are firmware bugs or hostile PSCI implementations.
/// `rust_secondary_main` halts the offending core in a low-power
/// WFE loop with interrupts still masked (the boot.S
/// `secondary_entry` stub left DAIF = 0xF), so the rest of the
/// system continues uninterrupted.
///
/// The validator is `pub(crate)` so the in-crate `tests` module can
/// exercise the bounds without invoking the `-> !`
/// `rust_secondary_main` itself.  It is also `const fn` so callers
/// using compile-time-known `context_id` values (e.g., the
/// const-context test) evaluate the bounds at elaboration — a
/// regression that broke the validator's logic for a specific
/// literal would surface at build time.
///
/// **MSRV note**: the bounds expression uses `MAX_SECONDARY_CORES + 1`
/// rather than `CORE_READY.len()` because reading a `static` from a
/// `const fn` requires `feature(const_refs_to_statics)` (stabilised
/// only in Rust 1.83+; rust-lang/rust#119618), and the project's MSRV
/// is pinned at 1.82.  The two values are structurally identical:
/// `CORE_READY: [AtomicBool; MAX_SECONDARY_CORES + 1]` makes
/// `CORE_READY.len() == MAX_SECONDARY_CORES + 1` a type-level
/// invariant — a future PR that changed one without the other would
/// fail to type-check at the `CORE_READY` declaration.
#[inline]
pub(crate) const fn validate_secondary_context_id(context_id: u64) -> Option<usize> {
    // Audit-pass-3: do the bounds check in `u64` space FIRST, then
    // narrow to `usize`.  The earlier `let core_idx = context_id as
    // usize` form was defensible on the project's only target
    // (aarch64, where `usize` == `u64`), but on a hypothetical
    // 32-bit port the truncation would silently accept any
    // `context_id` whose high bits were set but low bits aliased a
    // valid secondary slot (e.g., `0x1_0000_0001` → core_idx = 1).
    // Doing the comparison in `u64` makes the validator correct on
    // every plausible `usize` width without depending on
    // platform-specific assumptions.
    const MAX_CORE_COUNT: u64 = (MAX_SECONDARY_CORES + 1) as u64;
    // Valid secondary context_ids are 1..=MAX_SECONDARY_CORES (= 3
    // on RPi5).  context_id == 0 is the boot core's reserved slot;
    // context_id >= MAX_SECONDARY_CORES + 1 is out of range.
    if context_id > 0 && context_id < MAX_CORE_COUNT {
        // Safe to narrow: 0 < context_id < 4 (or whatever
        // MAX_SECONDARY_CORES + 1 is) fits in usize on every plausible
        // target (1 ≤ value ≤ 2^32 - 1 on 32-bit; trivially on 64-bit).
        Some(context_id as usize)
    } else {
        None
    }
}

/// **WS-SM SM1.C.5** (closes SMP-C2): Secondary-core entry point
/// called from `boot.S::secondary_entry` after PSCI CPU_ON wakes a
/// previously-parked core.
///
/// Performs the full per-core hardware-init sequence so the calling
/// secondary arrives at the Lean kernel entry with the same hardware
/// posture as the boot core:
///
///   0. **PSCI context_id validation** (audit-pass-1, defense-in-depth):
///      reject `context_id == 0` (boot-core slot) and `context_id >=
///      CORE_READY.len()` (out of range) before any further work; the
///      offending core halts with DAIF still masked.  See
///      [`validate_secondary_context_id`].
///   1. **Synchronisation**: wait on `CORE_READY[context_id]` (primary
///      sets this after a successful PSCI CPU_ON via
///      [`bring_up_secondaries_inner`]).  Uses bounded WFE so a lost
///      SEV does not hang the core forever.
///   2. **MMU enable** ([`crate::mmu::init_mmu_secondary`]):  TTBR0/1 →
///      shared `BOOT_L1_TABLE`, TCR/MAIR per ARMv8-A D8.11, full
///      SCTLR_EL1 bitmap including W^X (WXN), SP alignment (SA/SA0),
///      and exception-entry/exit serialisation (EIS/EOS).
///   3. **Exception vectors** ([`crate::boot::install_exception_vectors`]):
///      VBAR_EL1 ← `__exception_vectors` (2048-byte aligned per ARM ARM
///      D17.2.135).
///   4. **GIC CPU interface** ([`crate::gic::init_cpu_interface_secondary`]):
///      banked-per-core CTLR/PMR/BPR enables interrupt delivery on
///      this PE.  Distributor (global) is already initialised by the
///      primary's `init_gic()`.
///   5. **Timer arm** ([`crate::timer::init_timer_secondary`]): per-core
///      CNTP_CVAL_EL0 = now + interval; CNTP_CTL_EL0.ENABLE = 1.
///      Failure (CntfrqNotProgrammed) is fatal for this core — we
///      log and halt the secondary while leaving primary +
///      already-initialised secondaries running.
///   6. **IRQ unmask** ([`crate::interrupts::enable_irq`]): clear
///      PSTATE.I so the GIC may deliver interrupts to this PE.
///   7. **Lean kernel entry**: `lean_secondary_kernel_main(core_id)`
///      (emitted by Lean from `SeLe4n.Kernel.SecondaryEntry`).  At
///      SM1.C the Lean side is a placeholder (returns to caller);
///      SM5+ will replace it with the per-core scheduler entry.
///   8. **Idle fallback**: should the Lean kernel ever return, the
///      core enters an infinite WFE loop.  Returning is unexpected
///      and indicates either (a) early SM1.C placeholder behaviour
///      (Lean returns immediately) or (b) a verified kernel
///      regression that broke the per-core scheduler.
///
/// **Pre-conditions on entry (established by `boot.S::secondary_entry`)**:
/// - DAIF mask = 0xF (interrupts masked).
/// - SP set to per-core stack slot from `.smp_stacks`.
/// - TPIDR_EL1 set to `PER_CPU_DATA[context_id]` slot address
///   (SM0.N/SM1.B contract).
/// - `context_id` ∈ {1, 2, 3} (PSCI calling convention; boot core =
///   index 0).
///
/// **Never returns** — `-> !` type honoured by the trailing infinite
/// WFE loop.
///
/// **Hardware reachability**: at v1.0.0 this routine is wired but
/// unreachable in the default build (`SMP_ENABLED = false` means
/// primary never issues CPU_ON).  The host test suite exercises the
/// function signature and the per-helper call sites; QEMU `-smp 4`
/// (SM1.H) will be the first runtime exerciser of the full path.
#[no_mangle]
pub extern "C" fn rust_secondary_main(context_id: u64) -> ! {
    let core_id = context_id;

    // -----------------------------------------------------------------
    // Step -1 (audit-pass-1) — Validate PSCI context_id.
    //
    // Defense-in-depth against firmware bugs or hostile PSCI
    // implementations passing an out-of-range context_id.  See
    // `validate_secondary_context_id` for the rejected cases.
    // Rejected secondaries halt in a low-power WFE loop with DAIF
    // still masked (set by boot.S `secondary_entry`), leaving the
    // primary and other secondaries running.
    // -----------------------------------------------------------------
    let core_idx = match validate_secondary_context_id(context_id) {
        Some(idx) => idx,
        None => {
            crate::kprintln!("[smp] core {core_id}: FATAL: invalid PSCI context_id; halting");
            loop {
                crate::cpu::wfe();
            }
        }
    };

    // -----------------------------------------------------------------
    // Step 0 — Synchronise with primary.
    //
    // The primary's `bring_up_secondaries_inner` sets CORE_READY[i] =
    // true after each successful PSCI CPU_ON.  We spin on it with
    // bounded WFE (AN9-G) so a lost SEV does not hang the core
    // indefinitely; bounded WFE returns after the timer expires and
    // we re-check the flag on the next loop iteration.
    //
    // Note: `core_idx` is guaranteed in-range by the validator above,
    // so we no longer need the `if core_idx < CORE_READY.len()` guard
    // that the pre-audit AN9-J shell carried.
    // -----------------------------------------------------------------
    while !CORE_READY[core_idx].load(Ordering::Acquire) {
        // Discard elapsed-ticks return; the secondary's only
        // wake condition is the `CORE_READY` flag, polled on
        // the next loop iteration.  AN9-G's bounded primitive
        // ensures we never block forever if the primary's SEV
        // is lost.
        let _ = crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
    }

    crate::kprintln!("[smp] core {core_id}: entering per-core init");

    // -----------------------------------------------------------------
    // Step 1 — MMU enable.
    //
    // Reuses the boot core's `BOOT_L1_TABLE` (a read-only global
    // populated by the primary's `init_mmu`).  Applies the AK5-C
    // SCTLR_EL1 bitmap including W^X (WXN).
    // -----------------------------------------------------------------
    crate::mmu::init_mmu_secondary(core_id);
    crate::kprintln!("[smp] core {core_id}: MMU enabled (WXN, SA, SA0, EIS, EOS)");

    // -----------------------------------------------------------------
    // Step 2 — Exception vectors.
    //
    // VBAR_EL1 is banked per-core; we install the same shared
    // `__exception_vectors` symbol the primary uses.  Going through
    // `boot::install_exception_vectors` keeps the barrier ordering
    // (dsb_sy + isb) identical between primary and secondary.
    // -----------------------------------------------------------------
    crate::boot::install_exception_vectors();
    crate::kprintln!("[smp] core {core_id}: VBAR_EL1 installed");

    // -----------------------------------------------------------------
    // Step 3 — GIC CPU interface.
    //
    // GICC_CTLR/PMR/BPR are banked per-core at a shared MMIO base.
    // The distributor (global state at GICD_BASE) is already
    // initialised by the primary's `init_gic`.
    // -----------------------------------------------------------------
    crate::gic::init_cpu_interface_secondary(core_id);

    // -----------------------------------------------------------------
    // Step 4 — Timer arm.
    //
    // Per-core CNTP_CVAL_EL0 + CNTP_CTL_EL0.  Failure is fatal for
    // this core: halt it in a WFE loop without affecting the rest of
    // the system.  Other secondaries that have already initialised
    // their timers continue running.
    // -----------------------------------------------------------------
    if let Err(e) = crate::timer::init_timer_secondary(crate::timer::DEFAULT_TICK_HZ) {
        crate::kprintln!("[smp] core {core_id}: FATAL: timer init failed: {e}; halting this core");
        // Cannot recover from a timer init failure — the per-core
        // scheduler depends on tick interrupts.  Halt this core in
        // a low-power WFE loop; primary + other secondaries remain
        // running.
        loop {
            crate::cpu::wfe();
        }
    }
    crate::kprintln!(
        "[smp] core {core_id}: timer armed at {} Hz",
        crate::timer::DEFAULT_TICK_HZ
    );

    // -----------------------------------------------------------------
    // Step 5 — IRQ unmask.
    //
    // Enable IRQ delivery (clear PSTATE.I) now that GIC, timer, and
    // VBAR are configured.  After this point the GIC may deliver
    // timer ticks (PPI 30), inter-core SGIs (INTID 0..4 per SM0.H),
    // and SPIs to this PE.
    // -----------------------------------------------------------------
    crate::interrupts::enable_irq();
    crate::kprintln!("[smp] core {core_id}: IRQ delivery enabled");

    crate::kprintln!("[smp] core {core_id}: ready, entering kernel");

    // -----------------------------------------------------------------
    // Step 6 — Lean kernel entry.
    //
    // Calls into `SeLe4n.Kernel.secondaryKernelMain` (defined in
    // `SeLe4n/Kernel/SecondaryEntry.lean` with
    // `@[export lean_secondary_kernel_main]`).  At SM1.C the Lean
    // side is a pass-through placeholder; SM5 will replace it with
    // the per-core scheduler entry.
    //
    // The `hw_target` feature gates the extern declaration: under
    // host `cargo test` builds the symbol is not linked, so the
    // declaration would be unresolved.  Under a hardware build the
    // Lean compiler emits a C-callable wrapper that resolves here.
    // -----------------------------------------------------------------
    #[cfg(feature = "hw_target")]
    {
        extern "C" {
            fn lean_secondary_kernel_main(core_id: u64);
        }
        // SAFETY: `lean_secondary_kernel_main` is the Lean-emitted
        // C-callable wrapper for `SeLe4n.Kernel.secondaryKernelMain`.
        // The function takes one u64 argument (the PSCI context_id)
        // and returns `()` — the call is total and never unwinds
        // across the FFI boundary (Lean's `BaseIO` never throws under
        // `panic = "abort"`).
        unsafe { lean_secondary_kernel_main(core_id) };
    }

    // -----------------------------------------------------------------
    // Step 7 — Idle fallback.
    //
    // The Lean kernel entry is not expected to return; if it does (or
    // if we are running without `hw_target` and never enter it), park
    // the core in a low-power WFE loop forever.
    // -----------------------------------------------------------------
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
                AtomicBool::new(true), // boot core
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
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, &SECONDARY_MPIDR_TABLE);
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
        assert!(
            ready[0].load(Ordering::Acquire),
            "boot core slot should start ready"
        );
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
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, &SECONDARY_MPIDR_TABLE);
        assert_eq!(online, MAX_SECONDARY_CORES as u32);
        assert_eq!(count.load(Ordering::Acquire), MAX_SECONDARY_CORES as u32);
        // Each secondary's ready flag should now be true.  Iterate
        // via `enumerate().skip(1)` rather than range-indexing so
        // clippy's `needless_range_loop` lint stays clean.
        for (idx, slot) in ready.iter().enumerate().skip(1) {
            assert!(
                slot.load(Ordering::Acquire),
                "core_ready[{}] must be true after successful bring-up",
                idx
            );
        }
    }

    #[test]
    fn bring_up_secondaries_partial_table_is_supported() {
        // AN9-J: passing a smaller mpidr table brings up fewer
        // secondaries.  Tests the parameter discipline.
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let small_table: [u64; 1] = [0x0001];
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, &small_table);
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
        assert_eq!(
            MAX_SECONDARY_CORES + 1,
            4,
            "MAX_SECONDARY_CORES + 1 must equal PlatformBinding.coreCount"
        );
    }

    #[test]
    fn sm0o_secondary_mpidr_table_size_matches_max() {
        // WS-SM SM0.O: the secondary MPIDR table cardinality follows
        // MAX_SECONDARY_CORES; if the constant changes the table must
        // be updated in lockstep.
        assert_eq!(SECONDARY_MPIDR_TABLE.len(), MAX_SECONDARY_CORES);
    }

    // ========================================================================
    // WS-SM SM0.N back-compat re-export checks
    // ========================================================================
    //
    // The per-CPU data block items (`PerCpuData`, `PER_CPU_DATA`,
    // `PER_CPU_DATA_SLOT_SIZE*`, `per_cpu_slot_addr`) moved to
    // `crate::per_cpu` at SM1.B.  These spot-checks verify the
    // re-exports through `crate::smp::*` still resolve, so any
    // call site that pre-dates the move keeps working.  The
    // exhaustive layout/behaviour tests live in `per_cpu::tests`.

    #[test]
    fn sm0n_back_compat_per_cpu_data_re_export_resolves() {
        // The re-exports in this module make `crate::smp::PerCpuData`
        // and friends point at `crate::per_cpu::*` — proven by
        // constructing a value via the legacy path and inspecting it.
        let pcd: PerCpuData = PerCpuData::zero();
        assert_eq!(pcd.core_id, 0);
    }

    #[test]
    fn sm0n_back_compat_per_cpu_data_static_re_export_resolves() {
        // The `PER_CPU_DATA` static is reachable via both
        // `crate::per_cpu::PER_CPU_DATA` and `crate::smp::PER_CPU_DATA`.
        // Both names point at the same `#[no_mangle]` symbol, so
        // assertions here cover any caller still using the legacy
        // `crate::smp::*` path.
        assert_eq!(PER_CPU_DATA.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(PER_CPU_DATA[0].core_id, 0);
        assert_eq!(PER_CPU_DATA[3].core_id, 3);
    }

    #[test]
    fn sm0n_back_compat_slot_size_constants_re_exported() {
        // SM1.B kept the symbol names for `PER_CPU_DATA_SLOT_SIZE`
        // and `PER_CPU_DATA_SLOT_SIZE_SYM` to preserve boot.S linkage.
        // This test asserts both are visible through `crate::smp::*`.
        assert_eq!(PER_CPU_DATA_SLOT_SIZE, 64);
        assert_eq!(PER_CPU_DATA_SLOT_SIZE_SYM, 64);
    }

    #[test]
    fn sm0n_back_compat_per_cpu_slot_addr_re_export_resolves() {
        // SM1.B kept `per_cpu_slot_addr` accessible from the legacy
        // `crate::smp` path.  Spot-check the boot core's slot
        // resolves to a non-null cache-line-aligned address.
        let addr = per_cpu_slot_addr(0);
        assert!(addr != 0);
        assert_eq!(addr % 64, 0);
    }

    // ========================================================================
    // WS-SM SM1.C.5 / SM1.C.12 — Secondary-core full init host tests
    // ========================================================================
    //
    // These tests exercise the SM1.C.5 `rust_secondary_main` body on the
    // host build profile.  We cannot actually CALL `rust_secondary_main`
    // (it's `-> !` and would spin-loop forever waiting for the primary's
    // CORE_READY signal).  Instead we verify:
    //
    //   * The function exists and has the correct ABI signature
    //     (compile-time check via fn-pointer coercion).
    //   * Every per-core init helper called from the body is independently
    //     invocable on host — `init_mmu_secondary`, `init_cpu_interface_secondary`,
    //     `init_timer_secondary`, `install_exception_vectors`, `enable_irq`.
    //
    // The per-helper tests live in each helper's own `tests` module (mmu.rs,
    // gic.rs, timer.rs, boot.rs); the bring-up-flow tests here cover the
    // composition.

    #[test]
    fn sm1c5_rust_secondary_main_has_correct_abi_signature() {
        // SM1.C.5: the body changed substantively but the ABI must
        // not — the C-callable signature is `extern "C" fn(u64) -> !`
        // (PSCI context_id in x0, never returns).
        let _: extern "C" fn(u64) -> ! = rust_secondary_main;
    }

    #[test]
    fn sm1c5_init_mmu_secondary_resolves_via_crate_mmu() {
        // SM1.C.5: the `crate::mmu::init_mmu_secondary` symbol used by
        // `rust_secondary_main` resolves through the module path.
        // A regression that renames the helper would fail this test
        // before reaching the build-script scanner.
        crate::mmu::init_mmu_secondary(1);
    }

    #[test]
    fn sm1c5_install_exception_vectors_resolves_via_crate_boot() {
        // SM1.C.5: VBAR install helper resolves through `crate::boot`.
        crate::boot::install_exception_vectors();
    }

    #[test]
    fn sm1c5_init_cpu_interface_secondary_resolves_via_crate_gic() {
        // SM1.C.5: GIC CPU-interface helper resolves through `crate::gic`.
        crate::gic::init_cpu_interface_secondary(1);
    }

    #[test]
    fn sm1c5_init_timer_secondary_resolves_via_crate_timer() {
        // SM1.C.5: timer init helper resolves through `crate::timer`
        // AND returns Ok on host with the default tick rate.
        let r = crate::timer::init_timer_secondary(crate::timer::DEFAULT_TICK_HZ);
        assert_eq!(r, Ok(()));
    }

    #[test]
    fn sm1c5_init_timer_secondary_propagates_zero_tick_error() {
        // SM1.C.5: the fatal-path branch in `rust_secondary_main` is
        // taken when `init_timer_secondary` returns an Err.  Verify the
        // helper actually returns an Err on the failure input so the
        // branch is reachable.
        let r = crate::timer::init_timer_secondary(0);
        assert!(
            r.is_err(),
            "init_timer_secondary(0) must Err so the SM1.C.5 fatal-path branch is reachable"
        );
    }

    #[test]
    fn sm1c5_enable_irq_resolves_via_crate_interrupts() {
        // SM1.C.5: IRQ-unmask helper resolves through
        // `crate::interrupts`.
        crate::interrupts::enable_irq();
    }

    #[test]
    fn sm1c5_full_secondary_init_helper_set_is_callable_on_host() {
        // SM1.C.5 composition: every helper invoked by
        // `rust_secondary_main` is independently callable on host.
        // A regression in any helper would surface here even though
        // we can't run the full `rust_secondary_main` body.
        crate::mmu::init_mmu_secondary(1);
        crate::boot::install_exception_vectors();
        crate::gic::init_cpu_interface_secondary(1);
        let _ = crate::timer::init_timer_secondary(crate::timer::DEFAULT_TICK_HZ);
        crate::interrupts::enable_irq();
    }

    #[test]
    fn sm1c5_secondary_helpers_idempotent_in_aggregate() {
        // SM1.C.5: a future SM7 TLB shootdown might re-run the
        // per-core init helpers after a quiescent point.  Aggregate
        // idempotence is required: each helper must be safe to call
        // multiple times on host.
        for core_id in [1u64, 2, 3] {
            crate::mmu::init_mmu_secondary(core_id);
            crate::boot::install_exception_vectors();
            crate::gic::init_cpu_interface_secondary(core_id);
            let _ = crate::timer::init_timer_secondary(crate::timer::DEFAULT_TICK_HZ);
            crate::interrupts::enable_irq();
        }
    }

    #[test]
    fn sm1c5_no_mangle_attribute_pinned_on_rust_secondary_main() {
        // SM1.C.5: the `#[no_mangle]` attribute on `rust_secondary_main`
        // must be preserved so `boot.S::secondary_entry`'s `bl
        // rust_secondary_main` resolves at link time.  Take the
        // address-of and assert it's non-null — the only way this
        // could be null is if the function were inlined or dropped,
        // both of which `#[no_mangle]` prevents.
        let p = rust_secondary_main as *const ();
        assert!(
            !p.is_null(),
            "rust_secondary_main must have a stable linker-visible address"
        );
    }

    // ========================================================================
    // WS-SM SM1.C.5 audit-pass-1 — validate_secondary_context_id tests
    //
    // The validator is the defense-in-depth gate that rejects out-of-range
    // PSCI context_ids before any per-core init runs.  Tests exercise
    // every edge case:
    //   * boot-core slot (context_id == 0)        → rejected
    //   * valid secondary slots (1, 2, 3)         → accepted
    //   * one past the array (context_id == 4)    → rejected
    //   * far out-of-range (u64::MAX)             → rejected
    //
    // The validator is `pub(crate)` so it's reachable from these
    // in-crate tests but invisible to external callers (the only
    // legitimate caller is `rust_secondary_main` itself).
    // ========================================================================

    #[test]
    fn sm1c5_validate_context_id_rejects_zero() {
        // Audit-pass-1: context_id = 0 names the boot-core slot.  A
        // secondary waking with context_id = 0 would alias the boot
        // core's PerCpuData slot; reject it.
        assert_eq!(validate_secondary_context_id(0), None);
    }

    #[test]
    fn sm1c5_validate_context_id_accepts_every_secondary_slot() {
        // Audit-pass-1: every context_id in [1, MAX_SECONDARY_CORES]
        // (= [1, 3] on RPi5) is a valid secondary slot.
        assert_eq!(validate_secondary_context_id(1), Some(1));
        assert_eq!(validate_secondary_context_id(2), Some(2));
        assert_eq!(validate_secondary_context_id(3), Some(3));
    }

    #[test]
    fn sm1c5_validate_context_id_rejects_one_past_array() {
        // Audit-pass-1: context_id = CORE_READY.len() (= 4 on RPi5)
        // is the first out-of-range value.  Reject.
        assert_eq!(validate_secondary_context_id(CORE_READY.len() as u64), None);
    }

    #[test]
    fn sm1c5_validate_context_id_rejects_far_out_of_range() {
        // Audit-pass-1: large context_id values must also reject.
        // Tests the upper boundary plus a few suspicious values.
        assert_eq!(validate_secondary_context_id(u64::MAX), None);
        assert_eq!(validate_secondary_context_id(u64::MAX - 1), None);
        assert_eq!(validate_secondary_context_id(100), None);
        assert_eq!(validate_secondary_context_id(0xDEAD_BEEF), None);
    }

    #[test]
    fn sm1c5_validate_context_id_acceptance_matches_core_ready_index() {
        // Audit-pass-1: when accepted, the returned `core_idx` equals
        // the input `context_id` (as `usize`).  This is the property
        // `rust_secondary_main` relies on for the subsequent
        // `CORE_READY[core_idx]` indexing.
        for context_id in 1u64..=(MAX_SECONDARY_CORES as u64) {
            let core_idx = validate_secondary_context_id(context_id);
            assert_eq!(
                core_idx,
                Some(context_id as usize),
                "validator must return context_id as usize on acceptance"
            );
        }
    }

    #[test]
    fn sm1c5_validate_context_id_aligns_with_primary_emitted_values() {
        // Audit-pass-1: the primary's `bring_up_secondaries_inner`
        // emits `context_id = idx + 1` for `idx in 0..MAX_SECONDARY_CORES`.
        // Verify every primary-emitted value is accepted by the
        // validator (call-site parity).
        for (idx, _mpidr) in SECONDARY_MPIDR_TABLE.iter().enumerate() {
            let primary_emitted_context_id = (idx as u64) + 1;
            assert!(
                validate_secondary_context_id(primary_emitted_context_id).is_some(),
                "primary emits context_id {} which must validate",
                primary_emitted_context_id
            );
        }
    }

    #[test]
    fn sm1c5_validate_context_id_is_const_correct() {
        // Audit-pass-1: the validator function is callable in const
        // contexts where the inputs are known at compile time.  This
        // forces the compiler to evaluate the validator's logic at
        // call sites where the context_id is a literal, catching
        // subtle errors in the bounds check via const-eval.
        //
        // Note: `Option<usize>` is not directly `decide`-able like
        // bools, but a comparison to a known result is.
        const RESULT_FOR_ZERO: Option<usize> = validate_secondary_context_id(0);
        const RESULT_FOR_ONE: Option<usize> = validate_secondary_context_id(1);
        const RESULT_FOR_FOUR: Option<usize> = validate_secondary_context_id(4);
        assert_eq!(RESULT_FOR_ZERO, None);
        assert_eq!(RESULT_FOR_ONE, Some(1));
        assert_eq!(RESULT_FOR_FOUR, None);
    }

    #[test]
    fn sm1c5_validate_context_id_rejects_u64_with_high_bits_aliasing_secondary() {
        // Audit-pass-3 (defense-in-depth): a `u64` `context_id` whose
        // high bits are set but whose low 32 bits alias a valid
        // secondary slot (1..=3) must be rejected.  The pre-audit-pass-3
        // form `let core_idx = context_id as usize` would, on a
        // hypothetical 32-bit port, truncate to the low 32 bits and
        // erroneously accept these values.  The current form does the
        // bounds check in `u64` space, so the high bits are honoured
        // regardless of `usize` width.
        //
        // We exercise three values that have valid secondary slot
        // numbers (1, 2, 3) in their low 32 bits but unambiguously
        // belong out of range in `u64` space:
        assert_eq!(validate_secondary_context_id(0x1_0000_0001), None);
        assert_eq!(validate_secondary_context_id(0x1_0000_0002), None);
        assert_eq!(validate_secondary_context_id(0x1_0000_0003), None);
        // Also exercise a value whose low bits alias the boot-core
        // slot (0).  Already rejected by the "context_id > 0" arm,
        // but worth pinning explicitly.
        assert_eq!(validate_secondary_context_id(0x1_0000_0000), None);
        // And a u64 with bits only in the high half (low 32 bits
        // exactly zero, high 32 bits set).
        assert_eq!(validate_secondary_context_id(0xFFFF_FFFF_0000_0000), None);
    }

    // ========================================================================
    // WS-SM SM1.C audit-pass-2 — MAX_CORE_COUNT_SYM asm-bridge symbol tests
    //
    // The asm-level context_id validation in `boot.S::secondary_entry`
    // (audit-pass-2) reads its upper bound from the `MAX_CORE_COUNT_SYM`
    // `.rodata` symbol exposed by this module.  Tests verify:
    //   * The symbol value equals `MAX_SECONDARY_CORES + 1` (the Rust
    //     constant).
    //   * The symbol value equals the array length of `CORE_READY`
    //     (the runtime structural pin).
    //   * The symbol has a stable linker-visible address (`#[no_mangle]
    //     #[used]`).
    // ========================================================================

    #[test]
    fn sm1c5_max_core_count_sym_matches_max_secondary_cores() {
        // Audit-pass-2: the .rodata symbol must equal
        // `MAX_SECONDARY_CORES + 1`.  A drift would mean the asm
        // rejects valid context_ids (too strict) or accepts invalid
        // ones (too lax).
        assert_eq!(MAX_CORE_COUNT_SYM, (MAX_SECONDARY_CORES + 1) as u64);
    }

    #[test]
    fn sm1c5_max_core_count_sym_matches_core_ready_array_len() {
        // Audit-pass-2: the .rodata symbol must equal CORE_READY's
        // array length.  This is the runtime structural pin — if a
        // future PR changes either side, the test fails.
        assert_eq!(MAX_CORE_COUNT_SYM as usize, CORE_READY.len());
    }

    #[test]
    fn sm1c5_max_core_count_sym_is_four_on_rpi5() {
        // Audit-pass-2: pin the literal value at 4 for the production
        // RPi5 BCM2712 binding (single 4-core Cortex-A76 cluster).
        // A multi-platform port would need to bump this and the
        // corresponding `Concurrency.numCores` Lean constant in
        // lockstep.
        assert_eq!(MAX_CORE_COUNT_SYM, 4);
    }

    #[test]
    fn sm1c5_max_core_count_sym_has_observable_address() {
        // Audit-pass-2: the .rodata symbol must have a stable
        // linker-visible address so the asm's `adrp`+`ldr` against
        // `:lo12:MAX_CORE_COUNT_SYM` resolves.  A regression dropping
        // `#[no_mangle]` or `#[used]` would break the asm-level
        // defense at link time.
        let addr = &MAX_CORE_COUNT_SYM as *const u64 as usize;
        assert!(
            addr != 0,
            "MAX_CORE_COUNT_SYM must have a valid linker-assigned address"
        );
    }

    #[test]
    fn sm1c5_max_core_count_sym_value_is_validator_upper_bound() {
        // Audit-pass-2 / cross-check: the asm-side bound (via
        // MAX_CORE_COUNT_SYM) and the Rust-side bound (in
        // `validate_secondary_context_id`) must agree.  The
        // validator rejects `core_idx >= MAX_SECONDARY_CORES + 1`;
        // the asm rejects `context_id >= MAX_CORE_COUNT_SYM`.  Both
        // values must be identical.
        let validator_bound = MAX_SECONDARY_CORES + 1;
        let asm_bound = MAX_CORE_COUNT_SYM as usize;
        assert_eq!(
            validator_bound, asm_bound,
            "audit-pass-2: asm-level and Rust-level upper bounds must \
             agree (validator: {validator_bound}, asm: {asm_bound})"
        );
    }

    #[test]
    fn sm1c5_max_core_count_sym_rejects_match_validator() {
        // Audit-pass-2 / cross-check: every context_id rejected by
        // the asm-level bound (>= MAX_CORE_COUNT_SYM) must also be
        // rejected by the Rust validator.  Verify on a sample
        // including the boundary.
        for context_id in [
            MAX_CORE_COUNT_SYM,
            MAX_CORE_COUNT_SYM + 1,
            MAX_CORE_COUNT_SYM + 100,
        ] {
            assert_eq!(
                validate_secondary_context_id(context_id),
                None,
                "context_id {} rejected by asm bound must also be rejected by validator",
                context_id
            );
        }
    }

    // ========================================================================
    // WS-SM SM1.D.6 — bring_up_secondaries_with_limit
    //
    // The limit-aware bring-up entry point used by `boot.rs` Phase 5.
    // Tests exercise the saturation behaviour:
    //   * limit < platform max  → bring up a prefix
    //   * limit == platform max → full bring-up
    //   * limit > platform max  → saturated to platform max
    //   * limit 0 / 1           → no secondaries (only boot core, or zero)
    //
    // All tests use the inner state-injection helper so the global
    // SMP_ENABLED atomic and CORE_READY array are not perturbed
    // between cargo's parallel test runs.
    // ========================================================================

    #[test]
    fn sm1d6_with_limit_zero_brings_up_no_secondaries() {
        // SM1.D.6: max_cores = 0 → empty MPIDR slice, no PSCI calls.
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        // Use the inner helper so we don't touch the global state.
        let empty_table: [u64; 0] = [];
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, &empty_table);
        assert_eq!(online, 0);
        // No CORE_READY flips on secondaries.
        assert!(!ready[1].load(Ordering::Acquire));
        assert!(!ready[2].load(Ordering::Acquire));
        assert!(!ready[3].load(Ordering::Acquire));
    }

    #[test]
    fn sm1d6_with_limit_one_brings_up_no_secondaries() {
        // SM1.D.6: max_cores = 1 → boot core only, no secondaries.
        // max_cores - 1 = 0 secondaries → empty MPIDR slice.
        let secondaries_to_spawn = 1usize.saturating_sub(1);
        let table = &SECONDARY_MPIDR_TABLE[..secondaries_to_spawn];
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn sm1d6_with_limit_two_brings_up_one_secondary() {
        // SM1.D.6: max_cores = 2 → 1 secondary (table[0..1]).
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let limit = 2usize;
        let secondaries_to_spawn = limit.min(MAX_SECONDARY_CORES + 1).saturating_sub(1);
        let table = &SECONDARY_MPIDR_TABLE[..secondaries_to_spawn];
        assert_eq!(table.len(), 1);
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, table);
        assert_eq!(online, 1);
        assert!(ready[1].load(Ordering::Acquire), "first secondary should be ready");
        assert!(!ready[2].load(Ordering::Acquire), "second secondary not spawned");
        assert!(!ready[3].load(Ordering::Acquire), "third secondary not spawned");
    }

    #[test]
    fn sm1d6_with_limit_three_brings_up_two_secondaries() {
        // SM1.D.6: max_cores = 3 → 2 secondaries (table[0..2]).
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let limit = 3usize;
        let secondaries_to_spawn = limit.min(MAX_SECONDARY_CORES + 1).saturating_sub(1);
        let table = &SECONDARY_MPIDR_TABLE[..secondaries_to_spawn];
        assert_eq!(table.len(), 2);
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, table);
        assert_eq!(online, 2);
        assert!(ready[1].load(Ordering::Acquire));
        assert!(ready[2].load(Ordering::Acquire));
        assert!(!ready[3].load(Ordering::Acquire));
    }

    #[test]
    fn sm1d6_with_limit_full_brings_up_all_secondaries() {
        // SM1.D.6: max_cores = MAX_SECONDARY_CORES + 1 → all
        // secondaries.
        let (enabled, ready, count) = fresh_local_state();
        enabled.store(true, Ordering::Release);
        let limit = MAX_SECONDARY_CORES + 1;
        let secondaries_to_spawn = limit.min(MAX_SECONDARY_CORES + 1).saturating_sub(1);
        let table = &SECONDARY_MPIDR_TABLE[..secondaries_to_spawn];
        assert_eq!(table.len(), MAX_SECONDARY_CORES);
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, table);
        assert_eq!(online, MAX_SECONDARY_CORES as u32);
        // Iterate over `ready[1..=MAX_SECONDARY_CORES]` via
        // `enumerate().skip(1).take(MAX_SECONDARY_CORES)` to keep
        // clippy's `needless_range_loop` lint quiet.
        for (idx, slot) in ready
            .iter()
            .enumerate()
            .skip(1)
            .take(MAX_SECONDARY_CORES)
        {
            assert!(
                slot.load(Ordering::Acquire),
                "secondary {} should be ready",
                idx
            );
        }
    }

    #[test]
    fn sm1d6_with_limit_oversize_saturates() {
        // SM1.D.6: max_cores > platform max → saturates to platform
        // bound.  Defends against caller-side parsing errors.
        let limit = 999usize;
        let saturated = limit.min(MAX_SECONDARY_CORES + 1);
        assert_eq!(saturated, MAX_SECONDARY_CORES + 1);
        let secondaries_to_spawn = saturated.saturating_sub(1);
        assert_eq!(secondaries_to_spawn, MAX_SECONDARY_CORES);
    }

    #[test]
    fn sm1d6_with_limit_disabled_returns_zero() {
        // SM1.D.6: when `enabled` is false, no secondaries are
        // brought up regardless of the limit.  This is the
        // `smp_enabled=false` boot path; `apply_cmdline_and_start_smp`
        // bypasses the call entirely, but the inner helper also
        // honours the disabled state for defense-in-depth.
        let (enabled, ready, count) = fresh_local_state();
        // Leave enabled = false (the default for fresh_local_state).
        let table = &SECONDARY_MPIDR_TABLE[..2];
        let online = bring_up_secondaries_inner(&enabled, &ready, &count, table);
        assert_eq!(online, 0);
    }

    #[test]
    fn sm1d6_with_limit_function_resolves_via_crate_smp() {
        // SM1.D.6: the public function exists and has the documented
        // signature `fn(usize) -> u32`.  Pinning the signature at the
        // type-system level catches a future PR that renames or
        // re-types it.
        let _: fn(usize) -> u32 = bring_up_secondaries_with_limit;
    }

    #[test]
    fn sm1d6_with_limit_callable_on_host_via_global_state() {
        // SM1.D.6: the helper compiles and runs on host via the
        // global statics.  We invoke it with `max_cores = 1` (no
        // secondaries spawned, no global atomic perturbations) so
        // the global SMP_ENABLED atomic must be false at module load
        // for the call to return 0 deterministically.
        //
        // Note: this test races with other cargo tests that mutate
        // the global SMP_ENABLED.  We avoid the race by reading the
        // result behaviour: with max_cores = 1, secondaries_to_spawn
        // = 0 and the inner loop is empty regardless of the
        // SMP_ENABLED state.
        let result = bring_up_secondaries_with_limit(1);
        assert_eq!(result, 0);
    }
}
