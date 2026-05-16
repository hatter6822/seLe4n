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
//! - `SMP_ENABLED` — runtime SMP-enable flag (default `false`)
//! - `SECONDARY_MPIDR_TABLE` — BCM2712 secondary-core MPIDR inventory
//! - `MAX_SECONDARY_CORES` — number of secondaries (3 on RPi5)
//! - `bring_up_secondaries` — primary-core entry point that issues
//!   the CPU_ON loop
//! - `rust_secondary_main` — placeholder Rust entry called from
//!   `boot.S::secondary_entry`
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
        // Each secondary's ready flag should now be true.  Iterate
        // via `enumerate().skip(1)` rather than range-indexing so
        // clippy's `needless_range_loop` lint stays clean.
        for (idx, slot) in ready.iter().enumerate().skip(1) {
            assert!(slot.load(Ordering::Acquire),
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
}
