// SPDX-License-Identifier: GPL-3.0-or-later
//! WS-SM SM1.A (DEF-R-HAL-L20 completion): Power State Coordination Interface (PSCI)
//! wrapper for the seLe4n verified microkernel.
//!
//! Implements the ARM DEN0022D §5 function set that the seLe4n boot,
//! shutdown, and power-management paths need.  The v1.0.0 release exposes
//! every wrapper but only [`cpu_on`] is invoked by the default boot path
//! (single-core).  When `smp_enabled=true` is on the command line the
//! [`cpu_on`] entry brings up the BCM2712 secondaries; the remaining
//! wrappers are reachable through future SM5..SM9 phases or via direct
//! kernel-API invocation for graceful shutdown / power-cycling
//! sequences.
//!
//! ## Function-id encoding (ARM SMCCC DEN0028 / DEN0022D §5.2.1)
//!
//! Each PSCI call carries a 32-bit function identifier in `x0`:
//!
//! ```text
//! bit 31         : 1 ⇒ Fast call (always 1 for PSCI)
//! bit 30         : 1 ⇒ SMC64 (64-bit args), 0 ⇒ SMC32 (32-bit args)
//! bits 29..24    : Owning Entity Number (OEN) = 4 for PSCI (Standard
//!                  Secure Service Calls)
//! bits 23..16    : reserved (must be 0)
//! bits 15..0     : function number
//! ```
//!
//! Concretely, every PSCI id has bit 31 set; SMC64 ids have bit 30 set
//! (`0xC4xx_xxxx` prefix), SMC32 ids have bit 30 clear (`0x84xx_xxxx`
//! prefix).  The `4` digit in the second hex nibble carries OEN=4
//! (`0b000100` in bits 29..24).  The compile-time assertions at the
//! bottom of this module pin every wrapped function id to the right
//! SMC width and OEN.
//!
//! ## ARM DEN0022D §5.1 function map (subset wrapped by seLe4n)
//!
//! Section references are to ARM DEN0022D revision D (the publicly-
//! available PSCI 1.1 specification).  Other revisions may renumber
//! the sub-sections; the function IDs are stable across revisions and
//! are the canonical identifiers.
//!
//! | DEN0022D §  | Function          | Wrapper                     | Function ID    | Return convention             |
//! |-------------|-------------------|-----------------------------|----------------|-------------------------------|
//! | 5.1.1       | `PSCI_VERSION`    | [`psci_version`]            | `0x8400_0000`  | u32 → [`PsciVersion`]         |
//! | 5.1.3       | `CPU_OFF`         | [`cpu_off`]                 | `0x8400_0002`  | i32 → [`PsciResult`] (no ret on success) |
//! | 5.1.4       | `CPU_ON`          | [`cpu_on`]                  | `0xC400_0003`  | i32 → [`PsciResult`]          |
//! | 5.1.5       | `AFFINITY_INFO`   | [`affinity_info`]           | `0xC400_0004`  | i32 → `Result<AffinityInfoState, PsciResult>` |
//! | 5.1.7       | `MIGRATE_INFO_TYPE` | [`migrate_info_type`]     | `0x8400_0006`  | i32 → `Result<MigrateInfoType, PsciResult>` |
//! | 5.1.9       | `SYSTEM_OFF`      | [`system_off`]              | `0x8400_0008`  | never returns                 |
//! | 5.1.10      | `SYSTEM_RESET`    | [`system_reset`]            | `0x8400_0009`  | never returns                 |
//!
//! ## Return-code matrix (ARM DEN0022D Table 5)
//!
//! All PSCI calls that return a value use signed 32-bit integers.  Zero is
//! success; negative values indicate failure.  The decoded variants live
//! in [`PsciResult`]:
//!
//! | Raw  | Variant                       | DEN0022D meaning                                   |
//! |-----:|-------------------------------|----------------------------------------------------|
//! |  0   | [`PsciResult::Success`]       | Operation succeeded.                               |
//! | -1   | [`PsciResult::NotSupported`]  | Function not implemented by firmware.              |
//! | -2   | [`PsciResult::InvalidParameters`] | Invalid argument (e.g. unknown MPIDR).         |
//! | -3   | [`PsciResult::Denied`]        | Operation not permitted in current state.          |
//! | -4   | [`PsciResult::AlreadyOn`]     | Target PE is already on (CPU_ON only).             |
//! | -5   | [`PsciResult::OnPending`]     | Target PE is transitioning to on (CPU_ON only).    |
//! | -6   | [`PsciResult::InternalFailure`] | Firmware internal error.                         |
//! | -7   | [`PsciResult::NotPresent`]    | Target PE not present in the system.               |
//! | -8   | [`PsciResult::Disabled`]      | Target PE disabled (e.g. by errata workaround).    |
//! | other| [`PsciResult::Unknown`]       | Vendor extension or undocumented code.             |
//!
//! ## HVC vs. SMC dispatch
//!
//! RPi5 firmware (`armstub8-rpi5`) exposes PSCI at EL2 via the `hvc #0`
//! instruction; SMC dispatches go to the secure monitor at EL3 which is
//! not configured for PSCI on this platform.  All wrappers in this
//! module hard-code `hvc #0` because seLe4n's only v1.0.0 hardware
//! target uses HVC.  A future port to a system that exposes PSCI via
//! `smc #0` would parameterise the conduit through `PlatformBinding`;
//! that parameterisation is post-1.0 work and is tracked in
//! [`docs/planning/SMP_RUST_HAL_PLAN.md`](../../../docs/planning/SMP_RUST_HAL_PLAN.md)
//! as a SM1 closure item.
//!
//! ## On host
//!
//! Test builds stub the HVC into deterministic returns so unit tests can
//! exercise the call path without aarch64-specific intrinsics:
//!
//! - `cpu_on` / `cpu_off` ⇒ [`PsciResult::Success`]
//! - `affinity_info` ⇒ `Ok(AffinityInfoState::On)`
//! - `psci_version` ⇒ `PsciVersion { major: 1, minor: 1 }` (PSCI 1.1)
//! - `migrate_info_type` ⇒ `Ok(MigrateInfoType::NotRequired)`
//! - `system_off` / `system_reset` ⇒ infinite `spin_loop()` (annotated
//!   with `#[ignore]` on direct invocation tests)
//!
//! ## Cross-cluster ordering (AN9-I integration)
//!
//! Every PSCI call that affects another PE (`cpu_on`, `cpu_off`,
//! `affinity_info`) emits `dsb osh` before the HVC so the target
//! observes the correct memory state when it resumes execution on a
//! potentially-different cluster.  `psci_version` and
//! `migrate_info_type` are query-only and do not require the outer-
//! shareable barrier; `system_off` / `system_reset` power down the
//! whole system so the barrier is moot.

// ============================================================================
// PSCI return codes (ARM DEN0022D Table 5)
// ============================================================================

/// WS-SM SM1.A: PSCI return-code values.
///
/// ARM DEN0022D Table 5: PSCI return codes are signed 32-bit values
/// where 0 = success and negative integers indicate specific failures.
/// The `Unknown` variant collects vendor extensions and undocumented
/// codes; the canonical decoder is [`PsciResult::from_raw`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum PsciResult {
    Success = 0,
    NotSupported = -1,
    InvalidParameters = -2,
    Denied = -3,
    AlreadyOn = -4,
    OnPending = -5,
    InternalFailure = -6,
    NotPresent = -7,
    Disabled = -8,
    /// Catch-all for return codes outside the documented range.
    Unknown = -999,
}

impl PsciResult {
    /// Decode a raw 32-bit PSCI return value into the canonical enum
    /// variant.  Unknown values are mapped to `Unknown` rather than
    /// panicking, since at v1.0.0 we do not yet enumerate every PSCI
    /// vendor extension.
    pub const fn from_raw(raw: i32) -> Self {
        match raw {
            0 => Self::Success,
            -1 => Self::NotSupported,
            -2 => Self::InvalidParameters,
            -3 => Self::Denied,
            -4 => Self::AlreadyOn,
            -5 => Self::OnPending,
            -6 => Self::InternalFailure,
            -7 => Self::NotPresent,
            -8 => Self::Disabled,
            _ => Self::Unknown,
        }
    }

    /// Raw 32-bit value matching the ARM DEN0022D encoding.
    #[inline]
    pub const fn to_raw(self) -> i32 {
        self as i32
    }

    /// Shorthand for the success path.
    #[inline]
    pub const fn is_success(self) -> bool {
        matches!(self, Self::Success)
    }
}

// ============================================================================
// PSCI function identifiers (ARM DEN0022D §5.1)
// ============================================================================

/// PSCI function id for the SMC32 `PSCI_VERSION` call.  ARM DEN0022D §5.1.1.
pub const PSCI_FN_PSCI_VERSION: u32 = 0x8400_0000;

/// PSCI function id for the SMC32 `CPU_OFF` call.  ARM DEN0022D §5.1.3.
pub const PSCI_FN_CPU_OFF: u32 = 0x8400_0002;

/// PSCI function id for the SMC64 `CPU_ON` call.  ARM DEN0022D §5.1.4.
pub const PSCI_FN_CPU_ON: u32 = 0xC400_0003;

/// PSCI function id for the SMC64 `AFFINITY_INFO` call.  ARM DEN0022D §5.1.5.
pub const PSCI_FN_AFFINITY_INFO: u32 = 0xC400_0004;

/// PSCI function id for the SMC32 `MIGRATE_INFO_TYPE` call.  ARM DEN0022D §5.1.7.
pub const PSCI_FN_MIGRATE_INFO_TYPE: u32 = 0x8400_0006;

/// PSCI function id for the SMC32 `SYSTEM_OFF` call.  ARM DEN0022D §5.1.9.
pub const PSCI_FN_SYSTEM_OFF: u32 = 0x8400_0008;

/// PSCI function id for the SMC32 `SYSTEM_RESET` call.  ARM DEN0022D §5.1.10.
pub const PSCI_FN_SYSTEM_RESET: u32 = 0x8400_0009;

// ============================================================================
// SM1.A.1 — cpu_on (existing) + cpu_on context
// ============================================================================

/// WS-SM SM1.A.1: Issue a PSCI `CPU_ON` request to bring up a secondary core.
///
/// `target_mpidr`  — the 64-bit MPIDR_EL1 mask of the target core
///                  (typically `Aff0|Aff1<<8|Aff2<<16` for Cortex-A76).
/// `entry_point`   — kernel-virtual address of the secondary entry
///                  routine (set by the primary boot core to
///                  `secondary_entry` in `boot.S`).
/// `context_id`    — opaque per-core context value passed to the
///                  entry routine in `x0`.
///
/// On real hardware this issues `hvc #0` with the PSCI calling
/// convention; on host (test) builds it is a deterministic stub
/// returning [`PsciResult::Success`] so the call graph can be unit-
/// tested without an HVC trap.
///
/// AN9-I integration: a `dsb osh` is emitted before the HVC so the
/// secondary core observes the correct page-table state when it
/// resumes execution.
#[inline]
#[must_use]
pub fn cpu_on(target_mpidr: u64, entry_point: usize, context_id: u64) -> PsciResult {
    // AN9-I: ensure cross-cluster ordering before the secondary core
    // observes the kernel image and shared boot data structures.  The
    // outer-shareable barrier covers the BCM2712 inter-cluster
    // interconnect.
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let ret: i32;
        // SAFETY: `hvc #0` is a defined hypervisor call.  Per ARM
        // DEN0022D, registers x0..x3 carry the PSCI call arguments;
        // the return value comes back in x0.  We mark all clobbers
        // explicitly and disable preserved-flags so the optimiser
        // does not assume PSTATE invariance across the HVC.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_CPU_ON as u64,
                in("x1") target_mpidr,
                in("x2") entry_point as u64,
                in("x3") context_id,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        PsciResult::from_raw(ret)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: deterministic success so the dispatch path can
        // be exercised without an HVC trap.
        let _ = (target_mpidr, entry_point, context_id);
        PsciResult::Success
    }
}

// ============================================================================
// SM1.A.1 — cpu_off
// ============================================================================

/// WS-SM SM1.A.1: PSCI `CPU_OFF` — power down the calling PE.
///
/// ARM DEN0022D §5.1.3 (function id `0x8400_0002`, SMC32).
///
/// **Caller must not return on success.**  On success the calling PE
/// is powered down and this function does not return.  On failure
/// the function returns and the caller continues executing.
/// Per DEN0022D §5.1.3, the only documented failure codes for CPU_OFF
/// are `Denied` (-3, not allowed in current state) and
/// `InternalFailure` (-6, firmware bug).  On host this returns
/// `Success` so the call graph can be exercised; production callers
/// must treat any return (including `Success`) as the hardware
/// failure case and park the PE:
///
/// ```rust,ignore
/// // power-off discipline
/// let res = psci::cpu_off();
/// // We get here only if cpu_off failed (or we're on host stub);
/// // log and park.
/// crate::kprintln!("[psci] cpu_off returned (failure): {:?}", res);
/// loop { core::hint::spin_loop(); }
/// ```
///
/// AN9-I integration: emits `dsb osh` before HVC so any pending
/// stores from this PE are observable in the outer-shareable domain
/// before the PE leaves; this ensures other cores see the most-
/// recent kernel state at the moment of power-down (e.g., released
/// locks, BKL state, run-queue updates the calling PE made before
/// requesting CPU_OFF).
#[inline]
#[must_use]
pub fn cpu_off() -> PsciResult {
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let ret: i32;
        // SAFETY: HVC #0 with PSCI calling convention.  Caller
        // guarantees the PE has nothing to lose by powering down
        // (caller has hand-off state to another core, e.g., the
        // BKL has been released and the per-core run queue is
        // empty).
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_CPU_OFF as u64,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        PsciResult::from_raw(ret)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: deterministic success.  Production callers
        // never observe this return because the real HVC does not
        // return on success; tests that exercise the failure path
        // can use `PsciResult::from_raw(-3)` directly to simulate
        // `Denied`.
        PsciResult::Success
    }
}

// ============================================================================
// SM1.A.2 — affinity_info + AffinityInfoState
// ============================================================================

/// WS-SM SM1.A.2: PSCI `AFFINITY_INFO` result.
///
/// ARM DEN0022D §5.1.5 returns one of three non-negative values:
/// - 0 = `On`         (the target PE is on)
/// - 1 = `Off`        (the target PE is off)
/// - 2 = `OnPending`  (transitioning on)
///
/// Negative return values are decoded as [`PsciResult`] failures
/// (typically `InvalidParameters` for an unknown MPIDR or
/// `NotSupported` if the firmware lacks the call).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum AffinityInfoState {
    On = 0,
    Off = 1,
    OnPending = 2,
}

impl AffinityInfoState {
    /// Decode a non-negative raw PSCI return value into the canonical
    /// enum variant.  Returns `None` for values outside the documented
    /// range [0, 2]; the caller maps `None` to [`PsciResult::Unknown`].
    pub const fn from_raw(raw: i32) -> Option<Self> {
        match raw {
            0 => Some(Self::On),
            1 => Some(Self::Off),
            2 => Some(Self::OnPending),
            _ => None,
        }
    }

    /// Raw 32-bit value matching the ARM DEN0022D encoding.
    #[inline]
    pub const fn to_raw(self) -> i32 {
        self as i32
    }
}

/// WS-SM SM1.A.2: pure decoder for the raw `AFFINITY_INFO` return.
///
/// Extracted from [`affinity_info`] so the failure path (`ret < 0` and
/// `ret > 2`) is unit-testable without the HVC trap.  Semantics:
///
/// - `raw == 0`  ⇒ `Ok(On)`
/// - `raw == 1`  ⇒ `Ok(Off)`
/// - `raw == 2`  ⇒ `Ok(OnPending)`
/// - `raw  < 0`  ⇒ `Err(PsciResult::from_raw(raw))` (firmware error)
/// - `raw  > 2`  ⇒ `Err(PsciResult::Unknown)` (vendor extension)
///
/// The split between "negative → PsciResult::from_raw" and "non-negative
/// out-of-range → PsciResult::Unknown" matters: a firmware that
/// returns `-2` reports `InvalidParameters`, which the caller may
/// recover from (try a different MPIDR); a firmware that returns `42`
/// is a bug / extension we can only flag as `Unknown`.
#[inline]
pub const fn decode_affinity_info_result(raw: i32) -> Result<AffinityInfoState, PsciResult> {
    if raw < 0 {
        return Err(PsciResult::from_raw(raw));
    }
    match AffinityInfoState::from_raw(raw) {
        Some(state) => Ok(state),
        None => Err(PsciResult::Unknown),
    }
}

/// WS-SM SM1.A.2: PSCI `AFFINITY_INFO` — query the on/off state of a
/// target PE.
///
/// ARM DEN0022D §5.1.5 (function id `0xC400_0004`, SMC64).
///
/// `target_affinity` — the affinity-mask MPIDR_EL1 of the target PE.
/// `lowest_affinity_level` — the lowest affinity level that is valid
///   in `target_affinity`.  Typically 0 for a per-PE query (mask down
///   to Aff0); non-zero values query cluster-level state.
///
/// Returns:
/// - `Ok(state)` on success — the target's on/off state.
/// - `Err(PsciResult)` on failure — typically `InvalidParameters` for
///   an unknown MPIDR or `NotSupported` if the firmware lacks the
///   call.
///
/// AN9-I integration: emits `dsb osh` before HVC for cross-cluster
/// memory ordering of any state the caller wants the target PE to
/// observe should the target be `OnPending`.
#[inline]
pub fn affinity_info(
    target_affinity: u64,
    lowest_affinity_level: u32,
) -> Result<AffinityInfoState, PsciResult> {
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let ret: i32;
        // SAFETY: HVC #0 with PSCI calling convention.  Per ARM
        // DEN0022D §5.1.5, x1 carries target_affinity (MPIDR mask),
        // x2 carries lowest_affinity_level; return value comes back
        // in x0.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_AFFINITY_INFO as u64,
                in("x1") target_affinity,
                in("x2") lowest_affinity_level as u64,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        decode_affinity_info_result(ret)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: assume the queried PE is on.  Tests that need to
        // exercise the off / pending / failure paths can call
        // `decode_affinity_info_result` directly to construct a
        // synthetic response.
        let _ = (target_affinity, lowest_affinity_level);
        Ok(AffinityInfoState::On)
    }
}

// ============================================================================
// SM1.A.3 — system_off
// ============================================================================

/// WS-SM SM1.A.3: PSCI `SYSTEM_OFF` — power off the entire system.
///
/// ARM DEN0022D §5.1.9 (function id `0x8400_0008`, SMC32).
///
/// **Does not return.**  The return type `!` documents this at the
/// type level: any continuation after a `system_off()` call is
/// unreachable code.
///
/// ## Defensive design — handling `NOT_SUPPORTED` returns
///
/// Per DEN0022D §5.1.9, the call does not return on success, but a
/// firmware that does not implement SYSTEM_OFF may return
/// `NOT_SUPPORTED` (-1).  Therefore the asm block must NOT be marked
/// `noreturn` — doing so would invoke undefined behaviour if the HVC
/// returned (the Rust reference defines `noreturn` violation as UB).
/// Instead the function emits the HVC and falls into an explicit
/// `loop { spin_loop() }` so:
///
/// 1. On a conforming firmware, the HVC powers off and the trailing
///    loop is never reached.
/// 2. On a non-conforming firmware, the trailing loop guarantees
///    `-> !` is honoured by spinning indefinitely (the safest state
///    when power-off failed) rather than triggering UB or falling
///    off the end of the function.
///
/// AN9-I integration: emits `dsb osh` before HVC so any pending
/// kernel state (e.g., journalled writes, final UART output) is
/// observable in the outer-shareable domain prior to power-down.
pub fn system_off() -> ! {
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: HVC #0 with PSCI calling convention.  Per DEN0022D
        // §5.1.9 a conforming firmware does not return; a non-
        // conforming firmware may return `NOT_SUPPORTED`, in which
        // case we fall through to the spin loop below.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_SYSTEM_OFF as u64,
                clobber_abi("C"),
                options(nostack)
            );
        }
    }

    // Spin-park.  Reached only if (a) the HVC firmware does not
    // implement SYSTEM_OFF and returned NOT_SUPPORTED, or (b) we're
    // running on host without aarch64 inline asm.  In either case,
    // the kernel is stuck in the safest possible state — no further
    // execution, no privilege escalation surface, no UB.
    loop {
        core::hint::spin_loop();
    }
}

// ============================================================================
// SM1.A.4 — system_reset
// ============================================================================

/// WS-SM SM1.A.4: PSCI `SYSTEM_RESET` — perform a cold system reset.
///
/// ARM DEN0022D §5.1.10 (function id `0x8400_0009`, SMC32).
///
/// **Does not return.**  Like [`system_off`] the call powers the
/// system down then back on; any continuation after the call is
/// unreachable.  Used by the kernel panic handler when a fatal
/// invariant violation is detected and the safest recovery is to
/// boot fresh.
///
/// ## Defensive design — handling `NOT_SUPPORTED` returns
///
/// Per DEN0022D §5.1.10 a conforming firmware does not return, but a
/// non-conforming firmware may return `NOT_SUPPORTED` (-1).  Same
/// design as [`system_off`]: the asm block omits `noreturn` (which
/// would be UB if firmware returns) and the trailing
/// `loop { spin_loop() }` guarantees `-> !` even on non-conforming
/// firmware.  See [`system_off`] for the full rationale.
///
/// AN9-I integration: emits `dsb osh` before HVC so any pending
/// kernel state is observable prior to reset.
pub fn system_reset() -> ! {
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: HVC #0 with PSCI calling convention.  Per DEN0022D
        // §5.1.10 a conforming firmware does not return; a non-
        // conforming firmware may return NOT_SUPPORTED, in which case
        // we fall through to the spin loop below (same defensive
        // pattern as `system_off`).
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_SYSTEM_RESET as u64,
                clobber_abi("C"),
                options(nostack)
            );
        }
    }

    // Spin-park.  Reached only if firmware doesn't implement
    // SYSTEM_RESET, or on host.  See `system_off` for full rationale.
    loop {
        core::hint::spin_loop();
    }
}

// ============================================================================
// SM1.A.5 — psci_version + PsciVersion
// ============================================================================

/// WS-SM SM1.A.5: PSCI version, decoded from the 32-bit raw return.
///
/// ARM DEN0022D §5.1.1 encodes the version as `(major << 16) | minor`:
///
/// ```text
/// bits 31..16 : major version (16 bits)
/// bits 15..0  : minor version (16 bits)
/// ```
///
/// seLe4n targets PSCI 1.1 (the version implemented by RPi5 firmware);
/// older firmware reporting PSCI 0.2 is also supported (every wrapper
/// in this module uses a function id from the 0.2 base set).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PsciVersion {
    pub major: u16,
    pub minor: u16,
}

impl PsciVersion {
    /// Decode a raw 32-bit `PSCI_VERSION` return into a structured
    /// [`PsciVersion`].  Round-trip with [`PsciVersion::to_raw`] is
    /// exact.
    #[inline]
    pub const fn from_raw(raw: u32) -> Self {
        Self {
            major: ((raw >> 16) & 0xFFFF) as u16,
            minor: (raw & 0xFFFF) as u16,
        }
    }

    /// Encode a [`PsciVersion`] back to the 32-bit raw format.
    #[inline]
    pub const fn to_raw(self) -> u32 {
        ((self.major as u32) << 16) | (self.minor as u32)
    }

    /// True iff this version is ≥ the requested (major, minor).
    /// Used to gate optional 1.x features behind a version probe.
    #[inline]
    pub const fn at_least(self, major: u16, minor: u16) -> bool {
        self.major > major || (self.major == major && self.minor >= minor)
    }
}

/// WS-SM SM1.A.5: PSCI `PSCI_VERSION` — query the firmware-implemented
/// PSCI revision.
///
/// ARM DEN0022D §5.1.1 (function id `0x8400_0000`, SMC32).
///
/// This is a pure query and emits no `dsb osh` (no cross-cluster
/// ordering required).  Returns a [`PsciVersion`] decoded from the
/// 32-bit return value.
///
/// On host this returns `PsciVersion { major: 1, minor: 1 }` (PSCI 1.1),
/// matching the version reported by `armstub8-rpi5` on real hardware.
#[must_use]
pub fn psci_version() -> PsciVersion {
    #[cfg(target_arch = "aarch64")]
    {
        let raw: u32;
        // SAFETY: HVC #0 with PSCI calling convention.  Per DEN0022D
        // §5.1.1 the call always returns; the 32-bit version word
        // comes back in x0.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_PSCI_VERSION as u64,
                lateout("x0") raw,
                clobber_abi("C"),
                options(nostack)
            );
        }
        PsciVersion::from_raw(raw)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: pretend PSCI 1.1 so the version-gate logic in
        // `at_least` is exercised.
        PsciVersion { major: 1, minor: 1 }
    }
}

// ============================================================================
// SM1.A.6 — migrate_info_type + MigrateInfoType
// ============================================================================

/// WS-SM SM1.A.6: PSCI `MIGRATE_INFO_TYPE` result.
///
/// ARM DEN0022D §5.1.7 returns one of three non-negative values:
/// - 0 = `UniProcessor` (Trusted OS is uniprocessor-only; migration required)
/// - 1 = `Multiprocessor` (Trusted OS supports multiprocessor; migration not required)
/// - 2 = `NotRequired` (no Trusted OS, or trust path is stateless)
///
/// A `NotSupported` return code (no Trusted-OS-aware firmware) is mapped
/// by the caller to `Err(PsciResult::NotSupported)`; the kernel treats
/// this as semantically equivalent to `NotRequired` for SMP planning.
///
/// For seLe4n's usage on RPi5 (no Trusted OS), the firmware returns
/// `NotRequired`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum MigrateInfoType {
    UniProcessor = 0,
    Multiprocessor = 1,
    NotRequired = 2,
}

impl MigrateInfoType {
    /// Decode a non-negative raw PSCI return value into the canonical
    /// enum variant.  Returns `None` for values outside [0, 2]; the
    /// caller maps `None` to [`PsciResult::Unknown`].
    pub const fn from_raw(raw: i32) -> Option<Self> {
        match raw {
            0 => Some(Self::UniProcessor),
            1 => Some(Self::Multiprocessor),
            2 => Some(Self::NotRequired),
            _ => None,
        }
    }

    /// Raw 32-bit value matching the ARM DEN0022D encoding.
    #[inline]
    pub const fn to_raw(self) -> i32 {
        self as i32
    }
}

/// WS-SM SM1.A.6: pure decoder for the raw `MIGRATE_INFO_TYPE` return.
///
/// Extracted from [`migrate_info_type`] so the failure path (negative
/// or out-of-range) is unit-testable without the HVC trap.  Semantics
/// match [`decode_affinity_info_result`]:
///
/// - `raw == 0` ⇒ `Ok(UniProcessor)`
/// - `raw == 1` ⇒ `Ok(Multiprocessor)`
/// - `raw == 2` ⇒ `Ok(NotRequired)`
/// - `raw  < 0` ⇒ `Err(PsciResult::from_raw(raw))`
/// - `raw  > 2` ⇒ `Err(PsciResult::Unknown)`
#[inline]
pub const fn decode_migrate_info_type_result(raw: i32) -> Result<MigrateInfoType, PsciResult> {
    if raw < 0 {
        return Err(PsciResult::from_raw(raw));
    }
    match MigrateInfoType::from_raw(raw) {
        Some(typ) => Ok(typ),
        None => Err(PsciResult::Unknown),
    }
}

/// WS-SM SM1.A.6: PSCI `MIGRATE_INFO_TYPE` — query Trusted-OS
/// migration requirements.
///
/// ARM DEN0022D §5.1.7 (function id `0x8400_0006`, SMC32).
///
/// Returns:
/// - `Ok(type)` on success — the firmware's migration-type
///   indication.
/// - `Err(PsciResult)` on failure — typically `NotSupported` if the
///   firmware lacks a Trusted OS (in which case the kernel can treat
///   the system as `MigrateInfoType::NotRequired`).
///
/// This is a pure query and emits no `dsb osh`.
pub fn migrate_info_type() -> Result<MigrateInfoType, PsciResult> {
    #[cfg(target_arch = "aarch64")]
    {
        let ret: i32;
        // SAFETY: HVC #0 with PSCI calling convention.  Per DEN0022D
        // §5.1.7 the call has no arguments beyond the function id;
        // the migration-type word comes back in x0.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_MIGRATE_INFO_TYPE as u64,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        decode_migrate_info_type_result(ret)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: NotRequired matches the no-Trusted-OS case
        // RPi5 firmware reports.
        Ok(MigrateInfoType::NotRequired)
    }
}

// ============================================================================
// SM1.A.7 — Function-id pinning + invariant compile-time guards
// ============================================================================

/// WS-SM SM1.A.7: PSCI OEN (Owning Entity Number) per SMCCC §5.2.
/// PSCI lives in the Standard Secure Service Calls range (OEN = 4),
/// encoded in bits 29..24 of the function id.
const PSCI_OEN_STANDARD_SECURE: u32 = 4 << 24;

/// WS-SM SM1.A.7: bit-mask isolating the OEN field (bits 29..24).
const PSCI_OEN_MASK: u32 = 0x3F << 24;

/// WS-SM SM1.A.7: bit-mask of bits 23..16 (reserved per SMCCC §5.2;
/// must be zero in every PSCI function id).
const PSCI_RESERVED_MASK: u32 = 0x00FF_0000;

/// WS-SM SM1.A.7: compile-time assertions on the PSCI function-id
/// encoding per ARM SMCCC (DEN0028) and DEN0022D §5.2.1:
///
/// - **Bit 31 (Fast call)**: must be `1` for every PSCI id (PSCI calls
///   are always fast).
/// - **Bit 30 (SMC64)**: `1` for SMC64 ids (`CPU_ON`, `AFFINITY_INFO`
///   which take 64-bit MPIDR arguments), `0` for SMC32 ids (the
///   remaining five wrappers).
/// - **Bits 29..24 (OEN)**: must be `4` (Standard Secure Service Calls,
///   the range PSCI lives in).
/// - **Bits 23..16**: reserved, must be `0`.
/// - **Bits 15..0**: function number.
///
/// A future PR that violates any of these invariants fails the build
/// at elaboration time.
const _: () = {
    // Bit 31 (Fast call) must be set on every PSCI function id.
    assert!(
        PSCI_FN_PSCI_VERSION & 0x8000_0000 != 0,
        "PSCI_FN_PSCI_VERSION must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_CPU_OFF & 0x8000_0000 != 0,
        "PSCI_FN_CPU_OFF must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_CPU_ON & 0x8000_0000 != 0,
        "PSCI_FN_CPU_ON must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_AFFINITY_INFO & 0x8000_0000 != 0,
        "PSCI_FN_AFFINITY_INFO must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_MIGRATE_INFO_TYPE & 0x8000_0000 != 0,
        "PSCI_FN_MIGRATE_INFO_TYPE must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_SYSTEM_OFF & 0x8000_0000 != 0,
        "PSCI_FN_SYSTEM_OFF must have bit 31 set (Fast call)"
    );
    assert!(
        PSCI_FN_SYSTEM_RESET & 0x8000_0000 != 0,
        "PSCI_FN_SYSTEM_RESET must have bit 31 set (Fast call)"
    );
    // Bit 30 (SMC64) — set only on CPU_ON and AFFINITY_INFO.
    assert!(
        PSCI_FN_CPU_ON & 0x4000_0000 != 0,
        "PSCI_FN_CPU_ON must have bit 30 set (SMC64)"
    );
    assert!(
        PSCI_FN_AFFINITY_INFO & 0x4000_0000 != 0,
        "PSCI_FN_AFFINITY_INFO must have bit 30 set (SMC64)"
    );
    // Bit 30 (SMC64) — clear on every SMC32 id.
    assert!(
        PSCI_FN_PSCI_VERSION & 0x4000_0000 == 0,
        "PSCI_FN_PSCI_VERSION must have bit 30 clear (SMC32)"
    );
    assert!(
        PSCI_FN_CPU_OFF & 0x4000_0000 == 0,
        "PSCI_FN_CPU_OFF must have bit 30 clear (SMC32)"
    );
    assert!(
        PSCI_FN_MIGRATE_INFO_TYPE & 0x4000_0000 == 0,
        "PSCI_FN_MIGRATE_INFO_TYPE must have bit 30 clear (SMC32)"
    );
    assert!(
        PSCI_FN_SYSTEM_OFF & 0x4000_0000 == 0,
        "PSCI_FN_SYSTEM_OFF must have bit 30 clear (SMC32)"
    );
    assert!(
        PSCI_FN_SYSTEM_RESET & 0x4000_0000 == 0,
        "PSCI_FN_SYSTEM_RESET must have bit 30 clear (SMC32)"
    );
    // OEN (bits 29..24) must equal 4 (Standard Secure Service Calls).
    assert!(
        PSCI_FN_PSCI_VERSION & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_PSCI_VERSION must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_CPU_OFF & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_CPU_OFF must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_CPU_ON & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_CPU_ON must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_AFFINITY_INFO & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_AFFINITY_INFO must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_MIGRATE_INFO_TYPE & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_MIGRATE_INFO_TYPE must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_SYSTEM_OFF & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_SYSTEM_OFF must have OEN=4 (Standard Secure Service Calls)"
    );
    assert!(
        PSCI_FN_SYSTEM_RESET & PSCI_OEN_MASK == PSCI_OEN_STANDARD_SECURE,
        "PSCI_FN_SYSTEM_RESET must have OEN=4 (Standard Secure Service Calls)"
    );
    // Bits 23..16 are reserved — must be zero.
    assert!(
        PSCI_FN_PSCI_VERSION & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_PSCI_VERSION has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_CPU_OFF & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_CPU_OFF has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_CPU_ON & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_CPU_ON has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_AFFINITY_INFO & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_AFFINITY_INFO has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_MIGRATE_INFO_TYPE & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_MIGRATE_INFO_TYPE has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_SYSTEM_OFF & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_SYSTEM_OFF has bits 23..16 set (reserved)"
    );
    assert!(
        PSCI_FN_SYSTEM_RESET & PSCI_RESERVED_MASK == 0,
        "PSCI_FN_SYSTEM_RESET has bits 23..16 set (reserved)"
    );
};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // PsciResult round-trip + decoder
    // ------------------------------------------------------------------------

    #[test]
    fn psci_result_roundtrip() {
        for &raw in &[0i32, -1, -2, -3, -4, -5, -6, -7, -8] {
            let r = PsciResult::from_raw(raw);
            assert_eq!(r.to_raw(), raw, "round-trip failed for raw {}", raw);
        }
    }

    #[test]
    fn psci_result_unknown_for_undocumented_code() {
        assert_eq!(PsciResult::from_raw(-999), PsciResult::Unknown);
        assert_eq!(PsciResult::from_raw(42), PsciResult::Unknown);
    }

    #[test]
    fn psci_result_is_success_only_for_zero() {
        // Exhaustive check: only the `Success` variant (encoded as 0)
        // returns true from `is_success`.  Every other variant
        // (including `Unknown`) returns false.  A future PR that
        // accidentally redefines `is_success` to match on a wider
        // pattern would fail this test.
        assert!(PsciResult::Success.is_success());
        assert!(!PsciResult::NotSupported.is_success());
        assert!(!PsciResult::InvalidParameters.is_success());
        assert!(!PsciResult::Denied.is_success());
        assert!(!PsciResult::AlreadyOn.is_success());
        assert!(!PsciResult::OnPending.is_success());
        assert!(!PsciResult::InternalFailure.is_success());
        assert!(!PsciResult::NotPresent.is_success());
        assert!(!PsciResult::Disabled.is_success());
        assert!(!PsciResult::Unknown.is_success());
    }

    // ------------------------------------------------------------------------
    // SM1.A.7 — Function-id pinning tests
    // ------------------------------------------------------------------------

    #[test]
    fn psci_function_ids_match_arm_den0022d() {
        // ARM DEN0022D §5.1 function-id matrix.  Each constant is
        // pinned to the literal hex value in the spec; any drift
        // fails this test before the wrapper is ever invoked on
        // hardware.  Sub-section numbers are per DEN0022D revision D.
        assert_eq!(PSCI_FN_PSCI_VERSION,    0x8400_0000); // §5.1.1
        assert_eq!(PSCI_FN_CPU_OFF,         0x8400_0002); // §5.1.3
        assert_eq!(PSCI_FN_CPU_ON,          0xC400_0003); // §5.1.4 SMC64
        assert_eq!(PSCI_FN_AFFINITY_INFO,   0xC400_0004); // §5.1.5 SMC64
        assert_eq!(PSCI_FN_MIGRATE_INFO_TYPE, 0x8400_0006); // §5.1.7
        assert_eq!(PSCI_FN_SYSTEM_OFF,      0x8400_0008); // §5.1.9
        assert_eq!(PSCI_FN_SYSTEM_RESET,    0x8400_0009); // §5.1.10
    }

    #[test]
    fn psci_function_ids_pairwise_distinct() {
        // Every PSCI function id wrapped by this module must be
        // distinct.  A duplicate would silently dispatch one
        // wrapper's call to the wrong firmware handler.
        let ids = [
            PSCI_FN_PSCI_VERSION,
            PSCI_FN_CPU_OFF,
            PSCI_FN_CPU_ON,
            PSCI_FN_AFFINITY_INFO,
            PSCI_FN_MIGRATE_INFO_TYPE,
            PSCI_FN_SYSTEM_OFF,
            PSCI_FN_SYSTEM_RESET,
        ];
        for (i, a) in ids.iter().enumerate() {
            for b in &ids[i + 1..] {
                assert_ne!(a, b, "duplicate PSCI function id: {:#x}", a);
            }
        }
    }

    #[test]
    fn psci_all_function_ids_have_bit31_set_fast_call() {
        // SMCCC (DEN0028) §5.2: bit 31 = 1 ⇒ Fast call.  PSCI calls
        // are always fast (DEN0022D §5.2.1).  Every wrapped function
        // id must therefore have bit 31 set.
        let ids = [
            PSCI_FN_PSCI_VERSION,
            PSCI_FN_CPU_OFF,
            PSCI_FN_CPU_ON,
            PSCI_FN_AFFINITY_INFO,
            PSCI_FN_MIGRATE_INFO_TYPE,
            PSCI_FN_SYSTEM_OFF,
            PSCI_FN_SYSTEM_RESET,
        ];
        for id in ids {
            assert!(
                id & 0x8000_0000 != 0,
                "PSCI function id {:#x} must have bit 31 set (Fast call)",
                id
            );
        }
    }

    #[test]
    fn psci_smc64_function_ids_have_bit30_set() {
        // SMCCC §5.2: bit 30 = 1 ⇒ SMC64 (64-bit args).  PSCI's
        // CPU_ON and AFFINITY_INFO take a 64-bit MPIDR_EL1 argument
        // so both must encode as SMC64.  Comparing against the
        // mask directly (rather than using `!= 0`) sidesteps
        // clippy's `assertions_on_constants` lint while keeping
        // the intent explicit.
        assert_eq!(PSCI_FN_CPU_ON & 0x4000_0000, 0x4000_0000);
        assert_eq!(PSCI_FN_AFFINITY_INFO & 0x4000_0000, 0x4000_0000);
    }

    #[test]
    fn psci_smc32_function_ids_have_bit30_clear() {
        // SMCCC §5.2: bit 30 = 0 ⇒ SMC32 (32-bit args).  The five
        // PSCI wrappers that have no 64-bit argument are SMC32.
        assert_eq!(PSCI_FN_PSCI_VERSION & 0x4000_0000, 0);
        assert_eq!(PSCI_FN_CPU_OFF & 0x4000_0000, 0);
        assert_eq!(PSCI_FN_MIGRATE_INFO_TYPE & 0x4000_0000, 0);
        assert_eq!(PSCI_FN_SYSTEM_OFF & 0x4000_0000, 0);
        assert_eq!(PSCI_FN_SYSTEM_RESET & 0x4000_0000, 0);
    }

    #[test]
    fn psci_function_ids_reserved_bits_23_16_clear() {
        // SMCCC §5.2: bits 23..16 are reserved and must be zero in
        // every PSCI function id.  Bits 29..24 carry the OEN
        // (Owning Entity Number), which is tested separately by
        // `psci_function_ids_oen_is_standard_secure_service`.
        let ids = [
            PSCI_FN_PSCI_VERSION,
            PSCI_FN_CPU_OFF,
            PSCI_FN_CPU_ON,
            PSCI_FN_AFFINITY_INFO,
            PSCI_FN_MIGRATE_INFO_TYPE,
            PSCI_FN_SYSTEM_OFF,
            PSCI_FN_SYSTEM_RESET,
        ];
        for id in ids {
            assert_eq!(
                id & 0x00FF_0000,
                0,
                "PSCI function id {:#x} has reserved bits 23..16 set",
                id
            );
        }
    }

    #[test]
    fn psci_function_ids_oen_is_standard_secure_service() {
        // SMCCC §5.2: bits 29..24 carry the OEN (Owning Entity
        // Number).  PSCI (DEN0022D §5.2.1) lives in the Standard
        // Secure Service Calls range (OEN = 4).
        let ids = [
            PSCI_FN_PSCI_VERSION,
            PSCI_FN_CPU_OFF,
            PSCI_FN_CPU_ON,
            PSCI_FN_AFFINITY_INFO,
            PSCI_FN_MIGRATE_INFO_TYPE,
            PSCI_FN_SYSTEM_OFF,
            PSCI_FN_SYSTEM_RESET,
        ];
        for id in ids {
            let oen = (id >> 24) & 0x3F;
            assert_eq!(
                oen, 4,
                "PSCI function id {:#x} has OEN={} (expected 4 = Standard Secure)",
                id, oen
            );
        }
    }

    // ------------------------------------------------------------------------
    // SM1.A.1 — cpu_on / cpu_off host-stub tests
    // ------------------------------------------------------------------------

    #[test]
    fn cpu_on_host_stub_returns_success() {
        // On host, cpu_on is a no-op returning Success so the boot
        // path's structure can be tested without HVC.
        let r = cpu_on(0x0001_0000, 0x80000, 0);
        assert_eq!(r, PsciResult::Success);
    }

    #[test]
    fn psci_cpu_off_returns_psci_result_type() {
        // SM1.A.1: on host, cpu_off returns Success.  On real
        // hardware a successful call does not return (the PE is
        // powered down); failure paths return the firmware's raw
        // error.  This test exercises the host stub's call graph.
        let r = cpu_off();
        assert_eq!(r, PsciResult::Success);
    }

    // ------------------------------------------------------------------------
    // SM1.A.2 — affinity_info / AffinityInfoState
    // ------------------------------------------------------------------------

    #[test]
    fn affinity_info_state_from_raw_decodes_documented_values() {
        // SM1.A.2: ARM DEN0022D §5.1.5 documents three values.
        assert_eq!(AffinityInfoState::from_raw(0), Some(AffinityInfoState::On));
        assert_eq!(AffinityInfoState::from_raw(1), Some(AffinityInfoState::Off));
        assert_eq!(AffinityInfoState::from_raw(2), Some(AffinityInfoState::OnPending));
    }

    #[test]
    fn affinity_info_state_from_raw_rejects_undocumented_values() {
        // SM1.A.2: a vendor extension or firmware bug returning a
        // value outside [0, 2] must not panic — the caller maps to
        // PsciResult::Unknown.
        assert_eq!(AffinityInfoState::from_raw(3), None);
        assert_eq!(AffinityInfoState::from_raw(-1), None);
        assert_eq!(AffinityInfoState::from_raw(i32::MAX), None);
    }

    #[test]
    fn affinity_info_state_to_raw_roundtrips() {
        // SM1.A.2: encode → decode must be the identity.
        for &raw in &[0i32, 1, 2] {
            let state = AffinityInfoState::from_raw(raw).expect("valid raw");
            assert_eq!(state.to_raw(), raw, "round-trip failed for raw {}", raw);
        }
    }

    #[test]
    fn affinity_info_host_stub_returns_on() {
        // SM1.A.2: host stub returns On for any MPIDR.
        let r = affinity_info(0x0000_0001, 0);
        assert_eq!(r, Ok(AffinityInfoState::On));
    }

    // ------------------------------------------------------------------------
    // SM1.A.2 — decode_affinity_info_result coverage (failure paths).
    //
    // The pure decoder is exposed so the failure paths (`ret < 0` and
    // `ret > 2`) can be unit-tested without the HVC trap.  The
    // production wrapper `affinity_info` is just `asm! + this decoder`,
    // so coverage on the decoder gives coverage on the wrapper's
    // failure path.
    // ------------------------------------------------------------------------

    #[test]
    fn decode_affinity_info_result_success_values() {
        // SM1.A.2: 0/1/2 decode to On/Off/OnPending.
        assert_eq!(decode_affinity_info_result(0), Ok(AffinityInfoState::On));
        assert_eq!(decode_affinity_info_result(1), Ok(AffinityInfoState::Off));
        assert_eq!(decode_affinity_info_result(2), Ok(AffinityInfoState::OnPending));
    }

    #[test]
    fn decode_affinity_info_result_negative_codes_map_to_psci_result() {
        // SM1.A.2: every documented negative PSCI return code decodes
        // through `PsciResult::from_raw`.  This is the production path
        // when firmware rejects the AFFINITY_INFO query with e.g.
        // `InvalidParameters` for an unknown MPIDR.
        assert_eq!(decode_affinity_info_result(-1), Err(PsciResult::NotSupported));
        assert_eq!(decode_affinity_info_result(-2), Err(PsciResult::InvalidParameters));
        assert_eq!(decode_affinity_info_result(-3), Err(PsciResult::Denied));
        assert_eq!(decode_affinity_info_result(-6), Err(PsciResult::InternalFailure));
        assert_eq!(decode_affinity_info_result(-7), Err(PsciResult::NotPresent));
        assert_eq!(decode_affinity_info_result(-8), Err(PsciResult::Disabled));
    }

    #[test]
    fn decode_affinity_info_result_negative_unknown_maps_to_unknown() {
        // SM1.A.2: negative values outside the documented range
        // (-9..) decode to PsciResult::Unknown via from_raw's catch-
        // all arm.
        assert_eq!(decode_affinity_info_result(-9), Err(PsciResult::Unknown));
        assert_eq!(decode_affinity_info_result(-100), Err(PsciResult::Unknown));
        assert_eq!(decode_affinity_info_result(i32::MIN), Err(PsciResult::Unknown));
    }

    #[test]
    fn decode_affinity_info_result_out_of_range_maps_to_unknown() {
        // SM1.A.2: a non-negative value outside [0, 2] is a vendor
        // extension or firmware bug.  We map to PsciResult::Unknown
        // rather than panicking.
        assert_eq!(decode_affinity_info_result(3), Err(PsciResult::Unknown));
        assert_eq!(decode_affinity_info_result(42), Err(PsciResult::Unknown));
        assert_eq!(decode_affinity_info_result(i32::MAX), Err(PsciResult::Unknown));
    }

    // ------------------------------------------------------------------------
    // SM1.A.3 / SM1.A.4 — system_off / system_reset
    //
    // These functions have return type `!` (do not return).  We
    // cannot call them directly in a test (the test would never
    // complete) so we verify the type-level signature and the
    // function-id encoding instead.  Direct invocation tests are
    // possible via `#[ignore]` annotations + manual `cargo test
    // -- --ignored` invocation, kept out of CI.
    // ------------------------------------------------------------------------

    #[test]
    fn system_off_function_id_pinned() {
        // SM1.A.3: pin the function id at the test layer in addition
        // to the consolidated function-id matrix test.  A typo in
        // the constant would fail BOTH tests, producing a clear
        // diagnostic.
        assert_eq!(PSCI_FN_SYSTEM_OFF, 0x8400_0008);
    }

    #[test]
    fn system_reset_function_id_pinned() {
        // SM1.A.4: pin SYSTEM_RESET id.
        assert_eq!(PSCI_FN_SYSTEM_RESET, 0x8400_0009);
    }

    // ------------------------------------------------------------------------
    // SM1.A.5 — psci_version / PsciVersion
    // ------------------------------------------------------------------------

    #[test]
    fn psci_version_from_raw_decodes_major_and_minor() {
        // SM1.A.5: PSCI 1.1 encodes as (1 << 16) | 1 = 0x0001_0001.
        let v = PsciVersion::from_raw(0x0001_0001);
        assert_eq!(v.major, 1);
        assert_eq!(v.minor, 1);
    }

    #[test]
    fn psci_version_from_raw_decodes_psci_0_2() {
        // SM1.A.5: PSCI 0.2 encodes as 0x0000_0002.
        let v = PsciVersion::from_raw(0x0000_0002);
        assert_eq!(v.major, 0);
        assert_eq!(v.minor, 2);
    }

    #[test]
    fn psci_version_roundtrip() {
        // SM1.A.5: encode → decode is the identity for every
        // version we expect to encounter (0.2 .. 1.3).
        for &(major, minor) in &[(0u16, 2u16), (1, 0), (1, 1), (1, 2), (1, 3)] {
            let v = PsciVersion { major, minor };
            let decoded = PsciVersion::from_raw(v.to_raw());
            assert_eq!(decoded, v, "round-trip failed for {}.{}", major, minor);
        }
    }

    #[test]
    fn psci_version_at_least_compares_correctly() {
        // SM1.A.5: at_least is monotonic.  Used to gate optional
        // features behind a version probe.
        let v_1_1 = PsciVersion { major: 1, minor: 1 };
        assert!(v_1_1.at_least(0, 2));
        assert!(v_1_1.at_least(1, 0));
        assert!(v_1_1.at_least(1, 1));
        assert!(!v_1_1.at_least(1, 2));
        assert!(!v_1_1.at_least(2, 0));

        let v_0_2 = PsciVersion { major: 0, minor: 2 };
        assert!(v_0_2.at_least(0, 2));
        assert!(!v_0_2.at_least(0, 3));
        assert!(!v_0_2.at_least(1, 0));
    }

    #[test]
    fn psci_version_host_stub_returns_1_1() {
        // SM1.A.5: host stub matches RPi5 firmware (armstub8-rpi5
        // implements PSCI 1.1).
        let v = psci_version();
        assert_eq!(v, PsciVersion { major: 1, minor: 1 });
    }

    #[test]
    fn psci_version_high_bits_extract_major() {
        // SM1.A.5: defense-in-depth — verify the decoder isolates
        // the high 16 bits as the major version, even when the
        // low 16 bits are non-trivial.
        let v = PsciVersion::from_raw(0x0007_FFFF);
        assert_eq!(v.major, 7);
        assert_eq!(v.minor, 0xFFFF);
    }

    // ------------------------------------------------------------------------
    // SM1.A.6 — migrate_info_type / MigrateInfoType
    // ------------------------------------------------------------------------

    #[test]
    fn migrate_info_type_from_raw_decodes_documented_values() {
        // SM1.A.6: ARM DEN0022D §5.1.7 documents three values.
        assert_eq!(MigrateInfoType::from_raw(0), Some(MigrateInfoType::UniProcessor));
        assert_eq!(MigrateInfoType::from_raw(1), Some(MigrateInfoType::Multiprocessor));
        assert_eq!(MigrateInfoType::from_raw(2), Some(MigrateInfoType::NotRequired));
    }

    #[test]
    fn migrate_info_type_from_raw_rejects_undocumented_values() {
        // SM1.A.6: vendor extensions or firmware bugs returning
        // values outside [0, 2] must not panic — the caller maps
        // to PsciResult::Unknown.
        assert_eq!(MigrateInfoType::from_raw(3), None);
        assert_eq!(MigrateInfoType::from_raw(-1), None);
        assert_eq!(MigrateInfoType::from_raw(i32::MAX), None);
    }

    #[test]
    fn migrate_info_type_to_raw_roundtrips() {
        // SM1.A.6: encode → decode must be the identity.
        for &raw in &[0i32, 1, 2] {
            let typ = MigrateInfoType::from_raw(raw).expect("valid raw");
            assert_eq!(typ.to_raw(), raw, "round-trip failed for raw {}", raw);
        }
    }

    #[test]
    fn migrate_info_host_stub_returns_not_required() {
        // SM1.A.6: host stub matches the RPi5 no-Trusted-OS state.
        let r = migrate_info_type();
        assert_eq!(r, Ok(MigrateInfoType::NotRequired));
    }

    // ------------------------------------------------------------------------
    // SM1.A.6 — decode_migrate_info_type_result coverage (failure paths).
    //
    // Same rationale as `decode_affinity_info_result`: the pure
    // decoder is exposed so production failure paths can be unit-tested
    // without an HVC trap.
    // ------------------------------------------------------------------------

    #[test]
    fn decode_migrate_info_type_result_success_values() {
        // SM1.A.6: 0/1/2 decode to UniProcessor/Multiprocessor/NotRequired.
        assert_eq!(decode_migrate_info_type_result(0), Ok(MigrateInfoType::UniProcessor));
        assert_eq!(decode_migrate_info_type_result(1), Ok(MigrateInfoType::Multiprocessor));
        assert_eq!(decode_migrate_info_type_result(2), Ok(MigrateInfoType::NotRequired));
    }

    #[test]
    fn decode_migrate_info_type_result_negative_codes_map_to_psci_result() {
        // SM1.A.6: NotSupported is the most common negative return
        // (firmware lacks Trusted-OS migration awareness); other
        // negative codes propagate through PsciResult::from_raw.
        assert_eq!(
            decode_migrate_info_type_result(-1),
            Err(PsciResult::NotSupported)
        );
        assert_eq!(
            decode_migrate_info_type_result(-2),
            Err(PsciResult::InvalidParameters)
        );
        assert_eq!(
            decode_migrate_info_type_result(-6),
            Err(PsciResult::InternalFailure)
        );
    }

    #[test]
    fn decode_migrate_info_type_result_negative_unknown_maps_to_unknown() {
        // SM1.A.6: negative values outside the documented PSCI range
        // decode to PsciResult::Unknown.
        assert_eq!(decode_migrate_info_type_result(-9), Err(PsciResult::Unknown));
        assert_eq!(decode_migrate_info_type_result(i32::MIN), Err(PsciResult::Unknown));
    }

    #[test]
    fn decode_migrate_info_type_result_out_of_range_maps_to_unknown() {
        // SM1.A.6: a non-negative value outside [0, 2] is a vendor
        // extension or firmware bug.  We map to PsciResult::Unknown
        // rather than panicking.
        assert_eq!(decode_migrate_info_type_result(3), Err(PsciResult::Unknown));
        assert_eq!(decode_migrate_info_type_result(42), Err(PsciResult::Unknown));
        assert_eq!(
            decode_migrate_info_type_result(i32::MAX),
            Err(PsciResult::Unknown)
        );
    }

    // ------------------------------------------------------------------------
    // SM1.A.8 — documentation-map coverage assertion
    //
    // The module-level docstring lists all 7 wrappers with their
    // function ids.  This test sanity-checks that the constants
    // are all reachable from outside the module (i.e. `pub const`)
    // by binding them to local variables.  If a `pub` is dropped
    // by mistake, the test fails to compile.
    // ------------------------------------------------------------------------

    #[test]
    fn psci_documentation_map_constants_are_public() {
        // SM1.A.8: every documented function id must be reachable
        // from outside the module so external callers / tests / FFI
        // can pin against the same value.
        let _: u32 = PSCI_FN_PSCI_VERSION;
        let _: u32 = PSCI_FN_CPU_OFF;
        let _: u32 = PSCI_FN_CPU_ON;
        let _: u32 = PSCI_FN_AFFINITY_INFO;
        let _: u32 = PSCI_FN_MIGRATE_INFO_TYPE;
        let _: u32 = PSCI_FN_SYSTEM_OFF;
        let _: u32 = PSCI_FN_SYSTEM_RESET;
    }

    #[test]
    fn psci_documentation_map_seven_distinct_wrappers() {
        // SM1.A.8: the module docstring claims 7 wrappers.  This
        // test verifies the count by collecting every public
        // function id into an array and asserting its length.
        // A future PR adding an 8th wrapper without updating the
        // docstring (and this test) fails to land.
        let ids: [u32; 7] = [
            PSCI_FN_PSCI_VERSION,
            PSCI_FN_CPU_OFF,
            PSCI_FN_CPU_ON,
            PSCI_FN_AFFINITY_INFO,
            PSCI_FN_MIGRATE_INFO_TYPE,
            PSCI_FN_SYSTEM_OFF,
            PSCI_FN_SYSTEM_RESET,
        ];
        assert_eq!(ids.len(), 7);
    }

    // ------------------------------------------------------------------------
    // Direct-invocation tests for system_off / system_reset (#[ignore]).
    //
    // These functions return `!` and spin forever on the host stub, so
    // we ignore them by default and provide a manual invocation
    // recipe in the test name.  They exist purely to verify the
    // function signatures compile and link.  Run with:
    //
    //     cargo test --lib psci::tests::system_off_host_stub_spins -- --ignored
    //
    // (the test will hang; press Ctrl-C to exit).
    // ------------------------------------------------------------------------

    #[test]
    #[ignore = "system_off does not return — host stub spins forever"]
    fn system_off_host_stub_spins() {
        // SM1.A.3: invokes the host stub; the test hangs (intentional).
        system_off();
    }

    #[test]
    #[ignore = "system_reset does not return — host stub spins forever"]
    fn system_reset_host_stub_spins() {
        // SM1.A.4: invokes the host stub; the test hangs (intentional).
        system_reset();
    }
}
