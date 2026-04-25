//! AN9-J.1 (DEF-R-HAL-L20): PSCI (Power State Coordination Interface) wrapper.
//!
//! Implements the small PSCI ARM DEN0022 subset the seLe4n boot path
//! needs to bring up secondary cores under `smp_enabled=true`.  The
//! v1.0.0 release ships with `smp_enabled=false` so this module's
//! `cpu_on` entry point is reachable but not invoked in the default
//! configuration.
//!
//! ## Function-id encoding
//!
//! ARM DEN0022D §5.1.7 specifies the 32-bit PSCI function id for
//! `CPU_ON` as `0xC400_0003` for the SMC64 variant.  RPi5 firmware
//! exposes PSCI via HVC at EL2; hosting kernels at EL1 issue `hvc
//! #0` with the function id in `x0`.  We provide a single
//! [`cpu_on`] entry point that emits the HVC instruction and decodes
//! the return value into [`PsciResult`].
//!
//! ## On host
//!
//! Test builds stub the HVC into a no-op returning
//! `PsciResult::Success` so unit tests can exercise the call path
//! without aarch64-specific intrinsics.

/// AN9-J.1: PSCI return-code values (subset relevant to seLe4n).
///
/// ARM DEN0022D Table 5: PSCI return codes are signed 32-bit values
/// where 0 = success and negative integers indicate specific failures.
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
    /// AN9-J.1: decode a raw 32-bit PSCI return value into the
    /// canonical enum variant.  Unknown values are mapped to
    /// `Unknown` rather than panicking, since at v1.0.0 we do not
    /// yet enumerate every PSCI vendor extension.
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

    /// AN9-J.1: raw 32-bit value matching the ARM DEN0022D encoding.
    #[inline]
    pub const fn to_raw(self) -> i32 {
        self as i32
    }

    /// AN9-J.1: shorthand for the success path.
    #[inline]
    pub const fn is_success(self) -> bool {
        matches!(self, Self::Success)
    }
}

/// AN9-J.1: PSCI function id for the SMC64 `CPU_ON` call.
/// ARM DEN0022D §5.1.7.
pub const PSCI_FN_CPU_ON: u32 = 0xC400_0003;

/// AN9-J.1: PSCI function id for the SMC32 `CPU_OFF` call.
/// ARM DEN0022D §5.1.5 (kept for completeness; not invoked by the
/// v1.0.0 boot path which never powers cores down).
pub const PSCI_FN_CPU_OFF: u32 = 0x8400_0002;

/// AN9-J.1: Issue a PSCI `CPU_ON` request to bring up a secondary core.
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
pub fn cpu_on(target_mpidr: u64, entry_point: usize, context_id: u64) -> PsciResult {
    // AN9-I: ensure cross-cluster ordering before the secondary core
    // observes the kernel image and shared boot data structures.  The
    // outer-shareable barrier covers the BCM2712 inter-cluster
    // interconnect.
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let mut ret: i32;
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
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(PsciResult::Success.is_success());
        assert!(!PsciResult::AlreadyOn.is_success());
        assert!(!PsciResult::Denied.is_success());
        assert!(!PsciResult::Unknown.is_success());
    }

    #[test]
    fn psci_function_ids_match_arm_den0022d() {
        // ARM DEN0022D §5.1.7: CPU_ON is 0xC4000003 for SMC64
        assert_eq!(PSCI_FN_CPU_ON, 0xC400_0003);
        // ARM DEN0022D §5.1.5: CPU_OFF is 0x84000002 for SMC32
        assert_eq!(PSCI_FN_CPU_OFF, 0x8400_0002);
    }

    #[test]
    fn cpu_on_host_stub_returns_success() {
        // On host, cpu_on is a no-op returning Success so the boot
        // path's structure can be tested without HVC.
        let r = cpu_on(0x0001_0000, 0x80000, 0);
        assert_eq!(r, PsciResult::Success);
    }
}
