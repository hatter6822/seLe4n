//! CPU instruction wrappers for ARMv8-A.
//!
//! Each wrapper encapsulates a single privileged or hint instruction with a
//! `// SAFETY:` comment referencing the ARM Architecture Reference Manual
//! (ARM ARM DDI 0487).
//!
//! On non-AArch64 hosts, functions provide no-op stubs for compilation and
//! testing.

/// Wait For Event — hint instruction that places the PE in a low-power state
/// until an event is received (WFE wake-up event or interrupt).
///
/// ARM ARM C6.2.353: WFE causes the PE to enter a low-power state.
#[inline(always)]
pub fn wfe() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: WFE is a hint instruction with no side effects beyond entering
        // low-power state. Always safe to execute at EL1. (ARM ARM C6.2.353)
        unsafe { core::arch::asm!("wfe", options(nomem, nostack, preserves_flags)) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    core::hint::spin_loop();
}

/// Wait For Interrupt — hint instruction that places the PE in a low-power
/// state until an interrupt or debug event occurs.
///
/// ARM ARM C6.2.354: WFI suspends execution until a WFI wake-up event.
#[inline(always)]
pub fn wfi() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: WFI is a hint instruction. No side effects beyond entering
        // low-power state. Always safe at EL1. (ARM ARM C6.2.354)
        unsafe { core::arch::asm!("wfi", options(nomem, nostack, preserves_flags)) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    core::hint::spin_loop();
}

/// NOP — no operation hint instruction.
///
/// ARM ARM C6.2.202: NOP does nothing. Used for alignment or timing.
#[inline(always)]
pub fn nop() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: NOP has no side effects. (ARM ARM C6.2.202)
        unsafe { core::arch::asm!("nop", options(nomem, nostack, preserves_flags)) }
    }
}

/// Exception Return — returns from EL1 to the exception level recorded in
/// SPSR_EL1, restoring PC from ELR_EL1.
///
/// ARM ARM C6.2.67: ERET restores PSTATE from SPSR and branches to ELR.
///
/// # Safety
///
/// Caller must ensure ELR_EL1 and SPSR_EL1 contain valid values for the
/// target exception level. This function does not return.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
pub unsafe fn eret() -> ! {
    // SAFETY: ERET transfers control to the address in ELR_EL1 with the
    // processor state from SPSR_EL1. Caller guarantees valid state.
    // (ARM ARM C6.2.67)
    unsafe { core::arch::asm!("eret", options(noreturn)) }
}

/// Mask covering Aff0..Aff2 (bits [23:0]) of MPIDR_EL1.
///
/// AK5-I (R-HAL-M02/R-HAL-M09): BCM2712 is a 2-cluster × 4-core topology
/// (Cortex-A76). Identifying "the primary boot core" by Aff0 alone leaks
/// cross-cluster traffic: a core whose cluster ID is non-zero but whose
/// per-cluster core number is 0 would alias to the boot core.
///
/// ARMv8-A MPIDR_EL1 layout (ARM ARM D17.2.98):
/// - Aff0 (bits [7:0])    — core within cluster
/// - Aff1 (bits [15:8])   — cluster ID on symmetric topologies
/// - Aff2 (bits [23:16])  — cluster ID on some asymmetric / big.LITTLE topologies
/// - MT   (bit 24)        — multi-threading flag (ignored for core ID)
/// - U    (bit 30)        — uniprocessor flag (ignored)
/// - Aff3 (bits [39:32])  — extended affinity (out of scope for BCM2712)
///
/// We mask all three affinity fields so the check remains correct whether
/// the BCM2712 encoding places cluster ID in Aff1 or Aff2. Aff3 is ignored
/// because BCM2712 has a single die with only two clusters and does not
/// use the extended affinity field.
pub const MPIDR_CORE_ID_MASK: u64 = 0x00FF_FFFF;

/// Read the MPIDR_EL1 register to determine the current core ID.
///
/// AK5-I (R-HAL-M02/M09): Returns Aff1:Aff0 packed in bits [15:8] | [7:0].
/// Previously only Aff0 was returned, which aliased secondary-cluster cores
/// to the boot core on BCM2712 (2-cluster topology).
///
/// Use the result as an opaque core identifier; do not index arrays by it
/// directly (the space is non-contiguous). Equality with `0` still means
/// "cluster 0, core 0" and is the accepted primary-core identifier.
///
/// ARM ARM D17.2.98: MPIDR_EL1 Multiprocessor Affinity Register.
#[inline(always)]
pub fn current_core_id() -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        let mpidr: u64;
        // SAFETY: Reading MPIDR_EL1 is always safe at EL1. It is a read-only
        // identification register. (ARM ARM D17.2.98)
        unsafe {
            core::arch::asm!("mrs {}, mpidr_el1", out(reg) mpidr, options(nomem, nostack, preserves_flags));
        }
        mpidr & MPIDR_CORE_ID_MASK
    }
    #[cfg(not(target_arch = "aarch64"))]
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mpidr_mask_covers_all_low_affinity_fields() {
        // AK5-I: 0x00FF_FFFF covers Aff0, Aff1, Aff2 — all plausible
        // cluster-ID locations for BCM2712.
        assert_eq!(MPIDR_CORE_ID_MASK, 0x00FF_FFFF);
    }

    #[test]
    fn mpidr_mask_distinguishes_clusters() {
        // {Aff0=0, Aff1=0, Aff2=0} → 0 (boot core)
        assert_eq!(0u64 & MPIDR_CORE_ID_MASK, 0);
        // Secondary core within cluster 0
        assert_eq!(0x01u64 & MPIDR_CORE_ID_MASK, 0x01);
        // Aff1-encoded cluster (bit 8 = cluster 1): non-zero after mask
        assert_eq!(0x0100u64 & MPIDR_CORE_ID_MASK, 0x0100);
        // Aff2-encoded cluster (bit 16 = cluster 1): non-zero after mask
        assert_eq!(0x0001_0000u64 & MPIDR_CORE_ID_MASK, 0x0001_0000);
        // Aff3 (bits [39:32]) is IGNORED — BCM2712 does not use it.
        assert_eq!(0x0000_0080_0000_0000u64 & MPIDR_CORE_ID_MASK, 0);
    }

    #[test]
    fn mpidr_mask_strips_multiprocessor_extension_bits() {
        // Bits 24 (MT), 30 (U) are outside the affinity fields.
        assert_eq!(0x4100_0000u64 & MPIDR_CORE_ID_MASK, 0);
    }

    #[test]
    fn mpidr_mask_primary_only_accepts_zero() {
        // AK5-I invariant: primary boot core is the unique MPIDR whose
        // masked core ID is 0. Any non-zero cluster or core ID fails.
        for raw in [0x0001_u64, 0x0100, 0x0001_0000, 0x00FF_FFFF] {
            assert_ne!(raw & MPIDR_CORE_ID_MASK, 0,
                "MPIDR {raw:#x} incorrectly alias to boot core");
        }
    }

    #[test]
    fn current_core_id_on_host() {
        // On non-aarch64 hosts, current_core_id returns 0 (boot core alias).
        #[cfg(not(target_arch = "aarch64"))]
        assert_eq!(current_core_id(), 0);
    }
}
