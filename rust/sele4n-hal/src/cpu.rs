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

/// Read the MPIDR_EL1 register to determine the current core ID.
///
/// Returns the Aff0 field (bits [7:0]), which is the core number within a
/// cluster on Cortex-A76.
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
        mpidr & 0xFF
    }
    #[cfg(not(target_arch = "aarch64"))]
    0
}
