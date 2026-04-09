//! Memory barrier instruction wrappers for ARMv8-A.
//!
//! ARM ARM B2.3: Barrier instructions enforce ordering of memory accesses and
//! instruction execution. Required after page table updates, system register
//! writes, and device MMIO sequences.
//!
//! On non-AArch64 hosts, functions are no-ops for compilation and testing.

/// Data Memory Barrier (Inner Shareable) — ensures that all explicit memory
/// accesses before the DMB are observed before any explicit memory accesses
/// after the DMB, within the Inner Shareable domain.
///
/// ARM ARM C6.2.63: DMB ensures ordering of memory accesses.
#[inline(always)]
pub fn dmb_ish() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DMB ISH is a barrier instruction with no side effects beyond
        // enforcing memory ordering. Always safe at any EL. (ARM ARM C6.2.63)
        unsafe { core::arch::asm!("dmb ish", options(nostack, preserves_flags)) }
    }
}

/// Data Memory Barrier (System) — ensures ordering across the full system
/// domain. Used before cache maintenance operations that must be visible to
/// all agents.
///
/// ARM ARM C6.2.63: DMB SY is the strongest data barrier.
#[inline(always)]
pub fn dmb_sy() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DMB SY is a barrier with no side effects beyond enforcing
        // memory ordering across the full system. (ARM ARM C6.2.63)
        unsafe { core::arch::asm!("dmb sy", options(nostack, preserves_flags)) }
    }
}

/// Data Synchronization Barrier (Inner Shareable) — ensures all memory
/// accesses, cache operations, and TLB maintenance operations before the DSB
/// have completed before any instruction after the DSB executes.
///
/// ARM ARM C6.2.65: DSB is stronger than DMB — it also blocks instruction
/// fetch until all prior accesses complete.
#[inline(always)]
pub fn dsb_ish() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DSB ISH is a barrier instruction. No side effects beyond
        // enforcing completion of prior memory operations. (ARM ARM C6.2.65)
        unsafe { core::arch::asm!("dsb ish", options(nostack, preserves_flags)) }
    }
}

/// Data Synchronization Barrier (System) — strongest data synchronization.
/// Required before MMU enable/disable and after TLBI instructions.
///
/// ARM ARM C6.2.65: DSB SY ensures all memory accesses complete system-wide.
#[inline(always)]
pub fn dsb_sy() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DSB SY is a barrier instruction. No side effects beyond
        // enforcing completion of prior memory operations. (ARM ARM C6.2.65)
        unsafe { core::arch::asm!("dsb sy", options(nostack, preserves_flags)) }
    }
}

/// Instruction Synchronization Barrier — flushes the pipeline and ensures all
/// subsequent instructions are fetched from cache/memory after the ISB.
///
/// Required after:
/// - System register writes (SCTLR_EL1, TCR_EL1, etc.)
/// - TLBI instructions (after DSB)
/// - Code modification (self-modifying code)
///
/// ARM ARM C6.2.89: ISB flushes the instruction pipeline.
#[inline(always)]
pub fn isb() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: ISB is a barrier instruction. No side effects beyond flushing
        // the instruction pipeline. Always safe at any EL. (ARM ARM C6.2.89)
        unsafe { core::arch::asm!("isb", options(nostack, preserves_flags)) }
    }
}
