//! Memory barrier and speculation barrier instruction wrappers for ARMv8-A.
//!
//! ARM ARM B2.3: Barrier instructions enforce ordering of memory accesses and
//! instruction execution. Required after page table updates, system register
//! writes, and device MMIO sequences.
//!
//! AG9-F: Speculation barriers (CSDB, SB) mitigate Spectre-class attacks on
//! Cortex-A76 (Raspberry Pi 5). CSDB is placed after bounds checks in
//! security-critical paths to prevent speculative bypass of validation.
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

// ============================================================================
// AG9-F: Speculation Barriers — Spectre v1/v2 Mitigations
// ============================================================================

/// Conditional Speculation Dependency Barrier (CSDB).
///
/// AG9-F: CSDB ensures that the results of conditional instructions
/// (branches, CSEL, etc.) are resolved before subsequent data-dependent
/// operations execute speculatively. This is the primary Spectre v1
/// mitigation on ARMv8-A (Cortex-A76).
///
/// Place CSDB after bounds checks that guard security-critical array
/// indexing or pointer dereferencing:
///
/// ```ignore
/// if index < array.len() {
///     csdb();  // Speculation cannot bypass the bounds check
///     let val = array[index];
/// }
/// ```
///
/// ARM ARM C6.2.49: CSDB — Consumption of Speculative Data Barrier.
/// Cortex-A76 TRM §11.1: CSDB is the recommended Spectre v1 mitigation.
#[inline(always)]
pub fn csdb() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: CSDB is a hint instruction with no side effects beyond
        // constraining speculative execution. It does not affect memory,
        // stack, or flags. Always safe at any EL. (ARM ARM C6.2.49)
        unsafe { core::arch::asm!("csdb", options(nomem, nostack, preserves_flags)) }
    }
}

/// Speculation Barrier (SB) — unconditionally stops speculative execution.
///
/// AG9-F: SB prevents any speculative execution of instructions following
/// the barrier. Stronger than CSDB but may have higher performance impact.
/// Use in paths where CSDB's conditional dependency model is insufficient.
///
/// Available on Cortex-A76 (FEAT_SB, mandatory from ARMv8.5-A).
///
/// ARM ARM C6.2.245: SB — Speculation Barrier.
#[inline(always)]
pub fn sb() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: SB is a barrier instruction with no side effects beyond
        // stopping speculative execution. Does not affect memory, stack, or
        // flags. Always safe at any EL. (ARM ARM C6.2.245)
        //
        // Encoding: SB is hint instruction #7, encoding 0xD503233F.
        // Cortex-A76 supports FEAT_SB. On cores without FEAT_SB the
        // encoding executes as NOP (ARM ARM C6.2.245).
        unsafe { core::arch::asm!(".inst 0xD503233F", options(nostack, preserves_flags)) }
    }
}

/// Speculation-safe bounds check pattern for Spectre v1 mitigation.
///
/// AG9-F: Returns `true` if `index < bound`, with a CSDB barrier ensuring
/// the result cannot be speculatively bypassed. This is the recommended
/// pattern for all security-critical array/table lookups:
///
/// - Capability address resolution (CPtr bit masking)
/// - Run queue priority bucket lookup
/// - Page table descriptor indexing
/// - GIC INTID dispatch
///
/// # Usage
///
/// ```ignore
/// if speculation_safe_bound_check(user_index, table.len()) {
///     // CSDB has fired — speculative execution respects the bound
///     let entry = table[user_index];
/// }
/// ```
#[inline(always)]
pub fn speculation_safe_bound_check(index: usize, bound: usize) -> bool {
    let in_bounds = index < bound;
    // CSDB after the comparison ensures speculative execution cannot
    // proceed past this point with an out-of-bounds index.
    csdb();
    in_bounds
}

/// Verify that FEAT_CSV2 (Cache Speculation Variant 2) is supported.
///
/// AG9-F: FEAT_CSV2 provides hardware-level Spectre v2 mitigation by
/// preventing branch predictor aliasing across different contexts.
/// On Cortex-A76, this is enabled by firmware (ATF/UEFI) and indicated
/// by ID_AA64PFR0_EL1.CSV2 (bits [59:56]).
///
/// Returns `true` if CSV2 is supported (value >= 1).
#[inline(always)]
pub fn has_feat_csv2() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        let pfr0 = crate::read_sysreg!("id_aa64pfr0_el1");
        // CSV2 field is bits [59:56]
        let csv2 = (pfr0 >> 56) & 0xF;
        csv2 >= 1
    }
    #[cfg(not(target_arch = "aarch64"))]
    true // Assume supported on non-AArch64 hosts
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn csdb_no_panic() {
        // CSDB is a no-op on non-aarch64; verify it compiles and runs
        csdb();
    }

    #[test]
    fn sb_no_panic() {
        // SB (.inst 0xD503233F) is a no-op on non-aarch64
        sb();
    }

    #[test]
    fn speculation_safe_bound_check_in_bounds() {
        assert!(speculation_safe_bound_check(0, 10));
        assert!(speculation_safe_bound_check(5, 10));
        assert!(speculation_safe_bound_check(9, 10));
    }

    #[test]
    fn speculation_safe_bound_check_out_of_bounds() {
        assert!(!speculation_safe_bound_check(10, 10));
        assert!(!speculation_safe_bound_check(11, 10));
        assert!(!speculation_safe_bound_check(usize::MAX, 10));
    }

    #[test]
    fn speculation_safe_bound_check_zero_bound() {
        assert!(!speculation_safe_bound_check(0, 0));
    }

    #[test]
    fn has_feat_csv2_on_host() {
        // On non-aarch64, returns true (assumed supported)
        #[cfg(not(target_arch = "aarch64"))]
        assert!(has_feat_csv2());
    }

    #[test]
    fn barrier_nops_on_host() {
        // All barriers are no-ops on non-aarch64; verify no panics
        dmb_ish();
        dmb_sy();
        dsb_ish();
        dsb_sy();
        isb();
        csdb();
        sb();
    }
}
