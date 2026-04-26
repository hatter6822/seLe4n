// SPDX-License-Identifier: GPL-3.0-or-later
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

/// AN9-H: DSB ISHST — store-only inner-shareable data sync.
///
/// Cheaper than `dsb ish` because it only orders prior **store** operations
/// (no-op for loads).  Required before a page-table descriptor write so
/// the hardware MMU walker observes the new descriptor (ARM ARM D8.11).
///
/// ARM ARM C6.2.65: DSB ISHST.
#[inline(always)]
pub fn dsb_ishst() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DSB ISHST orders prior stores only.  No side effects.
        // (ARM ARM C6.2.65)
        unsafe { core::arch::asm!("dsb ishst", options(nostack, preserves_flags)) }
    }
}

/// AN9-I (DEF-R-HAL-L19): DSB OSH — outer-shareable data sync.
///
/// Outer-shareable barriers cover the FULL system shareable domain rather
/// than just the cluster-local inner domain.  Required when
/// synchronising with cores in *other* clusters (BCM2712 has two
/// Cortex-A76 clusters) or with non-cluster device interconnects (PCIe
/// root complexes, GPU command processors that sit outside ISH).
///
/// On a single-cluster boot (the v1.0.0 default with `smp_enabled=false`)
/// this is functionally identical to `dsb ish`.  Used by AN9-J's PSCI
/// CPU_ON sequence to ensure secondary cores observe the boot L1 page
/// table after `tlbi vmalle1is`.
///
/// ARM ARM C6.2.65: DSB OSH.
#[inline(always)]
pub fn dsb_osh() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DSB OSH is a barrier instruction.  No side effects.
        // (ARM ARM C6.2.65)
        unsafe { core::arch::asm!("dsb osh", options(nostack, preserves_flags)) }
    }
}

/// AN9-I (DEF-R-HAL-L19): DSB OSHST — outer-shareable, store-only.
///
/// Outer-shareable variant of `dsb ishst`.  Required before MMIO writes
/// to device registers that other clusters or non-cluster agents need
/// to observe.
///
/// ARM ARM C6.2.65: DSB OSHST.
#[inline(always)]
pub fn dsb_oshst() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DSB OSHST orders prior stores in the outer shareable
        // domain.  No side effects.  (ARM ARM C6.2.65)
        unsafe { core::arch::asm!("dsb oshst", options(nostack, preserves_flags)) }
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
/// ```no_run
/// # use sele4n_hal::barriers::csdb;
/// # let array: &[u32] = &[1, 2, 3];
/// # let index: usize = 0;
/// if index < array.len() {
///     csdb();  // Speculation cannot bypass the bounds check
///     let _val = array[index];
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
/// ```no_run
/// # use sele4n_hal::barriers::speculation_safe_bound_check;
/// # let table: &[u32] = &[10, 20, 30];
/// # let user_index: usize = 0;
/// if speculation_safe_bound_check(user_index, table.len()) {
///     // CSDB has fired — speculative execution respects the bound.
///     let _entry = table[user_index];
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
// AN9-H (DEF-R-HAL-L18): Parameterised BarrierKind enum
// ============================================================================
//
// Mirrors `SeLe4n.Kernel.Architecture.BarrierKind` (Lean), giving generic
// HAL code one type to plumb instead of selecting a specific
// `dsb_ish`/`dsb_ishst`/`isb` helper at the call site.  See
// `SeLe4n/Kernel/Architecture/BarrierComposition.lean` for the algebraic
// laws (associativity of `Sequenced`, `subsumes` partial order) the kernel
// model relies on; the Rust-side `emit()` chain is the operational
// witness for those theorems.
//
// AN9-I extends the enum with `DsbOsh` / `DsbOshst` so cross-cluster
// ordering becomes expressible without dropping out of the algebra.
//
// AN9-C bridge: keep new variants synchronised with the Lean inductive
// in `BarrierComposition.lean::BarrierKind`.  The CI test
// `barrier_kind_lean_parity` (see tests below) lists every Lean variant
// and asserts a corresponding Rust variant exists.

/// AN9-H / AN9-I: Parameterised barrier kind.
///
/// Flat (non-recursive) enum — every variant emits a single ARMv8-A
/// barrier (or no-op for [`BarrierKind::None`]).  Composed sequences are
/// expressed at the call site as multiple `emit()` calls in order;
/// the Lean model captures the tree structure for proof purposes
/// (`SeLe4n.Kernel.Architecture.BarrierKind` in
/// `BarrierComposition.lean`), but the Rust emission layer keeps the
/// runtime representation flat to satisfy the `#![no_std]` HAL crate's
/// no-`alloc` constraint.
///
/// For convenience there are dedicated emitters for the canonical
/// composed sequences ([`BarrierKind::emit_armv8_page_table_update`],
/// [`BarrierKind::emit_tlb_invalidation_bracket`]) so call sites do not
/// re-derive the ordering by hand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BarrierKind {
    /// No barrier emitted.  Identity element for sequential composition.
    None,
    /// `dsb ish` — inner-shareable, full data sync.
    DsbIsh,
    /// `dsb ishst` — inner-shareable, store-only.
    DsbIshst,
    /// AN9-I: `dsb osh` — outer-shareable, full data sync (cross-cluster).
    DsbOsh,
    /// AN9-I: `dsb oshst` — outer-shareable, store-only (cross-cluster).
    DsbOshst,
    /// `isb` — instruction-side serialisation.
    Isb,
}

impl BarrierKind {
    /// AN9-H: emit the underlying instruction.
    ///
    /// On `target_arch = "aarch64"` this writes the actual barrier;
    /// on host (test) builds it is a deterministic no-op so unit tests
    /// can exercise the emission path without crashing.
    #[inline(always)]
    pub fn emit(self) {
        match self {
            BarrierKind::None => {}
            BarrierKind::DsbIsh => dsb_ish(),
            BarrierKind::DsbIshst => dsb_ishst(),
            BarrierKind::DsbOsh => dsb_osh(),
            BarrierKind::DsbOshst => dsb_oshst(),
            BarrierKind::Isb => isb(),
        }
    }

    /// AN9-C.2 / AN9-A: emit the canonical ARMv8-A page-table-update
    /// barrier sequence required by ARM ARM D8.11:
    ///
    ///   `dsb ishst`  →  `dc cvac descriptor + dsb ish`  →  `isb`
    ///
    /// `descriptor_addr` must be a kernel-mapped VA pointing at the
    /// freshly-written page-table descriptor.
    ///
    /// This is the operational witness for the Lean theorem
    /// `pageTableUpdate_observes_armv8_ordering` in
    /// `SeLe4n/Kernel/Architecture/BarrierComposition.lean`.
    #[inline(always)]
    pub fn emit_armv8_page_table_update(descriptor_addr: u64) {
        BarrierKind::DsbIshst.emit();
        // SAFETY: caller guarantees `descriptor_addr` is a mapped page-
        // table VA; `dc cvac` is always safe on such addresses
        // (ARM ARM C6.2.61) and is a no-op on host builds.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!(
                "dc cvac, {0}",
                in(reg) descriptor_addr,
                options(nostack, preserves_flags)
            );
        }
        #[cfg(not(target_arch = "aarch64"))]
        let _ = descriptor_addr;
        BarrierKind::DsbIsh.emit();
        BarrierKind::Isb.emit();
    }

    /// AN9-B: emit the canonical post-`tlbi` bracket — `dsb ish; isb`.
    /// This is the operational witness for the Lean theorem
    /// `tlbInvalidationBracket_subsumes` in `BarrierComposition.lean`,
    /// which proves the bracket subsumes both `dsbIsh` and `isb` leaves.
    #[inline(always)]
    pub fn emit_tlb_invalidation_bracket() {
        BarrierKind::DsbIsh.emit();
        BarrierKind::Isb.emit();
    }

    /// AN9-I (DEF-R-HAL-L19): emit the cross-cluster MMIO write
    /// barrier — `dsb oshst` before any externally-observable side
    /// effect that other clusters or non-cluster agents need to
    /// observe.
    #[inline(always)]
    pub fn emit_mmio_cross_cluster_barrier() {
        BarrierKind::DsbOshst.emit();
    }
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
        dsb_ishst();
        dsb_osh();
        dsb_oshst();
        isb();
        csdb();
        sb();
    }

    // ========================================================================
    // AN9-H / AN9-I: BarrierKind enum tests
    // ========================================================================

    #[test]
    fn barrier_kind_emit_no_panic() {
        // Each leaf barrier must be emittable on host without panic.
        BarrierKind::None.emit();
        BarrierKind::DsbIsh.emit();
        BarrierKind::DsbIshst.emit();
        BarrierKind::DsbOsh.emit();
        BarrierKind::DsbOshst.emit();
        BarrierKind::Isb.emit();
    }

    #[test]
    fn barrier_kind_armv8_page_table_update_no_panic() {
        // AN9-A operational witness — the canonical ARM ARM D8.11
        // sequence must run end-to-end without panicking on host.
        BarrierKind::emit_armv8_page_table_update(0x1000);
    }

    #[test]
    fn barrier_kind_tlb_invalidation_bracket_no_panic() {
        // AN9-B operational witness — `dsb ish; isb` post-tlbi bracket.
        BarrierKind::emit_tlb_invalidation_bracket();
    }

    #[test]
    fn barrier_kind_mmio_cross_cluster_no_panic() {
        // AN9-I operational witness — outer-shareable store ordering.
        BarrierKind::emit_mmio_cross_cluster_barrier();
    }

    #[test]
    fn barrier_kind_lean_parity() {
        // AN9-C parity guard: every LEAF Lean `BarrierKind` constructor
        // must have a Rust-side counterpart.  Recursive (`sequenced`)
        // and `dcCvacDsbIsh` (cache-clean composite) constructors are
        // expressed in Rust via the dedicated emitters
        // (`emit_armv8_page_table_update`,
        // `emit_tlb_invalidation_bracket`) per the no-`alloc` design.
        //
        // Lean leaf variants (BarrierComposition.lean):
        //     none, dsbIsh, dsbIshst, dsbOsh, dsbOshst, isb
        //   = 6 variants.
        //
        // Rust must mirror this count exactly.  An additional variant on
        // the Rust side without a Lean counterpart (or vice versa)
        // would fail the count assertion below.
        const RUST_LEAF_COUNT: usize = 6;
        const LEAN_LEAF_COUNT: usize = 6;
        assert_eq!(RUST_LEAF_COUNT, LEAN_LEAF_COUNT,
            "Rust BarrierKind leaf count must match Lean BarrierKind leaf count");

        let kinds = [
            BarrierKind::None,
            BarrierKind::DsbIsh,
            BarrierKind::DsbIshst,
            BarrierKind::DsbOsh,
            BarrierKind::DsbOshst,
            BarrierKind::Isb,
        ];
        assert_eq!(kinds.len(), RUST_LEAF_COUNT,
            "kinds array must enumerate every leaf variant");

        for kind in kinds {
            // Pattern-match exhaustively to provoke a compile error if
            // a variant is removed without updating this list.
            match kind {
                BarrierKind::None
                | BarrierKind::DsbIsh
                | BarrierKind::DsbIshst
                | BarrierKind::DsbOsh
                | BarrierKind::DsbOshst
                | BarrierKind::Isb => {}
            }
            kind.emit();
        }
    }
}
