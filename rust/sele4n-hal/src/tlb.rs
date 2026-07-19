// SPDX-License-Identifier: GPL-3.0-or-later
//! TLB (Translation Lookaside Buffer) flush instruction wrappers for ARMv8-A.
//!
//! Each TLBI instruction is followed by a DSB barrier in the appropriate
//! shareability domain (ISH for cluster-local, OSH for cross-cluster) plus
//! ISB per ARM ARM D8.11:
//! "A TLB maintenance instruction is only guaranteed to be complete after the
//! execution of a DSB instruction." The ISB ensures the pipeline sees the new
//! translations.
//!
//! ## Module composition
//!
//! - **AG6-E / AG6-G**: original local TLBI variants (no broadcast).  Used
//!   by single-core code paths where the calling PE owns the only TLB
//!   that needs invalidation.  Now superseded by the IS variants for
//!   any path that runs after SMP enablement.
//! - **WS-SM SM1.E.1**: IS-variant TLBI instructions (`tlbi_*is`) that
//!   broadcast the invalidation to every PE in the inner-shareable
//!   domain.  Required on any post-SM1.D kernel because multiple cores
//!   may have cached the same translation.  Followed by the same
//!   `dsb ish` + `isb` bracket as the local variants — the difference
//!   is the TLBI instruction itself (broadcast vs local-only), not the
//!   barrier.
//! - **WS-SM SM1.E.2**: OS-variant TLBI instructions (`tlbi_*os`) that
//!   broadcast across the outer-shareable domain.  Pre-positioned for
//!   future multi-cluster ports (BCM2712 is single-cluster, so
//!   functionally identical to IS variants on RPi5).  Followed by
//!   `dsb osh` + `isb` (matching the broader scope).
//! - **WS-SM SM1.E.3**: `tlbi_for_sharing` dispatcher routes to either
//!   the IS or OS variant based on a `SharingDomain` enum, allowing
//!   generic kernel code to emit the correct broadcast without per-call
//!   platform branches.
//!
//! ## Why IS, not local
//!
//! On a quiescent single-core boot path (pre-Phase-5), the local
//! variants are sufficient — only the boot core owns a TLB.  But
//! every path reachable AFTER `apply_cmdline_and_start_smp` may run
//! with secondaries online, in which case a non-broadcast TLBI would
//! leave stale translations cached on the secondaries.  Once a
//! secondary executed code with a stale translation it could load a
//! page that the primary believes is unmapped (or worse, mapped for
//! a different process).
//!
//! Per WS-SM SM1.E.5, all kernel-side TLB invalidations route through
//! the `tlbi_for_sharing` dispatcher (which always selects an IS or
//! OS variant based on the platform's `SharingDomain`).  Direct calls
//! to the local variants (`tlbi_vmalle1`, etc.) are reserved for
//! the boot-time MMU-init path BEFORE secondaries have started, when
//! broadcast is not just unnecessary but actually wrong (the
//! secondaries are still parked in `boot.S::.L_secondary_spin` and
//! their TLBs are empty — issuing an IS broadcast at that point would
//! still be correct, just wasteful).
//!
//! ## Operand encoding
//!
//! The TLBI VAE1/VAE1IS/VAE1OS family takes a single Xt register
//! holding the encoded operand per ARM ARM C6.2.311 (DDI 0487):
//!
//! ```text
//! [63:48] = ASID (16 bits)
//! [47:44] = RES0 in ARMv8.0–8.3; TTL (Translation Table Level hint)
//!           in ARMv8.4+ (FEAT_TTL).  Cortex-A76 (RPi5) is ARMv8.2 so
//!           these bits MUST be zero on this hardware — leaving them
//!           non-zero is a contract violation and would silently
//!           change semantics on a FEAT_TTL hardware port.
//! [43:0]  = VA[55:12] (44 bits, page-aligned virtual address)
//! ```
//!
//! Accordingly the encoder masks `vaddr >> 12` to the **44-bit**
//! field [43:0] — NOT the 48-bit window — so adversarial vaddrs
//! exceeding 2^56 cannot pollute the RES0/TTL bits.  For well-formed
//! callers (vaddr < 2^48) the masked-vs-unmasked behaviour is
//! identical because `vaddr >> 12 < 2^36`; the defensive masking
//! exists to keep the encoder spec-compliant on every input.
//!
//! The TLBI ASIDE1/ASIDE1IS/ASIDE1OS family encodes only the ASID
//! in [63:48]; bits [47:0] are RES0.
//!
//! On non-AArch64 hosts, functions are no-ops for compilation and testing.
//!
//! References:
//! - ARM ARM C6.2.311–316: TLBI instructions
//! - ARM ARM D8.11: TLB maintenance requirements
//! - ARM ARM B2.7: Memory shareability domains
//! - ARM ARM D5.10.1 (FEAT_TTL): TTL field semantics in ARMv8.4+

use crate::barriers;

// ============================================================================
// Operand encoding — shared between every VA-by-ASID TLBI form.
// ============================================================================

/// TLBI operand encoding for VA-by-ASID forms (VAE1, VAE1IS, VAE1OS,
/// VALE1, VALE1IS, VALE1OS).
///
/// ARM ARM C6.2.311 (DDI 0487): bits [63:48] hold the 16-bit ASID;
/// bits [47:44] are RES0 in ARMv8.0–8.3 and TTL (Translation Table
/// Level hint) in ARMv8.4+ (FEAT_TTL); bits [43:0] hold VA[55:12]
/// (the upper 44 bits of the page-aligned VA, i.e., `vaddr >> 12`).
///
/// The encoder masks `vaddr >> 12` to the **44-bit** field [43:0],
/// NOT the 48-bit window covering RES0/TTL.  Two reasons:
///
/// 1. **Spec compliance**: leaving the RES0 bits [47:44] non-zero on
///    ARMv8.0–8.3 hardware (Cortex-A76 / RPi5) is a contract violation.
///    Even though current hardware accepts the encoding, future
///    revisions or microarchitectural changes are free to reject it.
/// 2. **Forward-compatibility on FEAT_TTL hardware**: an adversarial
///    `vaddr >= 2^56` would shift bit 44 (or higher) into the operand,
///    which on FEAT_TTL hardware is the TTL "level 1 hint" — silently
///    converting "invalidate all levels" into "invalidate level 1
///    only", leaving level 2/3 translations stale.
///
/// For well-formed callers (`vaddr < 2^48`, enforced by `TCR_EL1.IPS =
/// 0b101` = 48-bit IPA), `vaddr >> 12 < 2^36`, so masking with 44 vs
/// 48 bits is observationally identical.  The defensive mask exists
/// only to keep the encoder spec-compliant against adversarial inputs
/// (memory corruption, FFI ABI errors, etc.).
#[inline(always)]
const fn encode_va_asid_operand(asid: u16, vaddr: u64) -> u64 {
    // 44-bit mask for VA[55:12] field per ARM ARM C6.2.311.  Higher
    // bits (which would land in RES0/TTL on the operand) are zeroed.
    ((asid as u64) << 48) | ((vaddr >> 12) & 0x0000_0FFF_FFFF_FFFF)
}

/// TLBI operand encoding for ASID-only forms (ASIDE1, ASIDE1IS,
/// ASIDE1OS).
///
/// ARM ARM C6.2.312: bits [63:48] hold the 16-bit ASID; bits [47:0]
/// are RES0.
#[inline(always)]
const fn encode_asid_only_operand(asid: u16) -> u64 {
    (asid as u64) << 48
}

// ============================================================================
// AG6-E / AG6-G — Local TLBI variants (no broadcast)
//
// These remain available for the boot-time MMU-init path before
// secondaries start.  Post-SM1.D production kernel code should route
// through `tlbi_for_sharing` instead.
// ============================================================================

/// Flush all TLB entries at EL1 (TLBI VMALLE1).
///
/// Invalidates all stage 1 translations used at EL0 and EL1 for the
/// current VMID. Used for full address space flushes (e.g., after TTBR switch).
///
/// ARM ARM C6.2.316: TLBI VMALLE1
#[inline(always)]
pub fn tlbi_vmalle1() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VMALLE1 is a TLB maintenance instruction that
        // invalidates cached translations. No memory corruption — only forces
        // re-walk from page tables. (ARM ARM C6.2.316)
        unsafe {
            core::arch::asm!("tlbi vmalle1", options(nostack, preserves_flags));
        }
    }
    // AG6-G: DSB ISH + ISB after TLBI per ARM ARM D8.11
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush TLB entries by virtual address at EL1 (TLBI VAE1).
///
/// Invalidates all stage 1 translations for the specified virtual address
/// and ASID. The address must be right-shifted by 12 (page-aligned) and
/// the ASID occupies bits [63:48] of the operand.
///
/// ARM ARM C6.2.311: TLBI VAE1, Xt
#[inline(always)]
pub fn tlbi_vae1(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VAE1 invalidates TLB entries matching the specified
        // VA and ASID. No memory corruption. (ARM ARM C6.2.311)
        unsafe {
            core::arch::asm!("tlbi vae1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush TLB entries by ASID at EL1 (TLBI ASIDE1).
///
/// Invalidates all stage 1 translations for the specified ASID.
/// The ASID occupies bits [63:48] of the operand.
///
/// ARM ARM C6.2.312: TLBI ASIDE1, Xt
#[inline(always)]
pub fn tlbi_aside1(asid: u16) {
    let _operand = encode_asid_only_operand(asid);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI ASIDE1 invalidates TLB entries matching the ASID.
        // No memory corruption. (ARM ARM C6.2.312)
        unsafe {
            core::arch::asm!("tlbi aside1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush last-level TLB entries by VA at EL1 (TLBI VALE1).
///
/// Like VAE1 but only invalidates last-level (L3 page) TLB entries,
/// leaving intermediate level entries cached. More efficient for single
/// page unmap operations.
///
/// ARM ARM C6.2.313: TLBI VALE1, Xt
#[inline(always)]
pub fn tlbi_vale1(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VALE1 invalidates last-level TLB entries matching the
        // specified VA and ASID. No memory corruption. (ARM ARM C6.2.313)
        unsafe {
            core::arch::asm!("tlbi vale1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

// ============================================================================
// WS-SM SM1.E.1 — Inner-Shareable broadcast TLBI variants
//
// Each *IS variant broadcasts the invalidation to every PE in the
// inner-shareable domain.  On RPi5 (single-cluster Cortex-A76 quad)
// the IS domain covers all 4 cores; on a hypothetical multi-cluster
// port the OS variants would cover the additional clusters.
// ============================================================================

/// **WS-SM SM1.E.1**: TLBI VMALLE1IS — flush all TLB entries,
/// inner-shareable broadcast.
///
/// Invalidates all stage 1 translations used at EL0 and EL1 for the
/// current VMID, on EVERY PE in the inner-shareable domain.  Used for
/// full address-space flushes that must affect secondaries (e.g., after
/// a global TTBR switch under SMP).
///
/// Like the local `tlbi_vmalle1`, the IS variant is followed by
/// `dsb ish` + `isb` per ARM ARM D8.11 to ensure (a) the broadcast
/// has reached every PE and (b) the calling PE's pipeline observes
/// the new translations.
///
/// ARM ARM C6.2.316: TLBI VMALLE1IS
#[inline(always)]
pub fn tlbi_vmalle1is() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VMALLE1IS broadcasts a TLB invalidation across
        // the inner-shareable domain.  No memory corruption — only
        // forces re-walk from page tables on every PE. (ARM ARM C6.2.316)
        unsafe {
            core::arch::asm!("tlbi vmalle1is", options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// **WS-SM SM1.E.1**: TLBI VAE1IS — flush by VA + ASID,
/// inner-shareable broadcast.
///
/// Invalidates stage 1 translations for the specified virtual address
/// and ASID, on EVERY PE in the inner-shareable domain.  Required when
/// unmapping a page that may be cached in secondaries' TLBs.
///
/// ARM ARM C6.2.311: TLBI VAE1IS, Xt
#[inline(always)]
pub fn tlbi_vae1is(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VAE1IS broadcasts a VA+ASID invalidation across
        // the inner-shareable domain. (ARM ARM C6.2.311)
        unsafe {
            core::arch::asm!("tlbi vae1is, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// **WS-SM SM1.E.1**: TLBI ASIDE1IS — flush by ASID,
/// inner-shareable broadcast.
///
/// Invalidates all stage 1 translations for the specified ASID, on
/// EVERY PE in the inner-shareable domain.  Used when retiring an
/// ASID under SMP.
///
/// ARM ARM C6.2.312: TLBI ASIDE1IS, Xt
#[inline(always)]
pub fn tlbi_aside1is(asid: u16) {
    let _operand = encode_asid_only_operand(asid);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI ASIDE1IS broadcasts an ASID invalidation across
        // the inner-shareable domain. (ARM ARM C6.2.312)
        unsafe {
            core::arch::asm!("tlbi aside1is, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// **WS-SM SM1.E.1**: TLBI VALE1IS — flush last-level by VA + ASID,
/// inner-shareable broadcast.
///
/// Like VAE1IS but only invalidates last-level (L3 page) TLB entries.
/// More efficient for single-page unmap operations under SMP.
///
/// ARM ARM C6.2.313: TLBI VALE1IS, Xt
#[inline(always)]
pub fn tlbi_vale1is(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VALE1IS broadcasts a last-level VA+ASID
        // invalidation across the inner-shareable domain. (ARM ARM C6.2.313)
        unsafe {
            core::arch::asm!("tlbi vale1is, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

// ============================================================================
// WS-SM SM1.E.2 — Outer-Shareable broadcast TLBI variants
//
// The OS variants broadcast across the outer-shareable domain,
// covering observers outside the calling cluster.  RPi5 BCM2712 is
// single-cluster, so the OS variants are functionally identical to
// IS on this platform — but pre-positioning them lets future
// multi-cluster ports drop in the OS variant without rewriting the
// TLBI call sites.
//
// On the OS variants, the post-TLBI barrier is `dsb osh` (matching
// the broadcast scope) rather than `dsb ish`, so the calling PE
// waits for the broadcast to complete across the wider domain.
// ============================================================================

/// **WS-SM SM1.E.2**: TLBI VMALLE1OS — flush all TLB entries,
/// outer-shareable broadcast.
///
/// Invalidates all stage 1 translations on EVERY PE in the
/// outer-shareable domain.  On RPi5 (single-cluster) this is
/// functionally equivalent to `tlbi_vmalle1is`; on a multi-cluster
/// port it covers the additional clusters too.
///
/// Followed by `dsb osh` (matching the broadcast scope) and `isb`.
///
/// ARM ARM C6.2.316: TLBI VMALLE1OS
#[inline(always)]
pub fn tlbi_vmalle1os() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VMALLE1OS broadcasts a TLB invalidation across
        // the outer-shareable domain. (ARM ARM C6.2.316)
        unsafe {
            core::arch::asm!("tlbi vmalle1os", options(nostack, preserves_flags));
        }
    }
    barriers::dsb_osh();
    barriers::isb();
}

/// **WS-SM SM1.E.2**: TLBI VAE1OS — flush by VA + ASID,
/// outer-shareable broadcast.
///
/// Invalidates stage 1 translations for the specified VA + ASID on
/// EVERY PE in the outer-shareable domain.
///
/// ARM ARM C6.2.311: TLBI VAE1OS, Xt
#[inline(always)]
pub fn tlbi_vae1os(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VAE1OS broadcasts a VA+ASID invalidation across
        // the outer-shareable domain. (ARM ARM C6.2.311)
        unsafe {
            core::arch::asm!("tlbi vae1os, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_osh();
    barriers::isb();
}

/// **WS-SM SM1.E.2**: TLBI ASIDE1OS — flush by ASID,
/// outer-shareable broadcast.
///
/// Invalidates all stage 1 translations for the specified ASID on
/// EVERY PE in the outer-shareable domain.
///
/// ARM ARM C6.2.312: TLBI ASIDE1OS, Xt
#[inline(always)]
pub fn tlbi_aside1os(asid: u16) {
    let _operand = encode_asid_only_operand(asid);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI ASIDE1OS broadcasts an ASID invalidation across
        // the outer-shareable domain. (ARM ARM C6.2.312)
        unsafe {
            core::arch::asm!("tlbi aside1os, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_osh();
    barriers::isb();
}

/// **WS-SM SM1.E.2**: TLBI VALE1OS — flush last-level by VA + ASID,
/// outer-shareable broadcast.
///
/// Like VAE1OS but only invalidates last-level (L3 page) TLB entries.
///
/// ARM ARM C6.2.313: TLBI VALE1OS, Xt
#[inline(always)]
pub fn tlbi_vale1os(asid: u16, vaddr: u64) {
    let _operand = encode_va_asid_operand(asid, vaddr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VALE1OS broadcasts a last-level VA+ASID
        // invalidation across the outer-shareable domain. (ARM ARM C6.2.313)
        unsafe {
            core::arch::asm!("tlbi vale1os, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_osh();
    barriers::isb();
}

// ============================================================================
// WS-SM SM1.E.3 — `tlbi_for_sharing` dispatcher
//
// Routes a TLBI operation to the appropriate IS or OS variant based on
// the platform's `SharingDomain`.  This is the single entry point
// kernel code uses for TLB invalidation under SMP.
// ============================================================================

/// **WS-SM SM1.E.3**: Sharing-domain selector for TLBI broadcast scope.
///
/// Mirrors the Lean-side `SeLe4n.Kernel.Concurrency.SharingDomain`
/// enum (in `SeLe4n/Kernel/Concurrency/Types.lean`) so the Rust HAL
/// can route TLBI operations to the IS or OS variant based on the
/// platform's binding.  The Lean side is the source of truth for the
/// per-platform value (`PlatformBinding.sharingDomain`); the Rust
/// side mirrors the enum so generic kernel code does not have to
/// per-call-site branch on the sharing domain.
///
/// On RPi5 BCM2712 the value is `Inner` (single Cortex-A76 cluster);
/// the `Outer` variant is pre-positioned for multi-cluster ports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SharingDomain {
    /// Inner-shareable — covers PEs in the same cluster.  Default for
    /// single-cluster topologies.  Maps to the `*IS` TLBI variants
    /// (which use `dsb ish` for completion).
    Inner,
    /// Outer-shareable — covers PEs in additional clusters and
    /// non-cluster device interconnects.  Maps to the `*OS` TLBI
    /// variants (which use `dsb osh` for completion).
    Outer,
}

/// **WS-SM SM1.E.3**: TLBI operation kind selector.
///
/// One variant per logical TLBI operation; the dispatcher routes each
/// to the appropriate IS or OS instruction based on the
/// `SharingDomain` argument.
///
/// The four operations cover every kernel-side TLB invalidation
/// pattern:
///
/// - `Vmalle1`     — full address-space flush (used after TTBR switch
///   or ASID retirement).
/// - `Vae1{vaddr,asid}` — single-page invalidation including all
///   intermediate-level entries (used by full unmap paths).
/// - `Aside1{asid}` — full ASID flush (used when retiring an ASID).
/// - `Vale1{vaddr,asid}` — last-level-only single-page invalidation
///   (cheaper than `Vae1` when the caller knows the unmap is at the
///   page-table leaf).
///
/// Each variant carries the operand fields required by the underlying
/// asm encoding; `Vmalle1` takes no operand because the instruction
/// itself encodes the action.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TlbInvalidation {
    /// TLBI VMALLE1{IS,OS} — invalidate every entry at EL1.
    Vmalle1,
    /// TLBI VAE1{IS,OS} — invalidate by VA + ASID (all levels).
    Vae1 {
        /// 16-bit ASID
        asid: u16,
        /// Page-aligned virtual address
        vaddr: u64,
    },
    /// TLBI ASIDE1{IS,OS} — invalidate every entry for the given ASID.
    Aside1 {
        /// 16-bit ASID
        asid: u16,
    },
    /// TLBI VALE1{IS,OS} — invalidate last-level only by VA + ASID.
    Vale1 {
        /// 16-bit ASID
        asid: u16,
        /// Page-aligned virtual address
        vaddr: u64,
    },
}

/// **WS-SM SM1.E.3**: Sharing-domain-routed TLBI dispatcher.
///
/// Single entry point for kernel-side TLB invalidation.  Routes the
/// operation to the appropriate IS or OS variant based on the
/// platform's `SharingDomain`:
///
///   - `(Inner, Vmalle1)` → `tlbi_vmalle1is()`
///   - `(Outer, Vmalle1)` → `tlbi_vmalle1os()`
///   - `(Inner, Vae1 { ... })` → `tlbi_vae1is(asid, vaddr)`
///   - `(Outer, Vae1 { ... })` → `tlbi_vae1os(asid, vaddr)`
///   - ... and similarly for `Aside1` and `Vale1`.
///
/// Each underlying call emits the proper post-TLBI barrier sequence
/// (`dsb ish` + `isb` for IS, `dsb osh` + `isb` for OS), so the
/// dispatcher's caller does not need to pair it with a separate
/// barrier.
///
/// ## Usage
///
/// Production kernel code that needs to invalidate a TLB entry should
/// call `tlbi_for_sharing` with the platform's
/// `PlatformBinding.sharingDomain`, NOT call `tlbi_vae1is` or
/// `tlbi_vae1` directly.  The latter two skip the dispatcher and
/// hard-code the broadcast scope, which is incorrect for any
/// multi-cluster port.
///
/// ## Why not store the domain inside `TlbInvalidation`?
///
/// The domain is a per-platform invariant — every TLBI in the kernel
/// runs in the same domain selected by `PlatformBinding.sharingDomain`.
/// Storing it inside the operation enum would either (a) duplicate
/// the field on every variant or (b) force the caller to construct
/// the enum value with the platform binding in scope, leaking
/// platform configuration into pure operation descriptions.  Keeping
/// the domain as a separate `tlbi_for_sharing` argument makes the
/// platform binding explicit at the call site without polluting the
/// operation type.
#[inline(always)]
pub fn tlbi_for_sharing(domain: SharingDomain, op: TlbInvalidation) {
    match (domain, op) {
        (SharingDomain::Inner, TlbInvalidation::Vmalle1) => tlbi_vmalle1is(),
        (SharingDomain::Outer, TlbInvalidation::Vmalle1) => tlbi_vmalle1os(),
        (SharingDomain::Inner, TlbInvalidation::Vae1 { asid, vaddr }) => {
            tlbi_vae1is(asid, vaddr)
        }
        (SharingDomain::Outer, TlbInvalidation::Vae1 { asid, vaddr }) => {
            tlbi_vae1os(asid, vaddr)
        }
        (SharingDomain::Inner, TlbInvalidation::Aside1 { asid }) => tlbi_aside1is(asid),
        (SharingDomain::Outer, TlbInvalidation::Aside1 { asid }) => tlbi_aside1os(asid),
        (SharingDomain::Inner, TlbInvalidation::Vale1 { asid, vaddr }) => {
            tlbi_vale1is(asid, vaddr)
        }
        (SharingDomain::Outer, TlbInvalidation::Vale1 { asid, vaddr }) => {
            tlbi_vale1os(asid, vaddr)
        }
    }
}

/// **WS-SM SM7.B (per-descriptor handler retire)**: execute a single
/// invalidation operand on the **local** PE only (no inter-core
/// broadcast).  The local counterpart of [`tlbi_for_sharing`]: each
/// call ends with the primitive's own `dsb ish; isb` bracket.
///
/// Used by the `.tlbShootdownReq` handler to retire the round's exact
/// operands on the interrupted core — replacing the former blanket
/// `tlbi vmalle1`, so the runtime handler's TLB effect matches the Lean
/// model's per-descriptor `applyTlbInvalidations` exactly (the SM7.B
/// debt-(1) fidelity close).  A `Vmalle1` operand still means "flush
/// everything locally" (the conservative fallback / coalesced round).
#[inline]
pub fn tlbi_local(op: TlbInvalidation) {
    match op {
        TlbInvalidation::Vmalle1 => tlbi_vmalle1(),
        TlbInvalidation::Vae1 { asid, vaddr } => tlbi_vae1(asid, vaddr),
        TlbInvalidation::Aside1 { asid } => tlbi_aside1(asid),
        TlbInvalidation::Vale1 { asid, vaddr } => tlbi_vale1(asid, vaddr),
    }
}

/// **WS-SM SM7.B**: decode an `(op_tag, asid, vaddr)` triple into a
/// typed [`TlbInvalidation`], returning `None` on an out-of-range
/// `op_tag`.  The op-tag encoding mirrors the Lean
/// `Architecture.TlbInvalidation.toOpTag` (0=Vmalle1, 1=Vae1, 2=Aside1,
/// 3=Vale1) — pinned by the SM7.B conformance tests.  Shared by the
/// FFI `tlbiForSharing` dispatcher and the per-descriptor handler
/// retire path so both decode operands identically.
#[inline]
pub const fn decode_tlb_invalidation(op_tag: u32, asid: u16, vaddr: u64) -> Option<TlbInvalidation> {
    match op_tag {
        0 => Some(TlbInvalidation::Vmalle1),
        1 => Some(TlbInvalidation::Vae1 { asid, vaddr }),
        2 => Some(TlbInvalidation::Aside1 { asid }),
        3 => Some(TlbInvalidation::Vale1 { asid, vaddr }),
        _ => None,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // AG6-E (legacy local variants) — original tests preserved
    // ========================================================================

    #[test]
    fn test_tlbi_vmalle1_compiles() {
        // On non-aarch64, this is a no-op but must compile
        tlbi_vmalle1();
    }

    #[test]
    fn test_tlbi_vae1_compiles() {
        tlbi_vae1(42, 0x1000);
    }

    #[test]
    fn test_tlbi_aside1_compiles() {
        tlbi_aside1(42);
    }

    #[test]
    fn test_tlbi_vale1_compiles() {
        tlbi_vale1(42, 0x1000);
    }

    #[test]
    fn test_vae1_operand_encoding() {
        // ASID=5, VA=0x12345000
        // Expected: ASID in bits [63:48], VA[55:12] in bits [43:0]
        // (RES0/TTL bits [47:44] = 0).
        let asid: u16 = 5;
        let vaddr: u64 = 0x12345000;
        let operand = encode_va_asid_operand(asid, vaddr);
        assert_eq!(operand >> 48, 5);
        // The VA field is 44 bits ([43:0]), not 48 — assert the
        // narrower mask so a regression that loosens to 48 bits
        // surfaces here.
        assert_eq!(operand & 0x0FFF_FFFF_FFFF, 0x12345);
        // RES0/TTL bits [47:44] must be zero for spec compliance.
        assert_eq!((operand >> 44) & 0xF, 0, "RES0/TTL bits [47:44] must be 0");
    }

    #[test]
    fn test_aside1_operand_encoding() {
        let asid: u16 = 0xABCD;
        let operand = encode_asid_only_operand(asid);
        assert_eq!(operand >> 48, 0xABCD);
        assert_eq!(operand & 0x0000_FFFF_FFFF_FFFF, 0);
    }

    // ========================================================================
    // WS-SM SM1.E.1 — IS-variant TLBI tests
    // ========================================================================

    #[test]
    fn sm1e1_tlbi_vmalle1is_compiles_and_runs_on_host() {
        // Host stub: no-op + `dsb ish` (also no-op) + `isb` (no-op).
        // A regression that broke the asm encoding would fail to compile
        // on aarch64; on host this just verifies the function is callable.
        tlbi_vmalle1is();
    }

    #[test]
    fn sm1e1_tlbi_vae1is_compiles_and_runs_on_host() {
        // Exercise the IS variant with a representative ASID + VA.
        tlbi_vae1is(42, 0x1000);
    }

    #[test]
    fn sm1e1_tlbi_aside1is_compiles_and_runs_on_host() {
        tlbi_aside1is(42);
    }

    #[test]
    fn sm1e1_tlbi_vale1is_compiles_and_runs_on_host() {
        tlbi_vale1is(42, 0x1000);
    }

    #[test]
    fn sm1e1_tlbi_is_variants_accept_zero_asid() {
        // ASID 0 is a valid value (the kernel reserves it for shared
        // mappings on some configurations).  Exercise every IS variant
        // with ASID=0 to verify the operand encoding handles it.
        tlbi_vae1is(0, 0x1000);
        tlbi_aside1is(0);
        tlbi_vale1is(0, 0x1000);
    }

    #[test]
    fn sm1e1_tlbi_is_variants_accept_max_asid() {
        // 16-bit ASID maxes at 0xFFFF.  Exercise the upper boundary so
        // the encoding's bit-shift cannot silently truncate.
        tlbi_vae1is(0xFFFF, 0x1000);
        tlbi_aside1is(0xFFFF);
        tlbi_vale1is(0xFFFF, 0x1000);
    }

    #[test]
    fn sm1e1_tlbi_is_variants_accept_max_vaddr() {
        // 48-bit VA space (TCR_EL1.IPS = 0b101).  The encoder masks
        // `vaddr >> 12` to the 44-bit VA[55:12] field per ARM ARM
        // C6.2.311.  For a 48-bit VA, vaddr >> 12 fits in 36 bits,
        // well below the 44-bit field, so well-formed VAs encode
        // losslessly.  The encoder's bit-shift cannot silently
        // truncate the ASID or pollute the RES0/TTL bits.
        //
        // The max well-formed VA representable in 48-bit IPA is
        // (2^48 - 4096) = 0x0000_FFFF_FFFF_F000.  Exercise it.
        tlbi_vae1is(1, 0x0000_FFFF_FFFF_F000);
        tlbi_vale1is(1, 0x0000_FFFF_FFFF_F000);
    }

    #[test]
    fn sm1e1_tlbi_is_variants_signature_pin() {
        // Pin every IS-variant function pointer signature.  A future
        // refactor that changes the argument types or return type would
        // fail to compile here.
        let _: fn() = tlbi_vmalle1is;
        let _: fn(u16, u64) = tlbi_vae1is;
        let _: fn(u16) = tlbi_aside1is;
        let _: fn(u16, u64) = tlbi_vale1is;
    }

    // ========================================================================
    // WS-SM SM1.E.2 — OS-variant TLBI tests
    // ========================================================================

    #[test]
    fn sm1e2_tlbi_vmalle1os_compiles_and_runs_on_host() {
        tlbi_vmalle1os();
    }

    #[test]
    fn sm1e2_tlbi_vae1os_compiles_and_runs_on_host() {
        tlbi_vae1os(42, 0x1000);
    }

    #[test]
    fn sm1e2_tlbi_aside1os_compiles_and_runs_on_host() {
        tlbi_aside1os(42);
    }

    #[test]
    fn sm1e2_tlbi_vale1os_compiles_and_runs_on_host() {
        tlbi_vale1os(42, 0x1000);
    }

    #[test]
    fn sm1e2_tlbi_os_variants_signature_pin() {
        // Pin every OS-variant function pointer signature for refactor
        // safety.  Symmetric with the IS-variant pin above.
        let _: fn() = tlbi_vmalle1os;
        let _: fn(u16, u64) = tlbi_vae1os;
        let _: fn(u16) = tlbi_aside1os;
        let _: fn(u16, u64) = tlbi_vale1os;
    }

    // ========================================================================
    // WS-SM SM1.E.3 — `tlbi_for_sharing` dispatcher tests
    // ========================================================================

    #[test]
    fn sm1e3_tlbi_for_sharing_inner_vmalle1_callable() {
        tlbi_for_sharing(SharingDomain::Inner, TlbInvalidation::Vmalle1);
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_outer_vmalle1_callable() {
        tlbi_for_sharing(SharingDomain::Outer, TlbInvalidation::Vmalle1);
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_inner_vae1_callable() {
        tlbi_for_sharing(
            SharingDomain::Inner,
            TlbInvalidation::Vae1 { asid: 1, vaddr: 0x2000 },
        );
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_outer_vae1_callable() {
        tlbi_for_sharing(
            SharingDomain::Outer,
            TlbInvalidation::Vae1 { asid: 1, vaddr: 0x2000 },
        );
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_inner_aside1_callable() {
        tlbi_for_sharing(SharingDomain::Inner, TlbInvalidation::Aside1 { asid: 7 });
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_outer_aside1_callable() {
        tlbi_for_sharing(SharingDomain::Outer, TlbInvalidation::Aside1 { asid: 7 });
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_inner_vale1_callable() {
        tlbi_for_sharing(
            SharingDomain::Inner,
            TlbInvalidation::Vale1 { asid: 3, vaddr: 0x4000 },
        );
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_outer_vale1_callable() {
        tlbi_for_sharing(
            SharingDomain::Outer,
            TlbInvalidation::Vale1 { asid: 3, vaddr: 0x4000 },
        );
    }

    #[test]
    fn sm1e3_tlbi_for_sharing_dispatcher_signature_pin() {
        // The dispatcher must take (SharingDomain, TlbInvalidation) and
        // return ().  A refactor that changed either argument or added a
        // return value would fail this signature pin.
        let _: fn(SharingDomain, TlbInvalidation) = tlbi_for_sharing;
    }

    #[test]
    fn sm1e3_sharing_domain_eq_distinguishes_variants() {
        // The two SharingDomain variants must be Eq-distinguishable so
        // the dispatcher's match is exhaustive at compile time.
        assert_ne!(SharingDomain::Inner, SharingDomain::Outer);
        assert_eq!(SharingDomain::Inner, SharingDomain::Inner);
        assert_eq!(SharingDomain::Outer, SharingDomain::Outer);
    }

    #[test]
    fn sm1e3_tlb_invalidation_eq_distinguishes_variants() {
        // The four TlbInvalidation variants must each compare unequal
        // to the other three.  This is a smoke check that the derive
        // macros produced the correct Eq instance.
        let vmalle1 = TlbInvalidation::Vmalle1;
        let vae1 = TlbInvalidation::Vae1 { asid: 0, vaddr: 0 };
        let aside1 = TlbInvalidation::Aside1 { asid: 0 };
        let vale1 = TlbInvalidation::Vale1 { asid: 0, vaddr: 0 };
        assert_ne!(vmalle1, vae1);
        assert_ne!(vmalle1, aside1);
        assert_ne!(vmalle1, vale1);
        assert_ne!(vae1, aside1);
        assert_ne!(vae1, vale1);
        assert_ne!(aside1, vale1);
    }

    #[test]
    fn sm1e3_tlb_invalidation_vae1_distinguishes_operands() {
        // Two `Vae1` values with different operands must compare unequal.
        // This catches a regression where the derived Eq accidentally
        // ignored the carried fields.
        let a = TlbInvalidation::Vae1 { asid: 1, vaddr: 0x1000 };
        let b = TlbInvalidation::Vae1 { asid: 2, vaddr: 0x1000 };
        let c = TlbInvalidation::Vae1 { asid: 1, vaddr: 0x2000 };
        let d = TlbInvalidation::Vae1 { asid: 1, vaddr: 0x1000 };
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_eq!(a, d);
    }

    // ========================================================================
    // WS-SM SM1.E — Cross-variant invariants
    // ========================================================================

    #[test]
    fn sm1e_local_is_os_triplet_each_present() {
        // Every TLBI op has three forms: local, IS, and OS.  Pin them
        // pairwise via fn-pointer coercion.  This is the structural
        // witness that the SM1.E.1 + SM1.E.2 surface is complete.
        let _local: fn() = tlbi_vmalle1;
        let _is: fn() = tlbi_vmalle1is;
        let _os: fn() = tlbi_vmalle1os;
        let _local_va: fn(u16, u64) = tlbi_vae1;
        let _is_va: fn(u16, u64) = tlbi_vae1is;
        let _os_va: fn(u16, u64) = tlbi_vae1os;
        let _local_asid: fn(u16) = tlbi_aside1;
        let _is_asid: fn(u16) = tlbi_aside1is;
        let _os_asid: fn(u16) = tlbi_aside1os;
        let _local_vale: fn(u16, u64) = tlbi_vale1;
        let _is_vale: fn(u16, u64) = tlbi_vale1is;
        let _os_vale: fn(u16, u64) = tlbi_vale1os;
    }

    #[test]
    fn sm1e_encode_va_asid_operand_is_const_correct() {
        // SM1.E.1: operand encoding evaluates in const contexts, so
        // call sites with literal arguments compute the operand at
        // compile time.  This catches a regression that introduces
        // a non-const operation in the encoder.
        const OPERAND: u64 = encode_va_asid_operand(0xCAFE, 0x12345000);
        assert_eq!(OPERAND >> 48, 0xCAFE);
        // Narrow 44-bit mask check — RES0/TTL bits [47:44] must be 0.
        assert_eq!(OPERAND & 0x0FFF_FFFF_FFFF, 0x12345);
        assert_eq!((OPERAND >> 44) & 0xF, 0, "RES0/TTL bits [47:44] must be 0");
    }

    #[test]
    fn sm1e_encode_asid_only_operand_is_const_correct() {
        const OPERAND: u64 = encode_asid_only_operand(0xBEEF);
        assert_eq!(OPERAND, 0xBEEF_0000_0000_0000);
    }

    #[test]
    fn sm1e_encode_va_asid_operand_masks_high_va_bits_to_44() {
        // SM1.E.1 audit fix: the encoder takes the low 44 bits of
        // `vaddr >> 12` (bits [43:0] of the operand), per ARM ARM
        // C6.2.311.  Bits [47:44] are RES0 (or TTL on FEAT_TTL
        // hardware) and MUST be zero.  An adversarial vaddr >= 2^56
        // would shift into the RES0/TTL field; the mask zeros those
        // bits to keep the encoder spec-compliant.
        let asid: u16 = 0x1234;
        // VA = 2^56 → vaddr >> 12 = 2^44 → bit 44 of operand →
        // would land in TTL bit 0 if unmasked, silently corrupting
        // the invalidation semantics on FEAT_TTL hardware (TTL=0b0001
        // = "skip level 1 lookup").
        let vaddr: u64 = 1u64 << 56;
        let operand = encode_va_asid_operand(asid, vaddr);
        // ASID field must remain unchanged.
        assert_eq!(
            operand >> 48,
            0x1234,
            "ASID field corrupted by un-masked high vaddr bits"
        );
        // Bits [47:44] (RES0/TTL) must be zero.  The 44-bit mask
        // ensures this.
        assert_eq!(
            (operand >> 44) & 0xF,
            0,
            "RES0/TTL bits [47:44] not masked — would corrupt TLBI \
             semantics on FEAT_TTL hardware"
        );
        // Bits [43:0] (VA field) for this input: vaddr=2^56 yields
        // vaddr>>12 = 2^44, which is OUTSIDE the 44-bit field.
        // After masking, the entire VA field should be zero.
        assert_eq!(
            operand & 0x0FFF_FFFF_FFFF,
            0,
            "VA field [43:0] should be zero after 44-bit mask of 2^44"
        );
    }

    #[test]
    fn sm1e_encode_va_asid_operand_preserves_full_44bit_va() {
        // SM1.E.1 audit: with a vaddr at exactly the 44-bit VA field
        // boundary (vaddr = (2^44 - 1) << 12 ≈ 2^56 - 2^12), the
        // VA[55:12] field should be all-1s (44 bits set) and the
        // RES0/TTL bits should remain zero.
        let asid: u16 = 0xABCD;
        // (2^44 - 1) << 12 = 0x0FFF_FFFF_FFFF_F000 (highest valid VA
        // representable in 44-bit VA[55:12] field).
        let vaddr: u64 = (1u64 << 56) - (1u64 << 12);
        let operand = encode_va_asid_operand(asid, vaddr);
        assert_eq!(operand >> 48, 0xABCD, "ASID preserved");
        assert_eq!((operand >> 44) & 0xF, 0, "RES0/TTL bits [47:44] zero");
        assert_eq!(
            operand & 0x0FFF_FFFF_FFFF,
            0x0FFF_FFFF_FFFF,
            "VA field [43:0] should hold full 44-bit VA[55:12]"
        );
    }

    #[test]
    fn sm1e_encode_va_asid_operand_well_formed_vaddrs_unchanged() {
        // SM1.E.1 audit: confirm the 44-bit mask is observationally
        // identical to the (incorrect) 48-bit mask for ALL well-formed
        // VAs in the 48-bit IPA space the kernel actually uses.  This
        // is the defensive-no-regression check: changing the mask must
        // not break any production caller.
        //
        // For vaddr < 2^48, vaddr >> 12 < 2^36, which fits entirely
        // within the 36 low bits of the operand — far below the
        // [47:44] RES0/TTL field.  Mask change is observationally
        // identical.
        let cases: &[(u16, u64)] = &[
            (0, 0),
            (0, 0x1000),
            (5, 0x12345000),
            (0xFFFF, 0xFFFF_FFFF_F000),
            (1, 0x0000_8000_0000_0000 - 0x1000),  // vaddr just below 2^47
        ];
        for &(asid, vaddr) in cases {
            let operand = encode_va_asid_operand(asid, vaddr);
            assert_eq!(operand >> 48, asid as u64, "ASID for ({:#x}, {:#x})", asid, vaddr);
            assert_eq!(
                (operand >> 44) & 0xF,
                0,
                "RES0/TTL bits zero for well-formed ({:#x}, {:#x})",
                asid,
                vaddr
            );
            // VA[55:12] field equals vaddr >> 12 (for well-formed input).
            assert_eq!(
                operand & 0x0FFF_FFFF_FFFF,
                vaddr >> 12,
                "VA field for ({:#x}, {:#x})",
                asid,
                vaddr
            );
        }
    }
}
