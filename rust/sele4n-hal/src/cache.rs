//! Cache maintenance operations for ARMv8-A on Cortex-A76.
//!
//! AG6-I: Cache maintenance operations (H3-RUST-06)
//!
//! Provides data cache (DC) and instruction cache (IC) maintenance wrappers.
//! Cache line size on Cortex-A76: 64 bytes (from CTR_EL0).
//!
//! Required for:
//! - DMA coherency (DC CIVAC before DMA read, DC IVAC after DMA write)
//! - Self-modifying code / JIT (DC CVAC + IC IALLU + ISB)
//! - Page table updates (DC CIVAC on page table pages before TLBI)
//! - Zeroing memory (DC ZVA for fast cache-line zero)
//!
//! On non-AArch64 hosts, functions are no-ops for compilation and testing.
//!
//! References:
//! - ARM ARM C6.2.60–62: DC instructions
//! - ARM ARM C6.2.88: IC instructions

use crate::barriers;

/// Cortex-A76 cache line size in bytes (from CTR_EL0).
/// ARM Cortex-A76 TRM: D-cache line = 64 bytes, I-cache line = 64 bytes.
pub const CACHE_LINE_SIZE: u64 = 64;

/// Clean and Invalidate by VA to Point of Coherency (DC CIVAC).
///
/// Writes back dirty data to the Point of Coherency and invalidates the
/// cache line. Required before DMA reads (ensures device sees latest data)
/// and after page table updates (ensures all agents see the update).
///
/// ARM ARM C6.2.60: DC CIVAC, Xt
#[inline(always)]
pub fn dc_civac(addr: u64) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DC CIVAC operates on the cache line containing `addr`.
        // It writes dirty data back and invalidates — no corruption if the
        // address is valid. (ARM ARM C6.2.60)
        unsafe {
            core::arch::asm!("dc civac, {0}", in(reg) addr, options(nostack, preserves_flags));
        }
    }
    let _ = addr;
}

/// Clean by VA to Point of Coherency (DC CVAC).
///
/// Writes back dirty data without invalidating. Used when data must be
/// visible to other agents but the cache line should remain valid.
///
/// ARM ARM C6.2.61: DC CVAC, Xt
#[inline(always)]
pub fn dc_cvac(addr: u64) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DC CVAC writes back dirty data without invalidating.
        // Safe for any valid address. (ARM ARM C6.2.61)
        unsafe {
            core::arch::asm!("dc cvac, {0}", in(reg) addr, options(nostack, preserves_flags));
        }
    }
    let _ = addr;
}

/// Invalidate by VA to Point of Coherency (DC IVAC).
///
/// Discards the cache line without writing back. Use with caution — only
/// safe when the cache line is known to not contain dirty data (e.g.,
/// after DMA write completes, the device has written the authoritative copy).
///
/// ARM ARM C6.2.62: DC IVAC, Xt
#[inline(always)]
pub fn dc_ivac(addr: u64) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DC IVAC discards cache data. Caller must ensure no dirty
        // data is lost. (ARM ARM C6.2.62)
        unsafe {
            core::arch::asm!("dc ivac, {0}", in(reg) addr, options(nostack, preserves_flags));
        }
    }
    let _ = addr;
}

/// Zero by VA (DC ZVA).
///
/// Zeroes a cache-line-sized block of memory. On Cortex-A76, this is 64 bytes.
/// Much faster than store-based zeroing for large regions.
///
/// ARM ARM C6.2.62: DC ZVA, Xt
#[inline(always)]
pub fn dc_zva(addr: u64) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DC ZVA zeroes a naturally aligned cache-line block.
        // The address should be cache-line aligned. (ARM ARM C6.2.62)
        unsafe {
            core::arch::asm!("dc zva, {0}", in(reg) addr, options(nostack));
        }
    }
    let _ = addr;
}

/// Invalidate all instruction caches to Point of Unification (IC IALLU).
///
/// Invalidates all instruction cache entries. Required after code
/// modification to ensure the I-cache refetches from the D-cache/memory.
///
/// ARM ARM C6.2.88: IC IALLU
#[inline(always)]
pub fn ic_iallu() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: IC IALLU invalidates instruction caches. No data loss —
        // I-cache is read-only. (ARM ARM C6.2.88)
        unsafe {
            core::arch::asm!("ic iallu", options(nostack, preserves_flags));
        }
    }
}

/// Invalidate all instruction caches to PoU, Inner Shareable (IC IALLUIS).
///
/// Like IC IALLU but broadcasts to all cores in the Inner Shareable domain.
/// Required for SMP code modification scenarios.
///
/// ARM ARM C6.2.88: IC IALLUIS
#[inline(always)]
pub fn ic_ialluis() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: IC IALLUIS invalidates I-caches across all cores in the
        // Inner Shareable domain. No data loss. (ARM ARM C6.2.88)
        unsafe {
            core::arch::asm!("ic ialluis", options(nostack, preserves_flags));
        }
    }
}

/// Apply a cache maintenance operation over an address range.
///
/// Iterates from `start` to `end` (exclusive) in `CACHE_LINE_SIZE` increments,
/// calling `op` on each cache-line-aligned address.
///
/// # Arguments
/// * `op` - Cache maintenance function (e.g., `dc_civac`)
/// * `start` - Start address (will be rounded down to cache line boundary)
/// * `end` - End address (exclusive)
pub fn cache_range(op: fn(u64), start: u64, end: u64) {
    // AK5-K (R-HAL-M08 / MEDIUM): Always emit DSB ISH — even on an empty
    // range — so callers can rely on `cache_range` as a stable memory
    // ordering point regardless of whether `start >= end`. The previous
    // early return skipped the barrier, which could surprise callers that
    // used `cache_range(..., ptr, ptr)` as a zero-length "fence".
    if start >= end {
        barriers::dsb_ish();
        return;
    }
    let aligned_start = start & !(CACHE_LINE_SIZE - 1);
    let mut addr = aligned_start;
    while addr < end {
        op(addr);
        // Use saturating_add to prevent overflow near u64::MAX.
        // If addr saturates to u64::MAX, the loop terminates because
        // u64::MAX >= end for any valid end address.
        addr = addr.saturating_add(CACHE_LINE_SIZE);
    }
    barriers::dsb_ish();
}

/// Clean and invalidate a range of data cache lines (convenience wrapper).
pub fn clean_invalidate_range(start: u64, end: u64) {
    cache_range(dc_civac, start, end);
}

/// Clean a range of data cache lines (convenience wrapper).
pub fn clean_range(start: u64, end: u64) {
    cache_range(dc_cvac, start, end);
}

/// Invalidate a range of data cache lines (convenience wrapper).
/// CAUTION: Discards dirty data. Only use when dirty data loss is acceptable.
pub fn invalidate_range(start: u64, end: u64) {
    cache_range(dc_ivac, start, end);
}

/// AK5-D.1: Clean a contiguous range of addresses by VA to the Point of
/// Coherency.
///
/// Issues `dc cvac` for every cache line and a trailing DSB ISH to ensure
/// all cleans complete before any dependent operation (typically a TTBR or
/// SCTLR write). Used to clean boot page-table pages so the MMU walker
/// sees committed descriptors at MMU-enable time.
///
/// # Safety
///
/// Caller must ensure `addr..addr+len` is mapped and in RAM (cleanable —
/// device memory is not cacheable, so `dc cvac` there is a no-op but the
/// virtual address must still be a valid MMIO region or a mapped RAM page).
pub unsafe fn clean_pagetable_range(addr: usize, len: usize) {
    if len == 0 {
        // AK5-K (R-HAL-M08): Even for empty ranges, emit DSB ISH so the
        // caller can rely on a stable memory ordering point regardless of
        // range size.
        barriers::dsb_ish();
        return;
    }
    let line = CACHE_LINE_SIZE as usize;
    let end = addr.saturating_add(len);
    let mut cur = addr & !(line - 1);
    while cur < end {
        // SAFETY: dc cvac on a cleanable VA is always safe — it writes back
        // dirty data without invalidating. Caller guarantees the range is
        // a valid mapped region. (ARM ARM C6.2.61)
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!(
                "dc cvac, {0}",
                in(reg) cur,
                options(nostack, preserves_flags)
            );
        }
        #[cfg(not(target_arch = "aarch64"))]
        let _ = cur;
        cur = cur.saturating_add(line);
    }
    barriers::dsb_ish();
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_line_size() {
        // Cortex-A76 cache line is 64 bytes
        assert_eq!(CACHE_LINE_SIZE, 64);
    }

    #[test]
    fn test_dc_civac_compiles() {
        dc_civac(0x1000);
    }

    #[test]
    fn test_dc_cvac_compiles() {
        dc_cvac(0x1000);
    }

    #[test]
    fn test_dc_ivac_compiles() {
        dc_ivac(0x1000);
    }

    #[test]
    fn test_dc_zva_compiles() {
        dc_zva(0x1000);
    }

    #[test]
    fn test_ic_iallu_compiles() {
        ic_iallu();
    }

    #[test]
    fn test_ic_ialluis_compiles() {
        ic_ialluis();
    }

    #[test]
    fn test_cache_range_empty() {
        // Should not panic on empty range
        cache_range(dc_civac, 0x2000, 0x1000);
        cache_range(dc_civac, 0x1000, 0x1000);
    }

    #[test]
    fn test_clean_pagetable_range_empty() {
        // AK5-D.1/AK5-K: empty range still emits DSB ISH (no panic on host).
        unsafe { clean_pagetable_range(0x1000, 0); }
    }

    #[test]
    fn test_clean_pagetable_range_aligned_page() {
        // 4 KiB page at a 64-byte-aligned address: 64 lines cleaned.
        unsafe { clean_pagetable_range(0x1000, 4096); }
    }

    #[test]
    fn test_clean_pagetable_range_unaligned_start() {
        // Start not cache-line aligned: rounded down to line boundary.
        unsafe { clean_pagetable_range(0x1020, 128); }
    }

    #[test]
    fn test_cache_range_single_line() {
        // Single cache line
        cache_range(dc_civac, 0x1000, 0x1001);
    }

    #[test]
    fn test_cache_range_alignment() {
        // Start not aligned — should round down
        // 0x1020 rounds down to 0x1000 (64-byte aligned)
        // Range covers 0x1000..0x1080 → 2 cache lines
        cache_range(dc_civac, 0x1020, 0x1080);
    }

    #[test]
    fn test_clean_invalidate_range() {
        clean_invalidate_range(0x1000, 0x2000);
    }

    #[test]
    fn test_clean_range() {
        clean_range(0x1000, 0x2000);
    }
}
