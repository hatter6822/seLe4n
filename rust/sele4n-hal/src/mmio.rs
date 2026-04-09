//! MMIO Volatile Read/Write Primitives for ARMv8-A.
//!
//! AG7-C: Provides generic volatile memory access functions for hardware
//! register operations. These primitives are the low-level building blocks
//! used by device drivers (GIC, timer, UART) and exposed via the FFI bridge.
//!
//! ## Volatile semantics
//!
//! All functions use `core::ptr::{read_volatile, write_volatile}` to ensure:
//! - The compiler does not elide or reorder accesses
//! - Each access generates exactly one load/store instruction
//! - No speculative or cached access optimizations
//!
//! ## Alignment
//!
//! Debug builds include alignment assertions. On release builds, alignment
//! is the caller's responsibility (hardware may fault on unaligned MMIO).
//!
//! ## Bridge to Lean model
//!
//! FFI functions `ffi_mmio_read32` / `ffi_mmio_write32` (in `ffi.rs`) call
//! these primitives, connecting the `MmioSafe` model (`MmioAdapter.lean`)
//! to actual hardware register access.
//!
//! On non-AArch64 hosts, functions return 0 (reads) or are no-ops (writes)
//! for compilation and testing.

/// Read a 32-bit value from an MMIO address using volatile semantics.
///
/// # Arguments
/// * `addr` - Physical address of the MMIO register (must be 4-byte aligned)
///
/// # Safety note
/// The address must be within a valid device memory region mapped as
/// Device-nGnRnE or Device-nGnRE in the page tables.
#[inline(always)]
pub fn mmio_read32(addr: usize) -> u32 {
    debug_assert!(addr % 4 == 0, "MMIO read32: address {:#x} not 4-byte aligned", addr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid MMIO address within a mapped device
        // memory region. Volatile read ensures the access reaches the hardware
        // register without compiler optimization. (ARM ARM B2.1)
        unsafe { core::ptr::read_volatile(addr as *const u32) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = addr;
        0
    }
}

/// Write a 32-bit value to an MMIO address using volatile semantics.
///
/// # Arguments
/// * `addr` - Physical address of the MMIO register (must be 4-byte aligned)
/// * `val` - Value to write
#[inline(always)]
pub fn mmio_write32(addr: usize, val: u32) {
    debug_assert!(addr % 4 == 0, "MMIO write32: address {:#x} not 4-byte aligned", addr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid MMIO address within a mapped device
        // memory region. Volatile write ensures the value reaches the hardware
        // register. (ARM ARM B2.1)
        unsafe { core::ptr::write_volatile(addr as *mut u32, val) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (addr, val);
    }
}

/// Read a 64-bit value from an MMIO address using volatile semantics.
///
/// # Arguments
/// * `addr` - Physical address of the MMIO register (must be 8-byte aligned)
#[inline(always)]
pub fn mmio_read64(addr: usize) -> u64 {
    debug_assert!(addr % 8 == 0, "MMIO read64: address {:#x} not 8-byte aligned", addr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid 8-byte-aligned MMIO address.
        // Volatile read ensures the access reaches the hardware register. (ARM ARM B2.1)
        unsafe { core::ptr::read_volatile(addr as *const u64) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = addr;
        0
    }
}

/// Write a 64-bit value to an MMIO address using volatile semantics.
///
/// # Arguments
/// * `addr` - Physical address of the MMIO register (must be 8-byte aligned)
/// * `val` - Value to write
#[inline(always)]
pub fn mmio_write64(addr: usize, val: u64) {
    debug_assert!(addr % 8 == 0, "MMIO write64: address {:#x} not 8-byte aligned", addr);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid 8-byte-aligned MMIO address.
        // Volatile write ensures the value reaches the hardware register. (ARM ARM B2.1)
        unsafe { core::ptr::write_volatile(addr as *mut u64, val) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (addr, val);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mmio_read32_returns_zero_on_host() {
        // On non-aarch64, reads return 0
        assert_eq!(mmio_read32(0x1000), 0);
    }

    #[test]
    fn mmio_write32_no_panic() {
        mmio_write32(0x1000, 0xDEAD_BEEF);
    }

    #[test]
    fn mmio_read64_returns_zero_on_host() {
        assert_eq!(mmio_read64(0x1000), 0);
    }

    #[test]
    fn mmio_write64_no_panic() {
        mmio_write64(0x1000, 0xDEAD_BEEF_CAFE_BABE);
    }

    #[test]
    fn mmio_read32_aligned() {
        // 4-byte aligned addresses should not panic
        assert_eq!(mmio_read32(0x0), 0);
        assert_eq!(mmio_read32(0x4), 0);
        assert_eq!(mmio_read32(0x100), 0);
    }

    #[test]
    fn mmio_read64_aligned() {
        // 8-byte aligned addresses should not panic
        assert_eq!(mmio_read64(0x0), 0);
        assert_eq!(mmio_read64(0x8), 0);
        assert_eq!(mmio_read64(0x100), 0);
    }

    #[test]
    #[should_panic(expected = "not 4-byte aligned")]
    fn mmio_read32_unaligned_panics_debug() {
        // In debug mode, unaligned access should panic
        mmio_read32(0x1001);
    }

    #[test]
    #[should_panic(expected = "not 4-byte aligned")]
    fn mmio_write32_unaligned_panics_debug() {
        mmio_write32(0x1001, 0);
    }

    #[test]
    #[should_panic(expected = "not 8-byte aligned")]
    fn mmio_read64_unaligned_panics_debug() {
        mmio_read64(0x1001);
    }

    #[test]
    #[should_panic(expected = "not 8-byte aligned")]
    fn mmio_write64_unaligned_panics_debug() {
        mmio_write64(0x1001, 0);
    }
}
