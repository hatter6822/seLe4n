//! MMU configuration for ARMv8-A on Raspberry Pi 5.
//!
//! Sets up MAIR_EL1, TCR_EL1, identity-mapped boot page tables, and enables
//! the MMU via SCTLR_EL1. Initial mapping uses 1 GiB block descriptors at
//! L1 for simplicity; AG6 replaces this with 4 KiB page-level mappings.
//!
//! Memory attribute configuration:
//! - Index 0 (0xFF): Normal, Inner/Outer WB-WA-RA (cacheable RAM)
//! - Index 1 (0x00): Device-nGnRnE (strongly ordered MMIO)
//! - Index 2 (0x44): Normal Non-cacheable (DMA buffers)
//!
//! References: ARM ARM D8 (The AArch64 Virtual Memory System Architecture)

use crate::barriers;

// ---------------------------------------------------------------------------
// Page table descriptor bit definitions (ARMv8-A D8.3)
// ---------------------------------------------------------------------------

/// Valid bit (bit 0) — descriptor is active.
const DESC_VALID: u64 = 1 << 0;
/// Access Flag (bit 10) — must be set or hardware generates access fault.
const AF: u64 = 1 << 10;
/// Inner Shareable (bits [9:8] = 0b11).
const SH_INNER: u64 = 0b11 << 8;
/// Attribute Index 0 in bits [4:2] — Normal WB cacheable.
const ATTR_IDX_NORMAL: u64 = 0 << 2;
/// Attribute Index 1 in bits [4:2] — Device-nGnRnE.
const ATTR_IDX_DEVICE: u64 = 1 << 2;
/// AP[2:1] = 0b00 — Read/Write at EL1, no EL0 access.
const AP_RW_EL1: u64 = 0b00 << 6;
/// UXN (bit 54) — Unprivileged Execute Never.
const UXN: u64 = 1 << 54;
/// PXN (bit 53) — Privileged Execute Never (for device memory).
const PXN: u64 = 1 << 53;

/// Block descriptor for Normal memory: valid + block + AF + Inner Shareable +
/// Normal WB + RW EL1 + UXN (kernel code only, no user exec).
const BLOCK_NORMAL: u64 = DESC_VALID | AF | SH_INNER | ATTR_IDX_NORMAL | AP_RW_EL1 | UXN;

/// Block descriptor for Device memory: valid + block + AF + Device-nGnRnE +
/// RW EL1 + PXN + UXN (never execute from MMIO).
const BLOCK_DEVICE: u64 = DESC_VALID | AF | ATTR_IDX_DEVICE | AP_RW_EL1 | PXN | UXN;

// ---------------------------------------------------------------------------
// MAIR_EL1 configuration (ARM ARM D17.2.95)
// ---------------------------------------------------------------------------

/// MAIR_EL1 value with 3 attribute indices:
/// - Attr0 (bits [7:0])   = 0xFF: Normal, Inner/Outer WB-WA-RA
/// - Attr1 (bits [15:8])  = 0x00: Device-nGnRnE
/// - Attr2 (bits [23:16]) = 0x44: Normal Non-cacheable
const MAIR_VALUE: u64 = 0xFF | (0x44 << 16);
// Note: Attr1 = 0x00 (Device-nGnRnE) occupies bits [15:8] but is zero,
// so it does not appear in the OR expression.

// ---------------------------------------------------------------------------
// TCR_EL1 configuration (ARM ARM D17.2.136)
// ---------------------------------------------------------------------------

/// TCR_EL1 value for 48-bit VA, 4KiB granule, 44-bit PA (BCM2712):
///
/// - T0SZ  = 16 (bits [5:0]):   48-bit VA for TTBR0 (64 - 48 = 16)
/// - T1SZ  = 16 (bits [21:16]): 48-bit VA for TTBR1
/// - TG0   = 0b00 (bits [15:14]): 4 KiB granule for TTBR0
/// - TG1   = 0b10 (bits [31:30]): 4 KiB granule for TTBR1
/// - IPS   = 0b100 (bits [34:32]): 44-bit PA (16 TB, matches BCM2712)
/// - SH0   = 0b11 (bits [13:12]): Inner Shareable for TTBR0
/// - SH1   = 0b11 (bits [29:28]): Inner Shareable for TTBR1
/// - ORGN0 = 0b01 (bits [11:10]): Write-Back cacheable for TTBR0
/// - IRGN0 = 0b01 (bits [9:8]):   Write-Back cacheable for TTBR0
/// - ORGN1 = 0b01 (bits [27:26]): Write-Back cacheable for TTBR1
/// - IRGN1 = 0b01 (bits [25:24]): Write-Back cacheable for TTBR1
const TCR_VALUE: u64 = {
    let t0sz: u64 = 16;
    let t1sz: u64 = 16 << 16;
    let tg0: u64 = 0b00 << 14; // 4 KiB
    let tg1: u64 = 0b10 << 30; // 4 KiB
    let ips: u64 = 0b100 << 32; // 44-bit PA
    let sh0: u64 = 0b11 << 12; // Inner Shareable
    let sh1: u64 = 0b11 << 28; // Inner Shareable
    let orgn0: u64 = 0b01 << 10;
    let irgn0: u64 = 0b01 << 8;
    let orgn1: u64 = 0b01 << 26;
    let irgn1: u64 = 0b01 << 24;
    t0sz | t1sz | tg0 | tg1 | ips | sh0 | sh1 | orgn0 | irgn0 | orgn1 | irgn1
};

// ---------------------------------------------------------------------------
// Boot page tables
// ---------------------------------------------------------------------------

/// Number of L1 entries (512 for a 4KiB L0 table covering 512 GiB).
/// We only populate entries 0..3 (first 4 GiB) for the RPi5 4GB model.
const L1_ENTRIES: usize = 512;

/// L1 page table (identity map). Populated at boot time.
/// Must be 4096-byte aligned per ARM ARM D8.3.
///
/// Each L1 entry maps a 1 GiB block (2^30 bytes).
/// - Entries 0-2 (0x00000000 – 0xBFFFFFFF): Normal RAM
/// - Entry 3 (0xC0000000 – 0xFFFFFFFF): Device memory (covers peripherals
///   at 0xFE000000 – 0xFF850000 plus surrounding reserved regions)
#[repr(C, align(4096))]
struct PageTable {
    entries: [u64; L1_ENTRIES],
}

/// Boot L1 page table — placed in BSS, zeroed during boot.
static mut BOOT_L1_TABLE: PageTable = PageTable {
    entries: [0; L1_ENTRIES],
};

/// Build identity-mapped L1 page tables for boot.
///
/// Maps the first 4 GiB of physical address space:
/// - 0x00000000 – 0x3FFFFFFF (1 GiB): Normal RAM
/// - 0x40000000 – 0x7FFFFFFF (1 GiB): Normal RAM
/// - 0x80000000 – 0xBFFFFFFF (1 GiB): Normal RAM
/// - 0xC0000000 – 0xFFFFFFFF (1 GiB): Device memory
///
/// This is a simplified boot mapping. AG6 replaces it with fine-grained
/// 4 KiB page tables and proper kernel/user TTBR0/TTBR1 split.
#[allow(unsafe_code)]
fn build_identity_tables() {
    // SAFETY: Called from single-threaded boot context before MMU is enabled.
    // No concurrent access to BOOT_L1_TABLE is possible. Using &raw mut to
    // avoid creating intermediate references to static mut.
    unsafe {
        let table = &raw mut BOOT_L1_TABLE;
        // First 3 GiB: Normal cacheable RAM (block descriptors)
        for i in 0..3 {
            let addr = (i as u64) << 30; // 1 GiB per entry
            (*table).entries[i] = addr | BLOCK_NORMAL;
        }

        // 4th GiB: Device memory for BCM2712 peripherals
        // Covers 0xC0000000 – 0xFFFFFFFF including:
        //   0xFE000000 (peripheral base low)
        //   0xFF841000 (GIC distributor)
        //   0xFF842000 (GIC CPU interface)
        (*table).entries[3] = (3u64 << 30) | BLOCK_DEVICE;
    }
}

/// Configure MAIR_EL1 with memory attribute encodings.
fn configure_mair() {
    crate::registers::write_mair_el1(MAIR_VALUE);
}

/// Configure TCR_EL1 for 48-bit VA, 4KiB granule, 44-bit PA.
fn configure_tcr() {
    crate::registers::write_tcr_el1(TCR_VALUE);
}

/// Set TTBR0/TTBR1 and enable the MMU.
///
/// After this function returns, all memory accesses go through the page table.
/// The identity mapping ensures that existing code and data remain accessible
/// at the same physical addresses.
#[allow(unsafe_code)]
fn enable_mmu() {
    // Set TTBR0_EL1 and TTBR1_EL1 to the boot L1 table.
    // &raw const creates a raw pointer without an intermediate reference.
    let l1_addr = (&raw const BOOT_L1_TABLE) as u64;

    crate::registers::write_ttbr0_el1(l1_addr);
    crate::registers::write_ttbr1_el1(l1_addr);

    // Ensure page table writes are visible before enabling MMU
    barriers::dsb_ish();
    barriers::isb();

    // Enable MMU: set M bit (0), C bit (2, data cache), I bit (12, icache)
    let mut sctlr = crate::registers::read_sctlr_el1();
    sctlr |= (1 << 0) | (1 << 2) | (1 << 12); // M + C + I
    crate::registers::write_sctlr_el1(sctlr);

    // ISB after SCTLR write to synchronize the MMU enable
    barriers::isb();
}

/// Full MMU initialization sequence.
///
/// Called from `boot::rust_boot_main` after UART is available.
/// Configures MAIR, TCR, builds identity-mapped page tables, and enables
/// the MMU with data and instruction caches.
pub fn init_mmu() {
    configure_mair();
    configure_tcr();
    build_identity_tables();
    enable_mmu();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mair_attribute_indices() {
        // Attr0 (bits [7:0]) = 0xFF: Normal, Inner/Outer WB-WA-RA
        assert_eq!(MAIR_VALUE & 0xFF, 0xFF);
        // Attr1 (bits [15:8]) = 0x00: Device-nGnRnE
        assert_eq!((MAIR_VALUE >> 8) & 0xFF, 0x00);
        // Attr2 (bits [23:16]) = 0x44: Normal Non-cacheable
        assert_eq!((MAIR_VALUE >> 16) & 0xFF, 0x44);
    }

    #[test]
    fn tcr_t0sz_is_16() {
        // T0SZ in bits [5:0] = 16 → 48-bit VA for TTBR0
        assert_eq!(TCR_VALUE & 0x3F, 16);
    }

    #[test]
    fn tcr_t1sz_is_16() {
        // T1SZ in bits [21:16] = 16 → 48-bit VA for TTBR1
        assert_eq!((TCR_VALUE >> 16) & 0x3F, 16);
    }

    #[test]
    fn tcr_granule_4kib() {
        // TG0 in bits [15:14] = 0b00 → 4 KiB granule for TTBR0
        assert_eq!((TCR_VALUE >> 14) & 0x3, 0b00);
        // TG1 in bits [31:30] = 0b10 → 4 KiB granule for TTBR1
        assert_eq!((TCR_VALUE >> 30) & 0x3, 0b10);
    }

    #[test]
    fn tcr_ips_44bit() {
        // IPS in bits [34:32] = 0b100 → 44-bit PA (BCM2712)
        assert_eq!((TCR_VALUE >> 32) & 0x7, 0b100);
    }

    #[test]
    fn tcr_inner_shareable() {
        // SH0 in bits [13:12] = 0b11 → Inner Shareable
        assert_eq!((TCR_VALUE >> 12) & 0x3, 0b11);
        // SH1 in bits [29:28] = 0b11 → Inner Shareable
        assert_eq!((TCR_VALUE >> 28) & 0x3, 0b11);
    }

    #[test]
    fn block_normal_has_valid_and_af() {
        // Valid bit (bit 0) must be set
        assert_ne!(BLOCK_NORMAL & DESC_VALID, 0);
        // Access Flag (bit 10) must be set
        assert_ne!(BLOCK_NORMAL & AF, 0);
        // Inner Shareable
        assert_ne!(BLOCK_NORMAL & SH_INNER, 0);
        // AttrIndx = 0 (Normal memory)
        assert_eq!(BLOCK_NORMAL & ATTR_IDX_DEVICE, 0);
        // UXN set (no user execute from kernel pages)
        assert_ne!(BLOCK_NORMAL & UXN, 0);
    }

    #[test]
    fn block_device_has_pxn_and_uxn() {
        // Device memory must have PXN and UXN (never execute from MMIO)
        assert_ne!(BLOCK_DEVICE & PXN, 0);
        assert_ne!(BLOCK_DEVICE & UXN, 0);
        // AttrIndx = 1 (Device-nGnRnE)
        assert_ne!(BLOCK_DEVICE & ATTR_IDX_DEVICE, 0);
        // No Inner Shareable for device memory
        assert_eq!(BLOCK_DEVICE & SH_INNER, 0);
    }

    #[test]
    fn l1_table_alignment() {
        // PageTable must be 4096-byte aligned for ARMv8 TTBR
        assert_eq!(core::mem::align_of::<PageTable>(), 4096);
    }

    #[test]
    fn l1_table_has_512_entries() {
        assert_eq!(L1_ENTRIES, 512);
        assert_eq!(core::mem::size_of::<PageTable>(), 512 * 8);
    }
}
