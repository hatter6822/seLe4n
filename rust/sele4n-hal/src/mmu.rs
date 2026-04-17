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

use core::cell::UnsafeCell;

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
// AK5-C (R-HAL-H03): SCTLR_EL1 full bitmap
// ---------------------------------------------------------------------------
//
// The prior implementation OR'd only `M | C | I` into the reset value of
// SCTLR_EL1. On an ARMv8-A reset the reset value is IMPLEMENTATION DEFINED
// except for bits that must be 1 (reserved-1) and those enumerated below —
// relying on "whatever reset gave us" leaves WXN=0 (HW does not enforce
// W^X), SA=0 (no EL1 SP-alignment check), EOS=0 (no exception-exit
// serialization), and is dependent on bits a warm-reset may not clear.
//
// `compute_sctlr_el1_bitmap` produces the EXACT value seLe4n wants running,
// so we write it directly instead of OR-accumulating onto whatever the CPU
// powered up with.
//
// References:
// - ARM ARM D17.2.120: SCTLR_EL1 — System Control Register (EL1).
// - ARM ARM D8.11:     Architectural requirements for MMU enable.

/// SCTLR_EL1 bit positions (ARM ARM D17.2.120).
///
/// Bits marked `pub` are actively written in the bitmap; `#[allow(dead_code)]`
/// bits are included for documentation/readability so the bitmap's SAFETY
/// notes can reference them by name without triggering dead-code warnings.
mod sctlr_bits {
    pub const M:    u64 = 1 << 0;   // MMU enable
    #[allow(dead_code)]
    pub const A:    u64 = 1 << 1;   // Alignment check enable (EL0 + EL1)
    pub const C:    u64 = 1 << 2;   // Data cache enable
    pub const SA:   u64 = 1 << 3;   // SP alignment check enable (EL1)
    pub const SA0:  u64 = 1 << 4;   // SP alignment check enable (EL0, RES1)
    #[allow(dead_code)]
    pub const CP15BEN: u64 = 1 << 5; // AArch32 CP15 barrier enable (RES0 at AArch64)
    #[allow(dead_code)]
    pub const NAA:  u64 = 1 << 6;   // Non-aligned access: 0 = faults preserved
    pub const ITD:  u64 = 1 << 7;   // IT instruction disable (RES1 at AArch64)
    pub const SED:  u64 = 1 << 8;   // SETEND disable (RES1 at AArch64)
    #[allow(dead_code)]
    pub const UMA:  u64 = 1 << 9;   // User Mask Access (PAN-related)
    pub const EOS:  u64 = 1 << 11;  // Exception Exit Serialization (EL1, RES1)
    pub const I:    u64 = 1 << 12;  // Instruction cache enable
    pub const WXN:  u64 = 1 << 19;  // Write permission implies XN (HW W^X)
    pub const EIS:  u64 = 1 << 22;  // Exception Entry Serialization (EL1, RES1)
    pub const SPAN: u64 = 1 << 23;  // Set Privileged Access Never on exception (RES1)
    #[allow(dead_code)]
    pub const EE:   u64 = 1 << 25;  // Exception endianness: 0 = little-endian at EL1
    pub const TSCXT:u64 = 1 << 28;  // Trap EL0 access to SCXTNUM_EL0 (RES1)
    pub const RES1_BIT29: u64 = 1 << 29;  // Architecturally RES1
}

/// AK5-C: Compute the exact SCTLR_EL1 value seLe4n wants on boot.
///
/// This replaces the prior "read-modify-write of reset value" pattern which
/// inherited reserved bits from the previous state. The bitmap encodes:
///
/// | Bit  | Name  | Value | Rationale                                            |
/// |------|-------|-------|------------------------------------------------------|
/// | 0    | M     | 1     | Enable MMU                                           |
/// | 2    | C     | 1     | Enable D-cache                                       |
/// | 3    | SA    | 1     | SP-alignment check at EL1 (fault on unaligned SP)    |
/// | 4    | SA0   | 1     | SP-alignment check at EL0 (RES1 also)                |
/// | 7    | ITD   | 1     | AArch64 RES1 (no AArch32 IT-block support)           |
/// | 8    | SED   | 1     | AArch64 RES1 (no AArch32 SETEND support)             |
/// | 11   | EOS   | 1     | Exception-exit serialization (RES1)                  |
/// | 12   | I     | 1     | Enable I-cache                                       |
/// | 19   | WXN   | 1     | **HW W^X** — writable regions are non-executable     |
/// | 22   | EIS   | 1     | Exception-entry serialization (RES1)                 |
/// | 23   | SPAN  | 1     | RES1 (seLe4n does not use FEAT_PAN)                  |
/// | 28   | TSCXT | 1     | RES1                                                 |
/// | 29   | -     | 1     | Architecturally RES1                                 |
///
/// All other bits are 0. No read-modify-write — the bitmap is the complete
/// target state. Reserved bits that must be 1 on ARMv8.0-A are covered by
/// the RES1 entries above.
///
/// Defense-in-depth (four-layer W^X with AK3-B):
/// - L1: `fromPagePermissions` rejects W+X at the VSpace wrapper layer
/// - L2: `VSpaceBackend.mapPage` enforces `wxCompliant` at the backend
/// - L3: Page table descriptor encode strips `EL1XN` when `AP` is writable
/// - L4: SCTLR_EL1.WXN=1 at the HW layer (this bit)
#[inline(always)]
pub const fn compute_sctlr_el1_bitmap() -> u64 {
    use sctlr_bits::*;
    // Active functional bits.
    let functional = M | C | I | SA | WXN | EOS | EIS;
    // Reserved-1 bits per ARM ARM D17.2.120 (ARMv8.0-A SCTLR_EL1):
    // bits 4 (SA0), 7 (ITD), 8 (SED), 11 (EOS — already in functional),
    // 22 (EIS — already in functional), 23 (SPAN), 28 (TSCXT), 29.
    let res1 = SA0 | ITD | SED | SPAN | TSCXT | RES1_BIT29;
    functional | res1
}

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
pub struct BootL1Table {
    entries: [u64; L1_ENTRIES],
}

impl BootL1Table {
    const fn new() -> Self {
        Self { entries: [0; L1_ENTRIES] }
    }
}

/// AK5-E (R-HAL-H01, R-HAL-M03): Interior-mutable wrapper around the boot
/// L1 page table.
///
/// We cannot use `Mutex` because the mutex itself requires the MMU to be
/// enabled (for atomic CAS semantics across cache/memory) and we are
/// initializing the MMU here. Instead we rely on the single-threaded boot
/// invariant documented in `enable_mmu` plus the interrupts-disabled
/// precondition to serialize mutating accesses.
///
/// This replaces the deprecated-in-future-editions `static mut BOOT_L1_TABLE`
/// pattern that the audit flagged as technically unsound under Rust aliasing
/// rules.
#[repr(align(4096))]
pub struct PageTableCell {
    inner: UnsafeCell<BootL1Table>,
}

// SAFETY: The boot sequence is single-threaded (AK5-I core-0-only gate);
// mutation is gated by interrupts-disabled precondition in `with_inner_mut`.
unsafe impl Sync for PageTableCell {}

impl PageTableCell {
    const fn new(table: BootL1Table) -> Self {
        Self { inner: UnsafeCell::new(table) }
    }

    /// Run `f` with an `&mut BootL1Table`.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - Single-threaded context (boot or an interrupts-disabled window).
    /// - Either the MMU is disabled, OR the caller re-programs TTBR
    ///   atomically after mutation so concurrent walks cannot observe a
    ///   partial update.
    pub unsafe fn with_inner_mut<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut BootL1Table) -> R,
    {
        let ptr = self.inner.get();
        // SAFETY: caller obligations documented above.
        f(unsafe { &mut *ptr })
    }

    /// Physical address of the table (identity-mapped during boot).
    #[inline(always)]
    pub fn pa(&self) -> usize {
        self.inner.get() as usize
    }

    /// Byte size of the table (for D-cache maintenance range).
    #[inline(always)]
    pub const fn size() -> usize {
        core::mem::size_of::<BootL1Table>()
    }
}

/// Boot L1 page table — safe `PageTableCell` wrapping a zero-initialized
/// `BootL1Table`. Replaces `static mut BOOT_L1_TABLE` per AK5-E.
static BOOT_L1_TABLE: PageTableCell = PageTableCell::new(BootL1Table::new());

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
fn build_identity_tables() {
    // SAFETY: Boot context is single-threaded (core 0 only, per AK5-I), the
    // MMU has not been enabled yet, and interrupts are still masked by the
    // reset state. No concurrent access to BOOT_L1_TABLE is possible.
    unsafe {
        BOOT_L1_TABLE.with_inner_mut(|table| {
            // First 3 GiB: Normal cacheable RAM (block descriptors)
            for i in 0..3 {
                let addr = (i as u64) << 30; // 1 GiB per entry
                table.entries[i] = addr | BLOCK_NORMAL;
            }

            // 4th GiB: Device memory for BCM2712 peripherals
            // Covers 0xC0000000 – 0xFFFFFFFF including:
            //   0xFE000000 (peripheral base low)
            //   0xFF841000 (GIC distributor)
            //   0xFF842000 (GIC CPU interface)
            table.entries[3] = (3u64 << 30) | BLOCK_DEVICE;
        });
    }
}

// AK5-D: `configure_mair` and `configure_tcr` were collapsed into
// `enable_mmu` so that MAIR/TCR/TTBR/SCTLR are programmed as a single
// serialized sequence per ARM ARM D8.11. Callers should invoke
// `init_mmu()` for the full boot-time configuration.

/// AK5-E.3: TTBR0_EL1 BAADDR mask — bits [47:12] on ARMv8 (clears CnP bit 0,
/// common-not-private bit, and any reserved bits set on the raw PA).
const TTBR_BAADDR_MASK: u64 = 0x0000_FFFF_FFFF_F000;

/// Set TTBR0/TTBR1 and enable the MMU — AK5-D/AK5-C/AK5-E.3 full sequence.
///
/// # SAFETY preconditions
///
/// Caller must ensure (all six bullets hold before invocation):
///
/// 1. CPU is at EL1 (MMU can only be enabled from EL1; calling from EL0 or
///    EL2 is undefined).
/// 2. IRQs are DISABLED (DAIF.I == 1). The reset state satisfies this; if
///    the boot path has re-enabled IRQs at any point it must mask them
///    again before calling `enable_mmu`.
/// 3. `BOOT_L1_TABLE` has been initialized by `build_identity_tables` —
///    identity-map L1 block descriptors for every accessible RAM/MMIO
///    region the kernel will touch after MMU enable.
/// 4. `enable_mmu` is called exactly ONCE per core during boot. Re-entering
///    on a warm path would require TLB+cache maintenance around the new
///    TTBR write; we do not attempt that here.
/// 5. No other core is touching `BOOT_L1_TABLE` or TTBR0_EL1 concurrently.
///    The kernel boots core 0 only (AK5-I); secondary cores WFE-loop until
///    SMP bring-up is wired in WS-V.
/// 6. Caches and MMU are currently DISABLED (SCTLR.M/C/I == 0). This is
///    the reset state for ARMv8 (ARM ARM D7.2) and is re-established by
///    firmware before handing control to the kernel.
///
/// # SEQUENCE (ARM ARM D8.11 reference ordering)
///
/// 1. `tlbi vmalle1` + DSB ISH + ISB —
///    Invalidate stale TLB entries from prior boots / warm resets.
/// 2. `dc cvac` over `[BOOT_L1_TABLE.pa() .. pa()+size]` + DSB ISH —
///    Clean the page-table range to the Point of Coherency so the walker
///    sees committed descriptors once SCTLR.C=1.
/// 3. Program `TTBR0_EL1`, `TTBR1_EL1`, `TCR_EL1`, `MAIR_EL1`.
/// 4. DSB ISH + ISB —
///    Serialize the configuration writes.
/// 5. `msr SCTLR_EL1, compute_sctlr_el1_bitmap()` —
///    Write the full bitmap (AK5-C: M|C|I|SA|SA0|WXN|EOS|EIS|RES1) so
///    WXN, SP-alignment, and exception serialization are all enabled
///    atomically with the MMU.
/// 6. ISB —
///    Serialize the SCTLR write per ARM ARM D8.11 so subsequent fetches
///    go through translation.
#[allow(unsafe_code)]
fn enable_mmu() {
    // Step 1: Invalidate stale TLB entries (cold reset / warm-reset safety).
    // `tlbi_vmalle1()` emits DSB ISH + ISB internally.
    crate::tlb::tlbi_vmalle1();

    // Step 2: Resolve the L1 table PA and clean it to the PoC so the walker
    //         sees committed descriptors. Debug asserts catch misaligned or
    //         out-of-PA-window images.
    let pt_pa_raw = BOOT_L1_TABLE.pa();

    // AK5-E.3: L1 table must be 4 KiB aligned for TTBR BAADDR.
    debug_assert!(
        pt_pa_raw & 0xFFF == 0,
        "BOOT_L1_TABLE not 4 KiB-aligned"
    );
    // AK5-E.3: PA must be within the platform's physical address window
    // (RPi5 BCM2712: 44-bit PA per AJ3-B).
    debug_assert!(
        pt_pa_raw != 0 && pt_pa_raw < (1usize << 44),
        "BOOT_L1_TABLE PA out of 44-bit range"
    );

    let pt_size = PageTableCell::size();
    // SAFETY: `BOOT_L1_TABLE` is a valid RAM address (identity-mapped);
    // `pt_size` is its full extent. No concurrent write per SAFETY bullet 5.
    unsafe { crate::cache::clean_pagetable_range(pt_pa_raw, pt_size); }

    // Step 3: Program TTBR and configuration registers.
    let ttbr_baaddr = (pt_pa_raw as u64) & TTBR_BAADDR_MASK;
    crate::registers::write_ttbr0_el1(ttbr_baaddr);
    crate::registers::write_ttbr1_el1(ttbr_baaddr);
    crate::registers::write_tcr_el1(TCR_VALUE);
    crate::registers::write_mair_el1(MAIR_VALUE);

    // Step 4: Serialize config writes.
    barriers::dsb_ish();
    barriers::isb();

    // Step 5: Enable MMU + caches via the AK5-C full bitmap (M|C|I|SA|SA0|
    //         WXN|EOS|EIS|RES1). This replaces the prior read-modify-write
    //         pattern which inherited the reset value's undefined bits.
    crate::registers::write_sctlr_el1(compute_sctlr_el1_bitmap());

    // Step 6: ISB after SCTLR write per ARM ARM D8.11 — subsequent fetches
    //         must go through translation.
    barriers::isb();
}

/// Full MMU initialization sequence.
///
/// Called from `boot::rust_boot_main` after UART is available.
///
/// AK5-D: Builds identity-mapped page tables, then calls `enable_mmu`
/// which performs the full ARM ARM D8.11 MMU-enable sequence (TLBI,
/// D-cache clean of page-table range, TCR/MAIR/TTBR programming, SCTLR
/// write with the full AK5-C bitmap, serialization barriers).
pub fn init_mmu() {
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
        // BootL1Table must be 4096-byte aligned for ARMv8 TTBR
        assert_eq!(core::mem::align_of::<BootL1Table>(), 4096);
    }

    #[test]
    fn l1_table_has_512_entries() {
        assert_eq!(L1_ENTRIES, 512);
        assert_eq!(core::mem::size_of::<BootL1Table>(), 512 * 8);
    }

    // =====================================================================
    // AK5-C: SCTLR_EL1 bitmap tests
    // =====================================================================

    #[test]
    fn sctlr_bitmap_has_mmu_and_caches() {
        // M (bit 0), C (bit 2), I (bit 12): MMU + both caches.
        let sctlr = compute_sctlr_el1_bitmap();
        assert_ne!(sctlr & (1 << 0), 0, "M not set");
        assert_ne!(sctlr & (1 << 2), 0, "C not set");
        assert_ne!(sctlr & (1 << 12), 0, "I not set");
    }

    #[test]
    fn sctlr_bitmap_has_wxn() {
        // AK5-C: Bit 19 (WXN) MUST be set — HW layer of the four-layer
        // W^X defense-in-depth.
        let sctlr = compute_sctlr_el1_bitmap();
        assert_ne!(sctlr & (1 << 19), 0,
            "SCTLR_EL1.WXN is zero — HW W^X defeated");
    }

    #[test]
    fn sctlr_bitmap_has_sp_alignment() {
        // AK5-C: Bit 3 (SA) and bit 4 (SA0) enable SP alignment checks.
        let sctlr = compute_sctlr_el1_bitmap();
        assert_ne!(sctlr & (1 << 3), 0, "SA not set (EL1 SP alignment)");
        assert_ne!(sctlr & (1 << 4), 0, "SA0 not set (EL0 SP alignment)");
    }

    #[test]
    fn sctlr_bitmap_has_exception_serialization() {
        // AK5-C: Bit 11 (EOS) + bit 22 (EIS) = exception entry/exit
        // serialization.
        let sctlr = compute_sctlr_el1_bitmap();
        assert_ne!(sctlr & (1 << 11), 0, "EOS not set");
        assert_ne!(sctlr & (1 << 22), 0, "EIS not set");
    }

    #[test]
    fn sctlr_bitmap_res1_bits_are_set() {
        // AK5-C: Reserved-1 bits per ARM ARM D17.2.120 must all be 1.
        // Bits 4, 7, 11, 22, 23, 28, 29 are RES1 on ARMv8.0-A SCTLR_EL1.
        let sctlr = compute_sctlr_el1_bitmap();
        for bit in [4u32, 7, 11, 22, 23, 28, 29] {
            assert_ne!(sctlr & (1u64 << bit), 0,
                "RES1 bit {bit} is zero in SCTLR bitmap");
        }
    }

    #[test]
    fn sctlr_bitmap_is_const_computable() {
        // `compute_sctlr_el1_bitmap` is `const fn` — usable in a
        // compile-time assertion.
        const SCTLR: u64 = compute_sctlr_el1_bitmap();
        assert!(SCTLR != 0);
    }

    // =====================================================================
    // AK5-E: PageTableCell tests
    // =====================================================================

    #[test]
    fn boot_l1_table_size_matches_layout() {
        // 512 entries × 8 bytes = 4096 bytes.
        assert_eq!(PageTableCell::size(), 4096);
    }

    #[test]
    fn page_table_cell_pa_matches_inner() {
        // The PA returned by `pa()` must equal the raw pointer of the
        // underlying BootL1Table.
        let pa = BOOT_L1_TABLE.pa();
        assert_ne!(pa, 0);
        // 4 KiB alignment invariant needed by TTBR BAADDR.
        assert_eq!(pa & 0xFFF, 0);
    }

    #[test]
    fn ttbr_baaddr_mask_preserves_bits_47_12() {
        // AK5-E.3: BAADDR mask keeps [47:12] only.
        assert_eq!(TTBR_BAADDR_MASK, 0x0000_FFFF_FFFF_F000);
        let pa: u64 = 0x1234_5000;
        assert_eq!(pa & TTBR_BAADDR_MASK, pa);
        // CnP bit 0 and any reserved low bits are cleared.
        let dirty: u64 = 0x1234_5FFF;
        assert_eq!(dirty & TTBR_BAADDR_MASK, 0x1234_5000);
    }
}
