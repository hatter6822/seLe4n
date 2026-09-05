// SPDX-License-Identifier: GPL-3.0-or-later
//! MMU configuration for ARMv8-A on Raspberry Pi 5.
//!
//! Sets up MAIR_EL1, TCR_EL1, identity-mapped boot page tables, and enables
//! the MMU via SCTLR_EL1. Initial boot mapping uses 1 GiB block descriptors
//! at L1 for simplicity; the **runtime** kernel uses fine-grained 4 KiB
//! page-level mappings via `SeLe4n.Kernel.Architecture.PageTable` (AG6) and
//! `SeLe4n.Kernel.Architecture.VSpaceARMv8` (AG6-C/D), bridged to hardware
//! through the `VSpaceBackend` typeclass instance. AN8-D (RUST-M04): the
//! pre-AG6 stale "AG6 replaces this" comment is replaced with this clarified
//! description — the boot table and the runtime page-table are deliberately
//! distinct: the boot table covers the kernel image plus the device-memory
//! window so the kernel can run at all; the runtime page-table is built on
//! top of it once the kernel scheduler is alive.
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
/// - EPD1  = 1 (bit 23):        TTBR1 walks disabled (WS-RR RR7.1)
///
/// **WS-RR RR7.1 — `EPD1`**: the boot path installs no TTBR1 table, so a
/// translation in the top half of the virtual address space must **fault**.
/// Before RR7.1 TTBR1_EL1 was programmed with the TTBR0 identity table and
/// EPD1 was clear, so the top half silently aliased low physical memory.  The
/// AG6 kernel/user split is the cut that installs a real TTBR1 table; it clears
/// this bit in the same change that writes the table.  The remaining TTBR1
/// fields (T1SZ/TG1/SH1/ORGN1/IRGN1) are kept at their intended values so that
/// clearing EPD1 is the only edit that cut needs.
///
/// `T0SZ = 16` puts the initial TTBR0 lookup level at **0** for the 4 KiB
/// granule (ARM ARM D8.3), which is why [`BootPageTables`] starts with a level-0
/// table of Table descriptors rather than the level-1 block table that used to
/// sit under TTBR0.
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
    let epd1: u64 = 1 << 23; // WS-RR RR7.1: no TTBR1 table exists yet
    t0sz | t1sz | tg0 | tg1 | ips | sh0 | sh1 | orgn0 | irgn0 | orgn1 | irgn1 | epd1
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
/// AN8-D (RUST-M01): This module intentionally enumerates ALL bits that
/// seLe4n's bitmap explicitly sets or documents as "excluded by design".
/// A module-level `#[allow(dead_code)]` covers the reference-only constants
/// so the bitmap's SAFETY comments can cite them by name without cluttering
/// every constant with an individual attribute. The following bits are
/// **reference-only** (declared but not OR'd into
/// `compute_sctlr_el1_bitmap`):
///
/// | Bit | Name    | Excluded because                                                 |
/// |-----|---------|-------------------------------------------------------------------|
/// | 1   | A       | Alignment checks on data-memory accesses would false-fault on    |
/// |     |         | kernel byte-wise `memcpy` sequences; SA/SA0/WXN cover the SP     |
/// |     |         | and write-execute cases which are the security-relevant ones.   |
/// | 5   | CP15BEN | AArch32-only; seLe4n runs EL0/EL1 in AArch64.                    |
/// | 6   | NAA     | We WANT unaligned-access faults preserved (0 = default).         |
/// | 9   | UMA     | Related to FEAT_PAN which seLe4n does not use.                   |
/// | 25  | EE      | EL1 little-endian (default); flipping this corrupts all kernel   |
/// |     |         | memory accesses.                                                  |
mod sctlr_bits {
    #![allow(dead_code)]
    pub const M: u64 = 1 << 0; // MMU enable
    pub const A: u64 = 1 << 1; // Alignment check enable (EL0 + EL1)
    pub const C: u64 = 1 << 2; // Data cache enable
    pub const SA: u64 = 1 << 3; // SP alignment check enable (EL1)
    pub const SA0: u64 = 1 << 4; // SP alignment check enable (EL0, RES1)
    pub const CP15BEN: u64 = 1 << 5; // AArch32 CP15 barrier enable (RES0 at AArch64)
    pub const NAA: u64 = 1 << 6; // Non-aligned access: 0 = faults preserved
    pub const ITD: u64 = 1 << 7; // IT instruction disable (RES1 at AArch64)
    pub const SED: u64 = 1 << 8; // SETEND disable (RES1 at AArch64)
    pub const UMA: u64 = 1 << 9; // User Mask Access (PAN-related)
    pub const EOS: u64 = 1 << 11; // Exception Exit Serialization (EL1, RES1)
    pub const I: u64 = 1 << 12; // Instruction cache enable
    pub const WXN: u64 = 1 << 19; // Write permission implies XN (HW W^X)
    /// Bit 20 — architecturally RES1 on ARMv8.0-A; defined as IESB (Implicit
    /// Error Synchronization Barrier) in ARMv8.2-A+. Cortex-A76 implements
    /// ARMv8.2, so setting this to 1 also enables the implicit ESB on
    /// exception entry/exit — a defensive hardening for fault containment.
    pub const RES1_BIT20: u64 = 1 << 20;
    pub const EIS: u64 = 1 << 22; // Exception Entry Serialization (EL1, RES1)
    pub const SPAN: u64 = 1 << 23; // Set Privileged Access Never on exception (RES1)
    pub const EE: u64 = 1 << 25; // Exception endianness: 0 = little-endian at EL1
    pub const TSCXT: u64 = 1 << 28; // Trap EL0 access to SCXTNUM_EL0 (RES1)
    pub const RES1_BIT29: u64 = 1 << 29; // Architecturally RES1
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
/// | 20   | -     | 1     | RES1 on v8.0-A; IESB on v8.2-A+ (Cortex-A76)         |
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
    // Reserved-1 bits per ARM ARM D17.2.120 (ARMv8.0-A SCTLR_EL1).
    // Linux's `SCTLR_EL1_RES1` macro uses bits 11, 20, 22, 28, 29; seL4
    // adds 23 (SPAN) when PAN is not supported, and 4 (SA0), 7 (ITD), 8
    // (SED) are RES1 when AArch32 EL0 is absent (Cortex-A76 is
    // AArch64-only for EL0 in seLe4n).
    let res1 = SA0 | ITD | SED | RES1_BIT20 | SPAN | TSCXT | RES1_BIT29;
    functional | res1
}

// ---------------------------------------------------------------------------
// WS-RR RR7.1: the boot memory map — one declaration, every consumer
// ---------------------------------------------------------------------------
//
// The boot translation tables, the cacheable-window predicate the
// cache-maintenance FFI fails closed on ([`is_boot_cacheable_range`]) and the
// host tests all read the map from [`boot_mapping_for`].  Deriving them from
// one function is the project's "one question, one answer" discipline: before
// RR7.1 the table builder was the only statement of the map, so nothing else
// could ask it a question, and the 960 MiB of linker-declared RAM it typed as
// Device was invisible to every gate.
//
// The boundaries mirror `rpi5MemoryMapForConfig` in
// `SeLe4n/Platform/RPi5/Board.lean`, the project's canonical BCM2712 physical
// memory map; `scripts/check_physical_address_width.sh` holds the two equal and
// holds `LOW_RAM_TOP` equal to the RAM extent `link.ld` declares.

/// One past the last byte of the low RAM aperture (4032 MiB).
///
/// `link.ld` declares `RAM : ORIGIN = 0x80000, LENGTH = 0xFBF80000`, whose end
/// is exactly this address, and `rpi5MemoryMapForConfig`'s `peripheralBoundary`
/// is the same constant.  RAM below it is mapped Normal Write-Back cacheable;
/// nothing above it is RAM on any BCM2712 board.
pub const LOW_RAM_TOP: u64 = 0xFC00_0000;

/// Base of the device (peripheral) window: BCM2712 legacy peripherals at
/// `0xFE00_0000` through the GIC-400 at `0xFF84_1000` / `0xFF84_2000`.
///
/// `[LOW_RAM_TOP, DEVICE_WINDOW_BASE)` is the VideoCore firmware carve-out,
/// which the kernel must never touch — it is left **unmapped** so a stray
/// access faults rather than reaching the GPU's memory through a Device alias.
pub const DEVICE_WINDOW_BASE: u64 = 0xFE00_0000;

/// One past the last byte of the device window, rounded up to the L2 block
/// size from the Lean map's `0xFF85_0000` device extent.
///
/// `[DEVICE_WINDOW_TOP, HIGH_RAM_BASE)` is declared reserved by
/// `rpi5MemoryMapForConfig` and is left unmapped for the same fail-closed
/// reason as the firmware carve-out.
pub const DEVICE_WINDOW_TOP: u64 = 0xFFA0_0000;

/// Base of the RAM aperture above the 4 GiB boundary (8 GiB and 16 GiB
/// boards).  `rpi5MemoryMapForConfig` places its second RAM region here.
pub const HIGH_RAM_BASE: u64 = 0x1_0000_0000;

/// What the boot tables map an address as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BootMapping {
    /// Normal, Inner Shareable, Write-Back cacheable — RAM.
    NormalRam,
    /// Device-nGnRnE, PXN|UXN — MMIO.
    Device,
    /// No descriptor: an access takes a Translation fault.
    Unmapped,
}

/// **WS-RR RR7.1**: what the boot tables map `addr` as, on a board whose RAM
/// ends at `ram_top`.
///
/// `ram_top` is the exclusive top of physical RAM, already passed through
/// [`clamp_ram_top`] (see [`boot_ram_top`]).  Two clamps matter and neither is
/// cosmetic:
///
///   * RAM below `LOW_RAM_TOP` is Normal **only up to `ram_top`**.  A board
///     whose DRAM stops short of `0xFC00_0000` has nothing between its real top
///     and the firmware carve-out, and Normal memory is speculatively
///     accessible — mapping absent DRAM cacheable invites a speculative fetch
///     into an unbacked physical address.
///   * RAM above `HIGH_RAM_BASE` is Normal only up to `ram_top`, for the same
///     reason.  A 4 GiB board maps nothing there at all.
#[must_use]
pub const fn boot_mapping_for(addr: u64, ram_top: u64) -> BootMapping {
    let low_ram_top = if ram_top < LOW_RAM_TOP {
        ram_top
    } else {
        LOW_RAM_TOP
    };
    if addr < low_ram_top {
        BootMapping::NormalRam
    } else if addr < DEVICE_WINDOW_BASE {
        // VideoCore firmware carve-out, or absent DRAM on a small board.
        BootMapping::Unmapped
    } else if addr < DEVICE_WINDOW_TOP {
        BootMapping::Device
    } else if addr < HIGH_RAM_BASE {
        // Reserved above the GIC.
        BootMapping::Unmapped
    } else if addr < ram_top {
        BootMapping::NormalRam
    } else {
        BootMapping::Unmapped
    }
}

/// **WS-RR RR7.1**: round a device-tree-reported RAM top down to the
/// granularity the boot tables can describe there.
///
/// The tables describe `[0, 4 GiB)` with 2 MiB L2 blocks and everything above
/// with 1 GiB L1 blocks, so a RAM top that falls inside a block would make the
/// descriptor and [`boot_mapping_for`] disagree about the addresses in that
/// block — one question with two answers.  Rounding **down** keeps them equal
/// and is the fail-closed direction: at worst the kernel declines to map a
/// partial block of real RAM, which is a lost resource rather than a
/// speculative access into an unbacked address.
///
/// Every constant boundary of the map (`LOW_RAM_TOP`, `DEVICE_WINDOW_BASE`,
/// `DEVICE_WINDOW_TOP`, `HIGH_RAM_BASE`) is already 2 MiB aligned, so after
/// this clamp every boundary is block aligned at the granularity that describes
/// it.
#[must_use]
pub const fn clamp_ram_top(raw: u64) -> u64 {
    if raw >= HIGH_RAM_BASE {
        raw & !(L1_BLOCK_SIZE - 1)
    } else {
        raw & !(L2_BLOCK_SIZE - 1)
    }
}

/// **WS-RR RR7.1**: exclusive top of physical RAM, as the boot tables map it.
///
/// Written once by [`init_mmu`] from the device tree's `/memory` node before
/// the tables are built, and read afterwards by [`is_boot_cacheable_range`].
/// The initial value is [`LOW_RAM_TOP`] — the linker's own declaration, which
/// is what the image was built against and the honest fallback when no device
/// tree is available.
static BOOT_RAM_TOP: core::sync::atomic::AtomicU64 =
    core::sync::atomic::AtomicU64::new(LOW_RAM_TOP);

/// **WS-RR RR7.1**: the (clamped) RAM top the boot tables were built with.
#[inline]
#[must_use]
pub fn boot_ram_top() -> u64 {
    BOOT_RAM_TOP.load(core::sync::atomic::Ordering::Relaxed)
}

/// **WS-RR RR7.1**: record the RAM top the boot tables are about to be built
/// with.  Called by [`build_identity_tables`] on the boot core, and by tests;
/// secondaries never call it, since they reuse the primary's tables.
#[inline]
fn set_boot_ram_top(ram_top: u64) {
    BOOT_RAM_TOP.store(ram_top, core::sync::atomic::Ordering::Relaxed);
}

/// **WS-RR RR7.2**: is every byte of `[base, base + size)` inside the
/// identity-mapped Normal window?
///
/// This is the predicate the instruction- and data-cache maintenance FFI fails
/// closed on.  `IC IVAU` / `DC CVAU` take a **virtual** address, the kernel
/// passes a **physical** one, and the two are the same address only inside the
/// identity map: outside it the operand either faults at EL1 or operates
/// through a Device alias, and a silently under-maintained cache is a
/// correctness violation the caller cannot detect.
///
/// Asks the question for a *range* rather than for its first byte, because a
/// range that starts in RAM and runs off the end of it is exactly the
/// under-maintenance a per-address check would miss.  The Normal window is the
/// union of at most two intervals — `[0, min(ram_top, LOW_RAM_TOP))` and
/// `[HIGH_RAM_BASE, ram_top)` — so containment is decided directly rather than
/// by walking; `boot_cacheable_range_agrees_with_pointwise_mapping` pins the two
/// readings equal.  An empty range is vacuously contained; a range whose end
/// overflows `u64` is refused.
#[must_use]
pub fn is_boot_cacheable_range(base: u64, size: u64) -> bool {
    boot_cacheable_range_in(base, size, boot_ram_top())
}

/// **WS-RR RR7.2**: [`is_boot_cacheable_range`] over an explicit RAM top.
///
/// The pure core, so the witnesses decide the question without writing the
/// process-wide [`BOOT_RAM_TOP`] — a test that mutates it decides a *different*
/// test's answer when the harness runs them in parallel.
#[must_use]
pub const fn boot_cacheable_range_in(base: u64, size: u64, ram_top: u64) -> bool {
    if size == 0 {
        return true;
    }
    let Some(end) = base.checked_add(size) else {
        return false;
    };
    let low_ram_top = if ram_top < LOW_RAM_TOP {
        ram_top
    } else {
        LOW_RAM_TOP
    };
    // Wholly inside the low RAM aperture.
    if end <= low_ram_top {
        return true;
    }
    // Wholly inside the high RAM aperture.
    if base >= HIGH_RAM_BASE && end <= ram_top {
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Boot page tables
// ---------------------------------------------------------------------------

/// Entries in one 4 KiB translation table (4096 / 8).
const TABLE_ENTRIES: usize = 512;

/// Bytes one L1 block descriptor maps (1 GiB).
const L1_BLOCK_SIZE: u64 = 1 << 30;

/// Bytes one L2 block descriptor maps (2 MiB).
const L2_BLOCK_SIZE: u64 = 1 << 21;

/// How many gigabytes of the low physical address space are described at 2 MiB
/// granularity by dedicated L2 tables.
///
/// Every non-gigabyte-aligned boundary of the map — the low RAM top, the
/// firmware carve-out, the device window — lies inside the first 4 GiB, and a
/// board whose DRAM stops mid-gigabyte puts one more there.  Describing the
/// whole low 4 GiB at 2 MiB granularity means no partial L1 block ever has to
/// be either over-mapped (absent DRAM made speculatively accessible) or dropped
/// (real RAM lost, including the gigabyte the kernel image sits in).
const REFINED_GIB_COUNT: usize = 4;

/// Table descriptor type bits (`bits[1:0] = 0b11`, ARM ARM D8.3).
///
/// **WS-RR RR7.1**: the distinction from [`DESC_VALID`] is what the pre-RR7.1
/// boot table got wrong.  `TCR_EL1.T0SZ = 16` makes the input address 48 bits,
/// and with the 4 KiB granule that puts the **initial lookup level at 0**; a
/// level-0 descriptor with a 4 KiB granule may only be a Table descriptor
/// (level-0 blocks require FEAT_LPA2 with `TCR.DS = 1`, which the ARMv8.2-A
/// Cortex-A76 does not implement).  The table TTBR0_EL1 pointed at held 1 GiB
/// *block* descriptors — `bits[1:0] = 0b01` — so every walk decoded a reserved
/// level-0 descriptor and took a translation fault.  It never showed because no
/// image has booted yet.
const DESC_TABLE: u64 = 0b11;

/// Address mask for a next-level table pointer or a block output address
/// (bits [47:12]).
const DESC_ADDR_MASK: u64 = 0x0000_FFFF_FFFF_F000;

/// Boot translation tables: a level-0 table whose entry 0 reaches a level-1
/// table, whose first four entries reach level-2 tables.
///
/// Laid out as one `#[repr(C, align(4096))]` struct so all six tables are
/// contiguous and 4 KiB aligned (each array is exactly one 4 KiB page), which
/// lets [`enable_mmu`] clean the whole extent to the Point of Coherency in one
/// range operation.
///
/// - **L0** (entry 0 only): a Table descriptor to `l1`, covering VA
///   `[0, 512 GiB)`.  Every other L0 entry is invalid, so a virtual address
///   above 512 GiB faults.
/// - **L1**: entries 0..3 are Table descriptors to `l2_low`; entries 4.. are
///   1 GiB Normal blocks up to the board's RAM top, invalid above it.
/// - **L2** (`l2_low[g]`): 2 MiB blocks describing `[g GiB, (g+1) GiB)`.
#[repr(C, align(4096))]
pub struct BootPageTables {
    l0: [u64; TABLE_ENTRIES],
    l1: [u64; TABLE_ENTRIES],
    l2_low: [[u64; TABLE_ENTRIES]; REFINED_GIB_COUNT],
}

impl BootPageTables {
    const fn new() -> Self {
        Self {
            l0: [0; TABLE_ENTRIES],
            l1: [0; TABLE_ENTRIES],
            l2_low: [[0; TABLE_ENTRIES]; REFINED_GIB_COUNT],
        }
    }
}

/// AK5-E (R-HAL-H01, R-HAL-M03): Interior-mutable wrapper around the boot
/// translation tables.
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
    inner: UnsafeCell<BootPageTables>,
}

// SAFETY: The boot sequence is single-threaded (AK5-I core-0-only gate);
// mutation is gated by interrupts-disabled precondition in `with_inner_mut`.
unsafe impl Sync for PageTableCell {}

impl PageTableCell {
    const fn new(tables: BootPageTables) -> Self {
        Self {
            inner: UnsafeCell::new(tables),
        }
    }

    /// Run `f` with an `&mut BootPageTables`.
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
        F: FnOnce(&mut BootPageTables) -> R,
    {
        let ptr = self.inner.get();
        // SAFETY: caller obligations documented above.
        f(unsafe { &mut *ptr })
    }

    /// Physical address of the level-0 table — the value TTBR0_EL1 takes.
    ///
    /// The L0 array is the first member of a `#[repr(C)]` struct, so its
    /// address is the struct's.
    #[inline(always)]
    pub fn pa(&self) -> usize {
        self.inner.get() as usize
    }

    /// Byte size of the whole table extent (for D-cache maintenance range).
    #[inline(always)]
    pub const fn size() -> usize {
        core::mem::size_of::<BootPageTables>()
    }
}

/// Boot translation tables — safe `PageTableCell` wrapping a zero-initialized
/// `BootPageTables`. Replaces `static mut BOOT_L1_TABLE` per AK5-E.
static BOOT_TABLES: PageTableCell = PageTableCell::new(BootPageTables::new());

// AK5-E / AK5-D: compile-time enforcement of the TTBR BAADDR alignment
// contract. If either invariant is ever violated (linker bug, struct
// refactor losing `#[repr(align(4096))]`, etc.) the build fails loudly.
const _: () = assert!(core::mem::align_of::<PageTableCell>() == 4096);
const _: () = assert!(core::mem::align_of::<BootPageTables>() == 4096);

// AN8-E (R-HAL-L10): ARMv8 requires 4 KiB alignment for translation-table base
// addresses; each of the tables must be exactly one 4 KiB page so that the L1
// and L2 tables, which sit at struct offsets 4096 and 8192.., are 4 KiB aligned
// too — the alignment a Table descriptor's [47:12] address field assumes.
const _: () = assert!(
    TABLE_ENTRIES == 512,
    "TABLE_ENTRIES must be 512 (4 KiB / 8 bytes/entry) per ARMv8 D8.3"
);
const _: () = assert!(
    core::mem::size_of::<BootPageTables>() == (2 + REFINED_GIB_COUNT) * 4096,
    "BootPageTables must be a whole number of 4 KiB translation tables"
);
// The refined window must cover every non-gigabyte-aligned boundary of the map.
const _: () = assert!(
    DEVICE_WINDOW_TOP <= (REFINED_GIB_COUNT as u64) * L1_BLOCK_SIZE,
    "the device window must lie inside the L2-refined low window"
);
const _: () = assert!(
    HIGH_RAM_BASE == (REFINED_GIB_COUNT as u64) * L1_BLOCK_SIZE,
    "high RAM must start exactly where the L2-refined low window ends"
);
// Every constant boundary is 2 MiB aligned, which is what makes `clamp_ram_top`
// enough to keep the descriptors and `boot_mapping_for` in agreement.
const _: () = assert!(LOW_RAM_TOP.is_multiple_of(L2_BLOCK_SIZE));
const _: () = assert!(DEVICE_WINDOW_BASE.is_multiple_of(L2_BLOCK_SIZE));
const _: () = assert!(DEVICE_WINDOW_TOP.is_multiple_of(L2_BLOCK_SIZE));
const _: () = assert!(HIGH_RAM_BASE.is_multiple_of(L1_BLOCK_SIZE));

/// **WS-RR RR7.1**: physical address of the `g`-th L2 table, given the struct
/// base.  `l2_low[g]` sits after the L0 and L1 tables.
#[inline]
const fn l2_table_pa(base_pa: u64, g: usize) -> u64 {
    base_pa + ((2 + g) as u64) * 4096
}

/// **WS-RR RR7.1**: populate the boot translation tables in place.
///
/// Pure over its arguments so the host test suite can assert every descriptor
/// without an MMU: `base_pa` is the physical address of the whole
/// [`BootPageTables`] extent and `ram_top` the clamped exclusive top of
/// physical RAM.
///
/// Every descriptor is derived from [`boot_mapping_for`], so the tables and the
/// cacheable-window predicate cannot disagree about a single address.
fn populate_boot_tables(tables: &mut BootPageTables, base_pa: u64, ram_top: u64) {
    // Level 0: one Table descriptor covering VA [0, 512 GiB).  Everything else
    // stays invalid, so a virtual address above 512 GiB faults.
    tables.l0 = [0; TABLE_ENTRIES];
    tables.l0[0] = ((base_pa + 4096) & DESC_ADDR_MASK) | DESC_TABLE;

    tables.l1 = [0; TABLE_ENTRIES];
    for g in 0..TABLE_ENTRIES {
        if g < REFINED_GIB_COUNT {
            // The low 4 GiB is described at 2 MiB granularity.
            tables.l1[g] = (l2_table_pa(base_pa, g) & DESC_ADDR_MASK) | DESC_TABLE;
            continue;
        }
        // Above 4 GiB the only boundary is the RAM top, which `clamp_ram_top`
        // has aligned to `L1_BLOCK_SIZE`, so the whole gigabyte has one kind
        // and its base decides it.
        let base = (g as u64) * L1_BLOCK_SIZE;
        tables.l1[g] = match boot_mapping_for(base, ram_top) {
            BootMapping::NormalRam => base | BLOCK_NORMAL,
            // No device or partially-mapped region exists above 4 GiB.
            BootMapping::Device | BootMapping::Unmapped => 0,
        };
    }

    for g in 0..REFINED_GIB_COUNT {
        for i in 0..TABLE_ENTRIES {
            let base = (g as u64) * L1_BLOCK_SIZE + (i as u64) * L2_BLOCK_SIZE;
            tables.l2_low[g][i] = match boot_mapping_for(base, ram_top) {
                BootMapping::NormalRam => base | BLOCK_NORMAL,
                BootMapping::Device => base | BLOCK_DEVICE,
                BootMapping::Unmapped => 0,
            };
        }
    }
}

/// Build identity-mapped boot translation tables.
///
/// **WS-RR RR7.1**: the map is [`boot_mapping_for`]'s, which mirrors
/// `rpi5MemoryMapForConfig` in `SeLe4n/Platform/RPi5/Board.lean`:
///
/// - `0x0000_0000 – 0xFBFF_FFFF`: Normal RAM (clamped to the board's RAM top)
/// - `0xFC00_0000 – 0xFDFF_FFFF`: unmapped (VideoCore firmware carve-out)
/// - `0xFE00_0000 – 0xFF9F_FFFF`: Device (BCM2712 peripherals + GIC-400)
/// - `0xFFA0_0000 – 0xFFFF_FFFF`: unmapped (reserved above the GIC)
/// - `0x1_0000_0000 – ram_top`:   Normal RAM (8 GiB and 16 GiB boards)
///
/// Before RR7.1 this mapped `0xC000_0000 – 0xFFFF_FFFF` as one Device block, so
/// 960 MiB of the RAM `link.ld` declares was Device-typed — no cacheability, no
/// unaligned access, no speculation — and nothing above 4 GiB was mapped at all.
///
/// This is a boot mapping. AN8-D (RUST-M04): the runtime kernel uses
/// fine-grained 4 KiB page tables via
/// `SeLe4n.Kernel.Architecture.PageTable` + `VSpaceARMv8` (AG6); those tables
/// are built on top of this boot mapping once the scheduler is alive.
fn build_identity_tables(raw_ram_top: u64) {
    let ram_top = clamp_ram_top(raw_ram_top);
    set_boot_ram_top(ram_top);
    let base_pa = BOOT_TABLES.pa() as u64;
    // SAFETY: Boot context is single-threaded (core 0 only, per AK5-I), the
    // MMU has not been enabled yet, and interrupts are still masked by the
    // reset state. No concurrent access to BOOT_TABLES is possible.
    unsafe {
        BOOT_TABLES.with_inner_mut(|tables| {
            populate_boot_tables(tables, base_pa, ram_top);
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
/// 3. `BOOT_TABLES` has been initialized by `build_identity_tables` —
///    an identity map, at the granularity `boot_mapping_for` declares, of
///    every accessible RAM/MMIO region the kernel will touch after MMU
///    enable.
/// 4. `enable_mmu` is called exactly ONCE per core during boot. Re-entering
///    on a warm path would require TLB+cache maintenance around the new
///    TTBR write; we do not attempt that here.
/// 5. No other core is touching `BOOT_TABLES` or TTBR0_EL1 concurrently.
///    The kernel boots core 0 only (AK5-I); secondary cores WFE-loop until
///    SMP bring-up is wired by AN9-J (closes DEF-R-HAL-L20).
/// 6. Caches and MMU are currently DISABLED (SCTLR.M/C/I == 0). This is
///    the reset state for ARMv8 (ARM ARM D7.2) and is re-established by
///    firmware before handing control to the kernel.
///
/// # SEQUENCE (ARM ARM D8.11 reference ordering)
///
/// 1. `tlbi vmalle1` + DSB ISH + ISB —
///    Invalidate stale TLB entries from prior boots / warm resets.
/// 2. `dc cvac` over `[BOOT_TABLES.pa() .. pa()+size]` + DSB ISH —
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
    let pt_pa_raw = BOOT_TABLES.pa();

    // AK5-E.3: L1 table must be 4 KiB aligned for TTBR BAADDR.
    // The `repr(align(4096))` on `PageTableCell` and `BootPageTables`
    // guarantees this on every target (aarch64 production, x86_64
    // host); the runtime check is therefore portable.
    debug_assert!(pt_pa_raw & 0xFFF == 0, "BOOT_TABLES not 4 KiB-aligned");
    // AK5-E.3: PA must be within the platform's physical address window
    // (RPi5 BCM2712: 44-bit PA per AJ3-B).  Only checked on aarch64
    // because on host x86_64 the kernel-image base address is set by
    // the host loader and routinely exceeds 2^44 (e.g., 0x55... on a
    // PIE binary), which would false-fault the assert.  WS-SM SM1.C.1
    // exposed this in the per-core MMU helper tests.
    #[cfg(target_arch = "aarch64")]
    debug_assert!(
        pt_pa_raw != 0 && pt_pa_raw < (1usize << 44),
        "BOOT_TABLES PA out of 44-bit range"
    );

    let pt_size = PageTableCell::size();
    // SAFETY: `BOOT_TABLES` is a valid RAM address (identity-mapped);
    // `pt_size` is its full extent. No concurrent write per SAFETY bullet 5.
    unsafe {
        crate::cache::clean_pagetable_range(pt_pa_raw, pt_size);
    }

    // Step 3: Program TTBR and configuration registers.
    //
    // **WS-RR RR7.1**: TTBR1_EL1 is written 0 and `TCR_EL1.EPD1` disables the
    // TTBR1 walk entirely.  It used to be programmed with the *same* table as
    // TTBR0, which identity-mapped the top half of the virtual address space
    // onto low physical addresses: a stray kernel pointer above
    // `0xFFFF_0000_0000_0000` would have silently reached RAM rather than
    // faulted.  The kernel image and every boot allocation live in the TTBR0
    // half (`link.ld` loads at `0x80000`), so nothing needs the high half
    // until AG6's kernel/user split installs a real TTBR1 table — that cut
    // clears EPD1 and writes the table it builds.
    let ttbr_baaddr = (pt_pa_raw as u64) & TTBR_BAADDR_MASK;
    crate::registers::write_ttbr0_el1(ttbr_baaddr);
    crate::registers::write_ttbr1_el1(0);
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
/// Called from `boot::rust_boot_main` after UART is available, with the device
/// tree pointer the firmware left in `x0`.
///
/// AK5-D: Builds identity-mapped page tables, then calls `enable_mmu`
/// which performs the full ARM ARM D8.11 MMU-enable sequence (TLBI,
/// D-cache clean of page-table range, TCR/MAIR/TTBR programming, SCTLR
/// write with the full AK5-C bitmap, serialization barriers).
///
/// **WS-RR RR7.1**: the tables are sized to the board.  `dtb_ptr` is read for
/// the `/memory` node's extent so RAM above the 4 GiB boundary is mapped on an
/// 8 GiB or 16 GiB board and *not* mapped on a smaller one; a missing or
/// unparseable device tree falls back to [`LOW_RAM_TOP`], which is the RAM
/// extent `link.ld` declares and therefore what this image was built against.
pub fn init_mmu(dtb_ptr: u64) {
    let ram_top = crate::cmdline::ram_top_from_dtb(dtb_ptr).unwrap_or(LOW_RAM_TOP);
    build_identity_tables(ram_top);
    init_mmu_per_core(0);
}

/// **WS-SM SM1.C.1** (closes SMP-C2 MMU step): Per-core MMU enable
/// sequence shared between primary and secondary boot.
///
/// Applies the full ARM ARM D8.11 enable-MMU sequence on the calling
/// core: TLB invalidate, D-cache clean of the boot L1 page-table range,
/// TCR/MAIR/TTBR programming, SCTLR write (the AK5-C bitmap including
/// `M | C | I | SA | SA0 | WXN | EOS | EIS | RES1`), and the
/// serialising barriers (`dsb_ish` + `isb`).
///
/// **Caller obligations**:
/// - The primary must have called [`build_identity_tables`] before any
///   per-core invocation.  The boot L1 table is then read-only — every
///   secondary's TTBR0/TTBR1 point at the same physical address.
/// - CPU at EL1, IRQs disabled, MMU disabled (the reset state for
///   secondaries entering from PSCI CPU_ON satisfies this).
///
/// **`core_id` argument**: informational; the function does not branch
/// on it.  The primary passes `0`; each secondary passes its PSCI
/// `context_id`.  Future SM5+ work may use the parameter to populate
/// per-core diagnostic state without changing the call site.
///
/// **Safety**: The shared boot L1 table is read-only post-build, so
/// concurrent invocation from multiple secondaries is sound.  TTBR
/// writes program banked per-core registers; TLB invalidate is local
/// to the calling PE (ARM ARM C6.2.311).
#[inline]
pub fn init_mmu_per_core(core_id: u64) {
    // The `enable_mmu()` body owns the full ARM ARM D8.11 sequence; the
    // function is private because callers should always go through this
    // per-core wrapper (or the primary `init_mmu()` wrapper that adds
    // the table-build step).  Pass `core_id` through for symmetry — a
    // future refactor that uses it (per-core diagnostic logging, BKL
    // tracking, etc.) only needs to touch this function.
    let _ = core_id;
    enable_mmu();
}

/// **WS-SM SM1.C.1** (closes SMP-C2 MMU step): Secondary-core MMU
/// initialization.
///
/// Called from `smp::rust_secondary_main` Step 1 on every secondary
/// core after PSCI CPU_ON.  Reuses the boot L1 page tables that the
/// primary built (i.e., does NOT call `build_identity_tables` — the
/// table is a global static populated exactly once on the boot core)
/// and applies the per-core MMU enable sequence via
/// [`init_mmu_per_core`].
///
/// **`core_id`** is the PSCI context_id (1..=`MAX_SECONDARY_CORES`).  A
/// `debug_assert!` catches a misuse where `init_mmu_secondary` is
/// called on the boot core (which should call [`init_mmu`] instead).
///
/// **Defense in depth**: the W^X bitmap, SP-alignment checks, and
/// exception serialisation in `SCTLR_EL1` (encoded via
/// [`compute_sctlr_el1_bitmap`]) are applied identically on every core
/// — there is no "weaker bitmap on secondaries" path that would create
/// a security asymmetry between cores.
pub fn init_mmu_secondary(core_id: u64) {
    debug_assert!(
        core_id > 0,
        "init_mmu_secondary called with core_id 0 — use init_mmu() for the primary"
    );
    init_mmu_per_core(core_id);
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
        // BootPageTables must be 4096-byte aligned for ARMv8 TTBR
        assert_eq!(core::mem::align_of::<BootPageTables>(), 4096);
    }

    #[test]
    fn l1_table_has_512_entries() {
        assert_eq!(TABLE_ENTRIES, 512);
        assert_eq!(
            core::mem::size_of::<BootPageTables>(),
            (2 + REFINED_GIB_COUNT) * 512 * 8
        );
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
        assert_ne!(
            sctlr & (1 << 19),
            0,
            "SCTLR_EL1.WXN is zero — HW W^X defeated"
        );
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
        // Bits 4, 7, 8, 11, 20, 22, 23, 28, 29 are RES1 on ARMv8.0-A
        // SCTLR_EL1 (Linux `SCTLR_EL1_RES1` core set = {11, 20, 22, 28,
        // 29}; additional RES1 bits when AArch32 EL0 and PAN absent:
        // {4, 7, 8, 23}).
        let sctlr = compute_sctlr_el1_bitmap();
        for bit in [4u32, 7, 8, 11, 20, 22, 23, 28, 29] {
            assert_ne!(
                sctlr & (1u64 << bit),
                0,
                "RES1 bit {bit} is zero in SCTLR bitmap"
            );
        }
    }

    #[test]
    fn sctlr_bitmap_linux_res1_subset_matches() {
        // AK5-C cross-check: the minimal RES1 set used by the Linux
        // kernel (arch/arm64/include/asm/sysreg.h SCTLR_EL1_RES1) must
        // be a strict subset of our bitmap.
        let sctlr = compute_sctlr_el1_bitmap();
        const LINUX_RES1: u64 =
            (1u64 << 11) | (1u64 << 20) | (1u64 << 22) | (1u64 << 28) | (1u64 << 29);
        assert_eq!(
            sctlr & LINUX_RES1,
            LINUX_RES1,
            "SCTLR bitmap missing a Linux SCTLR_EL1_RES1 bit"
        );
    }

    #[test]
    fn sctlr_bitmap_excludes_optional_bits() {
        // AK5-C: verify we do NOT set optional bits that would change
        // functional behavior unintentionally.
        let sctlr = compute_sctlr_el1_bitmap();
        // A (bit 1) — we intentionally leave alignment checks off to
        // avoid false faults on kernel unaligned byte sequences.
        assert_eq!(sctlr & (1 << 1), 0, "A unexpectedly set");
        // EE (bit 25) — must be 0 (little-endian).
        assert_eq!(sctlr & (1 << 25), 0, "EE (EL1 big-endian) unexpectedly set");
        // E0E (bit 24) — must be 0 (EL0 little-endian).
        assert_eq!(
            sctlr & (1 << 24),
            0,
            "E0E (EL0 big-endian) unexpectedly set"
        );
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn sctlr_bitmap_is_const_computable() {
        // `compute_sctlr_el1_bitmap` is `const fn` — usable in a
        // compile-time assertion.  Clippy flags `assert!(SCTLR != 0)`
        // as a constant assertion (`assertions_on_constants`); we keep
        // the runtime assert so the property is observable in the
        // test report.  The local `#[allow]` suppresses the lint at
        // the test function level.
        const SCTLR: u64 = compute_sctlr_el1_bitmap();
        assert!(SCTLR != 0);
    }

    // =====================================================================
    // AK5-E: PageTableCell tests
    // =====================================================================

    #[test]
    fn boot_table_extent_is_the_six_translation_tables() {
        // **WS-RR RR7.1**: one L0 + one L1 + four L2 tables, each 512 entries
        // × 8 bytes = 4096 bytes.  `enable_mmu` cleans exactly this extent to
        // the Point of Coherency before the walker is switched on, so an
        // extent that under-reports the tables would leave a table dirty in
        // the D-cache while the walker reads memory.
        assert_eq!(PageTableCell::size(), (2 + REFINED_GIB_COUNT) * 4096);
        assert_eq!(PageTableCell::size(), 24576);
    }

    #[test]
    fn page_table_cell_pa_matches_inner() {
        // The PA returned by `pa()` must equal the raw pointer of the
        // underlying BootPageTables.
        let pa = BOOT_TABLES.pa();
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

    // =====================================================================
    // WS-SM SM1.C.1 — Per-core MMU helper tests
    // =====================================================================

    #[test]
    fn init_mmu_per_core_callable_on_host() {
        // SM1.C.1: host stub of `init_mmu_per_core` is a no-op chain
        // through the MMIO/register write helpers (each of which is a
        // no-op on non-aarch64).  This test exercises the call graph
        // so a regression that adds a panic on the host path surfaces
        // here.  `core_id = 0` is the boot-core slot.
        init_mmu_per_core(0);
    }

    #[test]
    fn init_mmu_per_core_accepts_secondary_core_ids() {
        // SM1.C.1: every plausible secondary core_id (1..=3 on RPi5)
        // must be callable.  This catches a regression where someone
        // adds a precondition `core_id < MAX_SECONDARY_CORES` to the
        // per-core helper itself (only `init_mmu_secondary` should
        // gate on `core_id > 0`).
        for core_id in [1u64, 2, 3] {
            init_mmu_per_core(core_id);
        }
    }

    #[test]
    fn init_mmu_secondary_callable_with_secondary_core_id() {
        // SM1.C.1: `init_mmu_secondary` is the production entry point
        // for secondary-core MMU enable.  Verify host invocation
        // succeeds for every secondary core_id.
        for core_id in [1u64, 2, 3] {
            init_mmu_secondary(core_id);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "init_mmu_secondary called with core_id 0")]
    fn init_mmu_secondary_panics_on_boot_core_id() {
        // SM1.C.1: passing `core_id = 0` to `init_mmu_secondary` is a
        // misuse (the boot core should call `init_mmu`).  The debug
        // assertion catches this regression.  Release builds skip the
        // assert so this test is gated on `debug_assertions`.
        init_mmu_secondary(0);
    }

    #[test]
    fn init_mmu_signature_takes_the_dtb_pointer() {
        // SM1.C.1 / **WS-RR RR7.1**: the primary `init_mmu` takes the device
        // tree pointer `rust_boot_main` receives in `x0`, because the identity
        // map is sized to the board's `/memory` node.  Pinned at the
        // type-system level so a refactor that drops the argument — and with
        // it every board larger than the linker's declared RAM extent — fails
        // to compile rather than silently under-mapping.
        let _: fn(u64) = init_mmu;
    }

    #[test]
    fn init_mmu_per_core_signature_takes_u64() {
        // SM1.C.1: the helper takes a u64 core_id (PSCI context_id
        // convention).  A future refactor to `usize` would break the
        // asm-side caller (`x0` from PSCI is u64), so we pin the
        // signature at the type-system level.
        let _: fn(u64) = init_mmu_per_core;
    }

    #[test]
    fn init_mmu_secondary_signature_takes_u64() {
        // SM1.C.1: same as above for the secondary entry point.
        let _: fn(u64) = init_mmu_secondary;
    }
}

// ===========================================================================
// WS-RR RR7.1: boot-memory-map and translation-table witnesses
//
// Every case here mutates the *relation* the check is about rather than
// deleting a token: the level-0 witness walks a descriptor rather than reading
// its bits, the RAM-typing witness keeps `0xC000_0000` mapped and asks what it
// is mapped *as*, and the agreement witness compares the tables against the
// predicate address by address rather than checking that both exist.
// ===========================================================================

#[cfg(test)]
mod boot_map_tests {
    use super::*;

    /// A 4 GiB board: RAM fills the low aperture and nothing sits above 4 GiB.
    const FOUR_GIB_RAM_TOP: u64 = LOW_RAM_TOP;
    /// An 8 GiB board: the low aperture plus 4 GiB at `HIGH_RAM_BASE`.
    const EIGHT_GIB_RAM_TOP: u64 = 0x2_0000_0000;

    /// Translate `va` the way the PE's table walker would, starting at level 0
    /// with a 4 KiB granule and `TCR_EL1.T0SZ = 16`.
    ///
    /// This is the witness for the level-0 defect: it follows descriptor
    /// *types* rather than reading values out of a chosen array, so a table of
    /// level-1 block descriptors installed under TTBR0 resolves to `None` here
    /// exactly as it faults on hardware.
    fn walk(tables: &BootPageTables, base_pa: u64, va: u64) -> Option<(u64, u64)> {
        // Level 0 — Table descriptors only (4 KiB granule, ARM ARM D8.3).
        let l0_index = ((va >> 39) & 0x1FF) as usize;
        let l0 = tables.l0[l0_index];
        if l0 & 0b11 != DESC_TABLE {
            return None;
        }
        let l1_pa = l0 & DESC_ADDR_MASK;
        if l1_pa != base_pa + 4096 {
            return None;
        }

        // Level 1 — Block (1 GiB) or Table.
        let l1_index = ((va >> 30) & 0x1FF) as usize;
        let l1 = tables.l1[l1_index];
        match l1 & 0b11 {
            0b01 => {
                let output = (l1 & DESC_ADDR_MASK) | (va & (L1_BLOCK_SIZE - 1));
                return Some((output, l1 & !DESC_ADDR_MASK));
            }
            0b11 => {}
            _ => return None,
        }
        let l2_pa = l1 & DESC_ADDR_MASK;
        let g = ((l2_pa - base_pa) / 4096) as usize - 2;
        if g >= REFINED_GIB_COUNT {
            return None;
        }

        // Level 2 — Block (2 MiB) or Table; the boot tables stop here.
        let l2_index = ((va >> 21) & 0x1FF) as usize;
        let l2 = tables.l2_low[g][l2_index];
        if l2 & 0b11 != 0b01 {
            return None;
        }
        let output = (l2 & DESC_ADDR_MASK) | (va & (L2_BLOCK_SIZE - 1));
        Some((output, l2 & !DESC_ADDR_MASK))
    }

    /// Build a table set at a synthetic (4 KiB-aligned) physical base.
    fn build(ram_top: u64) -> (BootPageTables, u64) {
        let base_pa: u64 = 0x0008_0000;
        let mut tables = BootPageTables::new();
        populate_boot_tables(&mut tables, base_pa, clamp_ram_top(ram_top));
        (tables, base_pa)
    }

    #[test]
    fn the_boot_map_boundaries_mirror_the_lean_memory_map() {
        // `rpi5MemoryMapForConfig` in `SeLe4n/Platform/RPi5/Board.lean`:
        // RAM to 0xFC00_0000, a 32 MiB reserved firmware carve-out, the
        // peripheral window from 0xFE00_0000, and high RAM at 0x1_0000_0000.
        assert_eq!(LOW_RAM_TOP, 0xFC00_0000);
        assert_eq!(DEVICE_WINDOW_BASE, 0xFE00_0000);
        assert_eq!(HIGH_RAM_BASE, 0x1_0000_0000);
        // The Lean map's device extent ends at 0xFF85_0000; the boot tables
        // describe the fourth GiB at 2 MiB granularity, so the window rounds
        // up to the next block boundary and the reserved tail above it is
        // left unmapped.
        assert_eq!(DEVICE_WINDOW_TOP, 0xFFA0_0000);
        const LEAN_DEVICE_EXTENT_TOP: u64 = 0xFF85_0000;
        const { assert!(LEAN_DEVICE_EXTENT_TOP <= DEVICE_WINDOW_TOP) };
        const { assert!(DEVICE_WINDOW_TOP - LEAN_DEVICE_EXTENT_TOP < L2_BLOCK_SIZE) };
    }

    #[test]
    fn the_level_zero_table_is_reached_by_a_table_descriptor() {
        // The pre-RR7.1 defect, stated as a walk: TTBR0 pointed at a table of
        // 1 GiB *block* descriptors while `T0SZ = 16` makes level 0 the
        // initial lookup level, where a block descriptor is reserved.  A walk
        // that follows descriptor types resolves the kernel's own load address
        // only if the level-0 entry is a Table descriptor.
        let (tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        assert_eq!(tables.l0[0] & 0b11, DESC_TABLE);
        assert_eq!(tables.l0[0] & DESC_ADDR_MASK, base_pa + 4096);
        // The kernel is loaded at 0x80000 by `link.ld`.
        let (pa, attrs) = walk(&tables, base_pa, 0x8_0000).expect("kernel load address must map");
        assert_eq!(pa, 0x8_0000);
        assert_eq!(
            attrs & (ATTR_IDX_DEVICE | PXN),
            0,
            "kernel text must be Normal"
        );
    }

    #[test]
    fn a_block_descriptor_at_level_zero_does_not_resolve() {
        // The mutation that keeps the token and breaks the relation: leave the
        // level-0 entry present and valid, but spell it the way the pre-RR7.1
        // builder did — a 1 GiB block.  The walk must refuse it, which is what
        // makes the witness above decisive rather than tautological.
        let (mut tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        tables.l0[0] = BLOCK_NORMAL; // physical base 0, block descriptor
        assert_ne!(tables.l0[0] & DESC_VALID, 0, "the entry is still valid");
        assert!(walk(&tables, base_pa, 0x8_0000).is_none());
    }

    #[test]
    fn every_level_zero_entry_above_the_first_is_invalid() {
        let (tables, _) = build(EIGHT_GIB_RAM_TOP);
        for (i, &entry) in tables.l0.iter().enumerate().skip(1) {
            assert_eq!(entry, 0, "L0 entry {i} must be invalid");
        }
    }

    #[test]
    fn linker_declared_ram_above_three_gibibytes_is_normal_not_device() {
        // WS-RR RR7.1's finding: `link.ld` declares RAM to 0xFC00_0000 while
        // the boot table typed 0xC000_0000–0xFFFF_FFFF as one Device block, so
        // 960 MiB of linker-declared RAM had no cacheability, no unaligned
        // access and no speculation.  Sample the span the old table got wrong.
        let (tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        for va in [0xC000_0000u64, 0xE000_0000, 0xFBE0_0000, LOW_RAM_TOP - 1] {
            let (pa, attrs) =
                walk(&tables, base_pa, va).unwrap_or_else(|| panic!("{va:#x} must be mapped"));
            assert_eq!(pa, va, "the boot map is an identity map");
            assert_eq!(
                attrs & ATTR_IDX_DEVICE,
                0,
                "{va:#x} is linker-declared RAM and must not be Device"
            );
            assert_ne!(attrs & SH_INNER, 0, "RAM must be Inner Shareable");
        }
    }

    #[test]
    fn the_firmware_carveout_and_the_reserved_tail_are_unmapped() {
        let (tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        for va in [LOW_RAM_TOP, 0xFD00_0000, DEVICE_WINDOW_BASE - 1] {
            assert!(walk(&tables, base_pa, va).is_none(), "{va:#x} must fault");
        }
        for va in [DEVICE_WINDOW_TOP, 0xFFF0_0000, 0xFFFF_FFFF] {
            assert!(walk(&tables, base_pa, va).is_none(), "{va:#x} must fault");
        }
    }

    #[test]
    fn the_device_window_covers_the_uart_and_both_gic_frames() {
        // `SeLe4n/Platform/RPi5/Board.lean`'s `mmioRegions`, and `gic.rs`'s
        // GICD_BASE / GICC_BASE.
        let (tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        for va in [0xFE20_1000u64, 0xFF84_1000, 0xFF84_2000] {
            let (pa, attrs) =
                walk(&tables, base_pa, va).unwrap_or_else(|| panic!("{va:#x} must be mapped"));
            assert_eq!(pa, va);
            assert_ne!(attrs & ATTR_IDX_DEVICE, 0, "{va:#x} must be Device");
            assert_ne!(attrs & PXN, 0, "MMIO must be privileged-execute-never");
            assert_ne!(attrs & UXN, 0, "MMIO must be unprivileged-execute-never");
            assert_eq!(attrs & SH_INNER, 0, "Device-nGnRnE carries no shareability");
        }
    }

    #[test]
    fn high_ram_is_mapped_on_an_eight_gibibyte_board() {
        let (tables, base_pa) = build(EIGHT_GIB_RAM_TOP);
        for va in [HIGH_RAM_BASE, 0x1_8000_0000, EIGHT_GIB_RAM_TOP - 1] {
            let (pa, attrs) =
                walk(&tables, base_pa, va).unwrap_or_else(|| panic!("{va:#x} must be mapped"));
            assert_eq!(pa, va);
            assert_eq!(attrs & ATTR_IDX_DEVICE, 0);
        }
    }

    #[test]
    fn high_ram_is_not_mapped_on_a_four_gibibyte_board() {
        // Normal memory is speculatively accessible, so mapping DRAM a board
        // does not have is not a harmless over-approximation.
        let (tables, base_pa) = build(FOUR_GIB_RAM_TOP);
        for va in [HIGH_RAM_BASE, 0x1_8000_0000] {
            assert!(walk(&tables, base_pa, va).is_none(), "{va:#x} must fault");
        }
    }

    #[test]
    fn absent_dram_below_the_low_ram_top_is_unmapped() {
        // A board whose `/memory` node stops at 960 MiB.
        let (tables, base_pa) = build(0x3C00_0000);
        assert!(walk(&tables, base_pa, 0x3BFF_FFFF).is_some());
        for va in [0x3C00_0000u64, 0x8000_0000, 0xF000_0000] {
            assert!(walk(&tables, base_pa, va).is_none(), "{va:#x} must fault");
        }
    }

    #[test]
    fn clamp_ram_top_rounds_down_to_the_block_that_describes_it() {
        // Below 4 GiB the tables use 2 MiB blocks; above it, 1 GiB blocks.
        assert_eq!(clamp_ram_top(0x3C00_0000), 0x3C00_0000);
        assert_eq!(clamp_ram_top(0x3C00_1000), 0x3C00_0000);
        assert_eq!(clamp_ram_top(LOW_RAM_TOP), LOW_RAM_TOP);
        assert_eq!(clamp_ram_top(0x2_0000_0000), 0x2_0000_0000);
        assert_eq!(clamp_ram_top(0x2_0020_0000), 0x2_0000_0000);
        // Rounding is down, never up: mapping a partial block of DRAM the
        // board does not have is the failure this clamp exists to prevent.
        assert!(clamp_ram_top(0x2_0020_0000) < 0x2_0020_0000);
    }

    #[test]
    fn every_descriptor_agrees_with_the_boot_mapping_predicate() {
        // The tables and the cacheable-window predicate must be two readings
        // of one declaration.  Walk every descriptor the builder produced and
        // compare it against `boot_mapping_for` at the block's base.
        for &raw_top in &[
            FOUR_GIB_RAM_TOP,
            EIGHT_GIB_RAM_TOP,
            0x3C00_0000,
            0x4_0000_0000,
        ] {
            let ram_top = clamp_ram_top(raw_top);
            let (tables, base_pa) = build(raw_top);
            for g in 0..TABLE_ENTRIES {
                if g < REFINED_GIB_COUNT {
                    assert_eq!(tables.l1[g] & 0b11, DESC_TABLE);
                    continue;
                }
                let base = (g as u64) * L1_BLOCK_SIZE;
                match boot_mapping_for(base, ram_top) {
                    BootMapping::NormalRam => {
                        assert_eq!(tables.l1[g], base | BLOCK_NORMAL, "L1[{g}]");
                        // A 1 GiB block is only sound if the whole gigabyte
                        // has the same kind.
                        assert_eq!(
                            boot_mapping_for(base + L1_BLOCK_SIZE - 1, ram_top),
                            BootMapping::NormalRam
                        );
                    }
                    _ => assert_eq!(tables.l1[g], 0, "L1[{g}]"),
                }
            }
            for g in 0..REFINED_GIB_COUNT {
                for i in 0..TABLE_ENTRIES {
                    let base = (g as u64) * L1_BLOCK_SIZE + (i as u64) * L2_BLOCK_SIZE;
                    let expected = match boot_mapping_for(base, ram_top) {
                        BootMapping::NormalRam => base | BLOCK_NORMAL,
                        BootMapping::Device => base | BLOCK_DEVICE,
                        BootMapping::Unmapped => 0,
                    };
                    assert_eq!(tables.l2_low[g][i], expected, "L2[{g}][{i}]");
                    // And the whole block is homogeneous, so the descriptor
                    // does not over- or under-map any byte of it.
                    assert_eq!(
                        boot_mapping_for(base + L2_BLOCK_SIZE - 1, ram_top),
                        boot_mapping_for(base, ram_top),
                        "L2[{g}][{i}] block is not homogeneous"
                    );
                }
            }
            let _ = base_pa;
        }
    }

    #[test]
    fn boot_cacheable_range_agrees_with_pointwise_mapping() {
        // `is_boot_cacheable_range` decides containment from the two Normal
        // intervals directly; pin it against the pointwise reading it stands
        // for, at every block boundary of the map and around each edge.
        let ram_top = clamp_ram_top(EIGHT_GIB_RAM_TOP);
        let probes: [u64; 12] = [
            0u64,
            0x8_0000,
            LOW_RAM_TOP - L2_BLOCK_SIZE,
            LOW_RAM_TOP - 1,
            LOW_RAM_TOP,
            DEVICE_WINDOW_BASE,
            DEVICE_WINDOW_TOP,
            HIGH_RAM_BASE - L2_BLOCK_SIZE,
            HIGH_RAM_BASE,
            ram_top - L2_BLOCK_SIZE,
            ram_top - 1,
            ram_top,
        ];
        for &base in &probes {
            for size in [1u64, 0x1000, L2_BLOCK_SIZE, L1_BLOCK_SIZE] {
                let expected = (0..size)
                    .step_by(0x1000)
                    .chain(core::iter::once(size - 1))
                    .all(|d: u64| {
                        base.checked_add(d)
                            .is_some_and(|a| boot_mapping_for(a, ram_top) == BootMapping::NormalRam)
                    });
                assert_eq!(
                    boot_cacheable_range_in(base, size, ram_top),
                    expected,
                    "range {base:#x}+{size:#x}"
                );
            }
        }
        // An empty range is vacuously contained; an overflowing one is refused.
        assert!(boot_cacheable_range_in(0x8_0000, 0, ram_top));
        assert!(!boot_cacheable_range_in(u64::MAX - 3, 16, ram_top));
    }

    #[test]
    fn a_range_that_runs_off_the_end_of_ram_is_refused() {
        // The relation a per-address check would miss: the first byte is
        // cacheable and the range is not.
        let ram_top = clamp_ram_top(FOUR_GIB_RAM_TOP);
        assert_eq!(
            boot_mapping_for(LOW_RAM_TOP - 0x1000, ram_top),
            BootMapping::NormalRam
        );
        assert!(boot_cacheable_range_in(
            LOW_RAM_TOP - 0x1000,
            0x1000,
            ram_top
        ));
        assert!(!boot_cacheable_range_in(
            LOW_RAM_TOP - 0x1000,
            0x2000,
            ram_top
        ));
        // A range wholly inside the device window is not cacheable at all.
        assert!(!boot_cacheable_range_in(0xFE20_1000, 0x1000, ram_top));
    }

    #[test]
    fn tcr_epd1_disables_the_ttbr1_walk() {
        // No TTBR1 table exists, so the top half of the virtual address space
        // must fault rather than alias the TTBR0 identity map.
        assert_ne!(TCR_VALUE & (1 << 23), 0, "EPD1 must be set");
    }

    #[test]
    fn the_default_ram_top_is_the_linker_declared_extent() {
        // `link.ld`: `RAM : ORIGIN = 0x80000, LENGTH = 0xFBF80000`.
        assert_eq!(0x80000u64 + 0xFBF8_0000, LOW_RAM_TOP);
        assert_eq!(boot_ram_top(), LOW_RAM_TOP);
    }
}
