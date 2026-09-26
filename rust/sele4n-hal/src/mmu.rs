// SPDX-License-Identifier: GPL-3.0-or-later
//! MMU configuration for ARMv8-A on Raspberry Pi 5.
//!
//! Sets up MAIR_EL1, TCR_EL1, identity-mapped boot page tables, and enables
//! the MMU via SCTLR_EL1.  **WS-BP BP2.6**: the boot map is built from the
//! image's own layout and board constants — the RAM every Raspberry Pi 5 has,
//! the kernel's text read-only and executable, its data never executable, and
//! the device window — and nothing is parsed before translation is enabled.
//! The **runtime** kernel uses fine-grained 4 KiB page-level mappings via
//! `SeLe4n.Kernel.Architecture.PageTable` (AG6) and
//! `SeLe4n.Kernel.Architecture.VSpaceARMv8` (AG6-C/D), bridged to hardware
//! through the `VSpaceBackend` typeclass instance; the boot table and the
//! runtime page-table are deliberately distinct: the boot table covers what the
//! kernel stands on so it can run at all, and the runtime page-table is built on
//! top of it once the kernel scheduler is alive.
//!
//! Memory attribute configuration:
//! - Index 0 (0xFF): Normal, Inner/Outer WB-WA-RA (cacheable RAM)
//! - Index 1 (0x00): Device-nGnRnE (strongly ordered MMIO)
//! - Index 2 (0x44): Normal Non-cacheable (DMA buffers)
//!
//! References: ARM ARM D8 (The AArch64 Virtual Memory System Architecture)

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

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
/// AP[2:1] = 0b10 — Read-only at EL1, no EL0 access.
const AP_RO_EL1: u64 = 0b10 << 6;
/// UXN (bit 54) — Unprivileged Execute Never.
const UXN: u64 = 1 << 54;
/// PXN (bit 53) — Privileged Execute Never.
const PXN: u64 = 1 << 53;

/// The fields every Normal (cacheable RAM) descriptor carries: valid + AF +
/// Inner Shareable + Normal WB, and UXN, since nothing in the boot map is
/// user-executable.
const NORMAL_BASE: u64 = DESC_VALID | AF | SH_INNER | ATTR_IDX_NORMAL | UXN;

/// Block descriptor for writable Normal memory: data, `.bss`, stacks, the Lean
/// heap and every byte of RAM outside the image.  **PXN**, so no
/// writable page is executable at EL1.
///
/// **WS-BP BP2.6**: this was the only Normal descriptor, and it carried no
/// PXN, so the kernel's own text was mapped writable.  `SCTLR_EL1.WXN` (set by
/// [`compute_sctlr_el1_bitmap`]) makes every EL1-writable region execute-never
/// at EL1, so the first instruction fetched after `enable_mmu` would have taken
/// a permission fault.  No image has run past that instruction yet, which is
/// why it never showed.  The text now has a descriptor of its own
/// ([`BLOCK_KERNEL_TEXT`]); the PXN here states for data what WXN already
/// enforces, so the two cannot disagree.
const BLOCK_NORMAL: u64 = NORMAL_BASE | AP_RW_EL1 | PXN;

/// Block descriptor for the kernel's text: read-only, executable at EL1.
const BLOCK_KERNEL_TEXT: u64 = NORMAL_BASE | AP_RO_EL1;

/// Block descriptor for the kernel's read-only data: read-only, never
/// executable.
const BLOCK_KERNEL_RODATA: u64 = NORMAL_BASE | AP_RO_EL1 | PXN;

/// Block descriptor for Device memory: valid + block + AF + Device-nGnRnE +
/// RW EL1 + PXN + UXN (never execute from MMIO).
const BLOCK_DEVICE: u64 = DESC_VALID | AF | ATTR_IDX_DEVICE | AP_RW_EL1 | PXN | UXN;

/// **WS-BP BP0.4**: a level-3 descriptor is a *page* with `bits[1:0] = 0b11`
/// (ARM ARM D8.3); the attribute fields are the block descriptor's.
const DESC_PAGE: u64 = 0b10;

/// Bytes one L3 page descriptor maps (4 KiB).
const L3_PAGE_SIZE: u64 = 1 << 12;

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

/// The `TCR_EL1` value this kernel programs: 48-bit VA, 4 KiB granule, and the
/// intermediate physical address size `ips_encoding` — the executing PE's own,
/// decoded from `ID_AA64MMFR0_EL1.PARange` by [`physical_address_size_of`]
/// (the v0.36.2 audit; a constant 44-bit `IPS` stood here, see
/// [`CORTEX_A76_PA_RANGE_FIELD`]):
///
/// - T0SZ  = 16 (bits [5:0]):   48-bit VA for TTBR0 (64 - 48 = 16)
/// - T1SZ  = 16 (bits [21:16]): 48-bit VA for TTBR1
/// - TG0   = 0b00 (bits [15:14]): 4 KiB granule for TTBR0
/// - TG1   = 0b10 (bits [31:30]): 4 KiB granule for TTBR1
/// - IPS   = `ips_encoding` (bits [34:32]): the PE's implemented PA size,
///   `0b010` (40 bits) on the Cortex-A76
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
pub const fn tcr_el1_value(ips_encoding: u64) -> u64 {
    let t0sz: u64 = 16;
    let t1sz: u64 = 16 << 16;
    let tg0: u64 = 0b00 << 14; // 4 KiB
    let tg1: u64 = 0b10 << 30; // 4 KiB
    let ips: u64 = (ips_encoding & 0b111) << 32;
    let sh0: u64 = 0b11 << 12; // Inner Shareable
    let sh1: u64 = 0b11 << 28; // Inner Shareable
    let orgn0: u64 = 0b01 << 10;
    let irgn0: u64 = 0b01 << 8;
    let orgn1: u64 = 0b01 << 26;
    let irgn1: u64 = 0b01 << 24;
    let epd1: u64 = 1 << 23; // WS-RR RR7.1: no TTBR1 table exists yet
    t0sz | t1sz | tg0 | tg1 | ips | sh0 | sh1 | orgn0 | irgn0 | orgn1 | irgn1 | epd1
}

/// **The v0.36.2 audit**: what `ID_AA64MMFR0_EL1.PARange` — bits [3:0] of the
/// AArch64 Memory Model Feature Register 0 (ARM ARM D19.2.64; Cortex-A76 TRM
/// r4p1 §B2.58) — says this PE can address, and the `TCR_EL1.IPS` encoding the
/// boot tables are walked under for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysicalAddressSize {
    /// The implemented physical address size, in bits.
    pub bits: u32,
    /// The `IPS` encoding programmed for it: the PE's own size, capped at 48
    /// bits — the boot tables are ARMv8.0-format descriptors whose output
    /// address is bits [47:12], so a 52- or 56-bit PE (FEAT_LPA, FEAT_D128) is
    /// walked at 48, which is already every address the tables can name.
    pub ips: u64,
}

/// Decode `ID_AA64MMFR0_EL1.PARange`, bits [3:0].
///
/// | `PARange` | PA size | `IPS`   |
/// |-----------|---------|---------|
/// | `0b0000`  | 32 bits | `0b000` |
/// | `0b0001`  | 36 bits | `0b001` |
/// | `0b0010`  | 40 bits | `0b010` — the Cortex-A76, so every Raspberry Pi 5 |
/// | `0b0011`  | 42 bits | `0b011` |
/// | `0b0100`  | 44 bits | `0b100` |
/// | `0b0101`  | 48 bits | `0b101` |
/// | `0b0110`  | 52 bits | `0b101` (capped; see [`PhysicalAddressSize::ips`]) |
/// | `0b0111`  | 56 bits | `0b101` (capped) |
///
/// A reserved encoding answers `None`: a PE reporting a size this table does
/// not know is refused rather than rounded, since rounding down programs an
/// `IPS` below what the PE addresses (every output address above it then
/// faults) and rounding up programs a value the architecture reserves.
///
/// Split out as a `const fn` over the raw register value, as
/// [`crate::tlb::tlbios_implemented`] is, so the field position and the table
/// are pinned by host unit tests; only [`physical_address_size_of_this_pe_or_halt`]
/// needs the PE.  The parameter is named for what the register *is* rather
/// than spelled `id_aa64mmfr0_el1`, because `check_identifier_naming.py` reads
/// `aa64…` as a workstream family followed by a code; the architectural
/// spelling belongs in this docstring and in the `read_sysreg!` template.
#[inline(always)]
pub const fn physical_address_size_of(memory_model_features: u64) -> Option<PhysicalAddressSize> {
    let (bits, ips) = match memory_model_features & 0xF {
        0b0000 => (32, 0b000),
        0b0001 => (36, 0b001),
        0b0010 => (40, 0b010),
        0b0011 => (42, 0b011),
        0b0100 => (44, 0b100),
        0b0101 => (48, 0b101),
        0b0110 => (52, 0b101),
        0b0111 => (56, 0b101),
        _ => return None,
    };
    Some(PhysicalAddressSize { bits, ips })
}

/// `ID_AA64MMFR0_EL1.PARange` as the Cortex-A76 reports it — `0b0010`, a 40-bit
/// physical address space (Cortex-A76 TRM r4p1 §B2.58) — so what every
/// Raspberry Pi 5 PE reports, and what `Board.lean`'s
/// `rpi5MachineConfig.physicalAddressWidth` (40) is held to through the shared
/// boot-map fixture (`the_lean_physical_address_width_is_the_pe_the_hal_programs_for`).
///
/// Until the v0.36.2 audit this module programmed a constant 44-bit `IPS`
/// under a comment claiming that matched the BCM2712, and the Lean model
/// bounded every physical address by the same 44: no Cortex-A76 implements
/// 44 bits, so the model admitted mappings in `[2^40, 2^44)` that the PE
/// answers with an Address size fault.  An `IPS` wider than the implemented
/// size is treated as the implemented size, which is why nothing broke — and
/// why the wrong number could survive under every test.
pub const CORTEX_A76_PA_RANGE_FIELD: u64 = 0b0010;

/// The physical address size of the PE this kernel is built for.
pub const CORTEX_A76_PHYSICAL_ADDRESS_SIZE: PhysicalAddressSize =
    match physical_address_size_of(CORTEX_A76_PA_RANGE_FIELD) {
        Some(size) => size,
        None => panic!("the Cortex-A76's PARange is a defined encoding"),
    };

/// How many bits of physical address a PE must implement to produce every
/// translation the boot tables can describe: [`BOOT_TABLE_REACH`] is the span of
/// the one level-0 entry they populate, so a PE narrower than this could be
/// handed an output address it cannot form.  Thirty-nine bits, which every
/// defined `PARange` encoding from 40 up satisfies and 36 does not.
pub const BOOT_TABLE_PA_BITS_REQUIRED: u32 = 64 - (BOOT_TABLE_REACH - 1).leading_zeros();

// The PE this kernel is built for forms every address the tables can describe,
// and the device window — the highest address the boot ever maps — is within
// that reach.  Compile-time, so the relation holds in every build rather than
// in the host tests alone.
const _: () = assert!(CORTEX_A76_PHYSICAL_ADDRESS_SIZE.bits >= BOOT_TABLE_PA_BITS_REQUIRED);
const _: () = assert!(DEVICE_WINDOW_TOP <= BOOT_TABLE_REACH);

/// The physical address size of the executing PE, or a halt.
///
/// Refuses, through `halt`, a PE whose `PARange` is a reserved encoding or
/// narrower than [`BOOT_TABLE_PA_BITS_REQUIRED`]: either is a PE the boot
/// tables would ask for translations it cannot form.  `halt` is the caller's,
/// as [`crate::cache::verify_cache_line_stride_or_halt`]'s is: the primary
/// runs this before any secondary exists and a secondary parks itself, so
/// both hand it [`crate::cpu::fatal_halt`] and the reason lives at the call.
/// On the host there is no register to read, so the answer is the PE this
/// kernel is built for ([`CORTEX_A76_PHYSICAL_ADDRESS_SIZE`]), which is what
/// makes the host lane exercise the translation-control value the hardware
/// programs rather than a stand-in.
pub fn physical_address_size_of_this_pe_or_halt(halt: fn() -> !) -> PhysicalAddressSize {
    #[cfg(target_arch = "aarch64")]
    {
        let features = crate::read_sysreg!("id_aa64mmfr0_el1");
        let Some(size) = physical_address_size_of(features) else {
            crate::kprintln!(
                "[mmu] FATAL: ID_AA64MMFR0_EL1 = {features:#x}: PARange {:#06b} is a reserved \
                 encoding; refusing to enable translation",
                features & 0xF
            );
            halt();
        };
        if size.bits < BOOT_TABLE_PA_BITS_REQUIRED {
            crate::kprintln!(
                "[mmu] FATAL: this PE implements a {}-bit physical address space and the boot \
                 tables describe {} bits; refusing to enable translation",
                size.bits,
                BOOT_TABLE_PA_BITS_REQUIRED
            );
            halt();
        }
        size
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = halt;
        CORTEX_A76_PHYSICAL_ADDRESS_SIZE
    }
}

/// The translation-control value at the Cortex-A76's size, for the host tests
/// that pin every other field of [`tcr_el1_value`]; [`enable_mmu`] programs the
/// value at the executing PE's own size.
#[cfg(test)]
const TCR_VALUE: u64 = tcr_el1_value(CORTEX_A76_PHYSICAL_ADDRESS_SIZE.ips);

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
// WS-BP BP2.6: the boot memory map, built from constants
// ---------------------------------------------------------------------------
//
// The boot translation tables, the cacheable-window predicate the
// cache-maintenance FFI fails closed on ([`is_boot_cacheable_range`]) and the
// host tests all read the map from [`boot_mapping_for`] — one declaration, every
// consumer (WS-RR RR7.1's discipline).
//
// **The map is a function of the image and the board, never of the device
// tree.**  Until BP2.6 `init_mmu` walked the firmware's device tree for a RAM
// size *before* translation was enabled — an attacker-influenced parser running
// with no memory protection and no recovery but a halt — to size a map that
// needs no size.  What the boot stands on is the image, its stacks, the Lean
// heap arena, the device tree's own bytes and the device window, and every one
// of those is a linker symbol or a board constant.  So the map is:
//
//   * `[0, KERNEL_RESERVED_END)`: Normal RAM — the kernel's reserved extent,
//     which holds everything the boot stands on and which every board the
//     deployment admits reports as RAM.  Inside it the image's text is
//     read-only and executable, its read-only data read-only, and everything
//     else — data, `.bss`, both stack regions, the Lean heap and the
//     device-tree window — writable and never executable.
//   * `[DEVICE_WINDOW_BASE, DEVICE_WINDOW_TOP)`: Device.
//   * everything else: unmapped.
//
// **WS-BP BP7.10**: the constant Normal window was `[0, GUARANTEED_RAM_TOP)`,
// the first gigabyte, on the reading that every Raspberry Pi 5 has it.  None
// does: the firmware keeps the top few MiB of the first gigabyte for itself
// (`[0x80000, 0x3FC00000)` is RAM on a Pi 5 8 GiB Rev 1.1), so the boot map
// described VideoCore memory as the kernel's own writable RAM, and the
// cacheable window let the cache FFI maintain it.  The constant is retired;
// nothing past the kernel's extent is mapped before the verified parse.
//
// **WS-BP BP4.6, BP7.10**: every other byte of RAM — the part of the first
// gigabyte the firmware reported, and everything above it — is mapped once the
// verified Lean parser has read the device tree with translation on.  Lean
// derives the RAM the bound configuration declares outside the kernel's extent
// (`bootRamExtensionsOf`) and hands each region to [`extend_boot_ram_map`], which
// adds descriptors only to entries these tables leave invalid and widens
// [`is_boot_cacheable_range`] by the same record.  The boot map stays a
// function of the image and the board; the board is decided by the verified
// parser rather than before translation is on.
//
// The map is checked against `rpi5MemoryMapForConfig` in
// `SeLe4n/Platform/RPi5/Board.lean` by driving, not mirroring (WS-BP BP0.4):
// `the_boot_map_agrees_with_the_lean_map` requires every address the constant
// map maps Normal to be RAM in **every** configuration the Lean table carries,
// and with each configuration's `extend` lines applied, the extended Normal
// window to be exactly **that** configuration's RAM — the firmware's withheld
// top of the first gigabyte unmapped.  `scripts/check_physical_address_width.sh`
// holds `link.ld`'s RAM region to [`KERNEL_RESERVED_END`], so the linker cannot
// place any part of the image outside the constant map.

/* **Tombstone (WS-BP BP7.10)**: `GUARANTEED_RAM_TOP` (`0x4000_0000`, "one past
 * the RAM every Raspberry Pi 5 has") is retired: no RAM beyond the kernel's
 * reserved extent is guaranteed.  The constant Normal window ends at
 * [`KERNEL_RESERVED_END`]; the first gigabyte's top survives on the Lean side
 * (`rpi5FirstGigabyteTop`) as the upper bound on the firmware's report. */

/// **WS-BP BP3.2**: the end of the kernel's reserved extent
/// `[0, KERNEL_RESERVED_END)` — the firmware's stub below `_start`, the image,
/// both stack regions, the Lean heap arena, and the window the firmware
/// places the device tree in.
///
/// The boot refuses an untyped that overlaps it (the Lean side's
/// `Platform.Boot.untypedPlacementRespected`, over
/// `MachineConfig.kernelReserved`), so nothing here is ever handed to a
/// thread.  **WS-BP BP7.10**: it is also the whole of the RAM the boot map
/// describes before the verified parse — the image, its stacks, the Lean heap
/// and the device-tree window all lie inside it (`link.ld`'s `ASSERT`s), and
/// the deployment refuses a board whose firmware does not report it as RAM
/// (`rpi5LowRamTopFloor`).  Three artefacts state the number and are held to one another:
/// `link.ld`'s `KERNEL_RESERVED_END`, whose `ASSERT` refuses an image that
/// outgrows it; the Lean `rpi5KernelReservedEnd`, which
/// `tests/Ak9PlatformSuite.lean` writes into `tests/fixtures/boot_map.expected`;
/// and this constant, which
/// `tests::the_kernel_reserved_extent_is_the_lean_and_linker_one` compares with
/// both.  `scripts/check_link_script.py` reads the linked symbol against the
/// same fixture line.
pub const KERNEL_RESERVED_END: u64 = 0x1000_0000;

// The reserved extent is whole 2 MiB blocks inside the first gigabyte, whose
// level-2 table describes it — a fact about constants, so the compiler decides
// it rather than a test.  Whole blocks, because the RAM an extension adds past
// it starts on a block boundary (`extend_boot_tables`).
const _: () = assert!(
    KERNEL_RESERVED_END <= L1_BLOCK_SIZE && KERNEL_RESERVED_END.is_multiple_of(L2_BLOCK_SIZE)
);

/// Base of the device (peripheral) window: the BCM2712's SoC-bus window,
/// `bcm2712.dtsi`'s `soc` node `ranges = <0x7c000000 0x10 0x7c000000
/// 0x04000000>` — bus addresses `[0x7C00_0000, 0x8000_0000)` at CPU physical
/// `0x10_7C00_0000`.  UART10 (`0x10_7D00_1000`) and the GIC-400
/// (`0x10_7FFF_9000` / `0x10_7FFF_A000`) both lie inside it.
///
/// **The BCM2712 address-map correction (v0.36.2)**: this was `0xFE00_0000`,
/// the BCM2711's (Raspberry Pi 4's) legacy peripheral window, which on the
/// BCM2712 is DRAM — so the boot map mapped memory as Device and left the real
/// UART and interrupt controller unmapped, and the first console write or GIC
/// access would have gone to RAM.  Every address between the RAM the boot
/// maps and this one is **unmapped**.
pub const DEVICE_WINDOW_BASE: u64 = 0x10_7C00_0000;

/// One past the last byte of the device window — exactly the end of the
/// `.device` region `rpi5MemoryMapForConfig` declares, and the end of the
/// gigabyte the window sits in.
///
/// Both ends are on 2 MiB boundaries, so the window is described by 2 MiB
/// Device blocks alone.  (Until v0.36.2 the window ended at the BCM2711's
/// `0xFF85_0000`, not a block boundary, and a level-3 table described the one
/// straddling block; with nothing left to straddle that table is deleted
/// rather than kept describing nothing.)
pub const DEVICE_WINDOW_TOP: u64 = 0x10_8000_0000;

/// What the boot tables map an address as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BootMapping {
    /// The kernel's text: Normal, read-only, executable at EL1.
    KernelText,
    /// The kernel's read-only data: Normal, read-only, never executable.
    KernelReadOnly,
    /// Every other byte of RAM the map describes: Normal, writable, never
    /// executable.
    NormalRam,
    /// Device-nGnRnE, PXN|UXN — MMIO.
    Device,
    /// No descriptor: an access takes a Translation fault.
    Unmapped,
}

impl BootMapping {
    /// Is this Normal (cacheable RAM), whatever its permissions?  The Lean map
    /// has one kind of RAM; the boot map's three are its permissions.
    #[must_use]
    pub const fn is_normal(self) -> bool {
        matches!(
            self,
            BootMapping::KernelText | BootMapping::KernelReadOnly | BootMapping::NormalRam
        )
    }
}

/// **WS-BP BP2.6**: where the image's permission boundaries sit.
///
/// `[text_start, text_end)` is the kernel's code (`.text.boot`,
/// `.text.vectors`, `.text`) and `[text_end, rodata_end)` its read-only data.
/// On hardware the three are `link.ld`'s `_start`, `__text_end` and
/// `__rodata_end` ([`image_layout`]); the host tests pass their own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageLayout {
    /// First byte of the kernel's text: the load address.
    pub text_start: u64,
    /// One past the text, and the first byte of the read-only data.
    pub text_end: u64,
    /// One past the read-only data.
    pub rodata_end: u64,
}

impl ImageLayout {
    /// Can the boot tables describe this layout exactly?
    ///
    /// Every boundary is page aligned (a permission cannot change inside a
    /// 4 KiB page), the text is not empty, the two spans are ordered, and both
    /// lie inside the kernel's reserved extent.  `link.ld`'s `ASSERT`s make every linked image
    /// satisfy this; [`init_mmu`] still refuses one that does not, because a
    /// map built over a malformed layout would describe permissions the tables
    /// cannot express.
    #[must_use]
    pub const fn is_well_formed(&self) -> bool {
        self.text_start.is_multiple_of(L3_PAGE_SIZE)
            && self.text_end.is_multiple_of(L3_PAGE_SIZE)
            && self.rodata_end.is_multiple_of(L3_PAGE_SIZE)
            && self.text_start < self.text_end
            && self.text_end <= self.rodata_end
            && self.rodata_end <= KERNEL_RESERVED_END
    }

    /// The layout's three boundaries, in address order.  A boundary that falls
    /// strictly inside a 2 MiB block is what forces that block to page
    /// granularity.
    const fn boundaries(&self) -> [u64; IMAGE_BOUNDARY_COUNT] {
        [self.text_start, self.text_end, self.rodata_end]
    }
}

/// **WS-BP BP2.6**: what the boot tables map `addr` as, for an image laid out
/// as `layout`.
///
/// A function of the address and the image alone: no device tree, no RAM size,
/// no state.  The kernel's reserved extent is Normal, with the image's text and
/// read-only data carrying their own permissions; the device window is Device;
/// every other address is unmapped.
#[must_use]
pub const fn boot_mapping_for(addr: u64, layout: &ImageLayout) -> BootMapping {
    if addr < KERNEL_RESERVED_END {
        if layout.text_start <= addr && addr < layout.text_end {
            BootMapping::KernelText
        } else if layout.text_end <= addr && addr < layout.rodata_end {
            BootMapping::KernelReadOnly
        } else {
            BootMapping::NormalRam
        }
    } else if DEVICE_WINDOW_BASE <= addr && addr < DEVICE_WINDOW_TOP {
        BootMapping::Device
    } else {
        BootMapping::Unmapped
    }
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
/// under-maintenance a per-address check would miss.  **WS-BP BP2.6**: the
/// Normal window was one interval, whatever the image's permissions inside it
/// (cache maintenance by address needs read access, which every Normal page
/// grants); since **WS-BP BP7.10** that interval is `[0, KERNEL_RESERVED_END)`,
/// not the first gigabyte the firmware partly withholds.  **WS-BP BP4.6**: it is that
/// interval together with every extension [`extend_boot_ram_map`] has
/// recorded — the RAM of the variant the verified device-tree parse selected —
/// so the window and the tables are widened by one call and cannot disagree.
/// [`ram_range_covered`] is the pure form, pinned against a walk of extended
/// tables by `boot_map_tests`.  An empty range is vacuously contained; a range
/// whose end overflows `u64` is refused.
#[must_use]
pub fn is_boot_cacheable_range(base: u64, size: u64) -> bool {
    let recorded = RAM_EXTENSION_COUNT
        .load(Ordering::Acquire)
        .min(MAX_RAM_EXTENSIONS);
    let mut extensions = [(0u64, 0u64); MAX_RAM_EXTENSIONS];
    for (i, slot) in extensions.iter_mut().enumerate().take(recorded) {
        *slot = (
            RAM_EXTENSIONS[i].0.load(Ordering::Relaxed),
            RAM_EXTENSIONS[i].1.load(Ordering::Relaxed),
        );
    }
    ram_range_covered(base, size, &extensions[..recorded])
}

/// **WS-BP BP4.6**: is every byte of `[base, base + size)` inside the kernel's
/// reserved extent or one of `extensions` (each a `(base, end)` interval)?
///
/// The intervals may abut — the first extension begins where the reserved
/// extent ends (**WS-BP BP7.10**) — so containment is asked of their union: advance a cursor through
/// whichever interval holds it until the range is covered or no interval holds
/// the cursor.  Each step moves the cursor to an interval's end, strictly past
/// where it was, so the loop runs at most once per interval plus one.
#[must_use]
pub const fn ram_range_covered(base: u64, size: u64, extensions: &[(u64, u64)]) -> bool {
    if size == 0 {
        return true;
    }
    let end = match base.checked_add(size) {
        Some(end) => end,
        None => return false,
    };
    let mut cursor = base;
    let mut steps = 0;
    while steps <= extensions.len() {
        if cursor >= end {
            return true;
        }
        let mut next = None;
        if cursor < KERNEL_RESERVED_END {
            next = Some(KERNEL_RESERVED_END);
        }
        let mut i = 0;
        while i < extensions.len() {
            let (lo, hi) = extensions[i];
            if lo <= cursor && cursor < hi {
                next = Some(hi);
            }
            i += 1;
        }
        match next {
            Some(hi) => cursor = hi,
            None => return false,
        }
        steps += 1;
    }
    cursor >= end
}

// ---------------------------------------------------------------------------
// Boot page tables
// ---------------------------------------------------------------------------

/// Entries in one 4 KiB translation table (4096 / 8).
const TABLE_ENTRIES: usize = 512;

/// Bytes one L1 entry spans (1 GiB).
const L1_BLOCK_SIZE: u64 = 1 << 30;

/// Bytes one L2 block descriptor maps (2 MiB).
const L2_BLOCK_SIZE: u64 = 1 << 21;

/// How many image boundaries [`ImageLayout`] has, and so the most 2 MiB blocks
/// of the reserved extent that need page granularity: a block is uniform unless a
/// boundary falls strictly inside it.
const IMAGE_BOUNDARY_COUNT: usize = 3;

/// The L1 index of the gigabyte holding the device window.
const DEVICE_GIB: usize = (DEVICE_WINDOW_BASE / L1_BLOCK_SIZE) as usize;

/// Table descriptor type bits (`bits[1:0] = 0b11`, ARM ARM D8.3).
///
/// **WS-RR RR7.1**: the distinction from [`DESC_VALID`] is what the pre-RR7.1
/// boot table got wrong.  `TCR_EL1.T0SZ = 16` makes the input address 48 bits,
/// and with the 4 KiB granule that puts the **initial lookup level at 0**; a
/// level-0 descriptor with a 4 KiB granule may only be a Table descriptor
/// (level-0 blocks require FEAT_LPA2 with `TCR.DS = 1`, which the ARMv8.2-A
/// Cortex-A76 does not implement).
const DESC_TABLE: u64 = 0b11;

/// Address mask for a next-level table pointer or a block output address
/// (bits [47:12]).
const DESC_ADDR_MASK: u64 = 0x0000_FFFF_FFFF_F000;

/// Boot translation tables.
///
/// Laid out as one `#[repr(C, align(4096))]` struct so all eight tables are
/// contiguous and 4 KiB aligned (each array is exactly one 4 KiB page), which
/// lets [`enable_mmu`] clean the whole extent to the Point of Coherency in one
/// range operation.
///
/// - **L0** (entry 0 only): a Table descriptor to `l1`, covering VA
///   `[0, 512 GiB)`.  Every other L0 entry is invalid.
/// - **L1**: entry 0 reaches `l2_ram` and entry [`DEVICE_GIB`] reaches
///   `l2_device`; every other entry is invalid.
/// - **L2** (`l2_ram`): 2 MiB blocks describing the kernel's reserved extent,
///   except the blocks an image boundary falls inside, which are Table
///   descriptors to `l3_image`.  The rest of the first gigabyte is invalid
///   until [`extend_boot_ram_map`] maps the part the firmware reported as RAM
///   (**WS-BP BP7.10**).
/// - **L2** (`l2_device`): 2 MiB Device blocks over the device window.
/// - **L3**: 4 KiB pages for the straddled image blocks.
#[repr(C, align(4096))]
pub struct BootPageTables {
    l0: [u64; TABLE_ENTRIES],
    l1: [u64; TABLE_ENTRIES],
    l2_ram: [u64; TABLE_ENTRIES],
    l2_device: [u64; TABLE_ENTRIES],
    l3_image: [[u64; TABLE_ENTRIES]; IMAGE_BOUNDARY_COUNT],
}

impl BootPageTables {
    const fn new() -> Self {
        Self {
            l0: [0; TABLE_ENTRIES],
            l1: [0; TABLE_ENTRIES],
            l2_ram: [0; TABLE_ENTRIES],
            l2_device: [0; TABLE_ENTRIES],
            l3_image: [[0; TABLE_ENTRIES]; IMAGE_BOUNDARY_COUNT],
        }
    }
}

/// How many 4 KiB tables [`BootPageTables`] holds.
const BOOT_TABLE_COUNT: usize = 4 + IMAGE_BOUNDARY_COUNT;

/// Index of each table within [`BootPageTables`], in 4 KiB pages from its base.
const L1_TABLE: u64 = 1;
const L2_RAM_TABLE: u64 = 2;
const L2_DEVICE_TABLE: u64 = 3;
const L3_IMAGE_TABLE_BASE: u64 = 4;

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
// addresses; each table must be exactly one 4 KiB page so that every table in
// the struct sits at a 4 KiB-aligned offset — the alignment a Table
// descriptor's [47:12] address field assumes.
const _: () = assert!(
    TABLE_ENTRIES == 512,
    "TABLE_ENTRIES must be 512 (4 KiB / 8 bytes/entry) per ARMv8 D8.3"
);
const _: () = assert!(
    core::mem::size_of::<BootPageTables>() == BOOT_TABLE_COUNT * 4096,
    "BootPageTables must be a whole number of 4 KiB translation tables"
);
// The device window is described by one L2 table, in a gigabyte of its own.
const _: () = assert!(DEVICE_GIB != 0);
const _: () = assert!(DEVICE_WINDOW_BASE.is_multiple_of(L2_BLOCK_SIZE));
const _: () = assert!(DEVICE_WINDOW_TOP <= (DEVICE_GIB as u64 + 1) * L1_BLOCK_SIZE);
// The BCM2712 address-map correction: the window's top is the Lean extent and a
// 2 MiB boundary, so 2 MiB Device blocks describe it exactly and no block of
// the window mixes kinds.
const _: () = assert!(DEVICE_WINDOW_TOP.is_multiple_of(L2_BLOCK_SIZE));
const _: () = assert!(DEVICE_WINDOW_BASE < DEVICE_WINDOW_TOP);
const _: () = assert!(L2_BLOCK_SIZE == 1 << 21);

// ---------------------------------------------------------------------------
// WS-BP BP4.6, BP7.10 — the verified board's RAM outside the kernel's extent
// ---------------------------------------------------------------------------

/// **WS-BP BP4.6**: one past the last address the boot tables can describe —
/// the span of `l0[0]`, the only level-0 entry they populate (512 GiB; the
/// largest Raspberry Pi 5 has 16 GiB, and the Cortex-A76's 40-bit physical
/// address space forms every address in it — [`BOOT_TABLE_PA_BITS_REQUIRED`]
/// is the floor `enable_mmu` holds a PE to).
pub const BOOT_TABLE_REACH: u64 = 1 << 39;

/// **WS-BP BP4.6**: how many RAM extensions the boot map can record.  Every
/// Raspberry Pi 5 needs at most two (**WS-BP BP7.10**): the part of the first
/// gigabyte the firmware reports past the kernel's reserved extent, and — on
/// a board larger than a gigabyte — its DRAM above the first gigabyte, which
/// is contiguous on the BCM2712.  The slack is for a future variant, never a
/// reason to leave one unrecorded.
pub const MAX_RAM_EXTENSIONS: usize = 4;

/// **WS-BP BP4.6**: why [`extend_boot_tables`] or [`extend_boot_ram_map`]
/// refused an extension.  Every refusal is decided before any descriptor is
/// written, so a refused extension leaves the tables exactly as they were.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RamExtensionRefusal {
    /// `size` is zero: an extension that maps nothing is a caller's mistake.
    Empty,
    /// `base + size` overflows `u64`.
    Overflow,
    /// `base` or `base + size` is not on a 2 MiB boundary — the smallest block
    /// an extension writes.
    Unaligned,
    /// The range begins inside the kernel's reserved extent
    /// `[0, KERNEL_RESERVED_END)`, which the boot map already describes with
    /// the image's own permissions.  (**WS-BP BP7.10** — was
    /// `BelowGuaranteedRam`, over the retired first-gigabyte window.)
    InsideKernelReserved,
    /// The range ends past [`BOOT_TABLE_REACH`].
    BeyondTableReach,
    /// The range covers part of a gigabyte whose level-1 entry is invalid: the
    /// tables have no level-2 table for it, so only a whole gigabyte (one
    /// 1 GiB block) can be mapped there.  The first gigabyte and the device
    /// window's gigabyte have level-2 tables of their own and take 2 MiB
    /// blocks ([`level2_table`]).
    PartialGigabyte,
    /// A descriptor the range needs is already valid — the kernel's reserved
    /// extent, the device window, or an earlier extension.  Extending never rewrites a
    /// valid descriptor, which is what makes it safe without break-before-make
    /// and without a TLB invalidation: a translation that faults is never
    /// cached (ARM ARM D8.14).
    AlreadyMapped,
    /// [`MAX_RAM_EXTENSIONS`] are already recorded.
    RecordFull,
    /// The boot map was sealed ([`seal_boot_map`]): a secondary may already be
    /// walking these tables, and the tables are no longer single-writer.
    Sealed,
}

/// **WS-BP BP4.6**: the per-gigabyte step both passes of
/// [`extend_boot_tables`] walk — `(gigabyte index, lo, hi)` for the part of
/// `[base, end)` inside each gigabyte, in address order.
fn gigabytes_of(base: u64, end: u64) -> impl Iterator<Item = (usize, u64, u64)> {
    let first = base / L1_BLOCK_SIZE;
    let last = (end - 1) / L1_BLOCK_SIZE;
    (first..=last).map(move |g| {
        let gib = g * L1_BLOCK_SIZE;
        (g as usize, base.max(gib), end.min(gib + L1_BLOCK_SIZE))
    })
}

/// **WS-BP BP7.10**: the level-2 table the boot tables hold for gigabyte `g`,
/// if they hold one — `l2_ram` for the first gigabyte (the kernel's reserved
/// extent and whatever the firmware reports past it), `l2_device` for the
/// device window's.  Every other gigabyte has no level-2 table, so an
/// extension maps it only as one 1 GiB block.
///
/// One answer for both passes of [`extend_boot_tables`], so the pass that
/// decides and the pass that writes cannot pick different tables.
fn level2_table(tables: &mut BootPageTables, g: usize) -> Option<&mut [u64; TABLE_ENTRIES]> {
    if g == 0 {
        Some(&mut tables.l2_ram)
    } else if g == DEVICE_GIB {
        Some(&mut tables.l2_device)
    } else {
        None
    }
}

/// **WS-BP BP4.6**: extend `tables`' identity map over `[base, base + size)` as
/// Normal RAM — writable, never executable ([`BootMapping::NormalRam`]).
///
/// Pure over its arguments so the host suite drives it against the Lean map.
/// Two passes: every refusal ([`RamExtensionRefusal`]) is decided by the first,
/// so the second, which writes, cannot fail half way.  A whole gigabyte is one
/// level-1 block descriptor; a gigabyte with a level-2 table ([`level2_table`]:
/// the first, since **WS-BP BP7.10**, and the device window's) takes 2 MiB
/// block descriptors in its invalid entries.  Only entries the tables leave
/// **invalid** are written, never a valid one.
///
/// # Errors
///
/// The [`RamExtensionRefusal`] the range violates, with `tables` unchanged.
pub fn extend_boot_tables(
    tables: &mut BootPageTables,
    base: u64,
    size: u64,
) -> Result<(), RamExtensionRefusal> {
    if size == 0 {
        return Err(RamExtensionRefusal::Empty);
    }
    let end = base
        .checked_add(size)
        .ok_or(RamExtensionRefusal::Overflow)?;
    if !base.is_multiple_of(L2_BLOCK_SIZE) || !end.is_multiple_of(L2_BLOCK_SIZE) {
        return Err(RamExtensionRefusal::Unaligned);
    }
    if base < KERNEL_RESERVED_END {
        return Err(RamExtensionRefusal::InsideKernelReserved);
    }
    if end > BOOT_TABLE_REACH {
        return Err(RamExtensionRefusal::BeyondTableReach);
    }
    for (g, lo, hi) in gigabytes_of(base, end) {
        let gib = g as u64 * L1_BLOCK_SIZE;
        if let Some(l2) = level2_table(tables, g) {
            let mut block = lo;
            while block < hi {
                if l2[((block - gib) / L2_BLOCK_SIZE) as usize] != 0 {
                    return Err(RamExtensionRefusal::AlreadyMapped);
                }
                block += L2_BLOCK_SIZE;
            }
        } else {
            if tables.l1[g] != 0 {
                return Err(RamExtensionRefusal::AlreadyMapped);
            }
            if lo != gib || hi != gib + L1_BLOCK_SIZE {
                return Err(RamExtensionRefusal::PartialGigabyte);
            }
        }
    }
    for (g, lo, hi) in gigabytes_of(base, end) {
        let gib = g as u64 * L1_BLOCK_SIZE;
        if let Some(l2) = level2_table(tables, g) {
            let mut block = lo;
            while block < hi {
                l2[((block - gib) / L2_BLOCK_SIZE) as usize] =
                    block_descriptor(block, BootMapping::NormalRam);
                block += L2_BLOCK_SIZE;
            }
        } else {
            // A level-1 block descriptor has the level-2 block's format (ARM
            // ARM D8.3); only the output address's alignment differs.
            tables.l1[g] = block_descriptor(gib, BootMapping::NormalRam);
        }
    }
    Ok(())
}

/// **WS-BP BP4.6**: the extensions recorded so far, as `(base, end)`, and how
/// many are published.  The count is stored `Release` after both words of its
/// slot, and read `Acquire` by [`is_boot_cacheable_range`], so a reader never
/// sees a slot before its contents.  One writer: the boot core, before
/// [`seal_boot_map`].
static RAM_EXTENSIONS: [(AtomicU64, AtomicU64); MAX_RAM_EXTENSIONS] =
    [const { (AtomicU64::new(0), AtomicU64::new(0)) }; MAX_RAM_EXTENSIONS];
static RAM_EXTENSION_COUNT: AtomicUsize = AtomicUsize::new(0);

/// **WS-BP BP4.6**: set once, by the boot seam, before the permit that
/// releases a secondary exists (`lean_entry::enter_lean_kernel`).  After it
/// the boot tables are shared with every PE that enables translation, so they
/// are never written again.
static BOOT_MAP_SEALED: AtomicBool = AtomicBool::new(false);

/// **WS-BP BP4.6**: seal the boot map.  Called by the boot seam immediately
/// before it mints the `SecondaryReleasePermit`; every later
/// [`extend_boot_ram_map`] is refused with [`RamExtensionRefusal::Sealed`].
pub fn seal_boot_map() {
    BOOT_MAP_SEALED.store(true, Ordering::Release);
}

/// **WS-BP BP4.6**: extend the live boot map over `[base, base + size)` and
/// widen the cacheable window to match.
///
/// What the verified Lean boot calls, through `ffi_extend_boot_ram_map`, once
/// per RAM region of the variant the device tree selected
/// (`Platform.FFI.extendBootRamMap`).  The extension adds descriptors to entries
/// the tables leave invalid, so it needs no break-before-make and no TLB
/// invalidation.  The table extent is cleaned to the Point of Coherency — a
/// secondary enables translation with its data cache off — and one `DSB ISH`
/// makes the descriptors visible to the table walker (walks are
/// inner-shareable write-back cacheable, `TCR_EL1`'s `IRGN0`/`ORGN0`/`SH0`) and
/// one `ISB` to the instruction stream.  The record
/// is published after the barrier, so no caller can be told a range is
/// cacheable before a walk can resolve it.
///
/// # Errors
///
/// [`RamExtensionRefusal::Sealed`] after [`seal_boot_map`],
/// [`RamExtensionRefusal::RecordFull`] with the record full, and otherwise
/// [`extend_boot_tables`]'s refusal — each with nothing written.
pub fn extend_boot_ram_map(base: u64, size: u64) -> Result<(), RamExtensionRefusal> {
    if BOOT_MAP_SEALED.load(Ordering::Acquire) {
        return Err(RamExtensionRefusal::Sealed);
    }
    let recorded = RAM_EXTENSION_COUNT.load(Ordering::Relaxed);
    if recorded >= MAX_RAM_EXTENSIONS {
        return Err(RamExtensionRefusal::RecordFull);
    }
    // SAFETY: the boot map is not sealed, so no secondary has been released
    // and this runs on the boot core alone, inside the single-threaded boot
    // install; the only other reader of the tables is this PE's own walker,
    // and `extend_boot_tables` writes only descriptors that are invalid, which
    // no walk can have cached.
    unsafe { BOOT_TABLES.with_inner_mut(|tables| extend_boot_tables(tables, base, size)) }?;
    // SAFETY: `BOOT_TABLES` is the kernel's own `.bss`, identity-mapped Normal
    // RAM, and `PageTableCell::size()` is its whole extent.  Cleaning it to the
    // Point of Coherency is what `enable_mmu` does before its own enable: a
    // secondary enables translation with its data cache off, so the descriptors
    // just written with this PE's cache on must be in memory, not only in a
    // line this PE holds.  The call ends in `DSB ISH`, which also makes the
    // descriptors visible to this PE's own walker.
    unsafe { crate::cache::clean_pagetable_range(BOOT_TABLES.pa(), PageTableCell::size()) };
    barriers::dsb_ish();
    barriers::isb();
    RAM_EXTENSIONS[recorded].0.store(base, Ordering::Relaxed);
    RAM_EXTENSIONS[recorded]
        .1
        .store(base + size, Ordering::Relaxed);
    RAM_EXTENSION_COUNT.store(recorded + 1, Ordering::Release);
    Ok(())
}

/// Physical address of the table at index `table` of the struct at `base_pa`.
#[inline]
const fn table_pa(base_pa: u64, table: u64) -> u64 {
    base_pa + table * 4096
}

/// A Table descriptor pointing at the table at index `table`.
#[inline]
const fn table_descriptor(base_pa: u64, table: u64) -> u64 {
    (table_pa(base_pa, table) & DESC_ADDR_MASK) | DESC_TABLE
}

/// The block descriptor (L2, 2 MiB) mapping `base` as `kind`, or 0.
#[inline]
const fn block_descriptor(base: u64, kind: BootMapping) -> u64 {
    match kind {
        BootMapping::KernelText => base | BLOCK_KERNEL_TEXT,
        BootMapping::KernelReadOnly => base | BLOCK_KERNEL_RODATA,
        BootMapping::NormalRam => base | BLOCK_NORMAL,
        BootMapping::Device => base | BLOCK_DEVICE,
        BootMapping::Unmapped => 0,
    }
}

/// The page descriptor (L3, 4 KiB) mapping `page` as `kind`, or 0.  The
/// attributes are the block descriptor's; only the type bits differ.
#[inline]
const fn page_descriptor(page: u64, kind: BootMapping) -> u64 {
    match kind {
        BootMapping::Unmapped => 0,
        _ => block_descriptor(page, kind) | DESC_PAGE,
    }
}

/// **WS-BP BP2.6**: which `l3_image` table, if any, describes the 2 MiB block
/// at `base`.
///
/// A block needs page granularity exactly when an image boundary falls strictly
/// inside it; the tables are assigned in boundary order, one per distinct such
/// block, so at most [`IMAGE_BOUNDARY_COUNT`] are ever needed.
const fn image_l3_slot(layout: &ImageLayout, base: u64) -> Option<usize> {
    let boundaries = layout.boundaries();
    let mut slot = 0;
    let mut previous_block = u64::MAX;
    let mut i = 0;
    while i < IMAGE_BOUNDARY_COUNT {
        let b = boundaries[i];
        if !b.is_multiple_of(L2_BLOCK_SIZE) {
            let block = b & !(L2_BLOCK_SIZE - 1);
            if block != previous_block {
                if block == base {
                    return Some(slot);
                }
                slot += 1;
                previous_block = block;
            }
        }
        i += 1;
    }
    None
}

/// **WS-BP BP2.6**: populate the boot translation tables in place.
///
/// Pure over its arguments so the host test suite can assert every descriptor
/// without an MMU: `base_pa` is the physical address of the whole
/// [`BootPageTables`] extent and `layout` the image's permission boundaries.
///
/// Every descriptor is derived from [`boot_mapping_for`], so the tables and the
/// cacheable-window predicate cannot disagree about a single address.  A 2 MiB
/// block descriptor is used only where the whole block has one kind, which
/// holds everywhere except the blocks [`image_l3_slot`] names, each described
/// page by page.
fn populate_boot_tables(tables: &mut BootPageTables, base_pa: u64, layout: &ImageLayout) {
    // Level 0: one Table descriptor covering VA [0, 512 GiB).
    tables.l0 = [0; TABLE_ENTRIES];
    tables.l0[0] = table_descriptor(base_pa, L1_TABLE);

    // Level 1: the first gigabyte (the kernel's reserved extent, and room for
    // the RAM the firmware reports past it) and the device window; nothing
    // else.
    tables.l1 = [0; TABLE_ENTRIES];
    tables.l1[0] = table_descriptor(base_pa, L2_RAM_TABLE);
    tables.l1[DEVICE_GIB] = table_descriptor(base_pa, L2_DEVICE_TABLE);

    for (i, entry) in tables.l2_ram.iter_mut().enumerate() {
        let base = (i as u64) * L2_BLOCK_SIZE;
        *entry = match image_l3_slot(layout, base) {
            Some(slot) => table_descriptor(base_pa, L3_IMAGE_TABLE_BASE + slot as u64),
            None => block_descriptor(base, boot_mapping_for(base, layout)),
        };
        if let Some(slot) = image_l3_slot(layout, base) {
            for (k, page_entry) in tables.l3_image[slot].iter_mut().enumerate() {
                let page = base + (k as u64) * L3_PAGE_SIZE;
                *page_entry = page_descriptor(page, boot_mapping_for(page, layout));
            }
        }
    }

    let device_gib_base = (DEVICE_GIB as u64) * L1_BLOCK_SIZE;
    for (i, entry) in tables.l2_device.iter_mut().enumerate() {
        let base = device_gib_base + (i as u64) * L2_BLOCK_SIZE;
        *entry = block_descriptor(base, boot_mapping_for(base, layout));
    }
}

/// Build identity-mapped boot translation tables for `layout`.
///
/// The map is [`boot_mapping_for`]'s:
///
/// - `[0, text_start)`:              Normal RAM, writable, execute-never
/// - `[text_start, text_end)`:       kernel text, read-only, executable at EL1
/// - `[text_end, rodata_end)`:       kernel read-only data, execute-never
/// - `[rodata_end, KERNEL_RESERVED_END)`: Normal RAM, writable, execute-never
/// - `0x10_7C00_0000 – 0x10_7FFF_FFFF`: Device (the BCM2712 SoC-bus window:
///   UART10 + GIC-400)
/// - everything else:                unmapped
///
/// This is a boot mapping. AN8-D (RUST-M04): the runtime kernel uses
/// fine-grained 4 KiB page tables via
/// `SeLe4n.Kernel.Architecture.PageTable` + `VSpaceARMv8` (AG6); those tables
/// are built on top of this boot mapping once the scheduler is alive.
fn build_identity_tables(layout: &ImageLayout) {
    let base_pa = BOOT_TABLES.pa() as u64;
    // SAFETY: Boot context is single-threaded (core 0 only, per AK5-I), the
    // MMU has not been enabled yet, and interrupts are still masked by the
    // reset state. No concurrent access to BOOT_TABLES is possible.
    unsafe {
        BOOT_TABLES.with_inner_mut(|tables| {
            populate_boot_tables(tables, base_pa, layout);
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
    // Step 0 (the v0.36.2 audit): what this PE can address, read off its own
    // ID_AA64MMFR0_EL1.PARange, before any translation is programmed for it.
    // A reserved encoding, or a PE narrower than the tables' reach, halts here
    // — the primary before any secondary exists, a secondary parking itself.
    let pa = physical_address_size_of_this_pe_or_halt(crate::cpu::fatal_halt);

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
    // AK5-E.3: the table's PA must be one this PE can form — its own
    // physical address size (`pa.bits`, 40 on the Cortex-A76; the bound read
    // `44` until the v0.36.2 audit).  Only checked on aarch64 because on host
    // x86_64 the kernel-image base address is set by the host loader and
    // routinely exceeds 2^40 (e.g., 0x55... on a PIE binary), which would
    // false-fault the assert.  WS-SM SM1.C.1 exposed this in the per-core MMU
    // helper tests.
    #[cfg(target_arch = "aarch64")]
    debug_assert!(
        pt_pa_raw != 0 && (pt_pa_raw as u64) < (1u64 << pa.bits),
        "BOOT_TABLES PA outside this PE's physical address space"
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
    crate::registers::write_tcr_el1(tcr_el1_value(pa.ips));
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
/// **WS-BP BP2.6: nothing is parsed before translation is enabled.**  The map
/// is [`boot_mapping_for`]'s, a function of the image's layout and board
/// constants, so the device tree is not read here at all — only its *pointer*
/// is checked.  Two refusals, each parking the PE with the reason on the UART:
///
/// - **a layout the tables cannot describe** ([`ImageLayout::is_well_formed`]);
///   `link.ld`'s `ASSERT`s make this unreachable for a linked image, and the
///   check keeps the builder from being handed one anyway;
/// - **a device-tree window the map does not cover**
///   ([`dtb_window_admissible`]): the bootargs reader and the boot seam read at
///   most [`crate::cmdline::MAX_DTB_SIZE`] bytes from the pointer, so that
///   window must lie in the kernel's reserved extent (below
///   [`KERNEL_RESERVED_END`], so no boot untyped can describe it — WS-BP BP3.2)
///   and outside the image, its stacks and the Lean heap arena — the firmware
///   places the blob by the image *file*'s size, and everything past the file
///   is `NOLOAD` (WS-BP BP2.1).  A null pointer reads nothing and is accepted.
///
/// `cpu::fatal_halt` rather than `gic::halt_all`: Phase 2 runs on the boot core
/// alone before the GIC exists — there is no other PE to halt, and the barrier
/// the rest of the tree calls is not yet callable.
pub fn init_mmu(dtb_ptr: u64) {
    let layout = image_layout();
    if !layout.is_well_formed() {
        crate::kprintln!(
            "[boot] FATAL: the image layout {:#x?} is not one the boot tables can describe; \
             refusing to enable translation",
            layout
        );
        crate::cpu::fatal_halt();
    }
    if !dtb_window_admissible(dtb_window(dtb_ptr), kernel_extent()) {
        crate::kprintln!(
            "[boot] FATAL: the device tree at {:#x} is not in the kernel's reserved extent \
             [0, {:#x}) outside the image, its stacks and the Lean heap arena; refusing to read it",
            dtb_ptr,
            KERNEL_RESERVED_END
        );
        crate::cpu::fatal_halt();
    }
    build_identity_tables(&layout);
    init_mmu_per_core(0);
}

/// **WS-BP BP2.6**: the image's permission boundaries, read off the linker's
/// own symbols (`link.ld`'s `_start`, `__text_end`, `__rodata_end`).
///
/// Only the symbols' *addresses* are taken, which forms no access.  The host
/// has no link script, so it reports the empty layout, which
/// [`ImageLayout::is_well_formed`] refuses; the host tests build tables from
/// layouts of their own.
#[must_use]
fn image_layout() -> ImageLayout {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static _start: u8;
            static __text_end: u8;
            static __rodata_end: u8;
        }
        ImageLayout {
            text_start: &raw const _start as u64,
            text_end: &raw const __text_end as u64,
            rodata_end: &raw const __rodata_end as u64,
        }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        ImageLayout {
            text_start: 0,
            text_end: 0,
            rodata_end: 0,
        }
    }
}

/// **WS-BP BP4.5**: the image's loaded bytes, `[_start, __image_load_end)` —
/// its text, read-only data and initialised data, which is everything the
/// firmware copies from the image file and so the only memory the boot makes
/// present that a thread could be handed as code.  The boot seam cleans it to
/// the Point of Unification ([`crate::cache::clean_boot_image_to_pou`]).
///
/// The host has no link script and reports the empty range.
#[must_use]
pub fn boot_image_loaded_extent() -> (u64, u64) {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static _start: u8;
            static __image_load_end: u8;
        }
        let start = &raw const _start as u64;
        let end = &raw const __image_load_end as u64;
        (start, end.saturating_sub(start))
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        (0, 0)
    }
}

/// **WS-BP BP2.6**: the memory the image owns, `[_start, __lean_heap_end)` —
/// its text, data, `.bss` (the boot tables live there), both stack regions and
/// the Lean heap arena, which `link.ld` places in that order.
///
/// The host has no link script and reports the empty range.
#[must_use]
fn kernel_extent() -> (u64, u64) {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static _start: u8;
        }
        let start = &raw const _start as u64;
        let (heap_start, heap_len) = crate::lean_heap::arena_extent();
        let end = heap_start as u64 + heap_len as u64;
        (start, end.saturating_sub(start))
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        (0, 0)
    }
}

/// **WS-BP BP2.6**: the bytes a reader of the device tree at `dtb_ptr` may
/// dereference: [`crate::cmdline::MAX_DTB_SIZE`] from the pointer, or nothing
/// for a null pointer.
///
/// Taken from the pointer alone, before anything is read: every reader of the
/// blob — the bootargs reader and the boot seam — bounds the header's
/// `totalsize` by the same constant before it forms a slice, so no read leaves
/// this window whatever the blob says.
#[must_use]
pub const fn dtb_window(dtb_ptr: u64) -> (u64, u64) {
    if dtb_ptr == 0 {
        (0, 0)
    } else {
        (dtb_ptr, crate::cmdline::MAX_DTB_SIZE as u64)
    }
}

/// **WS-BP BP2.6**: may the boot read the device tree at `window`?
///
/// The window must lie wholly inside the kernel's reserved extent —
/// `[0, KERNEL_RESERVED_END)`, which the boot map covers and no boot untyped
/// may describe (WS-BP BP3.2), so the blob is never memory a thread was handed
/// — and be disjoint from `kernel`, the memory the image owns.  An empty window
/// (a null pointer) reads nothing and is accepted; a window whose end overflows
/// is refused.
#[must_use]
pub const fn dtb_window_admissible(window: (u64, u64), kernel: (u64, u64)) -> bool {
    let (base, size) = window;
    if size == 0 {
        return true;
    }
    match base.checked_add(size) {
        Some(end) if end <= KERNEL_RESERVED_END => dtb_disjoint_from_image(window, &[kernel]),
        _ => false,
    }
}

/// **WS-BP BP2.1**: is the device tree's window disjoint from every range the
/// image occupies?
///
/// Stated over explicit ranges so the host decides it.  An empty range
/// overlaps nothing — a null pointer is dereferenced by nothing — and a range
/// whose end overflows is refused, since its extent is not a range at all.
#[must_use]
pub const fn dtb_disjoint_from_image(dtb: (u64, u64), image: &[(u64, u64)]) -> bool {
    let (base, size) = dtb;
    if size == 0 {
        return true;
    }
    let Some(end) = base.checked_add(size) else {
        return false;
    };
    let mut i = 0;
    while i < image.len() {
        let (image_base, image_size) = image[i];
        if image_size != 0 {
            let Some(image_end) = image_base.checked_add(image_size) else {
                return false;
            };
            if base < image_end && image_base < end {
                return false;
            }
        }
        i += 1;
    }
    true
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
    fn tcr_ips_is_the_pe_physical_address_size() {
        // IPS in bits [34:32] is the argument, and the Cortex-A76's is 0b010
        // (40 bits) — the value the kernel programs on every Raspberry Pi 5.
        assert_eq!((TCR_VALUE >> 32) & 0x7, 0b010);
        for (field, ips) in [
            (0b0000u64, 0b000u64),
            (0b0001, 0b001),
            (0b0010, 0b010),
            (0b0011, 0b011),
            (0b0100, 0b100),
            (0b0101, 0b101),
        ] {
            let size = physical_address_size_of(field).expect("a defined PARange encoding");
            assert_eq!(size.ips, ips, "PARange {field:#06b}");
            assert_eq!(
                (tcr_el1_value(size.ips) >> 32) & 0x7,
                ips,
                "PARange {field:#06b}"
            );
        }
        // Only IPS moves with the argument.
        assert_eq!(
            tcr_el1_value(0b000) & !(0b111 << 32),
            tcr_el1_value(0b101) & !(0b111 << 32)
        );
    }

    /// The v0.36.2 audit: `ID_AA64MMFR0_EL1.PARange` (bits [3:0]) decodes to the
    /// architecture's table, a 52- or 56-bit PE is walked at 48, and a reserved
    /// encoding is refused rather than rounded.
    #[test]
    fn physical_address_size_decodes_pa_range() {
        let bits = |field: u64| physical_address_size_of(field).map(|s| s.bits);
        assert_eq!(bits(0b0000), Some(32));
        assert_eq!(bits(0b0001), Some(36));
        assert_eq!(bits(0b0010), Some(40));
        assert_eq!(bits(0b0011), Some(42));
        assert_eq!(bits(0b0100), Some(44));
        assert_eq!(bits(0b0101), Some(48));
        assert_eq!(bits(0b0110), Some(52));
        assert_eq!(bits(0b0111), Some(56));
        for reserved in 0b1000..=0b1111u64 {
            assert_eq!(
                physical_address_size_of(reserved),
                None,
                "PARange {reserved:#06b}"
            );
        }
        // Capped at the 48 bits an ARMv8.0-format descriptor can name.
        assert_eq!(physical_address_size_of(0b0110).unwrap().ips, 0b101);
        assert_eq!(physical_address_size_of(0b0111).unwrap().ips, 0b101);
        // Only bits [3:0] are the field: the rest of the register is not read.
        assert_eq!(
            physical_address_size_of(0x0000_0000_0010_1122),
            physical_address_size_of(0b0010),
            "ASIDBits, BigEnd, SNSMem and the granule fields above PARange are ignored"
        );
        assert_eq!(
            CORTEX_A76_PHYSICAL_ADDRESS_SIZE,
            PhysicalAddressSize {
                bits: 40,
                ips: 0b010
            }
        );
        assert_eq!(
            physical_address_size_of_this_pe_or_halt(crate::cpu::fatal_halt),
            CORTEX_A76_PHYSICAL_ADDRESS_SIZE,
            "the host answers for the PE the kernel is built for"
        );
    }

    /// The floor `enable_mmu` holds a PE to is the tables' reach: 39 bits,
    /// which the next encoding below the Cortex-A76's (36 bits) does not clear.
    /// That the Cortex-A76 clears it, and that the device window is within the
    /// reach, are compile-time assertions beside `BOOT_TABLE_PA_BITS_REQUIRED`.
    #[test]
    fn the_boot_tables_reach_is_the_floor_a_pe_is_held_to() {
        assert_eq!(BOOT_TABLE_PA_BITS_REQUIRED, 39);
        assert_eq!(1u64 << BOOT_TABLE_PA_BITS_REQUIRED, BOOT_TABLE_REACH);
        for (field, admitted) in [
            (0b0000u64, false),
            (0b0001, false),
            (0b0010, true),
            (0b0101, true),
        ] {
            let bits = physical_address_size_of(field).unwrap().bits;
            assert_eq!(
                bits >= BOOT_TABLE_PA_BITS_REQUIRED,
                admitted,
                "PARange {field:#06b}"
            );
        }
    }

    /// The v0.36.2 audit: the width the Lean binding declares
    /// (`rpi5MachineConfig.physicalAddressWidth`, carried by the shared fixture's
    /// `physicalAddressWidth` line) is the PE's own PARange — the model bounds
    /// every physical address it admits by it, so a model wider than the PE
    /// admits mappings the PE answers with an Address size fault (the `44`
    /// this held until the audit).  And everything the boot tables can
    /// describe is inside the model's bound, so the HAL never maps what the
    /// model refuses.
    #[test]
    fn the_lean_physical_address_width_is_the_pe_the_hal_programs_for() {
        let lean_width = lean_boot_map_scalar("physicalAddressWidth");
        assert_eq!(
            lean_width,
            u64::from(CORTEX_A76_PHYSICAL_ADDRESS_SIZE.bits),
            "tests/fixtures/boot_map.expected's physicalAddressWidth is the Cortex-A76's PARange"
        );
        assert!(
            BOOT_TABLE_REACH <= 1u64 << lean_width,
            "every address the boot tables can describe is one the Lean model admits"
        );
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
        for desc in [BLOCK_NORMAL, BLOCK_KERNEL_TEXT, BLOCK_KERNEL_RODATA] {
            // Valid bit (bit 0) and Access Flag (bit 10) must be set
            assert_ne!(desc & DESC_VALID, 0);
            assert_ne!(desc & AF, 0);
            // Inner Shareable, AttrIndx = 0 (Normal memory)
            assert_ne!(desc & SH_INNER, 0);
            assert_eq!(desc & ATTR_IDX_DEVICE, 0);
            // UXN set (no user execute from kernel pages)
            assert_ne!(desc & UXN, 0);
        }
        // WS-BP BP2.6: writable data is never executable at EL1, the text is
        // read-only and executable, the read-only data neither.
        assert_eq!(BLOCK_NORMAL & AP_RO_EL1, 0);
        assert_ne!(BLOCK_NORMAL & PXN, 0);
        assert_ne!(BLOCK_KERNEL_TEXT & AP_RO_EL1, 0);
        assert_eq!(BLOCK_KERNEL_TEXT & PXN, 0);
        assert_ne!(BLOCK_KERNEL_RODATA & AP_RO_EL1, 0);
        assert_ne!(BLOCK_KERNEL_RODATA & PXN, 0);
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
            BOOT_TABLE_COUNT * 512 * 8
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
    fn boot_table_extent_is_every_translation_table() {
        // **WS-BP BP2.6**: one L0, one L1, two L2 (the first gigabyte, the
        // device window) and three L3 for the image's boundary blocks, each 512
        // entries × 8 bytes = 4096 bytes (the device tail's L3 went with the
        // BCM2712 address-map correction).  `enable_mmu`
        // cleans exactly this extent to
        // the Point of Coherency before the walker is switched on, so an
        // extent that under-reports the tables would leave a table dirty in
        // the D-cache while the walker reads memory.
        assert_eq!(PageTableCell::size(), BOOT_TABLE_COUNT * 4096);
        assert_eq!(PageTableCell::size(), 28672);
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
        // SM1.C.1 / **WS-BP BP2.6**: the primary `init_mmu` takes the device
        // tree pointer `rust_boot_main` receives in `x0` — not to size the map,
        // which is built from constants, but to refuse a blob whose window the
        // map does not cover before any reader dereferences it.
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

/// **The BCM2712 address-map correction (v0.36.2)**: the MMIO window the Lean
/// binding programs under `name` (`uart`, `gicd`, `gicc`), as `(base, size)`,
/// read from the `mmio` lines `tests/Ak9PlatformSuite.lean` writes into
/// `tests/fixtures/boot_map.expected` from `mmioRegions`.
///
/// The UART and GIC drivers' tests compare their base constants with this, so
/// the two sides are compared by running both.  Before it they asserted a
/// literal beside a comment naming `Board.lean`, and both sides then carried
/// the BCM2711's addresses together while every test passed.
#[cfg(test)]
pub(crate) fn lean_mmio_window(name: &str) -> (u64, u64) {
    const LEAN_TABLE: &str = include_str!("../../../tests/fixtures/boot_map.expected");
    let hex = |s: &str| u64::from_str_radix(s.trim_start_matches("0x"), 16).expect("hex");
    let mut found = None;
    for line in LEAN_TABLE.lines() {
        let mut cols = line.split_whitespace();
        if cols.next() == Some("mmio") && cols.next() == Some(name) {
            let base = hex(cols.next().expect("an mmio line carries a base"));
            let size = hex(cols.next().expect("an mmio line carries a size"));
            assert!(
                found.is_none(),
                "two `mmio {name}` lines in the boot-map table"
            );
            found = Some((base, size));
        }
    }
    found.unwrap_or_else(|| panic!("no `mmio {name}` line in the boot-map table"))
}

/// **The v0.36.2 audit**: a single-valued line of the shared boot-map table —
/// `physicalAddressWidth <bits>` (read back against the PE's `PARange` above)
/// and `declaredCores <n>` (read back by `boot.rs` against the handoff's
/// `LEAN_DECLARED_CORE_COUNT`) — as `tests/Ak9PlatformSuite.lean` writes it
/// into `tests/fixtures/boot_map.expected`.  Exactly one line carries `key`,
/// and it carries exactly one hexadecimal value.
#[cfg(test)]
pub(crate) fn lean_boot_map_scalar(key: &str) -> u64 {
    const LEAN_TABLE: &str = include_str!("../../../tests/fixtures/boot_map.expected");
    let hex = |s: &str| u64::from_str_radix(s.trim_start_matches("0x"), 16).expect("hex");
    let mut found = None;
    for line in LEAN_TABLE.lines() {
        let mut cols = line.split_whitespace();
        if cols.next() == Some(key) {
            let value = hex(cols
                .next()
                .unwrap_or_else(|| panic!("a `{key}` line carries a value")));
            assert!(cols.next().is_none(), "a `{key}` line carries one value");
            assert!(found.is_none(), "two `{key}` lines in the boot-map table");
            found = Some(value);
        }
    }
    found.unwrap_or_else(|| panic!("no `{key}` line in the boot-map table"))
}

#[cfg(test)]
mod boot_map_tests {
    use super::*;
    // WS-BP BP0.4: the Lean-table test parses a checked-in fixture into `Vec`s.
    extern crate std;
    use std::vec::Vec;

    /// An image shaped like `link.ld` produces: text from the load address
    /// across a block boundary, and read-only data ending in the same block as
    /// the text — two blocks need page granularity.
    const LAYOUT: ImageLayout = ImageLayout {
        text_start: 0x8_0000,
        text_end: 0x2A_3000,
        rodata_end: 0x3C_5000,
    };

    /// Every boundary in a block of its own: all three L3 image tables used.
    const SPREAD_LAYOUT: ImageLayout = ImageLayout {
        text_start: 0x8_0000,
        text_end: 0x61_F000,
        rodata_end: 0xA0_5000,
    };

    /// Every boundary on a block boundary: no L3 image table used.
    const BLOCK_ALIGNED_LAYOUT: ImageLayout = ImageLayout {
        text_start: 0x20_0000,
        text_end: 0x40_0000,
        rodata_end: 0x60_0000,
    };

    const LAYOUTS: [ImageLayout; 3] = [LAYOUT, SPREAD_LAYOUT, BLOCK_ALIGNED_LAYOUT];

    /// The table at `pa`, if `pa` is one of the struct's tables other than L0.
    fn table_at(tables: &BootPageTables, base_pa: u64, pa: u64) -> Option<&[u64; TABLE_ENTRIES]> {
        let index = pa.checked_sub(base_pa)? / 4096;
        if pa != table_pa(base_pa, index) {
            return None;
        }
        match index {
            L1_TABLE => Some(&tables.l1),
            L2_RAM_TABLE => Some(&tables.l2_ram),
            L2_DEVICE_TABLE => Some(&tables.l2_device),
            i if (L3_IMAGE_TABLE_BASE..L3_IMAGE_TABLE_BASE + IMAGE_BOUNDARY_COUNT as u64)
                .contains(&i) =>
            {
                Some(&tables.l3_image[(i - L3_IMAGE_TABLE_BASE) as usize])
            }
            _ => None,
        }
    }

    /// Translate `va` the way the PE's table walker would, starting at level 0
    /// with a 4 KiB granule and `TCR_EL1.T0SZ = 16`: `(output PA, attributes)`.
    ///
    /// Follows descriptor *types*: a block at level 0 or a page type anywhere
    /// but level 3 does not resolve, which is what makes the walk a witness
    /// rather than a reading of chosen arrays.
    fn walk(tables: &BootPageTables, base_pa: u64, va: u64) -> Option<(u64, u64)> {
        let mut table: &[u64; TABLE_ENTRIES] = &tables.l0;
        for level in 0..4u32 {
            let shift = 39 - 9 * level;
            let entry = table[((va >> shift) & 0x1FF) as usize];
            match (entry & 0b11, level) {
                (0b11, 3) | (0b01, 1 | 2) => {
                    let span = 1u64 << shift;
                    let output = (entry & DESC_ADDR_MASK & !(span - 1)) | (va & (span - 1));
                    return Some((output, entry & !DESC_ADDR_MASK));
                }
                (0b11, 0..=2) => table = table_at(tables, base_pa, entry & DESC_ADDR_MASK)?,
                _ => return None,
            }
        }
        None
    }

    /// Build a table set for `layout` at a synthetic (4 KiB-aligned) base.
    fn build(layout: &ImageLayout) -> (BootPageTables, u64) {
        let base_pa: u64 = 0x10_0000;
        let mut tables = BootPageTables::new();
        populate_boot_tables(&mut tables, base_pa, layout);
        (tables, base_pa)
    }

    /// Is this descriptor's page writable at EL1?  (`AP[2] == 0`.)
    fn writable(attrs: u64) -> bool {
        attrs & AP_RO_EL1 == 0
    }

    /// Is this descriptor's page executable at EL1?  (`PXN` clear.)
    fn executable(attrs: u64) -> bool {
        attrs & PXN == 0
    }

    /// **WS-BP BP0.4 / BP2.6**: the boot map, driven through the Lean map
    /// rather than mirrored from it.
    ///
    /// `tests/fixtures/boot_map.expected` is emitted by
    /// `tests/Ak9PlatformSuite.lean` from `rpi5MemoryMapForConfig` itself: for
    /// every RAM configuration — each variant uncut, and the firmware-cut
    /// configurations the suite's accounts bind — the regions the map declares
    /// and the kind `classifyAddress` gives at every probe.  Since BP2.6 the
    /// boot map is the same on every board, so the relation is an *inclusion*
    /// rather than an equality: every address it maps Normal is RAM in
    /// **every** configuration, and every address it maps Device is a device
    /// region in every configuration and conversely.  **WS-BP BP7.10**: the
    /// constant Normal window is exactly the kernel's reserved extent the table
    /// declares, and with each configuration's `extend` lines applied the
    /// extended Normal window is exactly that configuration's RAM — the top of
    /// the first gigabyte a cut configuration's firmware withholds unmapped.
    ///
    /// Probed at every fixture probe, every boundary constant of this map and
    /// every image boundary, each with the byte below it, through
    /// [`boot_mapping_for`] and through a walk of the built tables.
    #[test]
    fn the_boot_map_agrees_with_the_lean_map() {
        const LEAN_TABLE: &str = include_str!("../../../tests/fixtures/boot_map.expected");
        fn hex(s: &str) -> u64 {
            u64::from_str_radix(s.trim_start_matches("0x"), 16).expect("hex in the boot-map table")
        }
        struct Variant<'a> {
            ram_size: u64,
            low_ram_top: u64,
            regions: Vec<(u64, u64, &'a str)>,
            probes: Vec<(u64, &'a str)>,
            extensions: Vec<(u64, u64)>,
        }
        let mut variants: Vec<Variant> = Vec::new();
        let mut reserved: Vec<(u64, u64)> = Vec::new();
        for line in LEAN_TABLE.lines().filter(|l| !l.starts_with('#')) {
            let cols: Vec<&str> = line.split_whitespace().collect();
            match cols.as_slice() {
                ["variant", size, "lowRamTop", low] => variants.push(Variant {
                    ram_size: hex(size),
                    low_ram_top: hex(low),
                    regions: Vec::new(),
                    probes: Vec::new(),
                    extensions: Vec::new(),
                }),
                ["region", base, size, kind] => variants
                    .last_mut()
                    .expect("a region belongs to a variant")
                    .regions
                    .push((hex(base), hex(size), kind)),
                ["probe", addr, kind] => variants
                    .last_mut()
                    .expect("a probe belongs to a variant")
                    .probes
                    .push((hex(addr), kind)),
                // WS-BP BP4.6, BP7.10: what the boot maps outside the kernel's
                // reserved extent on this configuration, as `(base, size)`.
                ["extend", base, size] => variants
                    .last_mut()
                    .expect("an extension belongs to a variant")
                    .extensions
                    .push((hex(base), hex(size))),
                // WS-BP BP3.2: the reserved extent, which
                // `the_kernel_reserved_extent_is_the_lean_and_linker_one` reads.
                ["kernelReserved", base, end] => reserved.push((hex(base), hex(end))),
                // The BCM2712 address-map correction: the MMIO windows, which
                // `lean_mmio_window` reads for the UART and GIC tests.
                ["mmio", _, _, _] => {}
                // The v0.36.2 audit: the binding's physical address width and
                // declared PE count, which `lean_boot_map_scalar` reads for
                // `the_lean_physical_address_width_is_the_pe_the_hal_programs_for`
                // and `boot.rs`'s core-count pin.
                ["physicalAddressWidth", _] | ["declaredCores", _] => {}
                _ => panic!("unrecognised boot-map line {line:?}"),
            }
        }
        assert_eq!(
            variants.len(),
            8,
            "the Lean table carries the five RPi5 RAM variants and three firmware-cut configurations"
        );
        assert_eq!(
            reserved,
            [(0, KERNEL_RESERVED_END)],
            "the constant Normal window is the Lean kernel's reserved extent"
        );
        // WS-BP BP7.10: every configuration is extended over its first-gigabyte
        // RAM past the kernel's extent, and — above a gigabyte — over its DRAM
        // past the gigabyte; so the exact comparison below is not satisfied by a
        // table that carries no `extend` lines at all.
        for v in &variants {
            assert!(
                v.low_ram_top > KERNEL_RESERVED_END && v.low_ram_top <= L1_BLOCK_SIZE,
                "configuration {:#x}/{:#x}: the first-gigabyte RAM top is admissible",
                v.ram_size,
                v.low_ram_top
            );
            let expected_extensions = if v.ram_size > L1_BLOCK_SIZE { 2 } else { 1 };
            assert_eq!(
                v.extensions.len(),
                expected_extensions,
                "configuration {:#x}/{:#x}: one extension per RAM region outside the extent",
                v.ram_size,
                v.low_ram_top
            );
            assert_eq!(
                v.extensions[0],
                (KERNEL_RESERVED_END, v.low_ram_top - KERNEL_RESERVED_END),
                "configuration {:#x}/{:#x}: the first extension starts where the extent ends",
                v.ram_size,
                v.low_ram_top
            );
        }
        assert!(
            variants.iter().any(|v| v.low_ram_top < L1_BLOCK_SIZE),
            "the table carries a configuration whose firmware withholds part of the first gigabyte"
        );
        for layout in &LAYOUTS {
            let (tables, base_pa) = build(layout);
            for v in &variants {
                let lean_kind = |a: u64| -> &str {
                    v.regions
                        .iter()
                        .find(|&&(b, sz, _)| b <= a && a < b + sz)
                        .map_or("reserved", |&(_, _, k)| k)
                };
                let mut addrs: Vec<u64> = Vec::new();
                for &(a, kind) in &v.probes {
                    assert_eq!(
                        kind,
                        lean_kind(a),
                        "the table's probe at {a:#x} names its own regions"
                    );
                    addrs.push(a);
                }
                for c in [
                    KERNEL_RESERVED_END,
                    L1_BLOCK_SIZE,
                    DEVICE_WINDOW_BASE,
                    DEVICE_WINDOW_TOP,
                    v.low_ram_top,
                    v.ram_size,
                    layout.text_start,
                    layout.text_end,
                    layout.rodata_end,
                    1 << 39,
                ] {
                    addrs.push(c - 1);
                    addrs.push(c);
                }
                let (mut extended, _) = build(layout);
                let mut ranges: Vec<(u64, u64)> = Vec::new();
                for &(base, size) in &v.extensions {
                    extend_boot_tables(&mut extended, base, size).unwrap_or_else(|r| {
                        panic!(
                            "configuration {:#x}/{:#x}: [{base:#x}, +{size:#x}) refused: {r:?}",
                            v.ram_size, v.low_ram_top
                        )
                    });
                    ranges.push((base, base + size));
                    addrs.push(base);
                    addrs.push(base + size - 1);
                    addrs.push(base + size);
                }
                for &(b, sz, _) in &v.regions {
                    for c in [b, b + sz] {
                        addrs.push(c.saturating_sub(1));
                        addrs.push(c);
                    }
                }
                for a in addrs {
                    let kind = boot_mapping_for(a, layout);
                    let lean = lean_kind(a);
                    let cfg = (v.ram_size, v.low_ram_top);
                    if kind.is_normal() {
                        assert_eq!(lean, "ram", "configuration {cfg:x?}: {a:#x} maps Normal");
                    }
                    assert_eq!(
                        kind == BootMapping::Device,
                        lean == "device",
                        "configuration {cfg:x?}: {a:#x} is {lean} in the Lean map"
                    );
                    // WS-BP BP7.10: the constant Normal window is exactly the
                    // kernel's reserved extent, on every configuration.
                    assert_eq!(
                        kind.is_normal(),
                        a < KERNEL_RESERVED_END,
                        "{a:#x}: the constant Normal window is the kernel's extent"
                    );
                    // WS-BP BP4.6, BP7.10: with the configuration's extensions
                    // applied, the Normal window is exactly its RAM — through a
                    // walk of the extended tables and through the cacheable
                    // predicate — so the firmware's withheld top of the first
                    // gigabyte stays unmapped and uncacheable.
                    let extended_normal = walk(&extended, base_pa, a)
                        .is_some_and(|(_, attrs)| attrs & ATTR_IDX_DEVICE == 0);
                    assert_eq!(
                        extended_normal,
                        lean == "ram",
                        "configuration {cfg:x?} extended: {a:#x} is {lean} in the Lean map"
                    );
                    assert_eq!(
                        ram_range_covered(a, 1, &ranges),
                        lean == "ram",
                        "configuration {cfg:x?}: the cacheable window at {a:#x} is not its RAM"
                    );
                    if let Some((pa, attrs)) = walk(&extended, base_pa, a) {
                        assert_eq!(pa, a, "the extended map is an identity map");
                        if a >= KERNEL_RESERVED_END && attrs & ATTR_IDX_DEVICE == 0 {
                            assert!(
                                writable(attrs) && !executable(attrs),
                                "{a:#x}: extended RAM is writable and never executable"
                            );
                        }
                    }
                    let walked = walk(&tables, base_pa, a);
                    match kind {
                        BootMapping::Unmapped => {
                            assert!(walked.is_none(), "{a:#x} must fault")
                        }
                        _ => {
                            let (pa, attrs) = walked.unwrap_or_else(|| panic!("{a:#x} must map"));
                            assert_eq!(pa, a, "the boot map is an identity map");
                            assert_eq!(
                                attrs & ATTR_IDX_DEVICE != 0,
                                kind == BootMapping::Device,
                                "{a:#x} has the wrong memory type"
                            );
                        }
                    }
                }
            }
        }
    }

    /// **WS-BP BP4.6**: every refusal is decided before anything is written,
    /// so a refused extension leaves the tables byte-identical.
    #[test]
    fn a_refused_extension_writes_nothing() {
        const GIB: u64 = L1_BLOCK_SIZE;
        let cases: [(u64, u64, RamExtensionRefusal); 11] = [
            (GIB, 0, RamExtensionRefusal::Empty),
            (
                u64::MAX - L2_BLOCK_SIZE + 1,
                L2_BLOCK_SIZE,
                RamExtensionRefusal::Overflow,
            ),
            (GIB + 0x1000, L2_BLOCK_SIZE, RamExtensionRefusal::Unaligned),
            (GIB, L2_BLOCK_SIZE + 0x1000, RamExtensionRefusal::Unaligned),
            // WS-BP BP7.10: a range reaching back into the kernel's extent.
            (
                KERNEL_RESERVED_END - L2_BLOCK_SIZE,
                2 * L2_BLOCK_SIZE,
                RamExtensionRefusal::InsideKernelReserved,
            ),
            (0, GIB, RamExtensionRefusal::InsideKernelReserved),
            (
                BOOT_TABLE_REACH - GIB,
                2 * GIB,
                RamExtensionRefusal::BeyondTableReach,
            ),
            // A partial gigabyte outside the device window has no level-2 table.
            (GIB, GIB / 2, RamExtensionRefusal::PartialGigabyte),
            // The device window's own blocks are valid already.
            (
                DEVICE_WINDOW_BASE,
                L2_BLOCK_SIZE,
                RamExtensionRefusal::AlreadyMapped,
            ),
            // WS-BP BP7.10: the first gigabyte's RAM past the extent followed
            // by half of the next gigabyte, which has no level-2 table: the
            // second gigabyte's refusal must leave the first gigabyte's level-2
            // entries unwritten.
            (
                KERNEL_RESERVED_END,
                GIB - KERNEL_RESERVED_END + GIB / 2,
                RamExtensionRefusal::PartialGigabyte,
            ),
            // A whole gigabyte followed by the device window's gigabyte: the
            // second gigabyte's refusal must leave the first unwritten.
            (
                (DEVICE_GIB as u64 - 1) * GIB,
                2 * GIB,
                RamExtensionRefusal::AlreadyMapped,
            ),
        ];
        for (base, size, refusal) in cases {
            let (mut tables, _) = build(&LAYOUT);
            let (pristine, _) = build(&LAYOUT);
            assert_eq!(
                extend_boot_tables(&mut tables, base, size),
                Err(refusal),
                "[{base:#x}, +{size:#x})"
            );
            assert!(
                tables.l1 == pristine.l1
                    && tables.l2_ram == pristine.l2_ram
                    && tables.l2_device == pristine.l2_device,
                "[{base:#x}, +{size:#x}): a refusal wrote a descriptor"
            );
        }
    }

    /// **WS-BP BP4.6**: an extension never rewrites a valid descriptor — a
    /// second extension over the same range is refused, and so is one that
    /// overlaps it by a single block.
    #[test]
    fn an_extension_does_not_remap() {
        let (mut tables, base_pa) = build(&LAYOUT);
        assert_eq!(
            extend_boot_tables(&mut tables, L1_BLOCK_SIZE, L1_BLOCK_SIZE),
            Ok(())
        );
        assert_eq!(
            extend_boot_tables(&mut tables, L1_BLOCK_SIZE, L1_BLOCK_SIZE),
            Err(RamExtensionRefusal::AlreadyMapped)
        );
        // A partial extension inside the device window's gigabyte, the one
        // gigabyte with a level-2 table of its own.
        let gib = DEVICE_GIB as u64 * L1_BLOCK_SIZE;
        let end = gib + 0x2000_0000;
        assert_eq!(extend_boot_tables(&mut tables, gib, end - gib), Ok(()));
        assert_eq!(
            extend_boot_tables(&mut tables, end - L2_BLOCK_SIZE, 2 * L2_BLOCK_SIZE),
            Err(RamExtensionRefusal::AlreadyMapped)
        );
        // The first block after the extension is still unmapped, and the
        // device window is still Device.
        assert!(walk(&tables, base_pa, end).is_none());
        // WS-BP BP7.10: the first gigabyte has a level-2 table of its own too;
        // its RAM past the kernel's extent extends by 2 MiB blocks, the
        // reserved extent's own descriptors are never rewritten, and the block
        // past the extension — the top the firmware withholds — stays unmapped.
        let (pristine, _) = build(&LAYOUT);
        let low_top = 0x3FC0_0000;
        assert_eq!(
            extend_boot_tables(
                &mut tables,
                KERNEL_RESERVED_END,
                low_top - KERNEL_RESERVED_END
            ),
            Ok(())
        );
        assert_eq!(
            tables.l2_ram[..(KERNEL_RESERVED_END / L2_BLOCK_SIZE) as usize],
            pristine.l2_ram[..(KERNEL_RESERVED_END / L2_BLOCK_SIZE) as usize],
            "an extension never rewrites the kernel's extent"
        );
        assert_eq!(
            extend_boot_tables(&mut tables, low_top - L2_BLOCK_SIZE, L2_BLOCK_SIZE),
            Err(RamExtensionRefusal::AlreadyMapped)
        );
        let (pa, attrs) = walk(&tables, base_pa, low_top - 1).expect("reported RAM maps");
        assert_eq!(pa, low_top - 1);
        assert!(writable(attrs) && !executable(attrs) && attrs & ATTR_IDX_DEVICE == 0);
        assert!(walk(&tables, base_pa, low_top).is_none());
        assert!(walk(&tables, base_pa, L1_BLOCK_SIZE - 1).is_none());
        let (_, attrs) = walk(&tables, base_pa, DEVICE_WINDOW_BASE).expect("device maps");
        assert_ne!(attrs & ATTR_IDX_DEVICE, 0);
    }

    /// **WS-BP BP4.6**: the cacheable window is the union of the kernel's
    /// extent and the extensions — a range crossing from one into an abutting
    /// one is covered, one crossing into a gap is not.  **WS-BP BP7.10**: the
    /// gap may sit inside the first gigabyte, where the firmware withholds its
    /// top.
    #[test]
    fn the_cacheable_window_is_a_union() {
        const GIB: u64 = L1_BLOCK_SIZE;
        const KRE: u64 = KERNEL_RESERVED_END;
        let low_top = 0x3FC0_0000;
        let ext = [(KRE, low_top), (GIB, 3 * GIB), (4 * GIB, 8 * GIB)];
        assert!(ram_range_covered(KRE - 0x1000, 0x2000, &ext));
        assert!(ram_range_covered(0, low_top, &ext));
        assert!(!ram_range_covered(low_top - 0x1000, 0x2000, &ext));
        assert!(!ram_range_covered(low_top, 0x1000, &ext));
        assert!(!ram_range_covered(GIB - 0x1000, 0x2000, &ext));
        assert!(ram_range_covered(GIB, 2 * GIB, &ext));
        assert!(!ram_range_covered(3 * GIB - 0x1000, 0x2000, &ext));
        assert!(ram_range_covered(4 * GIB, 4 * GIB, &ext));
        assert!(!ram_range_covered(4 * GIB, 4 * GIB + 1, &ext));
        assert!(!ram_range_covered(KRE, 0x1000, &[]));
        assert!(ram_range_covered(KRE - 0x1000, 0x1000, &[]));
        assert!(ram_range_covered(8 * GIB, 0, &[]));
        assert!(!ram_range_covered(u64::MAX - 3, 16, &ext));
        // Order of the record does not matter.
        let reversed = [(4 * GIB, 8 * GIB), (GIB, 3 * GIB), (KRE, low_top)];
        assert!(ram_range_covered(0, low_top, &reversed));
        assert!(ram_range_covered(4 * GIB, 4 * GIB, &reversed));
    }

    #[test]
    fn the_level_zero_table_is_reached_by_a_table_descriptor() {
        // The pre-RR7.1 defect, stated as a walk: `T0SZ = 16` makes level 0 the
        // initial lookup level, where a block descriptor is reserved.
        let (tables, base_pa) = build(&LAYOUT);
        assert_eq!(tables.l0[0] & 0b11, DESC_TABLE);
        assert_eq!(tables.l0[0] & DESC_ADDR_MASK, base_pa + 4096);
        let (pa, _) = walk(&tables, base_pa, LAYOUT.text_start).expect("the load address maps");
        assert_eq!(pa, LAYOUT.text_start);
    }

    #[test]
    fn a_block_descriptor_at_level_zero_does_not_resolve() {
        // The mutation that keeps the token and breaks the relation: leave the
        // level-0 entry present and valid, spelled as a block.
        let (mut tables, base_pa) = build(&LAYOUT);
        tables.l0[0] = BLOCK_NORMAL;
        assert_ne!(tables.l0[0] & DESC_VALID, 0, "the entry is still valid");
        assert!(walk(&tables, base_pa, LAYOUT.text_start).is_none());
    }

    #[test]
    fn only_the_first_gigabyte_and_the_device_window_are_reachable() {
        let (tables, _) = build(&LAYOUT);
        for (i, &entry) in tables.l0.iter().enumerate().skip(1) {
            assert_eq!(entry, 0, "L0 entry {i} must be invalid");
        }
        for (g, &entry) in tables.l1.iter().enumerate() {
            assert_eq!(
                entry != 0,
                g == 0 || g == DEVICE_GIB,
                "L1 entry {g}: only the first gigabyte's table and the device window are mapped"
            );
        }
    }

    /// **WS-BP BP2.6**: the finding the section permissions close.  Every
    /// Normal page used to be mapped with one descriptor — writable, and
    /// executable at EL1 — while `SCTLR_EL1.WXN` makes every EL1-writable page
    /// execute-never, so the kernel's first fetch after the enable would have
    /// faulted.  No page of the new map is writable and executable, the text is
    /// executable, and the retired descriptor is exactly the one WXN forbids to
    /// execute from.
    #[test]
    fn no_page_is_writable_and_executable_and_the_text_executes() {
        assert_ne!(
            compute_sctlr_el1_bitmap() & sctlr_bits::WXN,
            0,
            "WXN is set"
        );
        let retired = DESC_VALID | AF | SH_INNER | ATTR_IDX_NORMAL | AP_RW_EL1 | UXN;
        assert!(
            writable(retired) && executable(retired),
            "the retired descriptor is W and X, which WXN turns into XN"
        );
        for layout in &LAYOUTS {
            let (tables, base_pa) = build(layout);
            let mut executable_pages = 0u64;
            let spans = [
                (0, KERNEL_RESERVED_END),
                (DEVICE_WINDOW_BASE, DEVICE_WINDOW_TOP),
            ];
            for (lo, hi) in spans {
                for page in (lo..hi).step_by(L3_PAGE_SIZE as usize) {
                    let (_, attrs) = walk(&tables, base_pa, page).expect("mapped");
                    assert!(
                        !(writable(attrs) && executable(attrs)),
                        "{page:#x} is writable and executable"
                    );
                    assert_ne!(attrs & UXN, 0, "{page:#x} is user-executable");
                    if executable(attrs) {
                        assert_eq!(boot_mapping_for(page, layout), BootMapping::KernelText);
                        executable_pages += 1;
                    }
                }
            }
            assert_eq!(
                executable_pages,
                (layout.text_end - layout.text_start) / L3_PAGE_SIZE,
                "exactly the text is executable"
            );
        }
    }

    #[test]
    fn each_image_section_has_its_own_permissions() {
        let (tables, base_pa) = build(&LAYOUT);
        let at = |va: u64| walk(&tables, base_pa, va).expect("mapped").1;
        for va in [LAYOUT.text_start, LAYOUT.text_end - 1] {
            assert!(!writable(at(va)) && executable(at(va)), "{va:#x} is text");
        }
        for va in [LAYOUT.text_end, LAYOUT.rodata_end - 1] {
            assert!(
                !writable(at(va)) && !executable(at(va)),
                "{va:#x} is rodata"
            );
        }
        for va in [
            0,
            LAYOUT.text_start - 1,
            LAYOUT.rodata_end,
            KERNEL_RESERVED_END - 1,
        ] {
            assert!(writable(at(va)) && !executable(at(va)), "{va:#x} is data");
            assert_ne!(at(va) & SH_INNER, 0, "RAM is Inner Shareable");
        }
    }

    #[test]
    fn everything_outside_the_two_windows_is_unmapped() {
        let (tables, base_pa) = build(&LAYOUT);
        for va in [
            // WS-BP BP7.10: the first gigabyte past the kernel's extent — RAM
            // on some boards, withheld by the firmware on every one at its
            // top — is not in the constant map.
            KERNEL_RESERVED_END,
            0x3FC0_0000,
            L1_BLOCK_SIZE - 1,
            L1_BLOCK_SIZE,
            0x8000_0000,
            0xFC00_0000,
            // The BCM2711's UART and GIC distributor, which the boot map
            // mapped Device until the BCM2712 address-map correction: on this
            // board they are DRAM above the first gigabyte.
            0xFE20_1000,
            0xFF84_1000,
            DEVICE_WINDOW_BASE - 1,
            DEVICE_WINDOW_TOP,
            0xFFFF_FFFF,
            0x1_0000_0000,
            0x2_0000_0000,
        ] {
            assert_eq!(boot_mapping_for(va, &LAYOUT), BootMapping::Unmapped);
            assert!(walk(&tables, base_pa, va).is_none(), "{va:#x} must fault");
        }
    }

    #[test]
    fn the_device_window_covers_the_uart_and_both_gic_frames() {
        // `SeLe4n/Platform/RPi5/Board.lean`'s `mmioRegions`, read from the
        // fixture the Lean suite writes, first and last byte of each.
        let (tables, base_pa) = build(&LAYOUT);
        let windows = ["uart", "gicd", "gicc"].map(lean_mmio_window);
        for va in windows.iter().flat_map(|&(b, sz)| [b, b + sz - 1]) {
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
    fn every_descriptor_agrees_with_the_boot_mapping_predicate() {
        // The tables and the predicate must be two readings of one declaration.
        // A block descriptor is sound only if every page of the block has the
        // kind its base has; a page table only where that fails.
        for layout in &LAYOUTS {
            let (tables, base_pa) = build(layout);
            let kind_of = |a: u64| boot_mapping_for(a, layout);
            let uniform = |base: u64| {
                (base..base + L2_BLOCK_SIZE)
                    .step_by(L3_PAGE_SIZE as usize)
                    .all(|p| kind_of(p) == kind_of(base))
            };
            for (i, &entry) in tables.l2_ram.iter().enumerate() {
                let base = (i as u64) * L2_BLOCK_SIZE;
                match image_l3_slot(layout, base) {
                    Some(slot) => {
                        assert!(!uniform(base), "block {base:#x} did not need pages");
                        assert_eq!(
                            entry,
                            table_descriptor(base_pa, L3_IMAGE_TABLE_BASE + slot as u64)
                        );
                        for (k, &page_entry) in tables.l3_image[slot].iter().enumerate() {
                            let page = base + (k as u64) * L3_PAGE_SIZE;
                            assert_eq!(page_entry, page_descriptor(page, kind_of(page)));
                        }
                    }
                    None => {
                        assert!(uniform(base), "block {base:#x} is not homogeneous");
                        assert_eq!(entry, block_descriptor(base, kind_of(base)));
                    }
                }
            }
            let device_gib_base = (DEVICE_GIB as u64) * L1_BLOCK_SIZE;
            for (i, &entry) in tables.l2_device.iter().enumerate() {
                let base = device_gib_base + (i as u64) * L2_BLOCK_SIZE;
                assert!(uniform(base), "device block {base:#x} is not homogeneous");
                assert_eq!(entry, block_descriptor(base, kind_of(base)));
            }
        }
    }

    /// **WS-BP BP2.6**: one L3 table per distinct block an image boundary falls
    /// strictly inside, assigned in order — so [`IMAGE_BOUNDARY_COUNT`] tables
    /// always suffice.
    #[test]
    fn image_page_tables_are_assigned_one_per_straddled_block() {
        let slots = |layout: &ImageLayout| -> Vec<(u64, usize)> {
            (0..KERNEL_RESERVED_END)
                .step_by(L2_BLOCK_SIZE as usize)
                .filter_map(|b| image_l3_slot(layout, b).map(|s| (b, s)))
                .collect()
        };
        assert_eq!(slots(&LAYOUT), [(0, 0), (0x20_0000, 1)]);
        assert_eq!(
            slots(&SPREAD_LAYOUT),
            [(0, 0), (0x60_0000, 1), (0xA0_0000, 2)]
        );
        assert!(slots(&BLOCK_ALIGNED_LAYOUT).is_empty());
    }

    #[test]
    fn a_layout_the_tables_cannot_describe_is_refused() {
        for layout in &LAYOUTS {
            assert!(layout.is_well_formed());
        }
        let page = L3_PAGE_SIZE;
        let broken = [
            ImageLayout {
                text_end: LAYOUT.text_end + 8,
                ..LAYOUT
            },
            ImageLayout {
                text_start: LAYOUT.text_start + 16,
                ..LAYOUT
            },
            ImageLayout {
                rodata_end: LAYOUT.rodata_end - 1,
                ..LAYOUT
            },
            ImageLayout {
                text_end: LAYOUT.text_start,
                ..LAYOUT
            },
            ImageLayout {
                rodata_end: LAYOUT.text_end - page,
                ..LAYOUT
            },
            ImageLayout {
                rodata_end: KERNEL_RESERVED_END + page,
                ..LAYOUT
            },
        ];
        for layout in broken {
            assert!(!layout.is_well_formed(), "{layout:#x?}");
        }
        // Read-only data may be empty; the text may reach the top exactly.
        assert!(ImageLayout {
            rodata_end: LAYOUT.text_end,
            ..LAYOUT
        }
        .is_well_formed());
        // The host has no link script: its layout is the empty one, refused, so
        // no host path builds tables from it.
        assert!(!image_layout().is_well_formed());
    }

    #[test]
    fn boot_cacheable_range_agrees_with_pointwise_mapping() {
        // `is_boot_cacheable_range` decides containment in one interval; pin it
        // against the pointwise reading it stands for.
        for &base in &[
            0u64,
            0x8_0000,
            LAYOUT.text_end,
            KERNEL_RESERVED_END - L2_BLOCK_SIZE,
            KERNEL_RESERVED_END - 1,
            KERNEL_RESERVED_END,
            L1_BLOCK_SIZE - 1,
            DEVICE_WINDOW_BASE,
            DEVICE_WINDOW_TOP,
        ] {
            for size in [1u64, 0x1000, L2_BLOCK_SIZE, L1_BLOCK_SIZE] {
                let expected = (0..size)
                    .step_by(0x1000)
                    .chain(core::iter::once(size - 1))
                    .all(|d: u64| {
                        base.checked_add(d)
                            .is_some_and(|a| boot_mapping_for(a, &LAYOUT).is_normal())
                    });
                assert_eq!(
                    is_boot_cacheable_range(base, size),
                    expected,
                    "range {base:#x}+{size:#x}"
                );
            }
        }
        // An empty range is vacuously contained; an overflowing one is refused.
        assert!(is_boot_cacheable_range(0x8_0000, 0));
        assert!(!is_boot_cacheable_range(u64::MAX - 3, 16));
    }

    #[test]
    fn a_range_that_runs_off_the_end_of_the_constant_window_is_refused() {
        // The relation a per-address check would miss: the first byte is
        // cacheable and the range is not.
        assert!(is_boot_cacheable_range(
            KERNEL_RESERVED_END - 0x1000,
            0x1000
        ));
        assert!(!is_boot_cacheable_range(
            KERNEL_RESERVED_END - 0x1000,
            0x2000
        ));
        // A range wholly inside the device window is not cacheable at all.
        assert!(!is_boot_cacheable_range(lean_mmio_window("uart").0, 0x1000));
    }

    #[test]
    fn tcr_epd1_disables_the_ttbr1_walk() {
        // No TTBR1 table exists, so the top half of the virtual address space
        // must fault rather than alias the TTBR0 identity map.
        assert_ne!(TCR_VALUE & (1 << 23), 0, "EPD1 must be set");
    }

    /// **WS-BP BP2.6**: the device tree's window is taken from the pointer
    /// alone and is exactly the bound its readers enforce.
    #[test]
    fn the_device_tree_window_is_the_readers_bound() {
        assert_eq!(dtb_window(0), (0, 0), "a null pointer reads nothing");
        let p = 0x0EFF_0000u64;
        assert_eq!(dtb_window(p), (p, crate::cmdline::MAX_DTB_SIZE as u64));
    }

    /// **WS-BP BP2.6 / BP3.2**: the window must lie in the kernel's reserved
    /// extent and outside the memory the image owns.  Each refused case keeps
    /// the window's size and moves it across exactly one of those edges.
    #[test]
    fn a_device_tree_window_outside_the_map_or_inside_the_image_is_refused() {
        let kernel = (0x8_0000u64, 0x440_0000u64);
        let kernel_end = kernel.0 + kernel.1;
        let size = crate::cmdline::MAX_DTB_SIZE as u64;
        // A null pointer reads nothing.
        assert!(dtb_window_admissible((0, 0), kernel));
        // Inside the reserved extent, touching the image's end (which is where
        // `link.ld`'s `.dtb_window` begins when nothing pads the heap -- WS-BP
        // BP5.3), and ending exactly at the reserved extent's end.
        for base in [0x0EFF_0000u64, kernel_end, KERNEL_RESERVED_END - size] {
            assert!(dtb_window_admissible((base, size), kernel), "{base:#x}");
        }
        // One byte into the image, straddling the reserved extent's end,
        // in first-gigabyte RAM a boot untyped may describe (the pre-BP3.2
        // admissible placement), straddling the first gigabyte's top, above
        // it, in the device window, and overflowing.
        for base in [
            kernel_end - 1,
            kernel.0 - 0x1000,
            KERNEL_RESERVED_END - size + 1,
            0x2EFF_0000,
            L1_BLOCK_SIZE - size + 1,
            0x8000_0000,
            DEVICE_WINDOW_BASE,
            u64::MAX - 4,
        ] {
            assert!(!dtb_window_admissible((base, size), kernel), "{base:#x}");
        }
    }

    /// **WS-BP BP2.1**: a device tree inside the image, its stacks or the
    /// Lean heap arena is refused; one beside them is not.
    #[test]
    fn a_device_tree_inside_the_image_or_the_arena_is_refused() {
        let image = [
            (0x8_0000u64, 0x1000u64),
            (0x8_1000, 0x1_0000),
            (0x9_1000, 0x3_0000),
            (0xC_2000, 0x400_0000),
        ];
        let arena_end = 0xC_2000 + 0x400_0000;
        for dtb in [
            (0x100u64, 0x2000u64),
            (arena_end, 0x1_0000),
            (0x2000_0000, 0x1_0000),
        ] {
            assert!(dtb_disjoint_from_image(dtb, &image), "{dtb:#x?}");
        }
        for dtb in [
            (0x100_0000u64, 0x1_0000u64),
            (0xC_1000, 0x2000),
            (0x9_2000, 0x40),
            (0x7_F000, 0x1001),
        ] {
            assert!(!dtb_disjoint_from_image(dtb, &image), "{dtb:#x?}");
        }
        assert!(dtb_disjoint_from_image((0, 0), &image));
        assert!(!dtb_disjoint_from_image((u64::MAX - 4, 0x10), &image));
    }

    /// **WS-BP BP3.2**: the reserved extent is one number in three places —
    /// this constant, the Lean `rpi5KernelReservedEnd` (read here out of the
    /// fixture the Lean suite writes), and `link.ld`'s `KERNEL_RESERVED_END`
    /// (read out of the script).  It is whole 2 MiB blocks of the first
    /// gigabyte, so the boot map describes it exactly and an extension past it
    /// starts on a block boundary.
    #[test]
    fn the_kernel_reserved_extent_is_the_lean_and_linker_one() {
        const LEAN_TABLE: &str = include_str!("../../../tests/fixtures/boot_map.expected");
        const LINK_SCRIPT: &str = include_str!("../link.ld");
        let lean: Vec<(u64, u64)> = LEAN_TABLE
            .lines()
            .filter_map(
                |l| match l.split_whitespace().collect::<Vec<_>>().as_slice() {
                    ["kernelReserved", base, end] => Some((
                        u64::from_str_radix(base.trim_start_matches("0x"), 16).expect("hex"),
                        u64::from_str_radix(end.trim_start_matches("0x"), 16).expect("hex"),
                    )),
                    _ => None,
                },
            )
            .collect();
        assert_eq!(
            lean,
            std::vec![(0, KERNEL_RESERVED_END)],
            "the Lean reserved extent"
        );
        let linker: Vec<u64> = LINK_SCRIPT
            .lines()
            .filter_map(|l| {
                let rest = l.trim().strip_prefix("KERNEL_RESERVED_END = ")?;
                let hex = rest.strip_suffix(';')?.trim_start_matches("0x");
                Some(u64::from_str_radix(hex, 16).expect("hex in link.ld"))
            })
            .collect();
        assert_eq!(
            linker,
            std::vec![KERNEL_RESERVED_END],
            "link.ld's reserved extent"
        );
    }

    /// **WS-BP BP5.3**: the window `link.ld` places the device tree in is
    /// exactly the extent a reader may dereference from its pointer
    /// ([`dtb_window`], [`crate::cmdline::MAX_DTB_SIZE`]).  A smaller window
    /// would let a reader leave it; a larger one would pin the firmware to a
    /// window whose tail no reader is bounded by.
    #[test]
    fn the_device_tree_window_is_the_dereference_bound() {
        const LINK_SCRIPT: &str = include_str!("../link.ld");
        let declared: Vec<u64> = LINK_SCRIPT
            .lines()
            .filter_map(|l| {
                let rest = l.trim().strip_prefix("DTB_WINDOW_SIZE = ")?;
                let hex = rest.strip_suffix(';')?.trim_start_matches("0x");
                Some(u64::from_str_radix(hex, 16).expect("hex in link.ld"))
            })
            .collect();
        assert_eq!(
            declared,
            std::vec![crate::cmdline::MAX_DTB_SIZE as u64],
            "link.ld's DTB_WINDOW_SIZE"
        );
        assert_eq!(dtb_window(0x1000).1, declared[0]);
    }

    /// **WS-BP BP7.10**: `link.ld`'s `RAM` region — the one memory region the
    /// linker may place the image in — ends exactly at the kernel's reserved
    /// extent, the constant Normal window, so no part of the image can be
    /// placed where the boot map does not reach.  Read out of the script
    /// rather than restated.
    #[test]
    fn the_linker_ram_region_is_the_constant_window() {
        const LINK_SCRIPT: &str = include_str!("../link.ld");
        let regions: Vec<(u64, u64)> = LINK_SCRIPT
            .lines()
            .filter_map(|l| {
                let rest = l.trim().strip_prefix("RAM (rwx) : ORIGIN = ")?;
                let (origin, length) = rest.split_once(", LENGTH = ")?;
                let parse = |h: &str| u64::from_str_radix(h.trim().trim_start_matches("0x"), 16);
                Some((parse(origin).ok()?, parse(length).ok()?))
            })
            .collect();
        assert_eq!(regions.len(), 1, "link.ld declares one RAM region");
        let (origin, length) = regions[0];
        assert_eq!(origin + length, KERNEL_RESERVED_END);
    }
}
