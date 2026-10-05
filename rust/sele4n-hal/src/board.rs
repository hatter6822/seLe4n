// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-BP BP8.1**: the board an image is built for.
//!
//! The HAL describes one machine at a time, chosen at build time: the
//! Raspberry Pi 5 (BCM2712) by default, QEMU's `virt` machine under the
//! `board_qemu_virt` feature.  QEMU ships no BCM2712 model, and `virt` is the
//! only machine it has that carries what the boot path needs — PSCI, a GICv2
//! and a PL011 — so a boot under QEMU runs an image whose device map is
//! `virt`'s rather than an RPi5 image that meets no device.
//!
//! Every board-dependent constant the boot path reads is a field of
//! [`BoardMap`] and nowhere else: the RAM the kernel's reserved extent sits at
//! the base of, the device window, the console and the interrupt controller.
//! The modules that used to carry them as literals (`mmu`, `uart`, `gic`) read
//! them off [`BOARD`], so a third board is one more `BoardMap`, never an edit
//! to a module that consumes one.
//!
//! What does **not** vary, and is asserted rather than assumed: the reserved
//! extent is whole 2 MiB blocks at the base of a gigabyte-aligned RAM, inside
//! that gigabyte, and the device window is whole 2 MiB blocks inside a
//! different gigabyte — the two level-2 tables the boot map describes them
//! with (`mmu::BootPageTables`).  The image is linked 512 KiB above the RAM
//! base on every board (`link.ld`'s `ORIGIN`), which is the offset the arm64
//! Image header in `boot.S` declares.

/// One board's physical address map, as the boot path reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoardMap {
    /// The board's name, as the boot banner prints it.
    pub name: &'static str,
    /// The first byte of RAM, and of the kernel's reserved extent.
    pub ram_base: u64,
    /// One past the kernel's reserved extent: the image, its stacks, the Lean
    /// heap, the device tree's window and the boot table pool all lie in
    /// `[ram_base, kernel_reserved_end)`.
    pub kernel_reserved_end: u64,
    /// First byte of the device window the boot map maps Device.
    pub device_window_base: u64,
    /// One past the device window.
    pub device_window_top: u64,
    /// The PL011 console's register block.
    pub uart_base: usize,
    /// The PL011's reference clock, in Hz.
    pub uart_clock_hz: u32,
    /// The GICv2 distributor.
    pub gicd_base: usize,
    /// The GICv2 CPU interface.
    pub gicc_base: usize,
    /// The interrupt lines the board's distributor implements and the kernel
    /// serves: INTIDs `[0, gic_intid_count)`, the 32 private ones and every
    /// SPI the board wires, in whole 32-line banks.  `gic::init_gic` refuses
    /// a distributor whose `GICD_TYPER.ITLinesNumber` reports fewer, and
    /// programs exactly these.  The Lean binding states the same count
    /// (`tests/fixtures/boot_map.expected`'s `gicIntIds` line).
    pub gic_intid_count: u32,
}

/// The Raspberry Pi 5 (BCM2712): DRAM contiguous from 0, UART10 and the
/// GIC-400 inside the SoC-bus window at `0x10_7C00_0000`
/// (`SeLe4n/Platform/RPi5/Board.lean`, held to these numbers by
/// `tests/fixtures/boot_map.expected`).  UART10's clock is `bcm2712.dtsi`'s
/// fixed `clk_uart`, 9.216 MHz — exactly `16 × 115200 × 5`, so the
/// 115200-baud divisor is `IBRD = 5, FBRD = 0` with no rounding error.
/// The GIC-400 carries 288 SPIs (320 INTIDs): `bcm2712.dtsi` wires devices
/// up to `GIC_SPI 276` (UARTA), rounded up to whole banks (Board.lean
/// `gicSpiCount`).
pub const RPI5: BoardMap = BoardMap {
    name: "Raspberry Pi 5 (BCM2712)",
    ram_base: 0x0,
    kernel_reserved_end: 0x1000_0000,
    device_window_base: 0x10_7C00_0000,
    device_window_top: 0x10_8000_0000,
    uart_base: 0x10_7D00_1000,
    uart_clock_hz: 9_216_000,
    gicd_base: 0x10_7FFF_9000,
    gicc_base: 0x10_7FFF_A000,
    gic_intid_count: 320,
};

/// QEMU's `virt` machine (`hw/arm/virt.c`, `base_memmap`): RAM from
/// `0x4000_0000`, the GICv2 distributor at `0x0800_0000` and its CPU
/// interface at `0x0801_0000` (run with `gic-version=2`), and the PL011 at
/// `0x0900_0000` on a 24 MHz `apb-pclk`.  The device window is the 32 MiB
/// `[0x0800_0000, 0x0A00_0000)` holding both, whole 2 MiB blocks in the
/// gigabyte below RAM.  The reserved extent is the same 256 MiB the RPi5
/// reserves, at the base of `virt`'s RAM.  QEMU's `NUM_IRQS` is 256, so the
/// GICv2 carries 288 INTIDs (`num-irq = NUM_IRQS + 32`).
pub const QEMU_VIRT: BoardMap = BoardMap {
    name: "QEMU virt (GICv2, PL011)",
    ram_base: 0x4000_0000,
    kernel_reserved_end: 0x5000_0000,
    device_window_base: 0x0800_0000,
    device_window_top: 0x0A00_0000,
    uart_base: 0x0900_0000,
    uart_clock_hz: 24_000_000,
    gicd_base: 0x0800_0000,
    gicc_base: 0x0801_0000,
    gic_intid_count: 288,
};

/// The board this image is built for.
#[cfg(not(feature = "board_qemu_virt"))]
pub const BOARD: BoardMap = RPI5;

/// The board this image is built for.
#[cfg(feature = "board_qemu_virt")]
pub const BOARD: BoardMap = QEMU_VIRT;

/// Bytes one level-1 entry spans (1 GiB).
const GIB: u64 = 1 << 30;

/// Bytes one level-2 block spans (2 MiB).
const L2_BLOCK: u64 = 1 << 21;

/// The shape every board's map must have for the boot tables to describe it —
/// decided by the compiler for both boards, so a board that breaks it fails
/// every build rather than only its own.
const fn well_formed(b: &BoardMap) -> bool {
    let ram_gib = b.ram_base / GIB;
    let device_gib = b.device_window_base / GIB;
    b.ram_base.is_multiple_of(GIB)
        && b.kernel_reserved_end > b.ram_base
        && b.kernel_reserved_end - b.ram_base <= GIB
        && b.kernel_reserved_end.is_multiple_of(L2_BLOCK)
        && b.device_window_base.is_multiple_of(L2_BLOCK)
        && b.device_window_top.is_multiple_of(L2_BLOCK)
        && b.device_window_base < b.device_window_top
        && b.device_window_top <= (device_gib + 1) * GIB
        && device_gib != ram_gib
        && (b.uart_base as u64) >= b.device_window_base
        && (b.uart_base as u64) < b.device_window_top
        && (b.gicd_base as u64) >= b.device_window_base
        && (b.gicd_base as u64) < b.device_window_top
        && (b.gicc_base as u64) >= b.device_window_base
        && (b.gicc_base as u64) < b.device_window_top
        && b.uart_clock_hz > 0
        && b.gic_intid_count > 32
        && b.gic_intid_count.is_multiple_of(32)
        && b.gic_intid_count <= crate::gic::MAX_SUPPORTED_INTID
}

const _: () = assert!(well_formed(&RPI5));
const _: () = assert!(well_formed(&QEMU_VIRT));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_default_board_is_the_raspberry_pi_5() {
        #[cfg(not(feature = "board_qemu_virt"))]
        assert_eq!(BOARD, RPI5);
    }

    #[test]
    fn a_board_whose_device_window_shares_the_ram_gigabyte_is_refused() {
        let bad = BoardMap {
            device_window_base: 0x5000_0000,
            device_window_top: 0x5200_0000,
            uart_base: 0x5000_1000,
            gicd_base: 0x5000_2000,
            gicc_base: 0x5000_3000,
            ..QEMU_VIRT
        };
        assert!(!well_formed(&bad));
        assert!(well_formed(&QEMU_VIRT));
    }

    #[test]
    fn a_reserved_extent_leaving_its_gigabyte_is_refused() {
        let bad = BoardMap {
            kernel_reserved_end: 0x8020_0000,
            ..QEMU_VIRT
        };
        assert!(!well_formed(&bad));
    }

    #[test]
    fn an_interrupt_line_count_outside_whole_banks_or_the_model_is_refused() {
        // A partial bank, the private lines alone, and more lines than the
        // model's `InterruptId` admits (`gic::MAX_SUPPORTED_INTID`) are each
        // refused; every board's own count is admitted.
        for count in [0, 32, 300, crate::gic::MAX_SUPPORTED_INTID + 32] {
            let bad = BoardMap {
                gic_intid_count: count,
                ..RPI5
            };
            assert!(!well_formed(&bad), "{count} interrupt lines admitted");
        }
        assert!(well_formed(&RPI5));
        assert!(well_formed(&QEMU_VIRT));
    }
}
