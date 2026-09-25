# AG9-B: RPi5 Hardware Constant Cross-Check Report

## Purpose

This document records the validation of all BCM2712 hardware constants
defined in `SeLe4n/Platform/RPi5/Board.lean` against actual Raspberry Pi 5
hardware. Each constant is verified by reading the corresponding hardware
register or memory region on a physical RPi5 board.

## Validation Method

Constants are verified using one of:
1. **Register read**: MRS instruction or MMIO read of the hardware register
2. **Memory probe**: Read/write test of the documented memory region
3. **Serial test**: UART character output verification on serial console
4. **Documentation cross-reference**: Verified against BCM2712 TRM / ARM ARM

## Validation Results

| # | Constant | Board.lean Value | Hardware Value | Status | Method |
|---|----------|-----------------|----------------|--------|--------|
| 1 | `gicDistributorBase` | `0x10_7FFF_9000` (BCM2712 GIC-400; `0xFF841000` was the BCM2711's until v0.36.2) | *pending* | PENDING | MMIO read GICD_IIDR at +0x008 |
| 2 | `gicCpuInterfaceBase` | `0x10_7FFF_A000` (`0xFF842000` until v0.36.2) | *pending* | PENDING | MMIO read GICC_IIDR at +0x0FC |
| 3 | `uart0Base` | `0x10_7D00_1000` (UART10, the debug header, 9.216 MHz; `0xFE201000` until v0.36.2) | *pending* | PENDING | Serial write test char |
| 4 | `timerFrequencyHz` | `54000000` | *pending* | PENDING | MRS CNTFRQ_EL0 |
| 5 | `rpi5MemoryMapForConfig` RAM | `[0, ramSize)` per variant (contiguous from 0 on the BCM2712; the `ramStart`/`ramEnd` pair with `ramEnd = 0xFC000000` was the BCM2711 map until v0.36.2) | *pending* | PENDING | Memory read/write test at both ends; compare the firmware's `/memory@0` account (see plan row BP7.10 — the account withholds the top of the first gigabyte) |
| 6 | `socPeripheralBase` / `socPeripheralSize` | `[0x10_7C00_0000, +64 MiB)` — the one device region (`peripheralStart`/`peripheralEnd` at `0xFE000000`/`0xFF850000` were the BCM2711's until v0.36.2) | *pending* | PENDING | MMIO access test at both ends of the window |
| 7 | `gicSpiCount` | `192` | *pending* | PENDING | Read GICD_TYPER ITLinesNumber |
| 8 | `timerPpiId` | `30` | *pending* | PENDING | Timer interrupt fires on INTID 30 |
| 9 | `registerWidth` | `64` | 64 | VERIFIED | ARM64 architecture invariant |
| 10 | `virtualAddressWidth` | `48` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.PARange |
| 11 | `physicalAddressWidth` | `44` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.PARange |
| 12 | `pageSize` | `4096` | 4096 | VERIFIED | ARM64 4KiB granule (standard) |
| 13 | `maxASID` | `65536` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.ASIDBits |

## Validation Script

Run `scripts/test_hw_crosscheck.sh` on physical RPi5 hardware to automate
available checks. The script currently validates:

- **Automated (PASS/FAIL)**: architecture (ARM64), physical address width
  (via `/proc/cpuinfo`), page size (via `getconf PAGESIZE`), timer frequency
  (via device tree `clock-frequency`).
- **Device tree probe**: GIC distributor node (`@ff841000`), UART0 node
  (`@fe201000`), virtual address width (from `/proc/kallsyms`).
- **Pending (bare-metal only)**: MMIO register reads (`devmem2`), GIC TYPER,
  PPI validation, ASID bits, peripheral boundaries.

Full MMIO validation requires the seLe4n kernel to boot on bare metal with
mapped device memory regions.

## Pre-Verified Constants

The following constants are verified by architecture specification:

- **registerWidth = 64**: ARM64 (AArch64) is a 64-bit architecture. All GPRs
  are 64-bit wide. This is an architecture invariant.

- **pageSize = 4096**: The default 4KiB page granule for ARMv8-A with 4KB
  granule configuration (TG0 = 0b00 in TCR_EL1).

## Notes

- All PENDING entries require physical RPi5 hardware access
- The validation script (`scripts/test_hw_crosscheck.sh`) can be run on the
  target board after booting the seLe4n kernel
- Discrepancies between Board.lean and hardware should be resolved by updating
  Board.lean with a rationale comment

## Hardware Environment

- **Board**: Raspberry Pi 5 (BCM2712)
- **CPU**: Cortex-A76 (4 cores @ 2.4 GHz)
- **RAM**: 4GB / 8GB model
- **Firmware**: RPi5 bootloader (standard load address 0x80000)
- **QEMU Model**: `raspi4b` (closest available, note: BCM2711 not BCM2712)

## Cross-Reference

- Board.lean: `SeLe4n/Platform/RPi5/Board.lean`
- Rust HAL constants: `rust/sele4n-hal/src/gic.rs`, `rust/sele4n-hal/src/timer.rs`
- ARM ARM: DDI 0487 (ARMv8-A Architecture Reference Manual)
- BCM2712 TRM: Broadcom BCM2712 Technical Reference Manual
