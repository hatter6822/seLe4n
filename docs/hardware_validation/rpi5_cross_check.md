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
| 1 | `gicDistributorBase` | `0xFF841000` | *pending* | PENDING | MMIO read GICD_IIDR at +0x008 |
| 2 | `gicCpuInterfaceBase` | `0xFF842000` | *pending* | PENDING | MMIO read GICC_IIDR at +0x0FC |
| 3 | `uart0Base` | `0xFE201000` | *pending* | PENDING | Serial write test char |
| 4 | `timerFrequencyHz` | `54000000` | *pending* | PENDING | MRS CNTFRQ_EL0 |
| 5 | `ramStart` | `0x00000000` | *pending* | PENDING | Memory read/write test |
| 6 | `ramEnd` | `0xFC000000` | *pending* | PENDING | Memory boundary probe |
| 7 | `peripheralStart` | `0xFE000000` | *pending* | PENDING | MMIO access test |
| 8 | `peripheralEnd` | `0xFF850000` | *pending* | PENDING | MMIO boundary probe |
| 9 | `gicSpiCount` | `192` | *pending* | PENDING | Read GICD_TYPER ITLinesNumber |
| 10 | `timerPpiId` | `30` | *pending* | PENDING | Timer interrupt fires on INTID 30 |
| 11 | `registerWidth` | `64` | 64 | VERIFIED | ARM64 architecture invariant |
| 12 | `virtualAddressWidth` | `48` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.PARange |
| 13 | `physicalAddressWidth` | `44` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.PARange |
| 14 | `pageSize` | `4096` | 4096 | VERIFIED | ARM64 4KiB granule (standard) |
| 15 | `maxASID` | `65536` | *pending* | PENDING | Read ID_AA64MMFR0_EL1.ASIDBits |

## Validation Script

Use `scripts/test_hw_crosscheck.sh` on physical RPi5 hardware to automate
these checks. The script reads hardware registers and compares against
Board.lean values.

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
