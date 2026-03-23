/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

/-!
# Raspberry Pi 5 — Board Definition (BCM2712)

Hardware constants for the Broadcom BCM2712 SoC used in the Raspberry Pi 5.
This module defines the physical memory map, peripheral base addresses, and
architectural parameters that platform contracts reference.

## References

- BCM2712 ARM Peripherals datasheet
- ARM Cortex-A76 Technical Reference Manual
- ARM Architecture Reference Manual (ARMv8-A)

## Status

H3-prep stub. Values are based on publicly available BCM2712 documentation.
Full register-level definitions will be added during the H3 platform-binding
workstream.
-/

namespace SeLe4n.Platform.RPi5

-- ============================================================================
-- BCM2712 physical address map
-- ============================================================================

/-- BCM2712 low-peripheral base address (legacy 32-bit peripheral window). -/
def peripheralBaseLow : SeLe4n.PAddr := ⟨0xFE000000⟩

/-- BCM2712 high-peripheral base address (new peripherals in BCM2712). -/
def peripheralBaseHigh : SeLe4n.PAddr := ⟨0x1000000000⟩

/-- GIC-400 distributor base address. -/
def gicDistributorBase : SeLe4n.PAddr := ⟨0xFF841000⟩

/-- GIC-400 CPU interface base address. -/
def gicCpuInterfaceBase : SeLe4n.PAddr := ⟨0xFF842000⟩

/-- ARM Generic Timer frequency (54 MHz crystal on RPi5). -/
def timerFrequencyHz : Nat := 54000000

/-- UART0 (PL011) base address for debug console. -/
def uart0Base : SeLe4n.PAddr := ⟨0xFE201000⟩

-- ============================================================================
-- RPi5 memory map
-- ============================================================================

/-- Standard Raspberry Pi 5 physical memory map (4 GB model).

    Regions are listed from low to high address:
    1. RAM: 0x0000_0000 – 0xFC00_0000 (4032 MiB usable before peripherals)
    2. GPU/VideoCore: 0xFC00_0000 – 0xFE00_0000 (32 MiB reserved for GPU firmware)
    3. Low peripherals: 0xFE00_0000 – 0xFF84_FFFF (legacy BCM2712 + GIC-400)
    4. Reserved: 0xFF85_0000 – 0xFFFF_FFFF (above GIC, to 4 GB boundary)
    5. High peripherals: 0x10_0000_0000+ (BCM2712-specific, not modeled yet) -/
def rpi5MemoryMap : List SeLe4n.MemoryRegion :=
  [ { base := ⟨0x00000000⟩
      size := 4032 * 1024 * 1024  -- 4032 MiB usable RAM
      kind := .ram }
  , { base := ⟨0xFC000000⟩
      size := 0x02000000  -- 32 MiB GPU/VideoCore firmware region
      kind := .reserved }
  , { base := ⟨0xFE000000⟩
      size := 0x01850000  -- ~24.3 MiB peripheral window (legacy + GIC-400)
      kind := .device }
  , { base := ⟨0xFF850000⟩
      size := 0x007B0000  -- reserved region above GIC to 4 GB boundary
      kind := .reserved }
  ]

-- ============================================================================
-- ARM64 architectural constants
-- ============================================================================

/-- ARMv8-A machine configuration for Raspberry Pi 5. -/
def rpi5MachineConfig : SeLe4n.MachineConfig :=
  {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 44   -- BCM2712 supports 44-bit PA
    pageSize := 4096             -- 4 KiB granule (standard)
    maxASID := 65536             -- 16-bit ASID with TTBR.ASID
    memoryMap := rpi5MemoryMap
  }

-- ============================================================================
-- GIC-400 IRQ constants
-- ============================================================================

/-- Number of shared peripheral interrupts (SPIs) on BCM2712 GIC-400. -/
def gicSpiCount : Nat := 192

/-- ARM Generic Timer PPI (Private Peripheral Interrupt) ID.
    Non-secure physical timer: INTID 30. -/
def timerPpiId : SeLe4n.Irq := ⟨30⟩

/-- ARM Generic Timer virtual timer PPI: INTID 27. -/
def virtualTimerPpiId : SeLe4n.Irq := ⟨27⟩

-- ============================================================================
-- WS-H15b/A-41: MMIO region definitions and disjointness
-- ============================================================================

/-- Known MMIO peripheral regions on BCM2712 that must not overlap with RAM.
    Each region covers a specific hardware peripheral's register space. -/
def mmioRegions : List SeLe4n.MemoryRegion :=
  [ { base := uart0Base,            size := 0x1000, kind := .device }  -- PL011 UART
  , { base := gicDistributorBase,   size := 0x1000, kind := .device }  -- GIC-400 distributor
  , { base := gicCpuInterfaceBase,  size := 0x2000, kind := .device }  -- GIC-400 CPU interface
  ]

/-- WS-H15b/A-41: Computable check that MMIO regions do not overlap with any
    RAM region in the RPi5 memory map. Returns `true` iff every MMIO-RAM pair
    is non-overlapping. -/
def mmioRegionDisjointCheck : Bool :=
  mmioRegions.all fun mmio =>
    rpi5MemoryMap.all fun ram =>
      ram.kind != .ram || !mmio.overlaps ram

/-- WS-H15b/A-41: Proof that RPi5 MMIO regions are disjoint from RAM. -/
theorem mmioRegionDisjoint_holds : mmioRegionDisjointCheck = true := by native_decide

/-- WS-H15b/A-41: The RPi5 machine configuration is well-formed: nonzero region
    sizes, no overlapping regions, power-of-two page size, positive widths,
    and all region end addresses fit within the 44-bit physical address space. -/
theorem rpi5MachineConfig_wellFormed : rpi5MachineConfig.wellFormed = true := by native_decide

/-!
## S5-F: BCM2712 Address Validation Checklist

**Pre-hardware-binding gate.** Before the H3 hardware binding workstream begins,
every address constant in this module must be cross-referenced against the
BCM2712 ARM Peripherals datasheet and ARM Cortex-A76 TRM. This checklist
tracks validation status.

| Constant | Expected Source | Datasheet Section | Validated? |
|----------|----------------|-------------------|------------|
| `peripheralBaseLow` (0xFE00_0000) | BCM2712 peripheral base | §1.2 Address Map | Pending |
| `peripheralBaseHigh` (0x10_0000_0000) | BCM2712 high-peripheral window | §1.2 Address Map | Pending |
| `gicDistributorBase` (0xFF84_1000) | GIC-400 distributor | §6.3 GIC-400 | Pending |
| `gicCpuInterfaceBase` (0xFF84_2000) | GIC-400 CPU interface | §6.3 GIC-400 | Pending |
| `timerFrequencyHz` (54 MHz) | ARM Generic Timer CNTFRQ_EL0 | Crystal spec | Pending |
| `uart0Base` (0xFE20_1000) | PL011 UART0 | §2.1 UART | Pending |
| `rpi5MemoryMap` RAM region (4032 MiB) | DRAM controller config | §1.2 Address Map | Pending |
| `rpi5MemoryMap` GPU region (32 MiB @ 0xFC00_0000) | VideoCore firmware reservation | GPU firmware | Pending |
| `rpi5MemoryMap` peripheral window (24.3 MiB) | Legacy peripheral range | §1.2 Address Map | Pending |
| `rpi5MachineConfig.physicalAddressWidth` (44-bit) | BCM2712 PA width | §1.1 Overview | Pending |
| `gicSpiCount` (192) | GIC-400 SPI count | §6.3 GIC-400 | Pending |
| `timerPpiId` (INTID 30) | NS physical timer PPI | ARM GIC spec | Pending |
| `virtualTimerPpiId` (INTID 27) | Virtual timer PPI | ARM GIC spec | Pending |
| `mmioRegions` (3 regions) | UART + GIC register spaces | §2.1, §6.3 | Pending |

**Process**: For each constant, record the exact datasheet reference (document
title, revision, page number) and the value found. Mark "Validated" only when
the model value matches the datasheet. Discrepancies must be resolved before
H3 proceeds.

**Automated verification**: `rpi5MachineConfig_wellFormed` (above) proves
structural well-formedness (non-overlap, valid sizes, PA width bounds) via
`native_decide`. This does not validate against the datasheet — it only
ensures internal consistency of the declared values.
-/

end SeLe4n.Platform.RPi5
