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

end SeLe4n.Platform.RPi5
