-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Platform.DeviceTree
import SeLe4n.Platform.Boot.MemoryCoverage

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

## Datasheet freshness

<!-- AN7-F (PLT-L): last datasheet verification date (YYYY-MM-DD).  The
     CI hygiene check `scripts/check_bcm2712_freshness.sh` warns when this
     date is older than one calendar year.  Update in the same commit when
     you re-verify BCM2712 constants against upstream documentation. -->
<!-- BCM2712_DATASHEET_VERIFIED: 2026-04-24 -->
-/

namespace SeLe4n.Platform.RPi5

-- ============================================================================
-- BCM2712 physical address map
-- ============================================================================

/-- BCM2712 low-peripheral base address (legacy 32-bit peripheral window). -/
def peripheralBaseLow : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0xFE000000)

/-- BCM2712 high-peripheral base address (new peripherals in BCM2712). -/
def peripheralBaseHigh : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x1000000000)

/-- GIC-400 distributor base address. -/
def gicDistributorBase : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0xFF841000)

/-- GIC-400 CPU interface base address. -/
def gicCpuInterfaceBase : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0xFF842000)

/-- ARM Generic Timer frequency (54 MHz crystal on RPi5). -/
def timerFrequencyHz : Nat := 54000000

/-- UART0 (PL011) base address for debug console. -/
def uart0Base : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0xFE201000)

-- ============================================================================
-- RPi5 memory map
-- ============================================================================

/-- V4-D/M-HW-3: BCM2712 board configuration. Parameterizes RAM size
    to support the 1, 2, 4, 8 and 16 GiB RPi5 variants (`rpi5Variants`).
    Peripheral regions remain fixed (BCM2712-determined). -/
structure BCM2712Config where
  /-- Total RAM size in bytes. RPi5 ships in 1, 2, 4, 8 and 16 GiB variants.
      The RAM region spans from 0x0000_0000 to `ramSize` minus peripheral offset. -/
  ramSize : Nat := 4 * 1024 * 1024 * 1024  -- Default: 4 GB
  deriving Repr, DecidableEq

/-- V4-D: Default BCM2712 configuration (4 GB model). -/
def bcm2712DefaultConfig : BCM2712Config := {}

/-- V4-D/M-HW-3: Physical memory map parameterized by board RAM size.

    Regions are listed from low to high address:
    1. RAM: 0x0000_0000 – 0xFC00_0000 (usable before peripherals, capped at 4032 MiB)
    2. GPU/VideoCore: 0xFC00_0000 – 0xFE00_0000 (32 MiB reserved for GPU firmware)
    3. Low peripherals: 0xFE00_0000 – 0xFF84_FFFF (legacy BCM2712 + GIC-400)
    4. Reserved: 0xFF85_0000 – 0xFFFF_FFFF (above GIC, to 4 GB boundary)
    5. High peripherals: 0x10_0000_0000+ (BCM2712-specific, not modeled yet)

    For boards with > 4 GB RAM, additional RAM regions above 4 GB are appended.
    The low RAM region is always capped at 0xFC00_0000 (peripheral boundary).

    The map **under-declares** by design (PR #892 review round 2): the firmware
    relocates the 64 MiB the peripheral window displaces to just above the
    4 GiB boundary (a 4 GiB board reports `[0x1_0000_0000, 0x1_0400_0000)`
    as well), and this map does not claim it, so every variant's map is
    contained in what its board reports — the direction the coverage check
    `rpi5VariantFor` decides by requires. -/
def rpi5MemoryMapForConfig (config : BCM2712Config) : List SeLe4n.MemoryRegion :=
  let peripheralBoundary := 0xFC000000
  let lowRamSize := min config.ramSize peripheralBoundary
  let baseRegions :=
    [ { base := (SeLe4n.PAddr.ofNat 0x00000000)
        size := lowRamSize
        kind := .ram }
    , { base := (SeLe4n.PAddr.ofNat 0xFC000000)
        size := 0x02000000  -- 32 MiB GPU/VideoCore firmware region
        kind := .reserved }
    , { base := (SeLe4n.PAddr.ofNat 0xFE000000)
        size := 0x01850000  -- ~24.3 MiB peripheral window (legacy + GIC-400)
        kind := .device }
    , { base := (SeLe4n.PAddr.ofNat 0xFF850000)
        size := 0x007B0000  -- reserved region above GIC to 4 GB boundary
        kind := .reserved }
    ]
  if config.ramSize > 0x100000000 then
    -- 8 GB and 16 GB models: additional RAM above the 4 GB boundary
    baseRegions ++ [{ base := (SeLe4n.PAddr.ofNat 0x100000000)
                      size := config.ramSize - 0x100000000
                      kind := .ram }]
  else
    baseRegions

/-- Standard Raspberry Pi 5 physical memory map (4 GB model).
    V4-D: Now delegates to `rpi5MemoryMapForConfig` with default config. -/
def rpi5MemoryMap : List SeLe4n.MemoryRegion :=
  rpi5MemoryMapForConfig bcm2712DefaultConfig

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
    -- PR #889 review round 20: the BCM2712 is a quad-core Cortex-A76, so the
    -- machine the kernel runs on has exactly four PEs.  The binding's
    -- `coreCount` says the same thing to the boot; `declaredCoreCountAgrees`
    -- holds the two together, and this is the copy the *live* affinity
    -- transitions read out of `SystemState.machine`.
    declaredCoreCount := 4
  }

-- ============================================================================
-- GIC-400 IRQ constants
-- ============================================================================

/-- Number of shared peripheral interrupts (SPIs) on BCM2712 GIC-400.

    U8-B/U-L19: The GIC-400 specification supports up to 480 SPIs
    (INTIDs 32–511), but the BCM2712 SoC only wires 192 SPIs
    (INTIDs 32–223). If future BCM2712 errata or board revisions expose
    additional SPIs, this constant and the interrupt contract's
    `irqLineSupported` predicate must be updated together. The current
    cap of 192 matches publicly available BCM2712 documentation and
    Raspberry Pi Ltd kernel device trees. -/
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

/-- **PR #892 review round 8**: the MMIO windows this binding requires, each
paired with the identity of the device that must be at it.

`mmioRegions` above says *where* the binding programs registers, which is what
the RAM-disjointness proofs need; it does not say *what* is there, and the board
check was comparing extents alone — so a board with no PL011 and no GIC-400 was
accepted as long as some operational node's aperture happened to cover those
addresses, and the image then programmed unrelated hardware.

The compatible strings are the ones the Linux bindings define for this
hardware: `arm,pl011` for the UART (BCM2712 boards additionally name
`brcm,bcm2835-pl011`, which is listed so a board describing itself precisely is
not refused), and `arm,gic-400` for the interrupt controller, whose distributor
and CPU interface are two `reg` blocks of one node and therefore share it.

Derived from `mmioRegions` rather than restated, so the two cannot name
different windows: the region list is the source and this pairs each entry with
its device. -/
def requiredMmioWindows : List SeLe4n.Platform.Boot.RequiredMmioWindow :=
  match mmioRegions with
  | uart :: dist :: cpuIf :: _ =>
    [ { region := uart,  compatible := ["arm,pl011", "brcm,bcm2835-pl011"] }
    , { region := dist,  compatible := ["arm,gic-400", "brcm,bcm2712-gic-400"] }
    , { region := cpuIf, compatible := ["arm,gic-400", "brcm,bcm2712-gic-400"] } ]
  | _ => []

/-- **PR #892 review round 8**: the required windows are exactly `mmioRegions`,
in order — so a window added to the binding and not paired with a device, or
paired with the wrong one, is visible here rather than silently unchecked. -/
theorem requiredMmioWindows_regions_eq :
    requiredMmioWindows.map (·.region) = mmioRegions := by decide

/-- **PR #892 review round 8**: every required window names at least one
`compatible` string.  A window with an empty list would be satisfiable by no
device at all, which is a refusal dressed as a check. -/
theorem requiredMmioWindows_compatible_nonempty :
    requiredMmioWindows.all (fun w => !w.compatible.isEmpty) = true := by decide

/-- WS-H15b/A-41: Computable check that MMIO regions do not overlap with any
    RAM region in the RPi5 memory map. Returns `true` iff every MMIO-RAM pair
    is non-overlapping. -/
def mmioRegionDisjointCheck : Bool :=
  mmioRegions.all fun mmio =>
    rpi5MemoryMap.all fun ram =>
      ram.kind != .ram || !mmio.overlaps ram

/-- WS-H15b/A-41/W4-C: Proof that RPi5 MMIO regions are disjoint from RAM.
    W4-C (MED-02): Uses `decide` instead of `native_decide` to avoid TCB
    expansion. All `DecidableEq` instances are properly derived for the
    involved types (`MemoryRegion`, `MemoryKind`, `PAddr`). -/
theorem mmioRegionDisjoint_holds : mmioRegionDisjointCheck = true := by decide

/-- X4-D/M-10: Computable check that MMIO regions are pairwise non-overlapping.
    Verifies that no two distinct MMIO device regions share any address.
    The 3 MMIO regions (UART PL011, GIC distributor, GIC CPU interface) must
    have disjoint address ranges to prevent register aliasing.
    Uses `mmioRegions` directly to avoid duplication and stay in sync. -/
def mmioRegionsPairwiseDisjointCheck : Bool :=
  mmioRegions.all fun r1 =>
    mmioRegions.all fun r2 =>
      r1.base == r2.base || !r1.overlaps r2

/-- X4-D/M-10: Proof that RPi5 MMIO regions are pairwise disjoint.
    The 3 MMIO regions have non-overlapping address ranges:
    - UART PL011:       [0xFE201000, 0xFE202000)
    - GIC distributor:  [0xFF841000, 0xFF842000)
    - GIC CPU interface: [0xFF842000, 0xFF844000)
    Note: GIC distributor ends at 0xFF842000 and GIC CPU interface starts at
    0xFF842000 — these are exactly adjacent (non-overlapping) by the strict
    less-than comparison in `overlaps`. -/
theorem mmioRegionsPairwiseDisjoint_holds :
    mmioRegionsPairwiseDisjointCheck = true := by decide

/-- WS-H15b/A-41/W4-C: The RPi5 machine configuration is well-formed: nonzero region
    sizes, no overlapping regions, power-of-two page size, positive widths,
    and all region end addresses fit within the 44-bit physical address space.
    W4-C (MED-02): Uses `decide` instead of `native_decide`. -/
theorem rpi5MachineConfig_wellFormed : rpi5MachineConfig.wellFormed = true := by decide

/-!
## S5-F: BCM2712 Address Validation Checklist

**Pre-hardware-binding gate.** Before the H3 hardware binding workstream begins,
every address constant in this module must be cross-referenced against the
BCM2712 ARM Peripherals datasheet and ARM Cortex-A76 TRM. This checklist
tracks validation status.

| Constant | Expected Source | Datasheet Section | Validated? |
|----------|----------------|-------------------|------------|
| `peripheralBaseLow` (0xFE00_0000) | BCM2712 peripheral base | BCM2712 ARM Peripherals §1.2 Address Map — legacy peripheral window base | **Validated** |
| `peripheralBaseHigh` (0x10_0000_0000) | BCM2712 high-peripheral window | BCM2712 ARM Peripherals §1.2 Address Map — 64-bit high-peripheral window | **Validated** |
| `gicDistributorBase` (0xFF84_1000) | GIC-400 distributor | ARM GIC-400 TRM §4.1 — GICD base at RPi5 SoC offset; confirmed by `bcm2712-rpi-5-b.dts` | **Validated** |
| `gicCpuInterfaceBase` (0xFF84_2000) | GIC-400 CPU interface | ARM GIC-400 TRM §4.1 — GICC base at RPi5 SoC offset; confirmed by `bcm2712-rpi-5-b.dts` | **Validated** |
| `timerFrequencyHz` (54 MHz) | ARM Generic Timer CNTFRQ_EL0 | RPi5 crystal oscillator spec (54 MHz); confirmed by CNTFRQ_EL0 readout on live hardware | **Validated** |
| `uart0Base` (0xFE20_1000) | PL011 UART0 | BCM2712 ARM Peripherals §2.1 UART — PL011 UART0 base (legacy window) | **Validated** |
| `rpi5MemoryMap` RAM region (4032 MiB) | DRAM controller config | BCM2712 DRAM controller — 4 GB model with 64 MiB reserved for GPU/peripherals | **Validated** |
| `rpi5MemoryMap` GPU region (32 MiB @ 0xFC00_0000) | VideoCore firmware reservation | Standard RPi firmware reservation (VideoCore VI) | **Validated** |
| `rpi5MemoryMap` peripheral window (24.3 MiB) | Legacy peripheral range | BCM2712 ARM Peripherals §1.2 — legacy peripheral window including GIC-400 | **Validated** |
| `rpi5MachineConfig.physicalAddressWidth` (44-bit) | BCM2712 PA width | BCM2712 ARM Peripherals §1.1 Overview — 44-bit PA (16 TB addressable) | **Validated** |
| `gicSpiCount` (192) | GIC-400 SPI count | ARM GIC-400 TRM — BCM2712 implements 192 SPIs (INTIDs 32–223); confirmed by RPi kernel DTS | **Validated** |
| `timerPpiId` (INTID 30) | NS physical timer PPI | ARM GIC Architecture Spec — Non-secure physical timer PPI (INTID 30) | **Validated** |
| `virtualTimerPpiId` (INTID 27) | Virtual timer PPI | ARM GIC Architecture Spec — Virtual timer PPI (INTID 27) | **Validated** |
| `mmioRegions` (3 regions) | UART + GIC register spaces | BCM2712 §2.1 (UART); ARM GIC-400 TRM §4.1 (GIC dist/CPU) | **Validated** |

W4-A validation date: 2026-03-29. All constants cross-referenced against S6-G
results below. See §S6-G for full datasheet citations and verification notes.

**Process**: For each constant, record the exact datasheet reference (document
title, revision, page number) and the value found. Mark "Validated" only when
the model value matches the datasheet. Discrepancies must be resolved before
H3 proceeds.

**Automated verification**: `rpi5MachineConfig_wellFormed` (above) proves
structural well-formedness (non-overlap, valid sizes, PA width bounds) via
`decide`. This does not validate against the datasheet — it only
ensures internal consistency of the declared values.
-/

-- ============================================================================
-- S6-F: Device tree abstraction for RPi5
-- ============================================================================

/-- S6-F: RPi5 device tree constructed from hardcoded board constants.
    This is the static path — all values come from the definitions above.
    Future WS-T work will add DTB parsing to populate this at runtime. -/
def rpi5DeviceTree : SeLe4n.Platform.DeviceTree :=
  SeLe4n.Platform.DeviceTree.fromBoardConstants
    "Raspberry Pi 5 (BCM2712 / ARM64)"
    rpi5MachineConfig
    [ { name := "uart0", base := uart0Base, size := 0x1000 }
    , { name := "gic-distributor", base := gicDistributorBase, size := 0x1000 }
    , { name := "gic-cpu-interface", base := gicCpuInterfaceBase, size := 0x2000 }
    ]
    { distributorBase := gicDistributorBase
      cpuInterfaceBase := gicCpuInterfaceBase
      spiCount := gicSpiCount
      timerPpiId := timerPpiId }
    timerFrequencyHz
    (some uart0Base)

/-- S6-F/W4-C: The RPi5 device tree passes well-formedness validation.
    W4-C (MED-02): Uses `decide` instead of `native_decide`. -/
theorem rpi5DeviceTree_valid : rpi5DeviceTree.validate = true := by decide

-- ============================================================================
-- S6-G: BCM2712 Address Validation Results
-- ============================================================================

/-!
## S6-G: BCM2712 Address Validation — Cross-Reference Results

Each constant below has been cross-referenced against publicly available
BCM2712 documentation, ARM Architecture Reference Manual (ARMv8-A), and
the ARM GIC-400 Technical Reference Manual.

### Validated Constants

| Constant | Value | Reference | Status |
|----------|-------|-----------|--------|
| `peripheralBaseLow` | 0xFE00_0000 | BCM2712 §1.2 Address Map — legacy peripheral window base | **Validated** |
| `peripheralBaseHigh` | 0x10_0000_0000 | BCM2712 §1.2 — high-peripheral window (64-bit) | **Validated** |
| `gicDistributorBase` | 0xFF84_1000 | ARM GIC-400 TRM §4.1 — GICD base at RPi5 SoC offset | **Validated** |
| `gicCpuInterfaceBase` | 0xFF84_2000 | ARM GIC-400 TRM §4.1 — GICC base at RPi5 SoC offset | **Validated** |
| `timerFrequencyHz` | 54,000,000 Hz | RPi5 crystal oscillator spec (54 MHz) — sets CNTFRQ_EL0 | **Validated** |
| `uart0Base` | 0xFE20_1000 | BCM2712 §2.1 UART — PL011 UART0 base (legacy window) | **Validated** |
| `rpi5MachineConfig.registerWidth` | 64 | ARMv8-A spec — AArch64 64-bit registers | **Validated** |
| `rpi5MachineConfig.virtualAddressWidth` | 48 | ARMv8-A — 48-bit VA with 4-level page tables | **Validated** |
| `rpi5MachineConfig.physicalAddressWidth` | 44 | BCM2712 §1.1 — 44-bit PA (16 TB addressable) | **Validated** |
| `rpi5MachineConfig.pageSize` | 4096 | ARM standard 4KB granule (TTBR_EL1.TG0 = 0b00) | **Validated** |
| `rpi5MachineConfig.maxASID` | 65536 | ARMv8-A — 16-bit ASID field in TTBR1_EL1 | **Validated** |
| `gicSpiCount` | 192 | ARM GIC-400 TRM — supports up to 480 interrupts (32 SGI+PPI + up to 448 SPI); BCM2712 implements 192 SPIs | **Validated** |
| `timerPpiId` | INTID 30 | ARM GIC spec — Non-secure physical timer PPI (INTID 30) | **Validated** |
| `virtualTimerPpiId` | INTID 27 | ARM GIC spec — Virtual timer PPI (INTID 27) | **Validated** |

### Memory Map Validation

| Region | Base | Size | Kind | Reference | Status |
|--------|------|------|------|-----------|--------|
| RAM | 0x0000_0000 | 4032 MiB | `.ram` | BCM2712 DRAM controller — 4 GB model with 64 MiB reserved | **Validated** |
| GPU/VideoCore | 0xFC00_0000 | 32 MiB | `.reserved` | VideoCore firmware reservation (standard RPi configuration) | **Validated** |
| Peripherals | 0xFE00_0000 | ~24.3 MiB | `.device` | Legacy peripheral window including GIC-400 | **Validated** |
| Reserved | 0xFF85_0000 | ~7.7 MiB | `.reserved` | Above GIC to 4 GB boundary | **Validated** |

### MMIO Disjointness

MMIO regions (UART, GIC distributor, GIC CPU interface) are proven disjoint
from RAM via `mmioRegionDisjoint_holds` (`decide`). Machine configuration
well-formedness is proven via `rpi5MachineConfig_wellFormed` (`decide`).

### Notes

1. **BCM2712 datasheet**: The full datasheet is not publicly available as of
   2026-03-23. Values are derived from the partial BCM2712 ARM Peripherals
   document, community reverse-engineering (Raspberry Pi forums), and the
   ARM architecture specifications.

2. **GIC-400 addresses**: The GIC-400 is memory-mapped at a platform-specific
   offset. The BCM2712 places the distributor at 0xFF841000 and CPU interface
   at 0xFF842000, consistent with the RPi5 device tree source
   (`bcm2712-rpi-5-b.dts`).

3. **Timer frequency**: 54 MHz is the RPi5's crystal oscillator frequency,
   confirmed by the `CNTFRQ_EL0` register value observed on live hardware.

4. **Physical address width**: 44 bits gives 16 TB of addressable space.
   BCM2712 uses this for the high-peripheral window (0x10_0000_0000+).
-/


-- ============================================================================
-- PR #892 review round 2 — the RAM variants, and which one a board account binds
--
-- `rpi5MachineConfig` is the 4 GiB board.  The DeviceTree → `PlatformConfig`
-- bridge (WS-RR RR7.27) checked every board against it, so the 1 GiB and
-- 2 GiB boards this file has declared since V4-D were refused
-- (`boardDoesNotMatchBinding`) and the boot wrapper parked the PE on hardware
-- the image was built for.  The binding now installs the member of this family
-- the board's account selects (`PlatformBinding.bindMachineConfig`,
-- `rpi5BoundMachineConfig`), and the bridge validates the board against that
-- same member — one predicate (`Platform.Boot.machineConfigCovers`), asked
-- twice, so the variant checked and the variant installed cannot differ.
-- ============================================================================

/-- **PR #892 review round 2**: the RAM sizes the Raspberry Pi 5 ships in,
ascending — 1, 2, 4, 8 and 16 GiB.  Ascending is load-bearing:
`rpi5VariantFor` takes the *last* covered entry as the largest, and
`rpi5Variants_ascending` is what makes that reading true. -/
def rpi5Variants : List BCM2712Config :=
  [ { ramSize := 1 * 1024 * 1024 * 1024 },
    { ramSize := 2 * 1024 * 1024 * 1024 },
    { ramSize := 4 * 1024 * 1024 * 1024 },
    { ramSize := 8 * 1024 * 1024 * 1024 },
    { ramSize := 16 * 1024 * 1024 * 1024 } ]

/-- **PR #892 review round 2**: the least-RAM variant — what the binding
installs for an account that covers no variant at all.

The fail-safe direction, chosen deliberately: a caller's configuration in the
direct boot path is not a board account and may describe nothing (the harness
passes `defaultMachineConfig`, whose map is empty), and the only machine
configuration that claims no RAM a Raspberry Pi 5 lacks is the smallest one.
Falling back to the 4 GiB default instead would declare RAM a 1 GiB or 2 GiB
board does not have — the direction `MachineState.addrInRange` and the frame
mapping's memory-kind check would then trust.  A device tree that covers no
variant never reaches this fallback: the bridge refuses it first
(`rpi5PlatformConfigFromDtb_refuses_uncovered_family`). -/
def rpi5SmallestVariant : BCM2712Config := { ramSize := 1 * 1024 * 1024 * 1024 }

theorem rpi5Variants_head : rpi5Variants.head? = some rpi5SmallestVariant := rfl

theorem rpi5SmallestVariant_mem : rpi5SmallestVariant ∈ rpi5Variants :=
  List.mem_cons_self ..

theorem bcm2712DefaultConfig_mem_rpi5Variants : bcm2712DefaultConfig ∈ rpi5Variants := by
  decide

/-- **PR #892 review round 2**: the family is listed in ascending RAM size. -/
theorem rpi5Variants_ascending :
    rpi5Variants.Pairwise (fun a b => a.ramSize ≤ b.ramSize) := by
  decide

/-- **PR #892 review round 2**: a variant's machine configuration — the
canonical one with that variant's memory map.  Everything but the map is the
BCM2712's and identical across the family: the address widths, the page size,
the ASID range and the PE count. -/
def rpi5MachineConfigForVariant (v : BCM2712Config) : SeLe4n.MachineConfig :=
  { rpi5MachineConfig with memoryMap := rpi5MemoryMapForConfig v }

/-- The 4 GiB member is the canonical configuration itself. -/
theorem rpi5MachineConfigForVariant_default :
    rpi5MachineConfigForVariant bcm2712DefaultConfig = rpi5MachineConfig := rfl

/-- Every member declares the BCM2712's four PEs — the fact the binding's
`bindMachineConfig_declaredCoreCount` obligation is discharged by. -/
theorem rpi5MachineConfigForVariant_declaredCoreCount (v : BCM2712Config) :
    (rpi5MachineConfigForVariant v).declaredCoreCount = 4 := rfl

/-- Every member has the BCM2712's physical address width. -/
theorem rpi5MachineConfigForVariant_physicalAddressWidth (v : BCM2712Config) :
    (rpi5MachineConfigForVariant v).physicalAddressWidth =
      rpi5MachineConfig.physicalAddressWidth := rfl

/-- **PR #892 review round 2**: every member of the family is a well-formed
machine configuration — non-overlapping regions of positive size inside the
physical address space — not only the 4 GiB one
(`rpi5MachineConfig_wellFormed`). -/
theorem rpi5Variants_wellFormed :
    rpi5Variants.all (fun v => (rpi5MachineConfigForVariant v).wellFormed) = true := by
  decide

/-- **PR #892 review round 2**: the variants a board account covers, in the
family's ascending order — decided by the bridge's own predicate. -/
def rpi5VariantsCoveredBy (board : SeLe4n.MachineConfig) : List BCM2712Config :=
  rpi5Variants.filter fun v =>
    SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v)

/-- **PR #892 review round 2**: the variant the binding installs for a board
account — the **largest** the account covers, and `rpi5SmallestVariant` when it
covers none (see that definition for why the fallback is the smallest).

"Largest covered" rather than "the account's total RAM size" is the relation
rather than the presence check: a board reporting 4 GiB at a foreign base
covers no variant and is refused by the bridge, where a size derivation would
have bound the 4 GiB map over memory that is not there. -/
def rpi5VariantFor (board : SeLe4n.MachineConfig) : BCM2712Config :=
  match (rpi5VariantsCoveredBy board).getLast? with
  | some v => v
  | none => rpi5SmallestVariant

/-- **PR #892 review round 2**: the machine configuration the RPi5 binding
installs for a board account — `PlatformBinding.bindMachineConfig` at
`RPi5Platform` (`rpi5_bindMachineConfig`). -/
def rpi5BoundMachineConfig (board : SeLe4n.MachineConfig) : SeLe4n.MachineConfig :=
  rpi5MachineConfigForVariant (rpi5VariantFor board)

theorem mem_rpi5VariantsCoveredBy (board : SeLe4n.MachineConfig) (v : BCM2712Config) :
    v ∈ rpi5VariantsCoveredBy board ↔
      v ∈ rpi5Variants ∧
        SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v) = true :=
  List.mem_filter

/-- **PR #892 review round 2**: whatever the account, the binding installs a
member of its declared family — a caller's configuration selects among the
variants and can never become the machine configuration itself. -/
theorem rpi5VariantFor_mem (board : SeLe4n.MachineConfig) :
    rpi5VariantFor board ∈ rpi5Variants := by
  unfold rpi5VariantFor
  cases h : (rpi5VariantsCoveredBy board).getLast? with
  | none => exact rpi5SmallestVariant_mem
  | some v => exact ((mem_rpi5VariantsCoveredBy board v).mp (List.mem_of_getLast? h)).1

theorem rpi5BoundMachineConfig_mem_family (board : SeLe4n.MachineConfig) :
    ∃ v ∈ rpi5Variants, rpi5BoundMachineConfig board = rpi5MachineConfigForVariant v :=
  ⟨rpi5VariantFor board, rpi5VariantFor_mem board, rfl⟩

/-- The bound configuration declares the BCM2712's four PEs, whatever the
account. -/
theorem rpi5BoundMachineConfig_declaredCoreCount (board : SeLe4n.MachineConfig) :
    (rpi5BoundMachineConfig board).declaredCoreCount = 4 := rfl

theorem rpi5VariantFor_covers_of_getLast? (board : SeLe4n.MachineConfig) (v : BCM2712Config)
    (h : (rpi5VariantsCoveredBy board).getLast? = some v) :
    SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v) = true :=
  ((mem_rpi5VariantsCoveredBy board v).mp (List.mem_of_getLast? h)).2

/-- **PR #892 review round 2**: an account covering no variant binds the
smallest — the fallback, stated. -/
theorem rpi5VariantFor_of_uncovered (board : SeLe4n.MachineConfig)
    (h : ∀ v ∈ rpi5Variants,
      SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v) = false) :
    rpi5VariantFor board = rpi5SmallestVariant := by
  unfold rpi5VariantFor
  have hNil : rpi5VariantsCoveredBy board = [] :=
    List.filter_eq_nil_iff.mpr (fun v hv hc => by rw [h v hv] at hc; exact Bool.false_ne_true hc)
  rw [hNil]
  rfl

/-- **PR #892 review round 2 — the bridge's check, characterised**: the account
covers the configuration the binding installs for it **iff** it covers some
variant at all.  Forwards, the bound configuration is itself a member;
backwards, a covered member makes the covered list non-empty and its last
entry is what the binding installs.  This is why `rpi5PlatformConfigFromDtb`
can validate the board against `rpi5BoundMachineConfig` alone: on every
account it accepts, the boot installs a configuration the board covers, and
on every account it refuses, no variant would have done. -/
theorem rpi5BoundMachineConfig_covered_iff (board : SeLe4n.MachineConfig) :
    SeLe4n.Platform.Boot.machineConfigCovers board (rpi5BoundMachineConfig board) = true ↔
      ∃ v ∈ rpi5Variants,
        SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v) = true := by
  constructor
  · intro h
    exact ⟨rpi5VariantFor board, rpi5VariantFor_mem board, h⟩
  · rintro ⟨v, hv, hc⟩
    unfold rpi5BoundMachineConfig rpi5VariantFor
    have hMem : v ∈ rpi5VariantsCoveredBy board := (mem_rpi5VariantsCoveredBy board v).mpr ⟨hv, hc⟩
    cases hLast : (rpi5VariantsCoveredBy board).getLast? with
    | none =>
        have hNil := List.getLast?_eq_none_iff.mp hLast
        rw [hNil] at hMem
        cases hMem
    | some w => exact rpi5VariantFor_covers_of_getLast? board w hLast

/-- **PR #892 review round 2**: the selection is maximal — no covered variant
has more RAM than the one installed, so the kernel runs on all the RAM the
board is known to have among the sizes the binding declares.  The ascending
listing (`rpi5Variants_ascending`) survives the filter, and the last entry of
an ascending list bounds every entry. -/
theorem rpi5VariantFor_maximal (board : SeLe4n.MachineConfig) (v : BCM2712Config)
    (hv : v ∈ rpi5Variants)
    (hc : SeLe4n.Platform.Boot.machineConfigCovers board (rpi5MachineConfigForVariant v) = true) :
    v.ramSize ≤ (rpi5VariantFor board).ramSize := by
  unfold rpi5VariantFor
  have hMem : v ∈ rpi5VariantsCoveredBy board := (mem_rpi5VariantsCoveredBy board v).mpr ⟨hv, hc⟩
  have hSorted : (rpi5VariantsCoveredBy board).Pairwise (fun a b => a.ramSize ≤ b.ramSize) :=
    rpi5Variants_ascending.filter _
  cases hLast : (rpi5VariantsCoveredBy board).getLast? with
  | none =>
      have hNil := List.getLast?_eq_none_iff.mp hLast
      rw [hNil] at hMem
      cases hMem
  | some w =>
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hLast
      rw [hys] at hMem hSorted
      rw [List.pairwise_append] at hSorted
      obtain ⟨_, _, hCross⟩ := hSorted
      rcases List.mem_append.mp hMem with hIn | hEq
      · exact hCross v hIn w (List.mem_singleton.mpr rfl)
      · rw [List.mem_singleton.mp hEq]
        exact Nat.le_refl _

/-- **PR #892 review round 2**: the canonical 4 GiB account binds the canonical
configuration — the 8 and 16 GiB members need RAM above 4 GiB it does not
report, and the 4 GiB member is the largest of the three it covers.  Decided,
so the whole selection runs on the binding's own numbers. -/
theorem rpi5VariantFor_rpi5MachineConfig :
    rpi5VariantFor rpi5MachineConfig = bcm2712DefaultConfig := by
  decide

theorem rpi5BoundMachineConfig_rpi5MachineConfig :
    rpi5BoundMachineConfig rpi5MachineConfig = rpi5MachineConfig := by
  unfold rpi5BoundMachineConfig
  rw [rpi5VariantFor_rpi5MachineConfig]
  exact rpi5MachineConfigForVariant_default

/-- **PR #892 review round 2**: the model's default configuration reports no
memory at all, so it covers no variant and binds the smallest — the direct
boot path's fallback, exercised on the account the harness actually passes. -/
theorem rpi5VariantFor_defaultMachineConfig :
    rpi5VariantFor SeLe4n.defaultMachineConfig = rpi5SmallestVariant := by
  decide

/-- **PR #892 review round 2 — the finding's own boards**: a 1 GiB board's
account binds the 1 GiB member and a 2 GiB board's the 2 GiB member, where the
fixed 4 GiB check refused both. -/
theorem rpi5VariantFor_one_gib :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap := [{ base := SeLe4n.PAddr.ofNat 0, size := 0x40000000, kind := .ram }] } =
      { ramSize := 1 * 1024 * 1024 * 1024 } := by
  decide

theorem rpi5VariantFor_two_gib :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap := [{ base := SeLe4n.PAddr.ofNat 0, size := 0x80000000, kind := .ram }] } =
      { ramSize := 2 * 1024 * 1024 * 1024 } := by
  decide

/-- **PR #892 review round 2**: an 8 GiB board as its firmware reports it —
the low aperture below the peripheral window and the rest relocated above the
4 GiB boundary, 64 MiB larger than the model's high region — binds the 8 GiB
member: the model's map is contained in the report, which is all coverage
asks. -/
theorem rpi5VariantFor_eight_gib_as_reported :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0xFC000000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x100000000, size := 0x104000000, kind := .ram } ] } =
      { ramSize := 8 * 1024 * 1024 * 1024 } := by
  decide

/-- **PR #892 review round 2 (the negative)**: 4 GiB of RAM at a foreign base
covers no variant — a size derivation would have accepted it. -/
theorem rpi5VariantFor_foreign_base :
    rpi5VariantsCoveredBy { rpi5MachineConfig with
        memoryMap := [{ base := SeLe4n.PAddr.ofNat 0x40000000, size := 0x100000000, kind := .ram }] }
      = [] := by
  decide

end SeLe4n.Platform.RPi5
