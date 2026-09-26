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
<!-- BCM2712_DATASHEET_VERIFIED: 2026-09-25 -->
-/

namespace SeLe4n.Platform.RPi5

-- ============================================================================
-- BCM2712 physical address map
-- ============================================================================

/- **Tombstone**: `peripheralBaseLow` (`0xFE00_0000`) is retired.  It was the
BCM2711's (Raspberry Pi 4's) legacy 32-bit peripheral window, which the BCM2712
does not have: on the Raspberry Pi 5 the SoC bus appears in the CPU's physical
address space at `socPeripheralBase` below, and the low four gigabytes are
DRAM.  Every address this module carried for the UART and the GIC-400 was in
that retired window (see `CHANGELOG.md` v0.36.2, the BCM2712 address-map
correction). -/

/-- BCM2712 high-peripheral base address: the start of the 64 GiB `axi`
window above DRAM (`bcm2712.dtsi`'s `axi` node maps `0x10_0000_0000` 1:1),
inside which the SoC bus, the GIC-400 and RP1's PCIe apertures sit. -/
def peripheralBaseHigh : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x1000000000)

/-- **The BCM2712 address-map correction (v0.36.2)**: where the SoC bus
appears to the CPU.  `bcm2712.dtsi`'s `soc` node carries
`ranges = <0x7c000000 0x10 0x7c000000 0x04000000>` — the 64 MiB of bus
addresses `[0x7C00_0000, 0x8000_0000)` at CPU physical `0x10_7C00_0000` — and
UART10 and the GIC-400 both sit inside it. -/
def socPeripheralBase : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x107C000000)

/-- The size of the SoC-bus window at `socPeripheralBase`: 64 MiB. -/
def socPeripheralSize : Nat := 0x04000000

/-- GIC-400 distributor base address: `bcm2712.dtsi`'s
`interrupt-controller@7fff9000`, first `reg` block `<0x10 0x7fff9000 0x0 0x1000>`. -/
def gicDistributorBase : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x107FFF9000)

/-- GIC-400 CPU interface base address: the same node's second `reg` block,
`<0x10 0x7fffa000 0x0 0x2000>`. -/
def gicCpuInterfaceBase : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x107FFFA000)

/-- ARM Generic Timer frequency (54 MHz crystal on RPi5). -/
def timerFrequencyHz : Nat := 54000000

/-- The debug console's PL011 base address: BCM2712 UART10 — the one on the
Raspberry Pi 5's three-pin debug header, labelled `uart0` in `bcm2712.dtsi`
(`serial@7d001000`, `reg = <0x7d001000 0x200>` on the SoC bus, so CPU physical
`0x10_7D00_1000` through the `soc` window).  The UARTs on GPIO 14/15 are RP1's,
behind PCIe, and are not the kernel's console. -/
def uart0Base : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x107D001000)

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

    Two regions, low to high:
    1. RAM: `[0, ramSize)` — the BCM2712's DRAM is contiguous from address 0
       (`bcm2712.dtsi`'s `axi` node maps `[0, 0x10_0000_0000)` 1:1 to DRAM),
       on every variant, 1 GiB through 16 GiB.
    2. The SoC-bus window `[socPeripheralBase, + socPeripheralSize)`
       (`0x10_7C00_0000`, 64 MiB), which holds UART10 and the GIC-400.

    **The BCM2712 address-map correction (v0.36.2)**: this map was the
    BCM2711's until then — RAM capped at `0xFC00_0000`, a "GPU carve-out" at
    `0xFC00_0000`, a device window `[0xFE00_0000, 0xFF85_0000)` holding the UART
    and the GIC, and a reserved tail to the 4 GiB boundary.  None of that is the
    Raspberry Pi 5: on the BCM2712 those addresses are DRAM, so the image would
    have programmed its UART and its interrupt controller by writing to memory,
    and declared 64 MiB of a 4 GiB board's RAM as something else.  What the
    firmware itself reserves inside DRAM is its business to say, and it says it
    through the device tree's reservation block and `/reserved-memory`, which
    `DeviceTree.fromDtbFull` subtracts. -/
def rpi5MemoryMapForConfig (config : BCM2712Config) : List SeLe4n.MemoryRegion :=
  [ { base := (SeLe4n.PAddr.ofNat 0x00000000)
      size := config.ramSize
      kind := .ram }
  , { base := socPeripheralBase
      size := socPeripheralSize
      kind := .device }
  ]

/-- Standard Raspberry Pi 5 physical memory map (4 GB model).
    V4-D: Now delegates to `rpi5MemoryMapForConfig` with default config. -/
def rpi5MemoryMap : List SeLe4n.MemoryRegion :=
  rpi5MemoryMapForConfig bcm2712DefaultConfig

-- ============================================================================
-- ARM64 architectural constants
-- ============================================================================

/-- **WS-BP BP3.2**: the end of the kernel's reserved extent on the RPi5 —
    `[0, rpi5KernelReservedEnd)` holds the firmware's stub below the image
    (`_start` is `0x80000`), the image, both stack regions, the Lean heap
    arena, and the window the image build places the device tree in.

    256 MiB, inside the guaranteed gigabyte.  The same number is `link.ld`'s
    `KERNEL_RESERVED_END` — whose `ASSERT` refuses an image that outgrows it —
    and the HAL's `mmu::KERNEL_RESERVED_END`, which refuses a device tree
    outside it; `tests/Ak9PlatformSuite.lean` writes this constant into
    `tests/fixtures/boot_map.expected`, and the HAL's test and
    `scripts/check_link_script.py` read it back, so the three cannot drift. -/
def rpi5KernelReservedEnd : Nat := 0x1000_0000

/-- **WS-BP BP3.2**: the kernel's reserved extent as a region list — what the
    boot refuses a boot untyped over (`Boot.untypedClearOfKernel`). -/
def rpi5KernelReserved : List SeLe4n.MemoryRegion :=
  [{ base := SeLe4n.PAddr.ofNat 0, size := rpi5KernelReservedEnd, kind := .reserved }]

/-- **WS-BP BP3.2**: the reserved extent lies inside the RAM every Raspberry
    Pi 5 has — the smallest board's gigabyte. -/
theorem rpi5KernelReservedEnd_le_guaranteedRam : rpi5KernelReservedEnd ≤ 0x4000_0000 := by
  decide

/-- ARMv8-A machine configuration for Raspberry Pi 5. -/
def rpi5MachineConfig : SeLe4n.MachineConfig :=
  {
    registerWidth := 64
    virtualAddressWidth := 48
    -- The v0.36.2 audit: the BCM2712's PEs are Cortex-A76 cores, whose
    -- `ID_AA64MMFR0_EL1.PARange` is `0b0010` — a 40-bit physical address
    -- space (Cortex-A76 TRM r4p1 §B2.58).  This field bounds every physical
    -- address the kernel admits (`MachineState.addrInRange`, the checked
    -- VSpace map decode, `MachineConfig.wellFormed`), so it is the PE's
    -- value and not a wider one: the `44` carried from AJ3-B admitted
    -- mappings in `[2^40, 2^44)` that the PE answers with an Address size
    -- fault.  The HAL derives `TCR_EL1.IPS` from the same register at
    -- `enable_mmu` and the shared boot-map fixture holds the two together
    -- (`tests/fixtures/boot_map.expected`, `physicalAddressWidth`).
    physicalAddressWidth := 40
    pageSize := 4096             -- 4 KiB granule (standard)
    maxASID := 65536             -- 16-bit ASID with TTBR.ASID
    memoryMap := rpi5MemoryMap
    -- PR #889 review round 20: the BCM2712 is a quad-core Cortex-A76, so the
    -- machine the kernel runs on has exactly four PEs.  The binding's
    -- `coreCount` says the same thing to the boot; `declaredCoreCountAgrees`
    -- holds the two together, and this is the copy the *live* affinity
    -- transitions read out of `SystemState.machine`.
    declaredCoreCount := 4
    -- WS-BP BP3.2: the kernel's reserved extent, identical on every variant
    -- (`rpi5MachineConfigForVariant` keeps it), since it is the image's.
    kernelReserved := rpi5KernelReserved
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
    Each region covers a specific hardware peripheral's register space, and
    each is **the register block the device tree declares**, because
    `deviceTreeCoversMmioRegions` requires the board's block to *contain* the
    window: a window wider than the block is refused, and the boot halts.

    The UART window is therefore `0x200` bytes, `bcm2712.dtsi`'s
    `serial@7d001000` `reg = <0x7d001000 0x200>`, not the PL011's nominal
    4 KiB register page (the `v0.36.2` audit found `0x1000` here against the
    `0x200` the same file quotes three sections above, which no fixture could
    show because every fixture's UART node was built from this constant).
    Every register the console driver touches — `UARTDR` through `UARTICR`,
    offsets `0x000`–`0x044` — lies inside it. -/
def mmioRegions : List SeLe4n.MemoryRegion :=
  [ { base := uart0Base,            size := 0x200,  kind := .device }  -- PL011 UART10
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
    - UART10 PL011:      [0x10_7D00_1000, 0x10_7D00_1200)
    - GIC distributor:   [0x10_7FFF_9000, 0x10_7FFF_A000)
    - GIC CPU interface: [0x10_7FFF_A000, 0x10_7FFF_C000)
    Note: GIC distributor ends at 0x10_7FFF_A000 and GIC CPU interface starts
    at 0x10_7FFF_A000 — these are exactly adjacent (non-overlapping) by the strict
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

| Constant | Value | Source | Status |
|----------|-------|--------|--------|
| `peripheralBaseHigh` | 0x10_0000_0000 | `bcm2712.dtsi` `axi` node `ranges` (1:1 above DRAM) | Cross-checked |
| `socPeripheralBase` / `socPeripheralSize` | 0x10_7C00_0000 / 64 MiB | `bcm2712.dtsi` `soc` node, `ranges = <0x7c000000 0x10 0x7c000000 0x04000000>` | Cross-checked |
| `gicDistributorBase` | 0x10_7FFF_9000 | `bcm2712.dtsi` `interrupt-controller@7fff9000`, `reg` block 0 | Cross-checked |
| `gicCpuInterfaceBase` | 0x10_7FFF_A000 | the same node, `reg` block 1 (8 KiB) | Cross-checked |
| `uart0Base` | 0x10_7D00_1000 | `bcm2712.dtsi` `uart0: serial@7d001000` (UART10, the debug header) through the `soc` window | Cross-checked |
| `rpi5MemoryMapForConfig` RAM | `[0, ramSize)` | `bcm2712.dtsi` `axi` `ranges <0x00 0 0x00 0 0x10 0>` — DRAM contiguous from 0 | Cross-checked |
| `timerFrequencyHz` | 54 MHz | RPi5 crystal; CNTFRQ_EL0 | Carried over |
| `rpi5MachineConfig.physicalAddressWidth` | 40-bit | Cortex-A76 TRM r4p1 §B2.58: `ID_AA64MMFR0_EL1.PARange = 0b0010` (the `44` carried over from AJ3-B was corrected by the v0.36.2 audit; the HAL derives `TCR_EL1.IPS` from the register, BP8.1 reads it back) | Cross-checked |
| `gicSpiCount`, `timerPpiId`, `virtualTimerPpiId` | 192, 30, 27 | ARM GIC architecture; RPi kernel DTS | Carried over |

**The BCM2712 address-map correction (v0.36.2).**  Until that version this
table marked `peripheralBaseLow` (`0xFE00_0000`), a UART at `0xFE20_1000`, a
GIC-400 at `0xFF84_1000` / `0xFF84_2000`, a RAM region capped at 4032 MiB and a
"GPU carve-out" at `0xFC00_0000` **Validated** against the BCM2712.  Every one
of those is the **BCM2711**'s (Raspberry Pi 4) map, and on the BCM2712 each of
those addresses is DRAM.  The marks were false, and nothing in the tree could
have caught them — no gate reads a datasheet.  The rows above are
cross-checked against `arch/arm64/boot/dts/broadcom/bcm2712.dtsi` in the
`raspberrypi/linux` tree, branch `rpi-6.6.y`, read 2026-09-25, and say so
rather than claiming a datasheet this project does not have; a board-level
readback (BP8.1) is what would promote them further.

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
    [ { name := "uart0", base := uart0Base, size := 0x200 }
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

### Constants

See the table in §S5-F above, which is the one list; a second copy of it here
is how the two came to disagree with the hardware together.

### MMIO Disjointness

MMIO regions (UART, GIC distributor, GIC CPU interface) are proven disjoint
from RAM via `mmioRegionDisjoint_holds` (`decide`). Machine configuration
well-formedness is proven via `rpi5MachineConfig_wellFormed` (`decide`).

### Notes

1. **BCM2712 datasheet**: The full datasheet is not publicly available as of
   2026-03-23. Values are derived from the partial BCM2712 ARM Peripherals
   document, community reverse-engineering (Raspberry Pi forums), and the
   ARM architecture specifications.

2. **GIC-400 addresses**: the BCM2712 places the distributor at
   `0x10_7FFF_9000` and the CPU interface at `0x10_7FFF_A000`
   (`bcm2712.dtsi`, `interrupt-controller@7fff9000`, whose `reg` blocks carry
   the `0x10` high cell explicitly).

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

/-- **WS-BP BP3.2**: every member reserves the kernel's extent — it is the
image's, not the board's. -/
theorem rpi5MachineConfigForVariant_kernelReserved (v : BCM2712Config) :
    (rpi5MachineConfigForVariant v).kernelReserved = rpi5KernelReserved := rfl

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

/-- **PR #892 review round 2**: an 8 GiB board reported as two banks either
side of the 4 GiB boundary binds the 8 GiB member: the model's one RAM region is
covered by the *union* of the two, which is all coverage asks.

(**The BCM2712 address-map correction, v0.36.2**: this was
`rpi5VariantFor_eight_gib_as_reported`, over a low bank ending at
`0xFC00_0000` and a high one 64 MiB larger than 4 GiB — the BCM2711's
relocation of the RAM its peripheral window displaced.  The BCM2712 has no such
window below 4 GiB, so a board reporting that shape would now leave
`[0xFC00_0000, 4 GiB)` uncovered and bind a smaller variant, which is the
fail-safe direction.) -/
theorem rpi5VariantFor_eight_gib_two_banks :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0x100000000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x100000000, size := 0x100000000, kind := .ram } ] } =
      { ramSize := 8 * 1024 * 1024 * 1024 } := by
  decide

/-- **PR #892 review round 2 (the negative)**: 4 GiB of RAM at a foreign base
covers no variant — a size derivation would have accepted it. -/
theorem rpi5VariantFor_foreign_base :
    rpi5VariantsCoveredBy { rpi5MachineConfig with
        memoryMap := [{ base := SeLe4n.PAddr.ofNat 0x40000000, size := 0x100000000, kind := .ram }] }
      = [] := by
  decide

-- ============================================================================
-- WS-BP BP4.6 — the verified board's RAM above the guaranteed gigabyte
-- ============================================================================

/-- **WS-BP BP4.6**: one past the RAM every Raspberry Pi 5 has — the smallest
variant's gigabyte.  The HAL's boot map describes `[0, rpi5GuaranteedRamTop)`
from constants before anything is parsed (`mmu::GUARANTEED_RAM_TOP`, WS-BP
BP2.6); everything a larger board has above it is mapped only once the verified
device-tree parse has chosen the variant (`bootRamExtensionsOf`). -/
def rpi5GuaranteedRamTop : Nat := 0x4000_0000

/-- The guaranteed gigabyte is the smallest variant's RAM. -/
theorem rpi5GuaranteedRamTop_eq_smallest : rpi5GuaranteedRamTop = rpi5SmallestVariant.ramSize :=
  rfl

/-- **WS-BP BP4.6**: the RAM a memory map declares above the guaranteed
gigabyte, one `(base, size)` per RAM region that reaches past it, clipped from
below to `rpi5GuaranteedRamTop` — and only where what is left is non-empty, so no
extension maps nothing (the HAL refuses an empty one).

Derived from the map rather than listed per variant, so a variant whose map
changes changes what the boot maps with it; `mem_bootRamExtensionsOf` and
`bootRamExtensionsOf_covers` state that the result is exactly the map's RAM
above the gigabyte, in both directions. -/
def bootRamExtensionsOf (map : List SeLe4n.MemoryRegion) : List (Nat × Nat) :=
  map.filterMap fun r =>
    if r.kind = .ram ∧ max r.base.toNat rpi5GuaranteedRamTop < r.endAddr then
      some (max r.base.toNat rpi5GuaranteedRamTop,
        r.endAddr - max r.base.toNat rpi5GuaranteedRamTop)
    else none

/-- **WS-BP BP4.6 (soundness)**: every extension is RAM — inside one RAM
region of the map, ending where it ends — non-empty, and above the guaranteed
gigabyte.  So the boot never maps as Normal memory an address the verified map
does not call RAM. -/
theorem mem_bootRamExtensionsOf (map : List SeLe4n.MemoryRegion) (e : Nat × Nat)
    (h : e ∈ bootRamExtensionsOf map) :
    ∃ r ∈ map, r.kind = .ram ∧ r.base.toNat ≤ e.1 ∧ e.1 + e.2 = r.endAddr ∧
      rpi5GuaranteedRamTop ≤ e.1 ∧ 0 < e.2 := by
  unfold bootRamExtensionsOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨r, hr, hsome⟩ := h
  by_cases hc : r.kind = .ram ∧ max r.base.toNat rpi5GuaranteedRamTop < r.endAddr
  · rw [if_pos hc] at hsome
    cases hsome
    have hg := hc.2
    refine ⟨r, hr, hc.1, Nat.le_max_left _ _, ?_, Nat.le_max_right _ _, ?_⟩
    · simp only
      omega
    · simp only
      omega
  · rw [if_neg hc] at hsome
    cases hsome

/-- **WS-BP BP4.6 (completeness)**: every RAM address of the map above the
guaranteed gigabyte lies in some extension — so on a board whose variant the
parse selected, no RAM the verified map declares is left unmapped. -/
theorem bootRamExtensionsOf_covers (map : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) (hr : r ∈ map) (hk : r.kind = .ram) (a : Nat)
    (hlo : r.base.toNat ≤ a) (hhi : a < r.endAddr) (hg : rpi5GuaranteedRamTop ≤ a) :
    ∃ e ∈ bootRamExtensionsOf map, e.1 ≤ a ∧ a < e.1 + e.2 := by
  have hc : r.kind = .ram ∧ max r.base.toNat rpi5GuaranteedRamTop < r.endAddr :=
    ⟨hk, Nat.max_lt.mpr ⟨by omega, by omega⟩⟩
  refine ⟨(max r.base.toNat rpi5GuaranteedRamTop,
      r.endAddr - max r.base.toNat rpi5GuaranteedRamTop), ?_, ?_, ?_⟩
  · unfold bootRamExtensionsOf
    exact List.mem_filterMap.mpr ⟨r, hr, by rw [if_pos hc]⟩
  · simp only
    omega
  · simp only
    omega

/-- **WS-BP BP4.6**: the extensions of variant `v` — what the boot maps above
the guaranteed gigabyte on a board of that variant. -/
def rpi5BootRamExtensions (v : BCM2712Config) : List (Nat × Nat) :=
  bootRamExtensionsOf (rpi5MemoryMapForConfig v)

/-- **WS-BP BP4.6**: the extensions the boot maps for a board account — those
of the variant the binding installs for it, so the map the HAL builds and the
memory map the boot state carries are one variant's. -/
def rpi5BootRamExtensionsFor (board : SeLe4n.MachineConfig) : List (Nat × Nat) :=
  bootRamExtensionsOf (rpi5BoundMachineConfig board).memoryMap

theorem rpi5BootRamExtensionsFor_eq (board : SeLe4n.MachineConfig) :
    rpi5BootRamExtensionsFor board = rpi5BootRamExtensions (rpi5VariantFor board) := rfl

/-- **WS-BP BP4.6**: the five variants' extensions, evaluated — nothing on the
1 GiB board, and on every other board one region: all of its DRAM above the
guaranteed gigabyte, since the BCM2712's DRAM is contiguous from 0. -/
theorem rpi5BootRamExtensions_values :
    rpi5Variants.map rpi5BootRamExtensions =
      [ [],
        [(0x4000_0000, 0x4000_0000)],
        [(0x4000_0000, 0xC000_0000)],
        [(0x4000_0000, 0x1_C000_0000)],
        [(0x4000_0000, 0x3_C000_0000)] ] := by
  decide

/-- **WS-BP BP4.6**: every extension of every variant is what the HAL's
extension accepts — both ends on a 2 MiB boundary (the smallest block it
writes), and the whole of it below the 512 GiB the boot tables reach
(`mmu::BOOT_TABLE_REACH`).  A variant that broke either would be refused on
hardware with the system halted; this is the theorem that it cannot. -/
theorem rpi5BootRamExtensions_admissible :
    rpi5Variants.all (fun v => (rpi5BootRamExtensions v).all fun e =>
      e.1 % 0x20_0000 == 0 && (e.1 + e.2) % 0x20_0000 == 0 && e.1 + e.2 ≤ 2 ^ 39) = true := by
  decide

end SeLe4n.Platform.RPi5
