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

/-- **WS-BP BP4.6, renamed at BP7.10**: the top of the first gigabyte —
`0x4000_0000`, the smallest variant's RAM size and the boundary above which a
board's RAM is the variant's (`bootRamExtensionsOf` names it on the HAL's side).

**WS-BP BP7.10**: this was `rpi5GuaranteedRamTop`, "one past the RAM every
Raspberry Pi 5 has", and that was false: a Raspberry Pi 5's firmware keeps the
top few MiB of the first gigabyte for itself and reports the rest as RAM
(`[0x80000, 0x3FC00000)` on a Pi 5 8 GiB Rev 1.1, `[0x80000, 0x3FB00000)` on a
CM5 4 GiB Rev 1.0).  So no RAM beyond the kernel's own extent is guaranteed; the
first gigabyte is an **upper bound** on the RAM the account may give the
deployment below the variant's part (`rpi5LowRamTopAdmissible`), and how much of
it the deployment declares is read off the account (`rpi5LowRamTopFor`). -/
def rpi5FirstGigabyteTop : Nat := 0x4000_0000

/- **Tombstone (WS-BP BP7.10)**: `rpi5GuaranteedRamTop` is `rpi5FirstGigabyteTop`
above; the rename retires the claim the old name made. -/

/-- **WS-BP BP3.2**: the end of the kernel's reserved extent on the RPi5 —
    `[0, rpi5KernelReservedEnd)` holds the firmware's stub below the image
    (`_start` is `0x80000`), the image, both stack regions, the Lean heap
    arena, and the window the image build places the device tree in.

    256 MiB, inside the first gigabyte.  The same number is `link.ld`'s
    `KERNEL_RESERVED_END` — whose `ASSERT` refuses an image that outgrows it —
    and the HAL's `mmu::KERNEL_RESERVED_END`, which refuses a device tree
    outside it and (**WS-BP BP7.10**) is the only RAM the HAL's boot map
    describes before the verified parse; `tests/Ak9PlatformSuite.lean` writes
    this constant into `tests/fixtures/boot_map.expected`, and the HAL's test
    and `scripts/check_link_script.py` read it back, so the three cannot
    drift. -/
def rpi5KernelReservedEnd : Nat := 0x1000_0000

/-- **WS-BP BP7.10**: the granule the deployment's first-gigabyte RAM is
    declared in — 2 MiB, the smallest block the HAL's boot map extends by
    (`mmu::extend_boot_tables`), so every byte the model calls RAM is a byte
    the boot map can describe as RAM and no byte beyond it. -/
def rpi5LowRamGranule : Nat := 0x20_0000

/-- **WS-BP BP7.10**: the least first-gigabyte RAM top the deployment admits —
    the kernel's reserved extent and one granule for the root task.  An account
    that does not reach it does not have the RAM the image already occupies,
    and is refused. -/
def rpi5LowRamTopFloor : Nat := rpi5KernelReservedEnd + rpi5LowRamGranule

/-- **WS-BP BP7.10**: a first-gigabyte RAM top the deployment can boot on — at
    least the floor (the kernel's extent lies inside the account's RAM, and the
    root task gets a non-empty untyped past it), at most the first gigabyte,
    and on a granule boundary. -/
def rpi5LowRamTopAdmissible (t : Nat) : Bool :=
  decide (rpi5LowRamTopFloor ≤ t) && decide (t ≤ rpi5FirstGigabyteTop) &&
    t % rpi5LowRamGranule == 0

theorem rpi5LowRamTopAdmissible_iff (t : Nat) :
    rpi5LowRamTopAdmissible t = true ↔
      rpi5LowRamTopFloor ≤ t ∧ t ≤ rpi5FirstGigabyteTop ∧ t % rpi5LowRamGranule = 0 := by
  simp [rpi5LowRamTopAdmissible, and_assoc]

/-- The floor is itself admissible — the fallback below is always a top the
    deployment boots on. -/
theorem rpi5LowRamTopFloor_admissible : rpi5LowRamTopAdmissible rpi5LowRamTopFloor = true := by
  decide

/-- The whole first gigabyte is admissible — the top a board that reports all
    of it binds. -/
theorem rpi5FirstGigabyteTop_admissible :
    rpi5LowRamTopAdmissible rpi5FirstGigabyteTop = true := by
  decide

/-- **WS-BP BP3.2**: the reserved extent lies below every admissible top, so
    the kernel's image is inside the RAM the deployment declares. -/
theorem rpi5KernelReservedEnd_lt_of_admissible (t : Nat)
    (h : rpi5LowRamTopAdmissible t = true) : rpi5KernelReservedEnd < t := by
  have := ((rpi5LowRamTopAdmissible_iff t).mp h).1
  unfold rpi5LowRamTopFloor rpi5LowRamGranule at this
  omega

/- **Tombstone (WS-BP BP7.10)**: `rpi5KernelReservedEnd_le_guaranteedRam` is
`rpi5KernelReservedEnd_lt_of_admissible` above — the reserved extent is below the
account's first-gigabyte RAM, which is what the old theorem's "guaranteed" RAM
was standing in for. -/

/-- V4-D/M-HW-3: BCM2712 board configuration — the board's RAM, as the
    deployment declares it.

    `ramSize` selects the variant (1, 2, 4, 8 or 16 GiB, `rpi5Variants`) and
    fixes the RAM **above** the first gigabyte.  `lowRamTop` (**WS-BP BP7.10**)
    is how much of the first gigabyte is RAM: the firmware keeps the top of it
    for itself and the amount varies by board and firmware, so it is read off
    the board's account (`rpi5LowRamTopFor`) rather than assumed.  Its default,
    the whole gigabyte, is what the five family members carry. -/
structure BCM2712Config where
  /-- Total RAM size in bytes. RPi5 ships in 1, 2, 4, 8 and 16 GiB variants. -/
  ramSize : Nat := 4 * 1024 * 1024 * 1024  -- Default: 4 GB
  /-- **WS-BP BP7.10**: one past the RAM the deployment declares in the first
      gigabyte, `[0, lowRamTop)`. -/
  lowRamTop : Nat := rpi5FirstGigabyteTop
  deriving Repr, DecidableEq

/-- V4-D: Default BCM2712 configuration (4 GB model). -/
def bcm2712DefaultConfig : BCM2712Config := {}

/-- **WS-BP BP7.10**: the family member a configuration is cut from — the same
    RAM size with the whole first gigabyte. -/
def BCM2712Config.uncut (v : BCM2712Config) : BCM2712Config :=
  { v with lowRamTop := rpi5FirstGigabyteTop }

/-- V4-D/M-HW-3, WS-BP BP7.10: Physical memory map of a board configuration.

    Three regions, low to high:
    1. RAM `[0, lowRamTop)` — the part of the first gigabyte the firmware
       reports as RAM (**WS-BP BP7.10**; the whole gigabyte on the family
       members, the account's own on a bound board).
    2. RAM `[rpi5FirstGigabyteTop, ramSize)`, on every variant larger than the
       first gigabyte — the BCM2712's DRAM is contiguous from 0
       (`bcm2712.dtsi`'s `axi` node maps `[0, 0x10_0000_0000)` 1:1 to DRAM).
    3. The SoC-bus window `[socPeripheralBase, + socPeripheralSize)`
       (`0x10_7C00_0000`, 64 MiB), which holds UART10 and the GIC-400.

    **WS-BP BP7.10**: until then the map was `[0, ramSize)` whole, and no
    real board's firmware account covered it — the firmware withholds the top
    of the first gigabyte — so every real board was refused.  The first
    gigabyte is now its own region, cut where the account says, and the gap
    between it and the variant's part is memory the deployment does not
    declare, map or hand to anyone.

    **The BCM2712 address-map correction (v0.36.2)**: this map was the
    BCM2711's until then — RAM capped at `0xFC00_0000`, a "GPU carve-out" at
    `0xFC00_0000`, a device window `[0xFE00_0000, 0xFF85_0000)` holding the UART
    and the GIC, and a reserved tail to the 4 GiB boundary.  None of that is the
    Raspberry Pi 5: on the BCM2712 those addresses are DRAM.  What the firmware
    itself reserves inside DRAM it says through the device tree's reservation
    block and `/reserved-memory`, which `DeviceTree.fromDtbFull` subtracts. -/
def rpi5MemoryMapForConfig (config : BCM2712Config) : List SeLe4n.MemoryRegion :=
  [ { base := (SeLe4n.PAddr.ofNat 0x00000000)
      size := config.lowRamTop
      kind := .ram } ] ++
  (if rpi5FirstGigabyteTop < config.ramSize then
    [ { base := SeLe4n.PAddr.ofNat rpi5FirstGigabyteTop
        size := config.ramSize - rpi5FirstGigabyteTop
        kind := .ram } ]
  else []) ++
  [ { base := socPeripheralBase
      size := socPeripheralSize
      kind := .device } ]

/-- Standard Raspberry Pi 5 physical memory map (4 GB model).
    V4-D: Now delegates to `rpi5MemoryMapForConfig` with default config. -/
def rpi5MemoryMap : List SeLe4n.MemoryRegion :=
  rpi5MemoryMapForConfig bcm2712DefaultConfig

-- ============================================================================
-- ARM64 architectural constants
-- ============================================================================

/-- **WS-BP BP3.2**: the kernel's reserved extent as a region list — what the
    boot refuses a boot untyped over (`Boot.untypedClearOfKernel`). -/
def rpi5KernelReserved : List SeLe4n.MemoryRegion :=
  [{ base := SeLe4n.PAddr.ofNat 0, size := rpi5KernelReservedEnd, kind := .reserved }]

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

/-- **WS-BP BP7.10**: every family member declares the whole first gigabyte —
    each is its own uncut form. -/
theorem rpi5Variants_uncut : ∀ v ∈ rpi5Variants, v.uncut = v := by decide

/-- **WS-BP BP7.10**: a board configuration the deployment boots on — cut from
    a family member, at an admissible first-gigabyte top.  Every family member
    is one (`rpi5Variants_admissible`), and so is every configuration the
    binding selects for a board account (`rpi5VariantFor_admissible`). -/
def BCM2712Config.Admissible (v : BCM2712Config) : Prop :=
  v.uncut ∈ rpi5Variants ∧ rpi5LowRamTopAdmissible v.lowRamTop = true

theorem rpi5Variants_admissible (v : BCM2712Config) (hv : v ∈ rpi5Variants) : v.Admissible := by
  refine ⟨(rpi5Variants_uncut v hv).symm ▸ hv, ?_⟩
  have h : v.lowRamTop = rpi5FirstGigabyteTop := by
    rw [← rpi5Variants_uncut v hv]; rfl
  rw [h]; exact rpi5FirstGigabyteTop_admissible

/-- A configuration cut from family member `m` at admissible top `t` is
    admissible. -/
theorem admissible_of_mem_cut (m : BCM2712Config) (hm : m ∈ rpi5Variants) (t : Nat)
    (ht : rpi5LowRamTopAdmissible t = true) : ({ m with lowRamTop := t } : BCM2712Config).Admissible := by
  refine ⟨?_, ht⟩
  have : ({ m with lowRamTop := t } : BCM2712Config).uncut = m.uncut := rfl
  rw [this, rpi5Variants_uncut m hm]; exact hm

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

/-- **WS-BP BP7.10**: a configuration's map is its uncut member's, with the
    first-gigabyte region cut to `lowRamTop` and nothing else changed — so
    region by region a non-empty sub-range, whenever the top is admissible. -/
theorem rpi5MemoryMapForConfig_within_uncut (v : BCM2712Config)
    (h : rpi5LowRamTopAdmissible v.lowRamTop = true) :
    SeLe4n.MachineConfig.regionsNonEmptyWithin (rpi5MemoryMapForConfig v)
      (rpi5MemoryMapForConfig v.uncut) := by
  have hKre := rpi5KernelReservedEnd_lt_of_admissible _ h
  have hTop := ((rpi5LowRamTopAdmissible_iff _).mp h).2.1
  unfold rpi5KernelReservedEnd at hKre
  have hRefl : ∀ r : SeLe4n.MemoryRegion, 0 < r.size →
      SeLe4n.MachineConfig.regionNonEmptyWithin r r := fun r hr =>
    ⟨hr, Nat.le_refl _, Nat.le_refl _⟩
  unfold rpi5MemoryMapForConfig BCM2712Config.uncut
  simp only [List.cons_append, List.nil_append]
  refine ⟨⟨by show 0 < v.lowRamTop; omega, Nat.le_refl _, ?_⟩, ?_⟩
  · simp only [SeLe4n.MemoryRegion.endAddr]
    unfold rpi5FirstGigabyteTop at hTop ⊢
    simpa using hTop
  · split
    · rename_i hGt
      exact ⟨hRefl _ (by simp; omega), hRefl _ (by decide), trivial⟩
    · exact ⟨hRefl _ (by decide), trivial⟩

/-- **WS-BP BP7.10**: every admissible configuration is a well-formed machine
    configuration — its map is its family member's, cut in the first gigabyte,
    and cutting a region preserves well-formedness
    (`MachineConfig.wellFormed_of_within`). -/
theorem rpi5MachineConfigForVariant_wellFormed (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5MachineConfigForVariant v).wellFormed = true :=
  SeLe4n.MachineConfig.wellFormed_of_within (rpi5MachineConfigForVariant v.uncut)
    (rpi5MemoryMapForConfig v) (rpi5MemoryMapForConfig_within_uncut v hv.2)
    (List.all_eq_true.mp rpi5Variants_wellFormed _ hv.1)

-- ============================================================================
-- WS-BP BP7.10 — the first gigabyte's RAM, read off the account
-- ============================================================================

/-- **WS-BP BP7.10**: the first-gigabyte RAM top the deployment declares on a
board account: how far the account reports RAM contiguously from `0`
(`Boot.ramPrefixTop`), clipped to the first gigabyte and rounded **down** to the
granule — and, when that is not admissible, the floor.

Rounding down and clipping are the fail-safe directions: each declares less
than the account reports, never more.  The fallback is the floor for the same
reason `rpi5SmallestVariant` is the smallest: an account that does not reach
the floor is either not a board's (the harness passes `defaultMachineConfig`,
whose map is empty) or a board the bridge refuses before this top is used
(`rpi5LowRamTop_covered` is the converse — an account reaching the floor is
always covered to the top it binds). -/
def rpi5LowRamTopFor (board : SeLe4n.MachineConfig) : Nat :=
  let reach := min (SeLe4n.Platform.Boot.ramPrefixTop board) rpi5FirstGigabyteTop
  let t := reach - reach % rpi5LowRamGranule
  if rpi5LowRamTopAdmissible t then t else rpi5LowRamTopFloor

/-- **WS-BP BP7.10**: whatever the account, the top is admissible. -/
theorem rpi5LowRamTopFor_admissible (board : SeLe4n.MachineConfig) :
    rpi5LowRamTopAdmissible (rpi5LowRamTopFor board) = true := by
  unfold rpi5LowRamTopFor
  dsimp only
  split
  · assumption
  · exact rpi5LowRamTopFloor_admissible

/-- **WS-BP BP7.10 (soundness)**: an account that reaches the floor binds a top
it reports — every address below the bound top is RAM the account reports as
RAM, so the deployment never declares first-gigabyte memory the firmware kept
for itself. -/
theorem rpi5LowRamTopFor_le_prefix (board : SeLe4n.MachineConfig)
    (h : rpi5LowRamTopFloor ≤ SeLe4n.Platform.Boot.ramPrefixTop board) :
    rpi5LowRamTopFor board ≤ SeLe4n.Platform.Boot.ramPrefixTop board := by
  unfold rpi5LowRamTopFor
  dsimp only
  split
  · omega
  · exact h

/-- **WS-BP BP7.10 (the payoff)**: an account that reaches the floor covers the
first-gigabyte region it binds — so the first gigabyte never refuses a board
whose firmware reports the kernel's extent as RAM, however much of the gigabyte
it withholds.  The union reading does the work, so an account that cuts the
gigabyte into pieces (`[0, 0x80000)` and `[0x80000, …)` on a Raspberry Pi 5) is
covered as well as one reporting it whole. -/
theorem rpi5LowRamTop_covered (board : SeLe4n.MachineConfig)
    (h : rpi5LowRamTopFloor ≤ SeLe4n.Platform.Boot.ramPrefixTop board) :
    SeLe4n.Platform.Boot.memoryRegionCovered board.memoryMap
      { base := SeLe4n.PAddr.ofNat 0, size := rpi5LowRamTopFor board, kind := .ram } = true := by
  apply SeLe4n.Platform.Boot.memoryRegionCovered_of_le_coverReach
  · rfl
  · simp only [SeLe4n.MemoryRegion.endAddr]
    have := rpi5LowRamTopFor_le_prefix board h
    unfold SeLe4n.Platform.Boot.ramPrefixTop at this
    simpa [SeLe4n.PAddr.ofNat, SeLe4n.PAddr.toNat] using this

/-- **PR #892 review round 2, WS-BP BP7.10**: the family members a board
account covers, in the family's ascending order — decided by the bridge's own
predicate, on each member cut to the account's first-gigabyte top. -/
def rpi5VariantsCoveredBy (board : SeLe4n.MachineConfig) : List BCM2712Config :=
  rpi5Variants.filter fun v =>
    SeLe4n.Platform.Boot.machineConfigCovers board
      (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board })

/-- **PR #892 review round 2**: the family member a board account selects — the
**largest** the account covers, and `rpi5SmallestVariant` when it covers none
(see that definition for why the fallback is the smallest).

"Largest covered" rather than "the account's total RAM size" is the relation
rather than the presence check: a board reporting 4 GiB at a foreign base
covers no variant and is refused by the bridge, where a size derivation would
have bound the 4 GiB map over memory that is not there. -/
def rpi5RamVariantFor (board : SeLe4n.MachineConfig) : BCM2712Config :=
  match (rpi5VariantsCoveredBy board).getLast? with
  | some v => v
  | none => rpi5SmallestVariant

/-- **WS-BP BP7.10**: the configuration the binding installs for a board
account — the member it selects (`rpi5RamVariantFor`), cut to the account's
first-gigabyte top (`rpi5LowRamTopFor`).  The variant is chosen by the RAM the
account reports above the first gigabyte; the first gigabyte is the account's
own. -/
def rpi5VariantFor (board : SeLe4n.MachineConfig) : BCM2712Config :=
  { rpi5RamVariantFor board with lowRamTop := rpi5LowRamTopFor board }

/-- **PR #892 review round 2**: the machine configuration the RPi5 binding
installs for a board account — `PlatformBinding.bindMachineConfig` at
`RPi5Platform` (`rpi5_bindMachineConfig`). -/
def rpi5BoundMachineConfig (board : SeLe4n.MachineConfig) : SeLe4n.MachineConfig :=
  rpi5MachineConfigForVariant (rpi5VariantFor board)

theorem mem_rpi5VariantsCoveredBy (board : SeLe4n.MachineConfig) (v : BCM2712Config) :
    v ∈ rpi5VariantsCoveredBy board ↔
      v ∈ rpi5Variants ∧
        SeLe4n.Platform.Boot.machineConfigCovers board
          (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board }) = true :=
  List.mem_filter

/-- **PR #892 review round 2**: whatever the account, the member selected is one
of the family's — a caller's configuration selects among the variants and can
never become the machine configuration itself. -/
theorem rpi5RamVariantFor_mem (board : SeLe4n.MachineConfig) :
    rpi5RamVariantFor board ∈ rpi5Variants := by
  unfold rpi5RamVariantFor
  cases h : (rpi5VariantsCoveredBy board).getLast? with
  | none => exact rpi5SmallestVariant_mem
  | some v => exact ((mem_rpi5VariantsCoveredBy board v).mp (List.mem_of_getLast? h)).1

/-- **WS-BP BP7.10**: whatever the account, the configuration the binding
installs is admissible — a family member cut to an admissible top.  Every
deployment theorem is stated over admissible configurations, which is why it
holds of every account. -/
theorem rpi5VariantFor_admissible (board : SeLe4n.MachineConfig) :
    (rpi5VariantFor board).Admissible :=
  admissible_of_mem_cut _ (rpi5RamVariantFor_mem board) _ (rpi5LowRamTopFor_admissible board)

/- **Tombstone (WS-BP BP7.10)**: `rpi5VariantFor_mem` is
`rpi5RamVariantFor_mem` (the member selected) and `rpi5VariantFor_admissible`
(the configuration installed): the installed configuration is no longer a
family member, since its first gigabyte is the account's. -/

theorem rpi5BoundMachineConfig_mem_family (board : SeLe4n.MachineConfig) :
    ∃ v, v.Admissible ∧ rpi5BoundMachineConfig board = rpi5MachineConfigForVariant v :=
  ⟨rpi5VariantFor board, rpi5VariantFor_admissible board, rfl⟩

/-- The bound configuration declares the BCM2712's four PEs, whatever the
account. -/
theorem rpi5BoundMachineConfig_declaredCoreCount (board : SeLe4n.MachineConfig) :
    (rpi5BoundMachineConfig board).declaredCoreCount = 4 := rfl

theorem rpi5VariantFor_covers_of_getLast? (board : SeLe4n.MachineConfig) (v : BCM2712Config)
    (h : (rpi5VariantsCoveredBy board).getLast? = some v) :
    SeLe4n.Platform.Boot.machineConfigCovers board
      (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board }) = true :=
  ((mem_rpi5VariantsCoveredBy board v).mp (List.mem_of_getLast? h)).2

/-- **PR #892 review round 2**: an account covering no variant binds the
smallest — the fallback, stated. -/
theorem rpi5RamVariantFor_of_uncovered (board : SeLe4n.MachineConfig)
    (h : ∀ v ∈ rpi5Variants,
      SeLe4n.Platform.Boot.machineConfigCovers board
        (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board }) = false) :
    rpi5RamVariantFor board = rpi5SmallestVariant := by
  unfold rpi5RamVariantFor
  have hNil : rpi5VariantsCoveredBy board = [] :=
    List.filter_eq_nil_iff.mpr (fun v hv hc => by rw [h v hv] at hc; exact Bool.false_ne_true hc)
  rw [hNil]
  rfl

/- **Tombstone (WS-BP BP7.10)**: `rpi5VariantFor_of_uncovered` is
`rpi5RamVariantFor_of_uncovered` above — the fallback picks the member; the
first gigabyte is the account's either way. -/

/-- **PR #892 review round 2 — the bridge's check, characterised**: the account
covers the configuration the binding installs for it **iff** it covers some
member cut to its own first-gigabyte top.  Forwards, the bound configuration is
itself such a cut; backwards, a covered member makes the covered list non-empty
and its last entry is what the binding installs.  This is why
`rpi5PlatformConfigFromDtb` can validate the board against
`rpi5BoundMachineConfig` alone. -/
theorem rpi5BoundMachineConfig_covered_iff (board : SeLe4n.MachineConfig) :
    SeLe4n.Platform.Boot.machineConfigCovers board (rpi5BoundMachineConfig board) = true ↔
      ∃ v ∈ rpi5Variants,
        SeLe4n.Platform.Boot.machineConfigCovers board
          (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board }) = true := by
  constructor
  · intro h
    exact ⟨rpi5RamVariantFor board, rpi5RamVariantFor_mem board, h⟩
  · rintro ⟨v, hv, hc⟩
    unfold rpi5BoundMachineConfig rpi5VariantFor rpi5RamVariantFor
    have hMem : v ∈ rpi5VariantsCoveredBy board := (mem_rpi5VariantsCoveredBy board v).mpr ⟨hv, hc⟩
    cases hLast : (rpi5VariantsCoveredBy board).getLast? with
    | none =>
        have hNil := List.getLast?_eq_none_iff.mp hLast
        rw [hNil] at hMem
        cases hMem
    | some w => exact rpi5VariantFor_covers_of_getLast? board w hLast

/-- **PR #892 review round 2**: the selection is maximal — no covered member
has more RAM than the one installed, so the kernel runs on all the RAM the
board is known to have among the sizes the binding declares.  The ascending
listing (`rpi5Variants_ascending`) survives the filter, and the last entry of
an ascending list bounds every entry. -/
theorem rpi5VariantFor_maximal (board : SeLe4n.MachineConfig) (v : BCM2712Config)
    (hv : v ∈ rpi5Variants)
    (hc : SeLe4n.Platform.Boot.machineConfigCovers board
      (rpi5MachineConfigForVariant { v with lowRamTop := rpi5LowRamTopFor board }) = true) :
    v.ramSize ≤ (rpi5VariantFor board).ramSize := by
  show v.ramSize ≤ (rpi5RamVariantFor board).ramSize
  unfold rpi5RamVariantFor
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
report, the 4 GiB member is the largest of the three it covers, and (WS-BP
BP7.10) it reports the whole first gigabyte.  Decided, so the whole selection
runs on the binding's own numbers. -/
theorem rpi5VariantFor_rpi5MachineConfig :
    rpi5VariantFor rpi5MachineConfig = bcm2712DefaultConfig := by
  decide

theorem rpi5BoundMachineConfig_rpi5MachineConfig :
    rpi5BoundMachineConfig rpi5MachineConfig = rpi5MachineConfig := by
  unfold rpi5BoundMachineConfig
  rw [rpi5VariantFor_rpi5MachineConfig]
  exact rpi5MachineConfigForVariant_default

/-- **PR #892 review round 2, WS-BP BP7.10**: the model's default configuration
reports no memory at all, so it covers no variant and binds the smallest, at
the floor — the direct boot path's fallback, exercised on the account the
harness actually passes. -/
theorem rpi5VariantFor_defaultMachineConfig :
    rpi5VariantFor SeLe4n.defaultMachineConfig =
      { rpi5SmallestVariant with lowRamTop := rpi5LowRamTopFloor } := by
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
side of the 4 GiB boundary binds the 8 GiB member: the model's RAM regions are
covered by the *union* of the two, which is all coverage asks. -/
theorem rpi5VariantFor_eight_gib_two_banks :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0x100000000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x100000000, size := 0x100000000, kind := .ram } ] } =
      { ramSize := 8 * 1024 * 1024 * 1024 } := by
  decide

/-- **PR #892 review round 2 (the negative)**: 4 GiB of RAM at a foreign base
covers no variant — a size derivation would have accepted it.  (WS-BP BP7.10:
it reports no RAM from `0`, so its first gigabyte is the floor, which it does
not cover either.) -/
theorem rpi5VariantFor_foreign_base :
    rpi5VariantsCoveredBy { rpi5MachineConfig with
        memoryMap := [{ base := SeLe4n.PAddr.ofNat 0x40000000, size := 0x100000000, kind := .ram }] }
      = [] := by
  decide

/-- **WS-BP BP7.10 — the finding's own board**: the account a Raspberry Pi 5
8 GiB Rev 1.1's firmware writes (`[0, 0x80000)`, `[0x80000, 0x3FC00000)`,
`[0x40000000, 0x200000000)`, read 2026-09-25) binds the 8 GiB member cut to
`0x3FC00000` — the four MiB the firmware keeps are neither declared nor
covered.  Until this row that account covered no variant and the boot
halted. -/
theorem rpi5VariantFor_rpi5_firmware_account :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0x80000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x80000, size := 0x3FB80000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x40000000, size := 0x1C0000000, kind := .ram } ] } =
      { ramSize := 8 * 1024 * 1024 * 1024, lowRamTop := 0x3FC00000 } := by
  decide

/-- **WS-BP BP7.10**: a CM5 4 GiB Rev 1.0's account (`[0x80000, 0x3FB00000)`
below the gigabyte) ends off the granule, and binds the 4 GiB member cut to
`0x3FA00000` — rounded **down**, so the half-granule the account reports past
it is declared nowhere rather than claimed. -/
theorem rpi5VariantFor_cm5_firmware_account :
    rpi5VariantFor { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0x80000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x80000, size := 0x3FA80000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x40000000, size := 0xC0000000, kind := .ram } ] } =
      { ramSize := 4 * 1024 * 1024 * 1024, lowRamTop := 0x3FA00000 } := by
  decide

/-- **WS-BP BP7.10 (the negative)**: an account whose RAM begins past the
kernel's extent — a firmware reservation over the image, say — reaches less
than the floor from `0`, so it binds the floor and covers no member: the board
is refused rather than booted over memory the account does not call RAM. -/
theorem rpi5VariantFor_kernel_extent_not_ram :
    rpi5VariantsCoveredBy { rpi5MachineConfig with
        memoryMap :=
          [ { base := SeLe4n.PAddr.ofNat 0, size := 0x8000000, kind := .ram },
            { base := SeLe4n.PAddr.ofNat 0x8200000, size := 0x37E00000, kind := .ram } ] }
      = [] := by
  decide

-- ============================================================================
-- WS-BP BP4.6, re-derived at BP7.10 — the RAM the boot maps after the parse
-- ============================================================================

/-- **WS-BP BP4.6, BP7.10**: the first gigabyte's top is the smallest variant's
    size — the most first-gigabyte RAM any configuration declares. -/
theorem rpi5FirstGigabyteTop_eq_smallest : rpi5FirstGigabyteTop = rpi5SmallestVariant.ramSize :=
  rfl

/-- **WS-BP BP7.10**: one region's contribution to `bootRamExtensionsOf` — its
part outside the kernel's reserved extent, when it is RAM and that part is
non-empty. -/
def bootRamExtensionOf? (r : SeLe4n.MemoryRegion) : Option (Nat × Nat) :=
  if r.kind = .ram ∧ max r.base.toNat rpi5KernelReservedEnd < r.endAddr then
    some (max r.base.toNat rpi5KernelReservedEnd,
      r.endAddr - max r.base.toNat rpi5KernelReservedEnd)
  else none

/-- A RAM region from `0` past the kernel's extent contributes the part past
it. -/
theorem bootRamExtensionOf?_low (t : Nat) (h : rpi5KernelReservedEnd < t) :
    bootRamExtensionOf? { base := SeLe4n.PAddr.ofNat 0, size := t, kind := .ram } =
      some (rpi5KernelReservedEnd, t - rpi5KernelReservedEnd) := by
  have hm : max (SeLe4n.PAddr.ofNat 0).toNat rpi5KernelReservedEnd = rpi5KernelReservedEnd :=
    Nat.max_eq_right (Nat.zero_le _)
  unfold bootRamExtensionOf?
  rw [hm, if_pos ⟨rfl, by show rpi5KernelReservedEnd < 0 + t; omega⟩]
  have h0 : (SeLe4n.PAddr.ofNat 0).toNat = 0 := rfl
  simp only [SeLe4n.MemoryRegion.endAddr, h0, Nat.zero_add]

/-- A RAM region from the first gigabyte's top contributes all of itself. -/
theorem bootRamExtensionOf?_high (s : Nat) (h : rpi5FirstGigabyteTop < s) :
    bootRamExtensionOf?
        { base := SeLe4n.PAddr.ofNat rpi5FirstGigabyteTop, size := s - rpi5FirstGigabyteTop, kind := .ram } =
      some (rpi5FirstGigabyteTop, s - rpi5FirstGigabyteTop) := by
  have hle : rpi5KernelReservedEnd ≤ rpi5FirstGigabyteTop := by
    unfold rpi5KernelReservedEnd rpi5FirstGigabyteTop; omega
  have hm : max (SeLe4n.PAddr.ofNat rpi5FirstGigabyteTop).toNat rpi5KernelReservedEnd =
      rpi5FirstGigabyteTop := Nat.max_eq_left hle
  unfold bootRamExtensionOf?
  rw [hm, if_pos ⟨rfl, by
    show rpi5FirstGigabyteTop < rpi5FirstGigabyteTop + (s - rpi5FirstGigabyteTop); omega⟩]
  have h1 : (SeLe4n.PAddr.ofNat rpi5FirstGigabyteTop).toNat = rpi5FirstGigabyteTop := rfl
  simp only [SeLe4n.MemoryRegion.endAddr, h1, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- A device region contributes nothing. -/
theorem bootRamExtensionOf?_device :
    bootRamExtensionOf? { base := socPeripheralBase, size := socPeripheralSize, kind := .device } =
      none := by
  unfold bootRamExtensionOf?
  exact if_neg (fun hc => nomatch hc.1)

/-- **WS-BP BP4.6, re-derived at BP7.10**: the RAM a memory map declares
outside the kernel's reserved extent, one `(base, size)` per RAM region that
reaches past it, clipped from below to `rpi5KernelReservedEnd` — and only where
what is left is non-empty, so no extension maps nothing (the HAL refuses an
empty one).

**WS-BP BP7.10**: this clipped at the first gigabyte, because the HAL's boot
map described `[0, 1 GiB)` from constants — memory a real board's firmware
keeps the top of.  The boot map's constant RAM is the kernel's own extent now,
so everything else the board has, first gigabyte included, is mapped from this
list once the verified parse has read it — and the same list is the root
task's untypeds (`rpi5RootTaskUntypeds`), so the RAM the boot maps, the RAM
the model declares outside the kernel, and the RAM the root task owns are one
derivation.  `mem_bootRamExtensionsOf` and `bootRamExtensionsOf_covers` state
that the result is exactly the map's RAM outside the kernel, in both
directions. -/
def bootRamExtensionsOf (map : List SeLe4n.MemoryRegion) : List (Nat × Nat) :=
  map.filterMap bootRamExtensionOf?

/-- **WS-BP BP4.6 (soundness)**: every extension is RAM — inside one RAM
region of the map, ending where it ends — non-empty, and clear of the kernel's
reserved extent.  So the boot never maps as Normal memory an address the
verified map does not call RAM, and never re-maps the kernel's own. -/
theorem mem_bootRamExtensionsOf (map : List SeLe4n.MemoryRegion) (e : Nat × Nat)
    (h : e ∈ bootRamExtensionsOf map) :
    ∃ r ∈ map, r.kind = .ram ∧ r.base.toNat ≤ e.1 ∧ e.1 + e.2 = r.endAddr ∧
      rpi5KernelReservedEnd ≤ e.1 ∧ 0 < e.2 := by
  unfold bootRamExtensionsOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨r, hr, hsome⟩ := h
  unfold bootRamExtensionOf? at hsome
  by_cases hc : r.kind = .ram ∧ max r.base.toNat rpi5KernelReservedEnd < r.endAddr
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

/-- **WS-BP BP4.6 (completeness)**: every RAM address of the map outside the
kernel's reserved extent lies in some extension — so on a board whose account
the parse accepted, no RAM the verified map declares is left unmapped. -/
theorem bootRamExtensionsOf_covers (map : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) (hr : r ∈ map) (hk : r.kind = .ram) (a : Nat)
    (hlo : r.base.toNat ≤ a) (hhi : a < r.endAddr) (hg : rpi5KernelReservedEnd ≤ a) :
    ∃ e ∈ bootRamExtensionsOf map, e.1 ≤ a ∧ a < e.1 + e.2 := by
  have hc : r.kind = .ram ∧ max r.base.toNat rpi5KernelReservedEnd < r.endAddr :=
    ⟨hk, Nat.max_lt.mpr ⟨by omega, by omega⟩⟩
  refine ⟨(max r.base.toNat rpi5KernelReservedEnd,
      r.endAddr - max r.base.toNat rpi5KernelReservedEnd), ?_, ?_, ?_⟩
  · unfold bootRamExtensionsOf
    exact List.mem_filterMap.mpr ⟨r, hr, by unfold bootRamExtensionOf?; rw [if_pos hc]⟩
  · simp only
    omega
  · simp only
    omega

/-- **WS-BP BP4.6**: the extensions of configuration `v` — what the boot maps
outside the kernel's extent on a board bound to it. -/
def rpi5BootRamExtensions (v : BCM2712Config) : List (Nat × Nat) :=
  bootRamExtensionsOf (rpi5MemoryMapForConfig v)

/-- **WS-BP BP4.6**: the extensions the boot maps for a board account — those
of the configuration the binding installs for it, so the map the HAL builds and
the memory map the boot state carries are one configuration's. -/
def rpi5BootRamExtensionsFor (board : SeLe4n.MachineConfig) : List (Nat × Nat) :=
  bootRamExtensionsOf (rpi5BoundMachineConfig board).memoryMap

theorem rpi5BootRamExtensionsFor_eq (board : SeLe4n.MachineConfig) :
    rpi5BootRamExtensionsFor board = rpi5BootRamExtensions (rpi5VariantFor board) := rfl

/-- **WS-BP BP7.10**: a configuration's map on a board larger than the first
gigabyte — the three regions, in closed form. -/
theorem rpi5MemoryMapForConfig_of_gt (v : BCM2712Config) (hG : rpi5FirstGigabyteTop < v.ramSize) :
    rpi5MemoryMapForConfig v =
      [ { base := SeLe4n.PAddr.ofNat 0, size := v.lowRamTop, kind := .ram },
        { base := SeLe4n.PAddr.ofNat rpi5FirstGigabyteTop,
          size := v.ramSize - rpi5FirstGigabyteTop, kind := .ram },
        { base := socPeripheralBase, size := socPeripheralSize, kind := .device } ] := by
  unfold rpi5MemoryMapForConfig; rw [if_pos hG]; rfl

/-- **WS-BP BP7.10**: ...and on the 1 GiB board, which has no RAM above it. -/
theorem rpi5MemoryMapForConfig_of_le (v : BCM2712Config) (hG : ¬ rpi5FirstGigabyteTop < v.ramSize) :
    rpi5MemoryMapForConfig v =
      [ { base := SeLe4n.PAddr.ofNat 0, size := v.lowRamTop, kind := .ram },
        { base := socPeripheralBase, size := socPeripheralSize, kind := .device } ] := by
  unfold rpi5MemoryMapForConfig; rw [if_neg hG]; rfl

/-- **WS-BP BP7.10**: the extensions of a configuration whose first-gigabyte
top lies past the kernel's extent, in closed form — the first gigabyte's RAM
outside the kernel, then the variant's RAM above the gigabyte when it has any. -/
theorem rpi5BootRamExtensions_eq (v : BCM2712Config)
    (h : rpi5KernelReservedEnd < v.lowRamTop) :
    rpi5BootRamExtensions v =
      [(rpi5KernelReservedEnd, v.lowRamTop - rpi5KernelReservedEnd)] ++
        (if rpi5FirstGigabyteTop < v.ramSize then
          [(rpi5FirstGigabyteTop, v.ramSize - rpi5FirstGigabyteTop)] else []) := by
  -- Rewritten to closed forms rather than `split` + `simp`: `simp`ing through
  -- the unfolded `if` builds a proof term the kernel rejects with "deep
  -- recursion", while each closed-form rewrite is a small, checked step.
  unfold rpi5BootRamExtensions bootRamExtensionsOf
  by_cases hG : rpi5FirstGigabyteTop < v.ramSize
  · rw [rpi5MemoryMapForConfig_of_gt v hG, if_pos hG, List.filterMap_cons,
      bootRamExtensionOf?_low _ h, List.filterMap_cons, bootRamExtensionOf?_high _ hG,
      List.filterMap_cons, bootRamExtensionOf?_device]
    rfl
  · rw [rpi5MemoryMapForConfig_of_le v hG, if_neg hG, List.filterMap_cons,
      bootRamExtensionOf?_low _ h, List.filterMap_cons, bootRamExtensionOf?_device]
    rfl

/-- **WS-BP BP4.6, BP7.10**: the five members' extensions, evaluated — the
first gigabyte outside the kernel on every board, and on every board above the
gigabyte one more region: all of its DRAM above it, since the BCM2712's DRAM is
contiguous from 0. -/
theorem rpi5BootRamExtensions_values :
    rpi5Variants.map rpi5BootRamExtensions =
      [ [(0x1000_0000, 0x3000_0000)],
        [(0x1000_0000, 0x3000_0000), (0x4000_0000, 0x4000_0000)],
        [(0x1000_0000, 0x3000_0000), (0x4000_0000, 0xC000_0000)],
        [(0x1000_0000, 0x3000_0000), (0x4000_0000, 0x1_C000_0000)],
        [(0x1000_0000, 0x3000_0000), (0x4000_0000, 0x3_C000_0000)] ] := by
  decide

/-- **WS-BP BP7.10**: an extension the HAL's `mmu::extend_boot_tables` accepts —
both ends on a 2 MiB boundary (the smallest block it writes), clear of the
kernel's reserved extent (which the constant boot map describes with the
image's own permissions), below the 512 GiB the boot tables reach
(`mmu::BOOT_TABLE_REACH`), and either inside the first gigabyte (which has a
level-2 table, so it takes 2 MiB blocks) or whole gigabytes (a 1 GiB block
each).  Stated as the HAL's own refusal list, so a theorem over it is a theorem
that no refusal fires. -/
def rpi5BootRamExtensionAccepted (e : Nat × Nat) : Bool :=
  0 < e.2 && e.1 % 0x20_0000 == 0 && (e.1 + e.2) % 0x20_0000 == 0 &&
    decide (rpi5KernelReservedEnd ≤ e.1) && decide (e.1 + e.2 ≤ 2 ^ 39) &&
    (decide (e.1 + e.2 ≤ rpi5FirstGigabyteTop) ||
      (e.1 % 0x4000_0000 == 0 && (e.1 + e.2) % 0x4000_0000 == 0))

/-- **WS-BP BP4.6, BP7.10**: every extension of every admissible configuration
is one the HAL accepts — the first-gigabyte one because its top is on the
granule and at most the gigabyte, the other because every family size is whole
gigabytes.  A configuration that broke this would be refused on hardware with
the system halted; this is the theorem that none the binding installs can. -/
theorem rpi5BootRamExtensions_admissible (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BootRamExtensions v).all rpi5BootRamExtensionAccepted = true := by
  obtain ⟨hMem, hTop⟩ := hv
  have hKre := rpi5KernelReservedEnd_lt_of_admissible _ hTop
  obtain ⟨_, hLe, hMod⟩ := (rpi5LowRamTopAdmissible_iff _).mp hTop
  have hLow : rpi5BootRamExtensionAccepted
      (rpi5KernelReservedEnd, v.lowRamTop - rpi5KernelReservedEnd) = true := by
    unfold rpi5BootRamExtensionAccepted rpi5LowRamTopFloor rpi5LowRamGranule
      rpi5KernelReservedEnd rpi5FirstGigabyteTop at *
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_true,
      Nat.reducePow]
    omega
  have hHigh : rpi5FirstGigabyteTop < v.ramSize → rpi5BootRamExtensionAccepted
      (rpi5FirstGigabyteTop, v.ramSize - rpi5FirstGigabyteTop) = true := by
    have hSize : v.ramSize = v.uncut.ramSize := rfl
    rw [hSize]
    simp only [rpi5Variants, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with h | h | h | h | h <;> rw [h] <;> decide
  rw [rpi5BootRamExtensions_eq v hKre]
  by_cases hG : rpi5FirstGigabyteTop < v.ramSize
  · simp [hG, hLow, hHigh hG]
  · simp [hG, hLow]

end SeLe4n.Platform.RPi5
