/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

/-!
# S6-F: Device Tree Abstraction

This module defines the `DeviceTree` structure — a platform-independent
representation of board configuration that can be populated either from
hardcoded constants (current approach) or from a parsed device tree blob
(future work for WS-T hardware binding).

## Design rationale

The Raspberry Pi 5 (and most ARM64 platforms) uses device tree blobs (DTBs)
to describe hardware topology at boot time. The bootloader (ARM Trusted
Firmware / U-Boot) passes a DTB pointer to the kernel, which parses it to
discover:

- Physical memory regions (RAM, device, reserved)
- Peripheral base addresses (UART, GIC, timers)
- Interrupt controller configuration
- CPU topology

Currently, `RPi5/Board.lean` hardcodes these values. This module provides
an abstraction layer so that:

1. **Static validation**: `DeviceTree.fromBoardConstants` constructs a
   `DeviceTree` from hardcoded constants, enabling compile-time consistency
   checks.
2. **Future DTB parsing**: `DeviceTree.fromDtb` (stub) will construct a
   `DeviceTree` from a raw DTB byte array, enabling runtime discovery.
3. **Platform-independent kernel**: The kernel operates on `DeviceTree`
   values, not platform-specific constants.

## Status

S6-F preparation — structure and static constructor defined. DTB parsing
is deferred to WS-T (Raspberry Pi 5 Hardware Binding).
-/

namespace SeLe4n.Platform

open SeLe4n

/-- S6-F: A peripheral device entry in the device tree.
    Describes a single MMIO-mapped hardware peripheral. -/
structure DeviceEntry where
  /-- Human-readable name (e.g., "uart0", "gic-distributor"). -/
  name : String
  /-- Base physical address of the peripheral's register space. -/
  base : PAddr
  /-- Size of the register space in bytes. -/
  size : Nat
  /-- Optional IRQ number associated with this peripheral. -/
  irq : Option Irq := none
  deriving Repr

/-- S6-F: An interrupt controller description in the device tree. -/
structure InterruptControllerInfo where
  /-- Distributor base address. -/
  distributorBase : PAddr
  /-- CPU interface base address. -/
  cpuInterfaceBase : PAddr
  /-- Number of supported shared peripheral interrupts (SPIs). -/
  spiCount : Nat
  /-- Timer PPI (Private Peripheral Interrupt) ID. -/
  timerPpiId : Irq
  deriving Repr

/-- S6-F: Platform board configuration parsed from device tree or constants.

    This structure captures all hardware-specific parameters that the kernel
    needs to configure itself at boot time. It serves as the single source
    of truth for platform configuration, replacing scattered hardcoded
    constants.

    **Invariant**: `memoryMap` must satisfy `MachineConfig.wellFormed` when
    combined with `machineConfig`. This is checked by `DeviceTree.validate`. -/
structure DeviceTree where
  /-- Platform identification string. -/
  platformName : String
  /-- Architectural parameters (register width, address widths, page size). -/
  machineConfig : MachineConfig
  /-- Peripheral devices discovered from the device tree. -/
  peripherals : List DeviceEntry
  /-- Interrupt controller configuration. -/
  interruptController : InterruptControllerInfo
  /-- Timer frequency in Hz (from CNTFRQ_EL0 or device tree). -/
  timerFrequencyHz : Nat
  /-- Debug console UART base address. -/
  debugUartBase : Option PAddr := none
  deriving Repr

/-- S6-F: Validate that a device tree's machine configuration is well-formed.
    Returns `true` iff the memory map has non-overlapping regions with valid
    sizes, and all region addresses fit within the physical address width. -/
def DeviceTree.validate (dt : DeviceTree) : Bool :=
  dt.machineConfig.wellFormed

/-- S6-F: Construct a `DeviceTree` from hardcoded board constants.
    This is the current path — all values come from compile-time constants
    in `RPi5/Board.lean`. The result can be validated at compile time via
    `native_decide` on `DeviceTree.validate`. -/
def DeviceTree.fromBoardConstants
    (name : String)
    (config : MachineConfig)
    (peripherals : List DeviceEntry)
    (ic : InterruptControllerInfo)
    (timerHz : Nat)
    (uartBase : Option PAddr := none) : DeviceTree :=
  { platformName := name
    machineConfig := config
    peripherals := peripherals
    interruptController := ic
    timerFrequencyHz := timerHz
    debugUartBase := uartBase }

/-- S6-F: Stub for future DTB parsing.
    Will construct a `DeviceTree` from a raw device tree blob byte array.
    Returns `none` if the DTB is malformed or contains unsupported nodes.

    **WS-T**: This function will be implemented during the Raspberry Pi 5
    hardware binding workstream. The DTB format follows the Devicetree
    Specification (v0.4) — a flattened tree of nodes with properties,
    starting with an `fdt_header` structure. -/
def DeviceTree.fromDtb (_blob : ByteArray) : Option DeviceTree :=
  none  -- WS-T: DTB parsing not yet implemented

-- ============================================================================
-- T6-M/M-ARCH-2: DTB parsing foundation
-- ============================================================================

/-! ## T6-M: Flattened Device Tree (FDT) Header Parsing

The Flattened Device Tree (FDT) format is defined by the Devicetree
Specification v0.4. An FDT blob begins with an `fdt_header` structure:

| Offset | Size | Field |
|--------|------|-------|
| 0x00 | 4 | magic (0xD00DFEED) |
| 0x04 | 4 | totalsize |
| 0x08 | 4 | off_dt_struct |
| 0x0C | 4 | off_dt_strings |
| 0x10 | 4 | off_mem_rsvmap |
| 0x14 | 4 | version |
| 0x18 | 4 | last_comp_version |
| 0x1C | 4 | boot_cpuid_phys |
| 0x20 | 4 | size_dt_strings |
| 0x24 | 4 | size_dt_struct |

This module implements header parsing and memory region extraction from the
`/memory` node. Full node traversal (including `/chosen`, `/cpus`, and
interrupt controllers) is deferred to WS-U. -/

/-- T6-M: FDT magic number (big-endian). -/
def fdtMagic : UInt32 := 0xD00DFEED

/-- T6-M: Parsed FDT header fields. -/
structure FdtHeader where
  magic : UInt32
  totalsize : UInt32
  offDtStruct : UInt32
  offDtStrings : UInt32
  offMemRsvmap : UInt32
  version : UInt32
  lastCompVersion : UInt32
  bootCpuidPhys : UInt32
  sizeDtStrings : UInt32
  sizeDtStruct : UInt32
  deriving Repr

/-- T6-M: Read a big-endian UInt32 from a ByteArray at the given offset.
    Returns `none` if the offset is out of bounds. -/
def readBE32 (blob : ByteArray) (offset : Nat) : Option UInt32 :=
  if offset + 4 ≤ blob.size then
    let b0 := blob.get! offset
    let b1 := blob.get! (offset + 1)
    let b2 := blob.get! (offset + 2)
    let b3 := blob.get! (offset + 3)
    some ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
          (b2.toUInt32 <<< 8) ||| b3.toUInt32)
  else none

/-- T6-M: Parse the FDT header from a device tree blob.
    Returns `none` if the blob is too small or has wrong magic. -/
def parseFdtHeader (blob : ByteArray) : Option FdtHeader := do
  if blob.size < 40 then none  -- Header is 40 bytes
  else
    let magic ← readBE32 blob 0
    if magic ≠ fdtMagic then none
    else
      let totalsize ← readBE32 blob 4
      let offDtStruct ← readBE32 blob 8
      let offDtStrings ← readBE32 blob 12
      let offMemRsvmap ← readBE32 blob 16
      let version ← readBE32 blob 20
      let lastCompVersion ← readBE32 blob 24
      let bootCpuidPhys ← readBE32 blob 28
      let sizeDtStrings ← readBE32 blob 32
      let sizeDtStruct ← readBE32 blob 36
      some { magic, totalsize, offDtStruct, offDtStrings, offMemRsvmap,
             version, lastCompVersion, bootCpuidPhys, sizeDtStrings, sizeDtStruct }

/-- T6-M: Validate an FDT header — magic is correct and sizes are consistent. -/
def FdtHeader.isValid (hdr : FdtHeader) : Bool :=
  hdr.magic == fdtMagic &&
  hdr.version.toNat ≥ 16 &&    -- Minimum supported DTB version
  hdr.totalsize.toNat ≥ 40 &&  -- At least header size
  hdr.offDtStruct.toNat < hdr.totalsize.toNat &&
  hdr.offDtStrings.toNat < hdr.totalsize.toNat

/-- T6-M: Parse FDT header and validate. Returns the header only if valid. -/
def parseAndValidateFdtHeader (blob : ByteArray) : Option FdtHeader := do
  let hdr ← parseFdtHeader blob
  if hdr.isValid then some hdr else none

/-- T6-M: Empty blobs have no valid FDT header. -/
theorem parseFdtHeader_empty :
    parseFdtHeader ByteArray.empty = none := by
  unfold parseFdtHeader
  simp only [ByteArray.size, ByteArray.empty, ByteArray.emptyWithCapacity]
  decide

-- ============================================================================
-- T6-M: FDT structure block constants and memory region extraction
-- ============================================================================

/-- T6-M: FDT token constants (Devicetree Specification v0.4, §5.4.1). -/
def fdtBeginNode : UInt32 := 0x00000001
def fdtEndNode   : UInt32 := 0x00000002
def fdtProp      : UInt32 := 0x00000003
def fdtNop       : UInt32 := 0x00000004
def fdtEnd       : UInt32 := 0x00000009

/-- T6-M: A parsed memory region from the `/memory` node's `reg` property.
    The `reg` property contains pairs of (base, size) as big-endian integers
    whose width is determined by the `#address-cells` and `#size-cells`
    properties of the parent node (typically both 2 for 64-bit platforms). -/
structure FdtMemoryRegion where
  base : Nat
  size : Nat
  deriving Repr

/-- T6-M: Read a big-endian UInt64 from a ByteArray at the given offset.
    Used for 64-bit address/size values in FDT `reg` properties on
    platforms with `#address-cells = 2` and `#size-cells = 2`. -/
def readBE64 (blob : ByteArray) (offset : Nat) : Option UInt64 :=
  if offset + 8 ≤ blob.size then
    match readBE32 blob offset, readBE32 blob (offset + 4) with
    | some hi, some lo => some ((hi.toUInt64 <<< 32) ||| lo.toUInt64)
    | _, _ => none
  else none

/-- T6-M: Extract memory regions from a raw `reg` property byte array.
    Assumes `#address-cells = 2` and `#size-cells = 2` (standard for 64-bit
    ARM platforms). Each region is a (base, size) pair of 64-bit big-endian
    values, so each entry consumes 16 bytes.

    **Fuel parameter**: Limits iteration to prevent infinite loops on
    malformed inputs. Set to `regBytes.size / 16` for well-formed data. -/
def extractMemoryRegions (regBytes : ByteArray) (fuel : Nat := regBytes.size / 16)
    : List FdtMemoryRegion :=
  go regBytes 0 fuel []
where
  go (blob : ByteArray) (offset : Nat) (fuel : Nat) (acc : List FdtMemoryRegion)
      : List FdtMemoryRegion :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      if offset + 16 ≤ blob.size then
        match readBE64 blob offset, readBE64 blob (offset + 8) with
        | some base, some size =>
          go blob (offset + 16) fuel'
            ({ base := base.toNat, size := size.toNat } :: acc)
        | _, _ => acc.reverse
      else acc.reverse

/-- T6-M: Classify an FDT memory region as a `MemoryKind`.
    RAM regions have `kind = .ram`. Device regions are not present in the
    `/memory` node — they come from individual device nodes (deferred to WS-U).
    Reserved regions are identified by the memory reservation block. -/
def classifyMemoryRegion (_region : FdtMemoryRegion) : MemoryKind :=
  .ram  -- /memory node entries are always RAM

/-- T6-M: Convert parsed FDT memory regions to `MemoryRegion` values. -/
def fdtRegionsToMemoryRegions (regions : List FdtMemoryRegion)
    : List MemoryRegion :=
  regions.map fun r =>
    { base := ⟨r.base⟩, size := r.size, kind := classifyMemoryRegion r }

/-- T6-M: Attempt to construct a `DeviceTree` from a DTB blob.
    Currently implements:
    1. FDT header parsing and validation
    2. Memory region extraction from raw `reg` property bytes (when provided)

    Full FDT structure block traversal (node/property iteration, string table
    lookup, `/chosen` and `/cpus` nodes) is deferred to WS-U. -/
def DeviceTree.fromDtbWithRegions (blob : ByteArray)
    (memoryRegBytes : Option ByteArray := none) : Option DeviceTree := do
  let hdr ← parseAndValidateFdtHeader blob
  let memRegions := match memoryRegBytes with
    | some regBlob => fdtRegionsToMemoryRegions (extractMemoryRegions regBlob)
    | none => []
  let config : MachineConfig := {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 48  -- default; platform-specific
    pageSize := 4096
    maxASID := 65536
    memoryMap := memRegions
  }
  some {
    platformName := s!"DTB-parsed (version {hdr.version.toNat})"
    machineConfig := config
    peripherals := []  -- WS-U: device node traversal
    interruptController := { distributorBase := ⟨0⟩, cpuInterfaceBase := ⟨0⟩,
                             spiCount := 0, timerPpiId := ⟨0⟩ }  -- WS-U: /interrupt-controller
    timerFrequencyHz := 0  -- WS-U: /timer or CNTFRQ_EL0
  }

/-- T6-M: Empty region bytes produce an empty memory map. -/
theorem extractMemoryRegions_empty :
    extractMemoryRegions ByteArray.empty = [] := by
  simp [extractMemoryRegions, extractMemoryRegions.go]

end SeLe4n.Platform
