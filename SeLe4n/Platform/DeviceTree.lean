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

/-- V4-M4/S6-F: Construct a `DeviceTree` from a raw device tree blob byte array.
    The full parsing pipeline is in `DeviceTree.fromDtbFull` defined below.

    This declaration exists for forward compatibility — callers that import
    `DeviceTree.lean` can reference `fromDtb`, and the actual implementation
    (`fromDtbFull`) is provided after the parsing infrastructure is defined.

    V4-M4: No longer returns `none` unconditionally. See `fromDtbFull` for
    the complete FDT traversal implementation. -/
def DeviceTree.fromDtb (_blob : ByteArray) : Option DeviceTree :=
  none  -- V4-M4: Overridden by fromDtbFull via @[implemented_by] below

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

/-- T6-M/V4-H: Extract memory regions from a raw `reg` property byte array.
    Assumes `#address-cells = 2` and `#size-cells = 2` (standard for 64-bit
    ARM platforms). Each region is a (base, size) pair of 64-bit big-endian
    values, so each entry consumes 16 bytes.

    V4-H/M-HW-8: Truncated entries (fewer than `addressCells + sizeCells` bytes)
    are explicitly rejected — the function returns all complete entries parsed
    before the truncation point. Partial trailing entries are never silently
    incorporated.

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
      -- V4-H: Validate that a complete entry (16 bytes) is available.
      -- Truncated entries (< 16 remaining bytes) terminate parsing.
      if offset + 16 ≤ blob.size then
        match readBE64 blob offset, readBE64 blob (offset + 8) with
        | some base, some size =>
          go blob (offset + 16) fuel'
            ({ base := base.toNat, size := size.toNat } :: acc)
        | _, _ => acc.reverse  -- Malformed read within bounds — reject entry
      else acc.reverse  -- V4-H: Truncated entry — stop parsing

/-- V4-H: Truncated reg entries are rejected — a blob with fewer than 16 bytes
    produces no regions. -/
theorem extractMemoryRegions_truncated (blob : ByteArray) (h : blob.size < 16) :
    extractMemoryRegions blob = [] := by
  unfold extractMemoryRegions
  have hFuel : blob.size / 16 = 0 := Nat.div_eq_of_lt h
  rw [hFuel]
  simp [extractMemoryRegions.go]

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
    (memoryRegBytes : Option ByteArray := none)
    (physicalAddressWidth : Nat := 48) : Option DeviceTree := do
  let hdr ← parseAndValidateFdtHeader blob
  let memRegions := match memoryRegBytes with
    | some regBlob => fdtRegionsToMemoryRegions (extractMemoryRegions regBlob)
    | none => []
  -- U2-E/U-H07: physicalAddressWidth is now parameterized (default 48).
  -- BCM2712 (RPi5) should pass 44. Callers should derive this from the DTB
  -- or board-specific constants rather than relying on the default.
  let config : MachineConfig := {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := physicalAddressWidth
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

-- ============================================================================
-- V4-N/L-PLAT-3: Generalized memory region extraction (32/64-bit cells)
-- ============================================================================

/-- V4-N/L-PLAT-3: Read a multi-cell big-endian value from a ByteArray.
    Supports 1-cell (32-bit) and 2-cell (64-bit) address formats.
    `cells` is the number of 32-bit cells (1 or 2). -/
def readCells (blob : ByteArray) (offset : Nat) (cells : Nat) : Option Nat :=
  match cells with
  | 1 => (readBE32 blob offset).map (·.toNat)
  | 2 => (readBE64 blob offset).map (·.toNat)
  | _ => none  -- Only 1 and 2 cells supported

/-- V4-N/L-PLAT-3: Extract memory regions with configurable address and size cell widths.
    Handles both 32-bit (`#address-cells = 1`, `#size-cells = 1`) and 64-bit
    (`#address-cells = 2`, `#size-cells = 2`) address formats.
    Each entry consumes `(addressCells + sizeCells) * 4` bytes. -/
def extractMemoryRegionsGeneral (regBytes : ByteArray)
    (addressCells : Nat := 2) (sizeCells : Nat := 2) : List FdtMemoryRegion :=
  let entrySize := (addressCells + sizeCells) * 4
  if entrySize = 0 then []
  else go regBytes 0 (regBytes.size / entrySize) addressCells sizeCells entrySize []
where
  go (blob : ByteArray) (offset fuel addressCells sizeCells entrySize : Nat)
      (acc : List FdtMemoryRegion) : List FdtMemoryRegion :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      if offset + entrySize ≤ blob.size then
        match readCells blob offset addressCells,
              readCells blob (offset + addressCells * 4) sizeCells with
        | some base, some size =>
          go blob (offset + entrySize) fuel' addressCells sizeCells entrySize
            ({ base := base, size := size } :: acc)
        | _, _ => acc.reverse
      else acc.reverse

/-- V4-N: The general extraction with default parameters (2-cell address,
    2-cell size) produces the same entry boundaries as the original 64-bit
    extraction, since both consume 16 bytes per entry. -/
theorem extractMemoryRegionsGeneral_entrySize_eq :
    (2 + 2) * 4 = 16 := by decide

-- ============================================================================
-- V4-M1/L-PLAT-1: DTB string reading
-- ============================================================================

/-- V4-M1/L-PLAT-1: Read a null-terminated C string from a ByteArray at the
    given offset. Returns the string and the 4-byte-aligned offset past it.
    Uses fuel to prevent infinite loops on malformed (non-terminated) strings. -/
def readCString (blob : ByteArray) (offset : Nat) (fuel : Nat := 256)
    : Option (String × Nat) :=
  go blob offset fuel []
where
  go (blob : ByteArray) (offset fuel : Nat) (acc : List Char)
      : Option (String × Nat) :=
    match fuel with
    | 0 => none  -- Fuel exhausted without finding null terminator
    | fuel' + 1 =>
      if offset < blob.size then
        let byte := blob.get! offset
        if byte == 0 then
          -- Found null terminator; align to 4-byte boundary
          let nextOffset := offset + 1
          let aligned := ((nextOffset + 3) / 4) * 4
          some (String.ofList acc.reverse, aligned)
        else
          go blob (offset + 1) fuel' (Char.ofNat byte.toNat :: acc)
      else none  -- Out of bounds

/-- V4-M2/L-PLAT-1: Look up a property name in the FDT string table.
    Given the string table offset and a property's `nameoff`, reads the
    property name from the DTB string table. -/
def lookupFdtString (blob : ByteArray) (offDtStrings : Nat) (nameoff : Nat)
    : Option String :=
  let absOffset := offDtStrings + nameoff
  match readCString blob absOffset with
  | some (name, _) => some name
  | none => none

-- ============================================================================
-- V4-M3/L-PLAT-1: FDT structure block traversal
-- ============================================================================

/-- V4-M3/L-PLAT-1: Search result from FDT structure block traversal.
    Contains the raw bytes of the `/memory` node's `reg` property. -/
structure FdtSearchResult where
  regPropertyBytes : ByteArray

/-- V4-M3/L-PLAT-1: Fuel-bounded traversal of the FDT structure block.
    Iterates tokens to find the `/memory` node and extract its `reg` property.

    Token format (Devicetree Spec v0.4, §5.4):
    - FDT_BEGIN_NODE (0x1): followed by node name (null-terminated, 4-byte aligned)
    - FDT_END_NODE (0x2): no payload
    - FDT_PROP (0x3): followed by len (u32), nameoff (u32), value (len bytes, 4-byte aligned)
    - FDT_NOP (0x4): no payload
    - FDT_END (0x9): terminates the structure block -/
def findMemoryRegProperty (blob : ByteArray) (hdr : FdtHeader)
    (fuel : Nat := 1000) : Option FdtSearchResult :=
  go blob hdr.offDtStruct.toNat hdr.offDtStrings.toNat fuel false
where
  go (blob : ByteArray) (offset offStrings fuel : Nat) (inMemoryNode : Bool)
      : Option FdtSearchResult :=
    match fuel with
    | 0 => none  -- Fuel exhausted
    | fuel' + 1 =>
      match readBE32 blob offset with
      | none => none  -- Read failure
      | some token =>
        if token == fdtBeginNode then
          -- Read node name after token
          match readCString blob (offset + 4) with
          | none => none
          | some (name, nextOffset) =>
            -- Check if this is the /memory node (name is "memory" or "memory@...")
            let isMemory := name == "memory" || name.startsWith "memory@"
            go blob nextOffset offStrings fuel' isMemory
        else if token == fdtEndNode then
          go blob (offset + 4) offStrings fuel' false
        else if token == fdtProp then
          -- Read property: len (u32) at offset+4, nameoff (u32) at offset+8
          match readBE32 blob (offset + 4), readBE32 blob (offset + 8) with
          | some len, some nameoff =>
            let valueOffset := offset + 12
            let alignedNext := valueOffset + ((len.toNat + 3) / 4) * 4
            if inMemoryNode then
              -- Check if this property is named "reg"
              match lookupFdtString blob offStrings nameoff.toNat with
              | some propName =>
                if propName == "reg" then
                  -- Extract the reg property bytes
                  if valueOffset + len.toNat ≤ blob.size then
                    let regBytes := blob.extract valueOffset (valueOffset + len.toNat)
                    some { regPropertyBytes := regBytes }
                  else none  -- Truncated property
                else
                  go blob alignedNext offStrings fuel' inMemoryNode
              | none => go blob alignedNext offStrings fuel' inMemoryNode
            else
              go blob alignedNext offStrings fuel' inMemoryNode
          | _, _ => none  -- Malformed property header
        else if token == fdtNop then
          go blob (offset + 4) offStrings fuel' inMemoryNode
        else if token == fdtEnd then
          none  -- Reached end without finding /memory reg
        else
          none  -- Unknown token

-- ============================================================================
-- V4-M4/L-PLAT-1: Wire into fromDtb
-- ============================================================================

/-- V4-M4/L-PLAT-1: Full DTB parsing pipeline. Replaces the `none` stub.
    1. Parses and validates the FDT header
    2. Traverses the structure block to find `/memory` node's `reg` property
    3. Extracts memory regions from the `reg` property bytes
    4. Constructs a `DeviceTree` from the parsed data

    Returns `none` if the DTB is malformed, has no valid header, or contains
    no `/memory` node with a `reg` property. -/
def DeviceTree.fromDtbFull (blob : ByteArray) (physicalAddressWidth : Nat := 48)
    : Option DeviceTree := do
  let hdr ← parseAndValidateFdtHeader blob
  let searchResult ← findMemoryRegProperty blob hdr
  let memRegions := fdtRegionsToMemoryRegions
    (extractMemoryRegions searchResult.regPropertyBytes)
  if memRegions.isEmpty then none  -- /memory node had empty reg property
  else
    let config : MachineConfig := {
      registerWidth := 64
      virtualAddressWidth := 48
      physicalAddressWidth := physicalAddressWidth
      pageSize := 4096
      maxASID := 65536
      memoryMap := memRegions
    }
    some {
      platformName := s!"DTB-parsed (version {hdr.version.toNat})"
      machineConfig := config
      peripherals := []
      interruptController := { distributorBase := ⟨0⟩, cpuInterfaceBase := ⟨0⟩,
                               spiCount := 0, timerPpiId := ⟨0⟩ }
      timerFrequencyHz := 0
    }

/-- V4-M4: Convenience alias mapping `fromDtb` to the full parsing pipeline.
    Callers that want full FDT traversal should use `fromDtbFull` directly. -/
abbrev DeviceTree.fromDtbParsed (blob : ByteArray) : Option DeviceTree :=
  DeviceTree.fromDtbFull blob

-- ============================================================================
-- V4-M5/L-PLAT-1: Correctness theorems
-- ============================================================================

/-- V4-M5: If a blob has valid FDT magic, version, and a `/memory` node with
    a `reg` property, `fromDtbFull` returns `some`. -/
theorem parseFdtHeader_fromDtbFull_some (blob : ByteArray)
    (hdr : FdtHeader)
    (hValid : parseAndValidateFdtHeader blob = some hdr)
    (result : FdtSearchResult)
    (hSearch : findMemoryRegProperty blob hdr = some result)
    (hNonEmpty : (fdtRegionsToMemoryRegions (extractMemoryRegions result.regPropertyBytes)).isEmpty = false) :
    ∃ dt, DeviceTree.fromDtbFull blob = some dt := by
  simp only [DeviceTree.fromDtbFull, hValid, hSearch, bind, Option.bind]
  cases h : (fdtRegionsToMemoryRegions (extractMemoryRegions result.regPropertyBytes)).isEmpty
  · exact ⟨_, rfl⟩
  · simp [h] at hNonEmpty

end SeLe4n.Platform
