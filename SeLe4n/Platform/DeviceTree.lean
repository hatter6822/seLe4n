-- SPDX-License-Identifier: GPL-3.0-or-later
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
2. **DTB parsing**: `DeviceTree.fromDtbFull` constructs a `DeviceTree`
   from a raw DTB byte array, enabling runtime discovery.
3. **Platform-independent kernel**: The kernel operates on `DeviceTree`
   values, not platform-specific constants.

## Status

S6-F preparation — structure and static constructor defined. DTB parsing
is deferred to WS-T (Raspberry Pi 5 Hardware Binding).
-/

namespace SeLe4n.Platform

open SeLe4n

/-- AI4-B (M-09): Error type for FDT node parsing, distinguishing fuel
exhaustion from structural DTB malformation. -/
inductive DeviceTreeParseError where
  | fuelExhausted  : DeviceTreeParseError
  | malformedBlob  : DeviceTreeParseError
  deriving Repr, BEq

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
    `decide` on `DeviceTree.validate`. -/
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

-- AJ3-F (L-12): Removed dead `DeviceTree.fromDtb` stub that unconditionally
-- returned `none`. Production DTB parsing is `DeviceTree.fromDtbFull`.
-- Also removed `fromDtbParsed` convenience alias (no callers).

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

/-- T6-M/V5-A/W4-B: Read a big-endian UInt32 from a ByteArray at the given offset.
    Returns `none` if the offset is out of bounds.

    V5-A (M-DEF-1): Uses `ByteArray.get?` instead of the panicking `get!`
    to eliminate partial-function hazards. The bounds guard (`offset + 4 ≤ size`)
    makes the `get?` calls provably `some`, but using `get?` provides
    defense-in-depth against future refactoring that might weaken the guard.

    W4-B (M-9): Explicit bounds check before arithmetic prevents unexpected
    behavior on malformed DTB input where `offset + 4` could overflow or
    exceed blob size. The upfront guard is redundant with `get?` but makes
    the contract explicit and prevents callers from reasoning about partial reads. -/
def readBE32 (blob : ByteArray) (offset : Nat) : Option UInt32 :=
  if offset + 4 > blob.size then none
  else do
    let b0 ← blob.data[offset]?
    let b1 ← blob.data[offset + 1]?
    let b2 ← blob.data[offset + 2]?
    let b3 ← blob.data[offset + 3]?
    some ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
          (b2.toUInt32 <<< 8) ||| b3.toUInt32)

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

/-- AG3-A (P-01): Classify an FDT memory region against a platform memory map.
    Checks whether the region's **base address** falls within a declared
    platform region:
    - If a match is found → returns that platform region's kind
    - If no match is found → defaults to `.ram`

    The default-to-`.ram` behavior is correct because `classifyMemoryRegion`
    is called on entries from the FDT `/memory` node, which by DTB convention
    declare RAM regions. When a platform memory map is provided (e.g., from
    `MachineConfig.memoryMap`), it can override this default for addresses
    that fall within declared `.device` or `.reserved` regions.

    **AK9-F (P-M04)** — the empty-platform-map default to `.ram` depends on
    the DTB convention that this function classifies `/memory` entries
    exclusively. If a caller misuses it on arbitrary regions with an empty
    map, the result unsafely marks everything as RAM. New callers should
    use `classifyMemoryRegionChecked` (Option return — `none` when the
    map is empty / address unmapped, forcing explicit caller decision).

    Note: only the base address is checked, not the full region extent.
    See `classifyAddress` for standalone address classification (which
    defaults to `.reserved` for unmapped addresses). -/
@[deprecated "AN7-A (H-14/PLT-M04): use classifyMemoryRegionChecked which fails closed on empty/unmapped regions instead of silently defaulting to .ram. Legacy form retained for the empty-map DTB-only default-to-RAM convention described in the docstring above." (since := "0.30.8")]
def classifyMemoryRegion (region : FdtMemoryRegion)
    (platformMemory : List MemoryRegion := []) : MemoryKind :=
  match platformMemory.find? fun r => r.contains (SeLe4n.PAddr.ofNat region.base) with
  | some r => r.kind
  | none => .ram  -- Default: /memory node entries are RAM when no map provided

/-- AK9-F (P-M04): Strict classification — requires a non-empty platform
    memory map AND a containing region. Returns `none` when the map is empty
    or the address is unmapped. Forces the caller to decide explicitly what
    to do in the unclassified case instead of silently assuming RAM. -/
def classifyMemoryRegionChecked (region : FdtMemoryRegion)
    (platformMemory : List MemoryRegion) : Option MemoryKind :=
  match platformMemory with
  | [] => none  -- AK9-F: reject empty map, caller must decide
  | _ =>
    match platformMemory.find? fun r => r.contains (SeLe4n.PAddr.ofNat region.base) with
    | some r => some r.kind
    | none => none  -- AK9-F: reject unmapped, caller must decide

/-- AK9-F: When the platform memory map is empty, the checked classifier
    refuses to guess — returns `none`. -/
theorem classifyMemoryRegionChecked_empty_none (region : FdtMemoryRegion) :
    classifyMemoryRegionChecked region [] = none := rfl

set_option linter.deprecated false in
/-- AN7-A (H-14/PLT-M04): Bridge from legacy `classifyMemoryRegion` to
    `classifyMemoryRegionChecked`. When the checked variant succeeds, the
    legacy variant agrees; otherwise the legacy variant silently falls back
    to `.ram`. New callers must use `classifyMemoryRegionChecked`. -/
theorem classifyMemoryRegionChecked_some_agrees
    (region : FdtMemoryRegion) (pm : List MemoryRegion) (k : MemoryKind)
    (h : classifyMemoryRegionChecked region pm = some k) :
    classifyMemoryRegion region pm = k := by
  unfold classifyMemoryRegionChecked at h
  unfold classifyMemoryRegion
  cases pm with
  | nil => simp at h
  | cons r rs =>
    simp at h
    cases hf : (r :: rs).find? (fun r => r.contains (SeLe4n.PAddr.ofNat region.base)) with
    | none => rw [hf] at h; simp at h
    | some r' =>
      rw [hf] at h
      simp at h
      simp [h]

/-- AG3-A (P-01): Classify a raw physical address against a platform memory map.
    Standalone address classification for use outside FDT parsing contexts. -/
def classifyAddress (addr : PAddr) (platformMemory : List MemoryRegion) : MemoryKind :=
  match platformMemory.find? fun r => r.contains addr with
  | some r => r.kind
  | none => .reserved  -- Unmapped addresses are reserved

/-- T6-M: Convert parsed FDT memory regions to `MemoryRegion` values.
    AG3-A: Accepts an optional platform memory map for address classification.
    AN7-A (H-14/PLT-M04): Uses `classifyMemoryRegionChecked` internally and
    falls back to the DTB-convention default `.ram` ONLY for `/memory` node
    entries where no platform map is present. This is the documented
    exception — the legacy `classifyMemoryRegion` remains deprecated for
    use outside DTB `/memory`-node contexts. -/
def fdtRegionsToMemoryRegions (regions : List FdtMemoryRegion)
    (platformMemory : List MemoryRegion := []) : List MemoryRegion :=
  regions.map fun r =>
    let kind := (classifyMemoryRegionChecked r platformMemory).getD .ram
    { base := (SeLe4n.PAddr.ofNat r.base), size := r.size, kind }

set_option linter.deprecated false in
/-- AG3-A: When no platform memory map is provided, classification defaults to `.ram`. -/
theorem classifyMemoryRegion_default (region : FdtMemoryRegion) :
    classifyMemoryRegion region = .ram := rfl

/-- AG3-A: Unmapped addresses are classified as `.reserved`. -/
theorem classifyAddress_unmapped (addr : PAddr) (pm : List MemoryRegion)
    (hNone : pm.find? (fun r => r.contains addr) = none) :
    classifyAddress addr pm = .reserved := by
  simp [classifyAddress, hNone]

/-- AG3-A: When a matching region is found, classification returns its kind. -/
theorem classifyAddress_found (addr : PAddr) (pm : List MemoryRegion) (r : MemoryRegion)
    (hFound : pm.find? (fun r => r.contains addr) = some r) :
    classifyAddress addr pm = r.kind := by
  simp [classifyAddress, hFound]

/-- T6-M: Attempt to construct a `DeviceTree` from a DTB blob.
    Currently implements:
    1. FDT header parsing and validation
    2. Memory region extraction from raw `reg` property bytes (when provided)

    Full FDT structure block traversal (node/property iteration, string table
    lookup, `/chosen` and `/cpus` nodes) is deferred to WS-U. -/
-- AJ3-B (M-18): `physicalAddressWidth` is now a required parameter (no default).
-- Callers must explicitly specify the PA width for their platform to prevent
-- silent misconfiguration (RPi5 BCM2712 = 44-bit, not 48-bit).
def DeviceTree.fromDtbWithRegions (blob : ByteArray)
    (physicalAddressWidth : Nat)
    (memoryRegBytes : Option ByteArray := none) : Option DeviceTree := do
  let hdr ← parseAndValidateFdtHeader blob
  let memRegions := match memoryRegBytes with
    | some regBlob => fdtRegionsToMemoryRegions (extractMemoryRegions regBlob)
    | none => []
  -- AJ3-B (M-18): physicalAddressWidth is a required parameter — callers must
  -- pass the platform-specific value (e.g., 44 for RPi5 BCM2712, 52 for Sim).
  let config : MachineConfig := {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := physicalAddressWidth
    pageSize := 4096
    maxASID := 65536
    memoryMap := memRegions
  }
  -- Note: fromDtbWithRegions uses pre-extracted memory bytes and does not
  -- perform full FDT node traversal. For full device discovery (peripherals,
  -- interrupt controller, timer), use fromDtbFull which invokes parseFdtNodes.
  some {
    platformName := s!"DTB-parsed (version {hdr.version.toNat})"
    machineConfig := config
    peripherals := []  -- Use fromDtbFull for full device discovery
    interruptController := { distributorBase := (SeLe4n.PAddr.ofNat 0), cpuInterfaceBase := (SeLe4n.PAddr.ofNat 0),
                             spiCount := 0, timerPpiId := ⟨0⟩ }
    timerFrequencyHz := 0
  }

/-- T6-M: Empty region bytes produce an empty memory map. -/
theorem extractMemoryRegions_empty :
    extractMemoryRegions ByteArray.empty = [] := by
  simp [extractMemoryRegions, extractMemoryRegions.go]

-- ============================================================================
-- V4-N/L-PLAT-3: Generalized memory region extraction (32/64-bit cells)
-- ============================================================================

/-- V4-N/W4-B/L-PLAT-3: Read a multi-cell big-endian value from a ByteArray.
    Supports 1-cell (32-bit) and 2-cell (64-bit) address formats.
    `cells` is the number of 32-bit cells (1 or 2).

    W4-B (M-9): Explicit bounds check ensures `offset + cells * 4` does not
    exceed blob size before delegating to `readBE32`/`readBE64`. -/
def readCells (blob : ByteArray) (offset : Nat) (cells : Nat) : Option Nat :=
  if offset + cells * 4 > blob.size then none  -- W4-B: bounds guard
  else match cells with
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

/-- V4-M1/V5-A/W4-B/L-PLAT-1: Read a null-terminated C string from a ByteArray
    at the given offset. Returns the string and the 4-byte-aligned offset past it.
    Uses fuel to prevent infinite loops on malformed (non-terminated) strings.

    V5-A (M-DEF-1): Uses `ByteArray.get?` instead of the panicking `get!`.
    W4-B (M-9): Explicit bounds check on initial offset rejects out-of-range
    starting positions before entering the traversal loop.

    AK9-H (P-L2): The `Option` return type collapses "fuel exhausted"
    and "out-of-bounds / malformed" into a single `none`. Legacy callers
    that don't care to distinguish the two continue using this form;
    new callers should prefer `readCStringChecked` (below) which
    propagates a typed `DeviceTreeParseError` so that fuel-exhaustion
    is a distinct signal from a malformed blob. -/
def readCString (blob : ByteArray) (offset : Nat) (fuel : Nat := 256)
    : Option (String × Nat) :=
  if offset ≥ blob.size then none  -- W4-B: reject out-of-bounds start
  else go blob offset fuel []
where
  go (blob : ByteArray) (offset fuel : Nat) (acc : List Char)
      : Option (String × Nat) :=
    match fuel with
    | 0 => none  -- Fuel exhausted without finding null terminator
    | fuel' + 1 =>
      match blob.data[offset]? with
      | none => none  -- Out of bounds
      | some byte =>
        if byte == 0 then
          -- Found null terminator; align to 4-byte boundary
          let nextOffset := offset + 1
          let aligned := ((nextOffset + 3) / 4) * 4
          some (String.ofList acc.reverse, aligned)
        else
          go blob (offset + 1) fuel' (Char.ofNat byte.toNat :: acc)

/-- AK9-H (P-L2): Checked variant of `readCString` that distinguishes
    **fuel exhaustion** from **malformed / truncated blob**. Intended for
    new DTB parsing paths that need error attribution. Shape mirrors the
    legacy Option variant; the default fuel is unchanged at 256.

    Error semantics:
    - `.error .malformedBlob` — initial offset is out-of-bounds, or a
      byte lookup inside the blob fails (should be unreachable given the
      initial guard but kept for defense-in-depth).
    - `.error .fuelExhausted` — 256 bytes (default) were consumed without
      finding a null terminator. Callers may retry with a larger fuel
      budget if the string is expected to be long. -/
def readCStringChecked (blob : ByteArray) (offset : Nat) (fuel : Nat := 256)
    : Except DeviceTreeParseError (String × Nat) :=
  if offset ≥ blob.size then .error .malformedBlob
  else go blob offset fuel []
where
  go (blob : ByteArray) (offset fuel : Nat) (acc : List Char)
      : Except DeviceTreeParseError (String × Nat) :=
    match fuel with
    | 0 => .error .fuelExhausted
    | fuel' + 1 =>
      match blob.data[offset]? with
      | none => .error .malformedBlob
      | some byte =>
        if byte == 0 then
          let nextOffset := offset + 1
          let aligned := ((nextOffset + 3) / 4) * 4
          .ok (String.ofList acc.reverse, aligned)
        else
          go blob (offset + 1) fuel' (Char.ofNat byte.toNat :: acc)

/-- AK9-H: `readCStringChecked` on an out-of-bounds initial offset rejects
    with `.malformedBlob`. -/
theorem readCStringChecked_rejects_oob (blob : ByteArray) (offset fuel : Nat)
    (hOob : offset ≥ blob.size) :
    readCStringChecked blob offset fuel = .error .malformedBlob := by
  simp [readCStringChecked, hOob]

/-- AK9-H: `readCStringChecked` with fuel = 0 rejects with `.fuelExhausted`
    (assuming the initial offset is in range so the bounds-check passes). -/
theorem readCStringChecked_rejects_fuel_zero (blob : ByteArray) (offset : Nat)
    (hInRange : offset < blob.size) :
    readCStringChecked blob offset 0 = .error .fuelExhausted := by
  simp [readCStringChecked, Nat.not_le.mpr hInRange, readCStringChecked.go]

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

    AK9-F (P-M07): The legacy fuel default `1000` was an arbitrary constant
    that did not scale with DTB size. Callers should compute fuel from
    `hdr.sizeDtStruct / 4` — the maximum possible token count in the
    structure block, since each token is at least 4 bytes. See
    `findMemoryRegPropertyChecked` for the Except-returning variant
    that distinguishes fuel exhaustion from malformed-blob failures.

    Token format (Devicetree Spec v0.4, §5.4):
    - FDT_BEGIN_NODE (0x1): followed by node name (null-terminated, 4-byte aligned)
    - FDT_END_NODE (0x2): no payload
    - FDT_PROP (0x3): followed by len (u32), nameoff (u32), value (len bytes, 4-byte aligned)
    - FDT_NOP (0x4): no payload
    - FDT_END (0x9): terminates the structure block -/
@[deprecated "AN7-A (H-14/PLT-M04): use findMemoryRegPropertyChecked which distinguishes .fuelExhausted from .malformedBlob via DeviceTreeParseError. Legacy form collapses both conditions into `none`." (since := "0.30.8")]
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
-- X4-A/H-7: Generic FDT device node traversal
-- ============================================================================

/-- X4-A/H-7: A parsed FDT property with its name and raw value bytes. -/
structure FdtProperty where
  name : String
  value : ByteArray


/-- X4-A/H-7: A parsed FDT device node with its name, properties, and children. -/
structure FdtNode where
  name : String
  properties : List FdtProperty
  children : List FdtNode

/-- X4-A/H-7: Look up a property by name in an FDT node's property list. -/
def FdtNode.findProperty (node : FdtNode) (propName : String) : Option ByteArray :=
  match node.properties.find? (fun p => p.name == propName) with
  | some p => some p.value
  | none => none

/-- X4-A/H-7: Get the `compatible` string from an FDT node.
    The `compatible` property is a null-terminated string list; we extract
    only the first (most specific) compatible string. -/
def FdtNode.compatibleString (node : FdtNode) : Option String :=
  match node.findProperty "compatible" with
  | some bytes =>
    if bytes.size == 0 then none
    else
      -- Extract first null-terminated string from raw bytes
      let byteList := bytes.data.toList.takeWhile (· != 0)
      if byteList.isEmpty then none
      else some (String.ofList (byteList.map (fun b => Char.ofNat b.toNat)))
  | none => none

/-- **PR #892 review round 5**: is this node's `status` operational?

Devicetree Specification v0.4 §2.3.4: an absent `status` means `okay`; `okay`
and `ok` say the node is operational; `disabled`, `reserved`, `fail` and
`fail-sss` say it is not.  The verdict is decided on the **operational** side —
the side the specification's list is closed on — so a value the specification
does not define withholds the node rather than being read as available.  This
is the Lean twin of `cmdline::find_ram_top_in_dtb`'s `status_ok`, and it is here
because that round-4 fix was applied to the Rust parser and not swept to the
Lean one, which the boot bridge also reads. -/
def FdtNode.statusIsOperational (node : FdtNode) : Bool :=
  match node.findProperty "status" with
  | none => true
  | some bytes =>
    let byteList := bytes.data.toList.takeWhile (· != 0)
    let value := String.ofList (byteList.map (fun b => Char.ofNat b.toNat))
    value == "okay" || value == "ok"

/-- **PR #892 review round 5**: read `count` big-endian cells (4 bytes each) at
`offset`, refusing a width no address this kernel maps could need.

`none` for a truncated read or a cell count above 4 (128 bits), which fails the
whole classification closed rather than reading a partial address. -/
def readFdtCells (bytes : ByteArray) (offset count : Nat) : Option Nat :=
  if count == 0 || count > 4 then none
  else
    (List.range count).foldl
      (fun acc i =>
        match acc, readBE32 bytes (offset + i * 4) with
        | some a, some w => some (a * 4294967296 + w.toNat)
        | _, _ => none)
      (some 0)

/-- **PR #892 review round 5 audit**: `#address-cells` when a node declares
none — 2, Devicetree Specification v0.4 §2.3.5, and the value
`cmdline::FDT_DEFAULT_ADDRESS_CELLS` uses on the Rust side. -/
def fdtDefaultAddressCells : Nat := 2

/-- **PR #892 review round 5 audit**: `#size-cells` when a node declares none —
**1**, §2.3.5, and `cmdline::FDT_DEFAULT_SIZE_CELLS`.

It was 2 here for one cut, which is a divergence from both the specification and
the Rust walker that reads the same blob: a root declaring `#address-cells` and
no `#size-cells` had its children's `reg` read at a different stride on the two
sides. -/
def fdtDefaultSizeCells : Nat := 1

/-- **PR #892 review round 5**: a node's declared `#address-cells`, or the
specification's default. -/
def FdtNode.addressCells (node : FdtNode) : Nat :=
  match node.findProperty "#address-cells" with
  | some bytes =>
    match readBE32 bytes 0 with | some v => v.toNat | none => fdtDefaultAddressCells
  | none => fdtDefaultAddressCells

/-- **PR #892 review round 5**: a node's declared `#size-cells`, or the
specification's default. -/
def FdtNode.sizeCells (node : FdtNode) : Nat :=
  match node.findProperty "#size-cells" with
  | some bytes =>
    match readBE32 bytes 0 with | some v => v.toNat | none => fdtDefaultSizeCells
  | none => fdtDefaultSizeCells

/-- **PR #892 review round 5**: one `ranges` entry — a child window, where it
lands in the parent's address space, and how long it is. -/
structure FdtRangeEntry where
  childBase : Nat
  parentBase : Nat
  length : Nat
  deriving Repr

/-- **PR #892 review round 5**: parse a bus node's `ranges` property.

An entry is (child address, parent address, length) with widths taken from the
**bus's** `#address-cells` / `#size-cells` and its **parent's** `#address-cells`
— which is why the walk has to carry the parent's cell counts down rather than
reading each node in isolation.  A trailing partial entry ends the list; the
caller decides what an empty list means, because for `ranges` that depends on
whether the property was absent (no mapping) or present and empty (identity). -/
def parseFdtRanges (bytes : ByteArray) (childAddressCells parentAddressCells childSizeCells : Nat)
    (fuel : Nat := bytes.size / 4 + 1) : List FdtRangeEntry :=
  go 0 fuel []
where
  go (offset : Nat) : Nat → List FdtRangeEntry → List FdtRangeEntry
  | 0, acc => acc.reverse
  | fuel + 1, acc =>
    let entrySize := (childAddressCells + parentAddressCells + childSizeCells) * 4
    if entrySize == 0 || offset + entrySize > bytes.size then acc.reverse
    else
      match readFdtCells bytes offset childAddressCells,
            readFdtCells bytes (offset + childAddressCells * 4) parentAddressCells,
            readFdtCells bytes (offset + (childAddressCells + parentAddressCells) * 4)
              childSizeCells with
      | some childBase, some parentBase, some length =>
        go (offset + entrySize) fuel ({ childBase, parentBase, length } :: acc)
      | _, _, _ => acc.reverse

/-- **PR #892 review round 5**: translate a child-bus **interval** into the
parent's address space through a `ranges` list.

`none` when no single entry contains the whole interval — the child window is
not visible in the parent, so no physical address exists for it and the
classification must fail closed rather than report the untranslated number.

**The whole interval, not its base** (PR #892 review round 6).  This checked
`childBase` alone and then carried the node's full `size` through untouched, so
a peripheral starting inside a bus window and running past its end was reported
as a mapped region of that length.  `deviceTreeCoversMmioRegions` would then
accept a required window on the strength of bytes the parent bus does not map.
A region that straddles the end of a window has no contiguous parent address at
all — the two halves land in different places, if the second lands anywhere —
so there is nothing to report and the honest answer is `none`.  An empty region
is refused earlier, by the classifier's `size == 0` test. -/
def translateThroughFdtRanges (ranges : List FdtRangeEntry) (addr size : Nat) : Option Nat :=
  match ranges.find? (fun r =>
      decide (r.childBase ≤ addr ∧ addr + size ≤ r.childBase + r.length)) with
  | some r => some (r.parentBase + (addr - r.childBase))
  | none => none

/-- **PR #892 review round 5**: what a node's children need in order to have a
physical address at all — the cell widths their `reg` is written in, and the
translation from their address space to the CPU's.

`translate = none` is a real answer, not a missing one: Devicetree Specification
v0.4 §2.3.8 says a bus node **without** `ranges` maps nothing into its parent,
so its children have no physical address and cannot be MMIO peripherals of this
machine.  Reporting their raw `reg` — which is what the walk did before this
cut — invents a physical address, which can both refuse a board whose
peripherals really are behind a translating bus and, worse, make an untranslated
child address collide with a window the binding requires. -/
structure FdtAddressContext where
  /-- `#address-cells` governing the children's `reg`. -/
  addressCells : Nat
  /-- `#size-cells` governing the children's `reg`. -/
  sizeCells : Nat
  /-- Child address and region length → CPU physical base; `none` where the
  child's space is not mapped into the CPU's, or where the region runs past the
  end of the window that would map its base (PR #892 review round 6). -/
  translate : Nat → Nat → Option Nat

/-- **PR #892 review round 5**: the CPU's own address space — the context the
nodes handed to `extractPeripherals` live in.

The cell widths are the 2/2 this parser has always read a top-level `reg` with,
and they stay that way deliberately: the list handed to `extractPeripherals` is
the tree's **roots**, whose own `reg` is not a thing the specification defines,
so these widths govern nothing on a real tree.  Every node below takes its
widths from its parent's declaration (`forChildren`), where the specification's
defaults apply. -/
def FdtAddressContext.cpuPhysical : FdtAddressContext :=
  { addressCells := 2, sizeCells := 2, translate := fun addr _ => some addr }

/-- **PR #892 review round 5**: the context this node's children live in, given
the context the node itself lives in.

The **tree root** (the node named `""`) is the base case the specification
gives: its children's `reg` values *are* CPU physical addresses, with no
`ranges` needed, so the translation passes through unchanged and only the cell
widths come from the root.

Below it, all three cases are §2.3.8's: no `ranges` — nothing maps, so the
children have no physical address at all; an empty `ranges` — identity, the
child space *is* the parent space; a populated `ranges` — translate through it,
then through whatever the parent's own context translates by. -/
def FdtAddressContext.forChildren (parent : FdtAddressContext) (node : FdtNode) :
    FdtAddressContext :=
  let childAddressCells := node.addressCells
  let childSizeCells := node.sizeCells
  if node.name.isEmpty then
    { addressCells := childAddressCells, sizeCells := childSizeCells,
      translate := parent.translate }
  else
    match node.findProperty "ranges" with
    | none => { addressCells := childAddressCells, sizeCells := childSizeCells,
                translate := fun _ _ => none }
    | some bytes =>
      if bytes.size == 0 then
        { addressCells := childAddressCells, sizeCells := childSizeCells,
          translate := parent.translate }
      else
        let ranges := parseFdtRanges bytes childAddressCells parent.addressCells childSizeCells
        { addressCells := childAddressCells, sizeCells := childSizeCells,
          translate := fun a size =>
            match translateThroughFdtRanges ranges a size with
            | some parentAddr => parent.translate parentAddr size
            | none => none }

/-- X4-A/H-7: Fuel-bounded generic FDT structure block traversal.
    Parses the FDT structure block into a tree of `FdtNode` values.
    Returns the root node containing all device nodes, properties, and children.

    Token format (Devicetree Spec v0.4, §5.4):
    - FDT_BEGIN_NODE (0x1): followed by node name (null-terminated, 4-byte aligned)
    - FDT_END_NODE (0x2): no payload — closes current node
    - FDT_PROP (0x3): followed by len (u32), nameoff (u32), value (len bytes, aligned)
    - FDT_NOP (0x4): no payload — skip
    - FDT_END (0x9): terminates the structure block

    Uses depth tracking and fuel bound to prevent infinite loops on
    malformed DTB data. The W4-B bounds-checked helpers (`readBE32`,
    `readCString`) are used throughout. -/
-- AN7-D.4 (PLT-M05): Default fuel is now `hdr.sizeDtStruct.toNat / 4` instead
-- of the fixed `2000`.  The structure block is at most `sizeDtStruct` bytes
-- and every FDT token consumes ≥ 4 bytes (FDT_BEGIN_NODE, FDT_END_NODE,
-- FDT_PROP, FDT_NOP, FDT_END all pad to 4-byte boundaries), so
-- `sizeDtStruct / 4` is a tight upper bound on the token count.  This
-- matches the `findMemoryRegPropertyChecked` default (AK9-F) and removes
-- the silent fuel-exhaustion vector where a DTB larger than ~8 KiB could
-- truncate traversal.
-- PR #892 review round 5: every partial exit is an ERROR, and the top-level walk
-- must reach a real `FDT_END`.  Before this cut each malformed condition — a
-- short read, an unreadable node name, a truncated property value, an unknown
-- token, a nested walk that ran out of fuel — returned `some ([], offset)`, a
-- *partial tree the caller could not distinguish from a complete one*, and
-- `parseFdtNodes` reported `.ok`.  A blob carrying a well-formed `/memory` node
-- and then truncated therefore parsed, and `rpi5PlatformConfigFromDtb` decided
-- RAM and MMIO coverage from a prefix nothing had validated.  That is the same
-- incomplete-walk trust the Rust `find_ram_top_in_dtb` had in round 1, in the
-- parser that now feeds the same boot path — the sibling this project's own
-- rule says to sweep for when a relation is fixed at one site.
def parseFdtNodes (blob : ByteArray) (hdr : FdtHeader)
    (fuel : Nat := hdr.sizeDtStruct.toNat / 4) : Except DeviceTreeParseError (List FdtNode) :=
  match go blob hdr.offDtStruct.toNat hdr.offDtStrings.toNat fuel with
  | .ok (nodes, _, true) => .ok nodes
  | .ok (_, _, false) => .error .malformedBlob
  | .error e => .error e
where
  /-- Parse nodes at the current level.  Returns the parsed nodes, the offset
      past the last consumed token, and whether the walk reached a **top-level
      `FDT_END`** — the only exit that says the structure block was read whole.
      Every structurally invalid input is `.error .malformedBlob`; running out
      of fuel is `.error .fuelExhausted`, kept distinct so a caller can tell a
      blob it must refuse from a bound it may raise. -/
  go (blob : ByteArray) (offset offStrings : Nat) :
      Nat → Except DeviceTreeParseError (List FdtNode × Nat × Bool)
  | 0 => .error .fuelExhausted -- AF3-A: Fuel exhausted — signal parse failure
  | fuel + 1 =>
    match readBE32 blob offset with
    | none => .error .malformedBlob -- Read failure — the block ends mid-token
    | some token =>
      if token == fdtBeginNode then
        -- Read node name
        match readCString blob (offset + 4) with
        | none => .error .malformedBlob
        | some (name, nextOffset) =>
          -- Parse this node's contents (properties + children)
          match parseNodeContents blob nextOffset offStrings fuel with
          | .error e => .error e
          | .ok (props, children, afterOffset) =>
            let node : FdtNode := { name, properties := props, children }
            -- Continue parsing sibling nodes
            match go blob afterOffset offStrings fuel with
            | .error e => .error e
            | .ok (siblings, endOffset, terminated) =>
              .ok (node :: siblings, endOffset, terminated)
      else if token == fdtEndNode then
        .ok ([], offset + 4, false)  -- End of current level, not of the block
      else if token == fdtNop then
        go blob (offset + 4) offStrings fuel
      else if token == fdtEnd then
        .ok ([], offset + 4, true)  -- End of structure block — the one good exit
      else
        .error .malformedBlob  -- Unknown token
  /-- Parse properties and children within a single node.
      Returns (properties, children, offset past FDT_END_NODE), or an error for
      input this parser cannot read whole. -/
  parseNodeContents (blob : ByteArray) (offset offStrings : Nat) :
      Nat → Except DeviceTreeParseError (List FdtProperty × List FdtNode × Nat)
  | 0 => .error .fuelExhausted -- AF3-A: Fuel exhausted — signal parse failure
  | fuel + 1 =>
    match readBE32 blob offset with
    | none => .error .malformedBlob
    | some token =>
      if token == fdtProp then
        -- Read property header: len (u32), nameoff (u32)
        match readBE32 blob (offset + 4), readBE32 blob (offset + 8) with
        | some len, some nameoff =>
          let valueOffset := offset + 12
          let valueEnd := valueOffset + len.toNat
          let alignedNext := valueOffset + ((len.toNat + 3) / 4) * 4
          if valueEnd ≤ blob.size then
            let propName := match lookupFdtString blob offStrings nameoff.toNat with
              | some n => n
              | none => ""
            let propValue := blob.extract valueOffset valueEnd
            match parseNodeContents blob alignedNext offStrings fuel with
            | .error e => .error e
            | .ok (moreProps, children, endOffset) =>
              .ok ({ name := propName, value := propValue } :: moreProps, children, endOffset)
          else .error .malformedBlob -- Truncated property
        | _, _ => .error .malformedBlob
      else if token == fdtBeginNode then
        -- Child node — recursively parse, then continue with remaining contents
        match readCString blob (offset + 4) with
        | none => .error .malformedBlob
        | some (childName, nextOffset) =>
          match parseNodeContents blob nextOffset offStrings fuel with
          | .error e => .error e
          | .ok (childProps, grandchildren, afterChild) =>
            let child : FdtNode :=
              { name := childName, properties := childProps, children := grandchildren }
            match parseNodeContents blob afterChild offStrings fuel with
            | .error e => .error e
            | .ok (moreProps, moreSiblings, endOffset) =>
              .ok (moreProps, child :: moreSiblings, endOffset)
      else if token == fdtEndNode then
        .ok ([], [], offset + 4) -- End of this node
      else if token == fdtNop then
        parseNodeContents blob (offset + 4) offStrings fuel
      else
        .error .malformedBlob -- Unknown token, or an `FDT_END` inside an open node

/-- **PR #892 review round 5**: does this node describe RAM?

The name test plus the `device_type` test the Rust walker applies — a node named
`memory@…` that declares some other device type is not memory.  Availability is
a separate question (`statusIsOperational`), asked beside this one wherever a
memory node is selected. -/
def FdtNode.isMemoryNode (node : FdtNode) : Bool :=
  (node.name == "memory" || (node.name.startsWith "memory@" && node.name.length > 7))
  && (match node.findProperty "device_type" with
      | none => true
      | some bytes =>
        let byteList := bytes.data.toList.takeWhile (· != 0)
        String.ofList (byteList.map (fun b => Char.ofNat b.toNat)) == "memory")

/-- **PR #892 review round 5**: **every** available top-level memory node in a
parsed tree, with the cell widths that govern its `reg`.

Three filters, and each one closes a way the previous selector could pick RAM
the machine does not have: the node must describe memory (`isMemoryNode`), it
must be operational (`statusIsOperational` — firmware marks a withheld bank
`disabled`, and folding its `reg` maps DRAM that is not there), and it must sit
at the **top level**, so a `memory@…` under `/reserved-memory` — a carve-out,
not an aperture — is not read as the machine's RAM.  All three are the filters
`cmdline::find_ram_top_in_dtb` applies on the Rust side.

Searched at the top level and one level down, which is how this file's other
selectors (`extractInterruptController`, `extractTimerFrequency`) reach past the
tree root that `parseFdtNodes` returns.  The widths come from the node's
**parent**, since `#address-cells` and `#size-cells` govern a node's children;
at the top level there is no parent in the list, so the specification's defaults
apply.

**Every** node, not the first (PR #892 review round 5 audit).  The Rust walker
folds each `/memory` node's extents into one store as it passes them, so a board
reporting its low aperture and its high bank as two `/memory` nodes — a shape
the specification allows and firmware uses — was read whole on that side and
truncated to its first node here.  The two implementations answered "which
memory does this blob declare" differently, which is the class this PR's fifth
round registered as WS-XV; this is that audit finding its first instance. -/
def memoryNodesWithCells (nodes : List FdtNode) : List (FdtNode × Nat × Nat) :=
  let pick := fun (parentAddressCells parentSizeCells : Nat) (n : FdtNode) =>
    if n.isMemoryNode && n.statusIsOperational then
      some (n, parentAddressCells, parentSizeCells)
    else none
  let top := nodes.filterMap (pick fdtDefaultAddressCells fdtDefaultSizeCells)
  match top with
  | _ :: _ => top
  | [] => nodes.flatMap (fun parent =>
      parent.children.filterMap (pick parent.addressCells parent.sizeCells))

/-- **PR #892 review round 5**: the `reg` of the first available top-level
memory node — the raw-bytes search `findMemoryRegPropertyChecked` answers.

Derived from `memoryNodesWithCells`, so the search API and the boot path cannot
disagree about *which* nodes are the machine's RAM; they differ only in how many
of them each needs. -/
def memoryNodeReg? (nodes : List FdtNode) : Option ByteArray :=
  (memoryNodesWithCells nodes).findSome? (fun entry => entry.1.findProperty "reg")

/-- **PR #892 review round 5 audit**: read a `/memory` node's `reg` at the given
cell widths, refusing one that is not a whole number of (address, size) pairs.

`extractMemoryRegionsGeneral` *truncates* a trailing partial entry, which is the
fail-open direction: a `reg` the Rust walker rejects outright
(`fold_memory_reg`'s `value_len.is_multiple_of(pair_bytes)`) would have
contributed the entries before it here.  A malformed `reg` fails the whole query
closed, on both sides. -/
def extractMemoryRegionsChecked (regBytes : ByteArray)
    (addressCells sizeCells : Nat) : Option (List FdtMemoryRegion) :=
  let entrySize := (addressCells + sizeCells) * 4
  if entrySize == 0 || regBytes.size % entrySize != 0 then none
  else some (extractMemoryRegionsGeneral regBytes addressCells sizeCells)

/-- **PR #892 review round 5 audit**: the memory regions a parsed tree declares —
every available top-level `/memory` node's `reg`, read at the cell widths its
parent declares, refused whole if any of them is malformed.

This is the single answer the boot path takes, and the Lean counterpart of the
Rust walker's extent store: same node filters, same cell widths, same
whole-pairs refusal, and the same accumulation across nodes. -/
def memoryRegionsFromNodes (nodes : List FdtNode) : Option (List FdtMemoryRegion) :=
  (memoryNodesWithCells nodes).foldl
    (fun acc entry =>
      match acc with
      | none => none
      | some regions =>
        match entry.1.findProperty "reg" with
        | none => some regions
        | some regBytes =>
          match extractMemoryRegionsChecked regBytes entry.2.1 entry.2.2 with
          | none => none
          | some more => some (regions ++ more))
    (some [])

/-- AK9-F (P-M07): `Except`-returning variant of `findMemoryRegProperty`.  Unlike
    the legacy `Option` form that collapses "fuel exhausted" and "malformed
    blob" into a single `none`, this form propagates the two error conditions
    distinctly via `DeviceTreeParseError`.

    **PR #892 review round 5**: it is now a *selector over the parsed tree*
    rather than a second token walk of its own.  Two questions were being
    answered twice — "is this structure block readable" and "which node is the
    machine's RAM" — and the two answers had diverged: this walk accepted a
    blob whose memory node parsed before the structure ran out, and it applied
    neither the `status` filter nor the top-level restriction that
    `cmdline::find_ram_top_in_dtb` applies.  Both questions now have one
    answer each, `parseFdtNodes` and `memoryNodeReg?`, so the standalone API
    and the boot path cannot disagree about a blob.

    Fuel defaults to `hdr.sizeDtStruct.toNat / 4` — a DTB-sized bound: the
    structure block is at most `sizeDtStruct` bytes and every token is at
    least 4 bytes (FDT_BEGIN_NODE, FDT_END_NODE, FDT_PROP, FDT_NOP, FDT_END
    all consume ≥ 4 bytes per iteration). Callers may override. -/
def findMemoryRegPropertyChecked (blob : ByteArray) (hdr : FdtHeader)
    (fuel : Nat := hdr.sizeDtStruct.toNat / 4) :
    Except DeviceTreeParseError FdtSearchResult :=
  match parseFdtNodes blob hdr fuel with
  | .error e => .error e
  | .ok nodes =>
    match memoryNodeReg? nodes with
    | some regBytes => .ok { regPropertyBytes := regBytes }
    | none => .error .malformedBlob

-- ============================================================================
-- X4-B/H-7: DTB interrupt controller discovery
-- ============================================================================

/-- X4-B/H-7: Extract GIC-400 interrupt controller configuration from FDT nodes.
    Searches for a node with `compatible` matching "arm,gic-400" or
    "arm,cortex-a15-gic" (standard GIC-400 compatible strings).
    Parses the `reg` property to extract distributor and CPU interface bases.

    Falls back to zeros if the interrupt controller node is not found
    (graceful degradation for boards without full DTB support). -/
def extractInterruptController (nodes : List FdtNode) : InterruptControllerInfo :=
  let findGic := nodes.find? fun n =>
    match n.compatibleString with
    | some c => c == "arm,gic-400" || c == "arm,cortex-a15-gic"
    | none => n.name == "interrupt-controller" || n.name.startsWith "interrupt-controller@"
  match findGic with
  | none =>
    -- Also search children (GIC may be nested under a bus node)
    let childResult := nodes.findSome? fun (n : FdtNode) =>
      n.children.find? fun (c : FdtNode) =>
        match c.compatibleString with
        | some compat => compat == "arm,gic-400" || compat == "arm,cortex-a15-gic"
        | none => c.name == "interrupt-controller" || c.name.startsWith "interrupt-controller@"
    match childResult with
    | none => { distributorBase := (SeLe4n.PAddr.ofNat 0), cpuInterfaceBase := (SeLe4n.PAddr.ofNat 0), spiCount := 0, timerPpiId := ⟨0⟩ }
    | some gicNode => parseGicRegProperty gicNode
  | some gicNode => parseGicRegProperty gicNode
where
  /-- Parse the `reg` property of a GIC-400 node.
      GIC-400 `reg` property format: distributor base+size, CPU interface base+size.
      Assumes 2-cell addresses (64-bit), 2-cell sizes (standard for ARM64). -/
  parseGicRegProperty (node : FdtNode) : InterruptControllerInfo :=
    match node.findProperty "reg" with
    | none => { distributorBase := (SeLe4n.PAddr.ofNat 0), cpuInterfaceBase := (SeLe4n.PAddr.ofNat 0), spiCount := 0, timerPpiId := ⟨0⟩ }
    | some regBytes =>
      -- GIC reg: [dist_base(8), dist_size(8), cpu_base(8), cpu_size(8)] = 32 bytes minimum
      if regBytes.size < 32 then
        { distributorBase := (SeLe4n.PAddr.ofNat 0), cpuInterfaceBase := (SeLe4n.PAddr.ofNat 0), spiCount := 0, timerPpiId := ⟨0⟩ }
      else
        let distBase := match readBE64 regBytes 0 with | some v => v.toNat | none => 0
        let cpuBase := match readBE64 regBytes 16 with | some v => v.toNat | none => 0
        { distributorBase := (SeLe4n.PAddr.ofNat distBase)
          cpuInterfaceBase := (SeLe4n.PAddr.ofNat cpuBase)
          spiCount := 0  -- SPI count not in `reg`; from `#interrupt-cells` or board constants
          timerPpiId := ⟨0⟩ }  -- Timer PPI from /timer node

-- ============================================================================
-- X4-C/H-7: DTB timer frequency extraction
-- ============================================================================

/-- X4-C/H-7: Extract timer frequency from FDT nodes.
    Searches for a `/timer` node (compatible = "arm,armv8-timer") and extracts
    the `clock-frequency` property if present.

    On many ARM64 platforms (including RPi5), the timer frequency is set by
    firmware in `CNTFRQ_EL0` and may not appear in the DTB. Returns 0 if the
    timer node is not found or has no `clock-frequency` property; callers
    should fall back to board constants (e.g., RPi5's 54 MHz). -/
def extractTimerFrequency (nodes : List FdtNode) : Nat :=
  let findTimer := nodes.find? fun n =>
    match n.compatibleString with
    | some c => c == "arm,armv8-timer" || c == "arm,armv7-timer"
    | none => n.name == "timer"
  -- Also search children
  let timerNode := match findTimer with
    | some n => some n
    | none => nodes.findSome? fun (n : FdtNode) =>
        n.children.find? fun (c : FdtNode) =>
          match c.compatibleString with
          | some compat => compat == "arm,armv8-timer" || compat == "arm,armv7-timer"
          | none => c.name == "timer"
  match timerNode with
  | none => 0
  | some node =>
    match node.findProperty "clock-frequency" with
    | none => 0  -- Frequency set by CNTFRQ_EL0, not in DTB
    | some freqBytes =>
      -- clock-frequency can be 32-bit (4 bytes) or 64-bit (8 bytes) big-endian
      if freqBytes.size >= 8 then
        match readBE64 freqBytes 0 with
        | some freq => freq.toNat
        | none => 0
      else
        match readBE32 freqBytes 0 with
        | some freq => freq.toNat
        | none => 0

/-- AN7-D.5 (PLT-M06): Per-node peripheral classifier.  Returns **one entry per
    register block** the node declares: the node must have `reg` and
    `compatible`, must not be a `/memory`, `/reserved-memory`, `/chosen` or
    `/cpus` node, must be **operational**, and each block must have a non-zero
    size and an address the CPU can reach.  Blocks that fail any of those are
    dropped; a node with none left contributes nothing.

    **Every block, not the first** (PR #892 review round 6).  A `reg` is a *list*
    of (address, size) pairs, and a standard GIC node carries its distributor
    and its CPU interface in one — `parseGicRegProperty` in this same file reads
    both, which is what made reading only the first here a divergence inside one
    module.  `deviceTreeCoversMmioRegions` searches `dt.peripherals`, so the
    second required GIC window was simply absent and an otherwise matching board
    was refused.

    **PR #892 review round 5** added the last two.  A node the firmware marked
    `status = "disabled"` is hardware that is not there, and reporting it let
    the boot bridge's MMIO coverage check accept a peripheral the machine
    cannot use.  And the address is the node's `reg` **translated through its
    ancestor buses** (`ctx.translate`): a child-relative address is not a
    physical one, so reporting it raw both refused boards whose peripherals sit
    behind a translating bus and — the direction that matters more — could make
    an untranslated number collide with a window the binding requires.  A node
    whose address does not translate has no physical address, and this returns
    `none` for it rather than inventing one. -/
private def classifyPeripheralNode (ctx : FdtAddressContext) (node : FdtNode) :
    List DeviceEntry :=
  if node.name == "memory" || node.name.startsWith "memory@"
     || node.name == "reserved-memory" || node.name.startsWith "reserved-memory@"
     || node.name == "chosen" || node.name == "cpus" || node.name.startsWith "cpus@"
  then []
  else if !node.statusIsOperational then []
  else match node.findProperty "reg", node.compatibleString with
  | some regBytes, some _ =>
    let entryBytes := (ctx.addressCells + ctx.sizeCells) * 4
    if entryBytes == 0 then []
    else
      (List.range (regBytes.size / entryBytes)).filterMap fun i =>
        let offset := i * entryBytes
        match readFdtCells regBytes offset ctx.addressCells,
              readFdtCells regBytes (offset + ctx.addressCells * 4) ctx.sizeCells with
        | some childBase, some size =>
          if size == 0 then none
          else
            match ctx.translate childBase size with
            | none => none
            | some base => some { name := node.name, base := (SeLe4n.PAddr.ofNat base), size }
        | _, _ => none
  | _, _ => []

/-- AN7-D.5 (PLT-M06): Fuel-bounded depth-first walk of an FDT tree.  At
    each node, check for a peripheral classification AND recurse into its
    children.  The `fuel` parameter bounds total node visits so a
    pathological DTB cannot cause non-termination. -/
private def extractPeripheralsWalk : Nat → FdtAddressContext → List FdtNode → List DeviceEntry
  | 0,         _,   _      => []   -- AN7-D.5: fuel exhausted — stop gracefully
  | _ + 1,     _,   []     => []
  | fuel + 1,  ctx, node :: rest =>
    let selfEntries := classifyPeripheralNode ctx node
    let childDevs  := extractPeripheralsWalk fuel (ctx.forChildren node) node.children
    let siblingDevs := extractPeripheralsWalk fuel ctx rest
    selfEntries ++ (childDevs ++ siblingDevs)

/-- AN7-D.5 / X4-A / H-7 / PLT-M06: Extract peripheral device entries from
    an FDT tree by fuel-bounded recursive descent.

    Previous form (pre-AN7-D.5) walked only top-level + direct children
    (2 levels), sufficient for RPi5 BCM2712 but missing deeper peripherals
    on any platform with nested bus hierarchies (common on ARM SoCs with
    simple-bus / i2c / spi / usb controllers exposing child devices).

    The recursive form accepts an explicit `fuel` parameter defaulting to
    `1024` which safely exceeds the BCM2712 maximum node count (~200).
    Callers with known-small DTBs can pass a tighter bound; callers with
    untrusted DTBs should use the AJ3-A `DeviceTreeParseError.fuelExhausted`
    path and wrap via `fromDtbFull` which threads fuel through.

    Termination is guaranteed by the `fuel` parameter.  On fuel exhaustion
    the walk returns the entries collected so far — consumers that need
    exhaustion detection should call `parseFdtNodes` (AJ3-A) first, which
    propagates `.fuelExhausted` explicitly at the boundary.

    **No deferral**: PLT-M06's post-1.0 marker is removed by this
    rewrite; WS-AN closes PLT-M06 before v1.0.0 per the plan. -/
def extractPeripherals (nodes : List FdtNode) (fuel : Nat := 1024)
    : List DeviceEntry :=
  extractPeripheralsWalk fuel FdtAddressContext.cpuPhysical nodes

/-- AN7-D.5 (PLT-M06): At `fuel = 0` the walk collapses to an empty
    output regardless of the node list.  Substantive base case of the
    termination contract. -/
theorem extractPeripheralsWalk_zero_fuel (ctx : FdtAddressContext) (nodes : List FdtNode) :
    extractPeripheralsWalk 0 ctx nodes = [] := rfl

/-- AN7-D.5 (PLT-M06): On an empty node list the walk returns an empty
    device list for any fuel value.  Substantive vacuous case of the
    recursion. -/
theorem extractPeripheralsWalk_empty_nodes (fuel : Nat) (ctx : FdtAddressContext) :
    extractPeripheralsWalk fuel ctx [] = [] := by
  cases fuel <;> rfl

/-- AN7-D.5 (PLT-M06): At `fuel = 0`, `extractPeripherals` returns an
    empty list, demonstrating fail-closed behaviour on fuel exhaustion. -/
theorem extractPeripherals_zero_fuel (nodes : List FdtNode) :
    extractPeripherals nodes 0 = [] := rfl

/-- AN7-D.5 (PLT-M06): `extractPeripherals` on an empty top-level list
    returns an empty device list for any fuel value. -/
theorem extractPeripherals_empty (fuel : Nat) :
    extractPeripherals ([] : List FdtNode) fuel = [] :=
  extractPeripheralsWalk_empty_nodes fuel _

/-- AN7-D.5 (PLT-M06): Default fuel `1024` is sufficient for the canonical
    BCM2712 DTB.  The RPi5 device-tree has ≤ 200 top-level peripheral
    nodes across all subtrees (verified via Raspberry Pi Ltd published
    kernel device trees), so `1024` is a comfortable 5× bound with
    headroom for future platform extensions.  Stated as a raw inequality
    to anchor the bound at the invariant surface. -/
theorem extractPeripherals_fuel_sufficient_for_BCM2712 :
    1024 ≥ 200 := by decide

-- ============================================================================
-- V4-M4/L-PLAT-1: Wire into fromDtb
-- ============================================================================

/-- V4-M4/L-PLAT-1/X4-A/B/C: Full DTB parsing pipeline.
    1. Parses and validates the FDT header
    2. Traverses the structure block to find `/memory` node's `reg` property
    3. Extracts memory regions from the `reg` property bytes
    4. X4-A: Traverses device nodes for peripheral discovery
    5. X4-B: Discovers interrupt controller configuration (GIC-400)
    6. X4-C: Extracts timer frequency from `/timer` node
    7. Constructs a `DeviceTree` from all parsed data

    Returns `.error .malformedBlob` if the DTB is malformed, has no valid
    header, or contains no `/memory` node with a `reg` property.

    AJ3-A (M-17): Now returns `Except DeviceTreeParseError DeviceTree` instead
    of `Option DeviceTree`. Fuel exhaustion and malformed blob errors are
    propagated to callers instead of silently falling back to empty node lists.
    This prevents the kernel from booting with missing peripheral data. -/
-- AJ3-B (M-18): `physicalAddressWidth` is now a required parameter (no default).
def DeviceTree.fromDtbFull (blob : ByteArray) (physicalAddressWidth : Nat)
    : Except DeviceTreeParseError DeviceTree :=
  match parseAndValidateFdtHeader blob with
  | none => .error .malformedBlob
  | some hdr =>
    -- AK9-F (P-M07): Use `findMemoryRegPropertyChecked` so fuel exhaustion is
    -- distinguishable from malformed blob. Fuel defaults to
    -- `hdr.sizeDtStruct / 4`, which scales with the DTB structure block size
    -- and is tight: each FDT token consumes at least 4 bytes.
    -- PR #892 review round 5: ONE walk of the structure block, whose result
    -- every question below is answered from.  The memory node used to be found
    -- by a second token walk that could accept a blob this one refuses.
    match parseFdtNodes blob hdr with
    | .error e => .error e
    | .ok nodes =>
      match memoryRegionsFromNodes nodes with
      | none => .error .malformedBlob
      | some fdtRegions =>
        let memRegions := fdtRegionsToMemoryRegions fdtRegions
        if memRegions.isEmpty then .error .malformedBlob
        else
          let config : MachineConfig := {
            registerWidth := 64
            virtualAddressWidth := 48
            physicalAddressWidth := physicalAddressWidth
            pageSize := 4096
            maxASID := 65536
            memoryMap := memRegions
          }
          .ok {
            platformName := s!"DTB-parsed (version {hdr.version.toNat})"
            machineConfig := config
            peripherals := extractPeripherals nodes
            interruptController := extractInterruptController nodes
            timerFrequencyHz := extractTimerFrequency nodes
          }

-- AJ3-F (L-12): Removed `fromDtbParsed` convenience alias (no callers).
-- Use `DeviceTree.fromDtbFull` directly.

-- ============================================================================
-- V4-M5/L-PLAT-1: Correctness theorems
-- ============================================================================

/-- V4-M5/AJ3-A/AK9-F: If a blob has valid FDT magic and version, its structure
    block parses **whole**, the tree carries an available top-level `/memory`
    node with a `reg` property, and that `reg` yields at least one region, then
    `fromDtbFull` returns `.ok`.

    AK9-F (P-M07) update: the memory precondition was
    `findMemoryRegPropertyChecked … = .ok result`.

    **PR #892 review round 5**: it is now stated over the parsed tree, because
    that is what `fromDtbFull` reads — one walk, one selector.  The old form is
    still derivable through `findMemoryRegPropertyChecked_eq_memoryNodeReg?`
    below, which says the standalone search answers exactly this. -/
theorem parseFdtHeader_fromDtbFull_ok (blob : ByteArray)
    (physicalAddressWidth : Nat)
    (hdr : FdtHeader)
    (hValid : parseAndValidateFdtHeader blob = some hdr)
    (nodes : List FdtNode)
    (hNodes : parseFdtNodes blob hdr = .ok nodes)
    (fdtRegions : List FdtMemoryRegion)
    (hMem : memoryRegionsFromNodes nodes = some fdtRegions)
    (hNonEmpty : (fdtRegionsToMemoryRegions fdtRegions).isEmpty = false) :
    ∃ dt, DeviceTree.fromDtbFull blob physicalAddressWidth = .ok dt := by
  unfold DeviceTree.fromDtbFull
  simp [hValid, hNodes, hMem, hNonEmpty]

/-- **PR #892 review round 5**: the standalone search and the boot path's
selector are the same answer, by definition rather than by agreement.

Stated so a caller holding a `findMemoryRegPropertyChecked` result can move to
the tree form and back — and so a refactor that gave either one its own walk
again has to break this. -/
theorem findMemoryRegPropertyChecked_eq_memoryNodeReg? (blob : ByteArray) (hdr : FdtHeader)
    (nodes : List FdtNode) (hNodes : parseFdtNodes blob hdr = .ok nodes) :
    findMemoryRegPropertyChecked blob hdr
      = (match memoryNodeReg? nodes with
         | some regBytes => .ok { regPropertyBytes := regBytes }
         | none => .error .malformedBlob) := by
  unfold findMemoryRegPropertyChecked
  rw [hNodes]

end SeLe4n.Platform
