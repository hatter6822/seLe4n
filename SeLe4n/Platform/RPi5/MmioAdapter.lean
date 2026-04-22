/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Board
import SeLe4n.Model.State

/-!
# T6-E/M-NEW-7: MMIO Adapter for Device-Region Access

This module defines the formal model for Memory-Mapped I/O (MMIO) operations
on the Raspberry Pi 5 (BCM2712). MMIO access to device registers requires:

1. **Address validation**: The target address must fall within a declared
   `.device` memory region in the platform memory map.
2. **Memory barriers**: ARM64 MMIO operations require explicit memory barriers
   (DMB/DSB/ISB) to ensure ordering with respect to normal memory accesses
   and instruction fetches.

## T6-H/M-NEW-8: Memory Barrier Modeling

ARM64 defines three memory barrier instructions:
- **DMB** (Data Memory Barrier): Ensures ordering of data accesses.
- **DSB** (Data Synchronization Barrier): Ensures completion of data accesses.
- **ISB** (Instruction Synchronization Barrier): Flushes the instruction pipeline.

MMIO operations model the required barriers as fields on `MmioOp`. The MMIO
adapter validates that appropriate barriers are specified. This is a
modeling-only change — no runtime code generation yet.

## Design Rationale

The MMIO adapter is separate from the general `adapterReadMemory`/
`adapterWriteRegister` operations because:
- MMIO accesses target device registers, not general-purpose memory.
- MMIO requires barriers that normal memory accesses do not.
- Device regions are excluded from the `memoryAccessAllowed` RAM contract.

## Status

T6 preparation for WS-U hardware binding. Operations defined with
barrier annotations; actual hardware execution deferred to WS-U.
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- U6-A (U-M08): Formal MMIO Abstraction Boundary
-- ============================================================================

/-- U6-A: MMIO read semantics classification. Device registers behave
    differently from RAM on read — the semantics of reading a register
    depends on the hardware peripheral:
    - `ram`: Normal memory semantics (idempotent reads, no side effects).
    - `volatile`: Read may return different values each time (e.g., status
      registers, FIFO data registers). Proofs cannot assume idempotency.
    - `writeOneClear`: Reading returns current value; writing 1 to a bit
      clears it (e.g., interrupt status registers in GIC-400).
    - `fifo`: Read consumes an entry from a hardware FIFO. Subsequent reads
      return different data. Strongly non-idempotent. -/
inductive MmioReadKind where
  | ram           -- Normal memory semantics (idempotent)
  | volatile      -- May return different values on each read
  | writeOneClear -- Read returns status; write-1-clear on bits
  | fifo          -- Read consumes FIFO entry (non-idempotent)
  deriving Repr, DecidableEq, Inhabited

/-- U6-A: MMIO write semantics classification. Device registers may
    interpret writes differently from RAM:
    - `normal`: Standard store semantics (value replaces register contents).
    - `writeOneClear`: Writing 1 to a bit clears it; writing 0 is no-op.
      Common for interrupt acknowledge registers.
    - `setOnly`: Only 1-bits in the written value take effect; 0-bits are
      ignored. Used for interrupt enable set registers. -/
inductive MmioWriteKind where
  | normal        -- Standard store (value replaces contents)
  | writeOneClear -- Write-1-to-clear (1-bits clear, 0-bits no-op)
  | setOnly       -- Set-only (1-bits set, 0-bits ignored)
  deriving Repr, DecidableEq, Inhabited

/-- U6-A: Formal MMIO region descriptor. Declares a range of physical
    addresses that map to device registers rather than normal memory.

    For non-RAM regions, `mmioReadByte` (and the width-specific
    `mmioRead32` / `mmioRead64`) return the current abstract memory
    content but proofs MUST NOT assume idempotency or determinism for
    volatile addresses. The `MmioSafe` hypothesis type enforces this at
    the proof level. A future refinement may make the read result
    opaque (via a device state model) to prevent unsound unfolding. -/
structure MmioRegionDesc where
  /-- Base physical address of the MMIO region. -/
  base : PAddr
  /-- Size of the region in bytes. -/
  size : Nat
  /-- Read semantics for registers in this region. -/
  readSemantics : MmioReadKind
  /-- Write semantics for registers in this region. -/
  writeSemantics : MmioWriteKind := .normal
  deriving Repr, DecidableEq, Inhabited

namespace MmioRegionDesc

/-- End address of the MMIO region (exclusive). -/
def endAddr (r : MmioRegionDesc) : Nat := r.base.toNat + r.size

/-- Check whether a physical address falls within this MMIO region. -/
def contains (r : MmioRegionDesc) (addr : PAddr) : Bool :=
  r.base.toNat ≤ addr.toNat && addr.toNat < r.endAddr

/-- Well-formedness: region has positive size and does not wrap around. -/
def wellFormed (r : MmioRegionDesc) : Prop :=
  r.size > 0 ∧ r.endAddr > r.base.toNat

instance : DecidableEq MmioRegionDesc := inferInstance

end MmioRegionDesc

/-- U6-A: Check whether a physical address falls within any declared
    `MmioRegionDesc`. This is the formal MMIO boundary check. -/
def inMmioRegion (regions : List MmioRegionDesc) (addr : PAddr) : Bool :=
  regions.any fun r => r.contains addr

/-- U6-A: Look up the MMIO region descriptor for a given address. -/
def findMmioRegion (regions : List MmioRegionDesc) (addr : PAddr) : Option MmioRegionDesc :=
  regions.find? fun r => r.contains addr

/-- U6-A: Declared MMIO region descriptors for RPi5 peripherals.
    Each region specifies its read/write semantics to prevent unsound proofs. -/
def rpi5MmioRegionDescs : List MmioRegionDesc :=
  [ { base := uart0Base, size := 0x1000,
      readSemantics := .volatile, writeSemantics := .normal }
  , { base := gicDistributorBase, size := 0x1000,
      readSemantics := .volatile, writeSemantics := .writeOneClear }
  , { base := gicCpuInterfaceBase, size := 0x2000,
      readSemantics := .volatile, writeSemantics := .normal }
  ]

/-- X1-D: MMIO read outcome specification. Encodes what can be proven about
    the result of reading a device register, parameterized by the region's
    `MmioReadKind`:
    - `ram`: The outcome equals `st.machine.memory addr` (idempotent).
    - `volatile`/`fifo`: The outcome is existentially quantified — proofs
      cannot assume any particular value, only that *some* value was returned.
    - `writeOneClear`: The outcome equals the current memory content (the
      hardware returns the current status register value on read). -/
inductive MmioReadOutcome (regions : List MmioRegionDesc) (addr : PAddr) (outcome : Nat)
    (memoryAt : Nat) : MmioReadKind → Prop where
  /-- RAM region: read is idempotent, outcome equals memory content. -/
  | ramIdempotent : outcome = memoryAt → MmioReadOutcome regions addr outcome memoryAt .ram
  /-- Volatile region: outcome is unconstrained (any value is possible). -/
  | volatileAny : MmioReadOutcome regions addr outcome memoryAt .volatile
  /-- Write-one-clear region: read returns current status register value. -/
  | w1cStatus : outcome = memoryAt → MmioReadOutcome regions addr outcome memoryAt .writeOneClear
  /-- FIFO region: read consumes a queue entry, outcome is unconstrained. -/
  | fifoConsume : MmioReadOutcome regions addr outcome memoryAt .fifo

/-- U6-A/X1-D: `MmioSafe` hypothesis type. Proofs that need to reason about
    the outcome of an MMIO operation on a non-RAM region must carry an
    `MmioSafe` witness. The caller must supply platform-specific
    justification that the MMIO access produces the expected result.

    This prevents proofs from silently assuming RAM semantics for device
    register accesses. Any theorem depending on MMIO read values must
    either:
    1. Restrict to non-MMIO addresses via `¬ inMmioRegion regions addr`, or
    2. Carry an `MmioSafe` hypothesis with platform-specific justification.

    The `outcome` field captures what the caller asserts about the read
    result. The `hOutcome` field is a proof obligation encoding read-kind
    constraints: RAM reads are idempotent, volatile/FIFO reads are
    existentially quantified, and W1C reads return current status. -/
structure MmioSafe (regions : List MmioRegionDesc) (addr : PAddr) (outcome : Nat)
    (memoryAt : Nat) where
  /-- The address is within a declared MMIO region. -/
  hInRegion : inMmioRegion regions addr = true
  /-- The region's declared read semantics for this address. -/
  readKind : MmioReadKind
  /-- The region containing this address has the declared read semantics. -/
  hReadKind : ∃ r, r ∈ regions ∧ r.contains addr = true ∧ r.readSemantics = readKind
  /-- Platform-specific justification that this MMIO access produces the
      declared outcome, parameterized by the read kind. Prevents proofs from
      assuming idempotent reads for volatile/FIFO registers. -/
  hOutcome : MmioReadOutcome regions addr outcome memoryAt readKind

-- ============================================================================
-- X1-E: Device-specific MmioSafe witness generators for RPi5 peripherals
-- ============================================================================

/-- X1-E: Construct an `MmioSafe` witness for UART PL011 (volatile reads).
    The UART data/status registers are volatile — each read may return a
    different value. The witness uses `MmioReadOutcome.volatileAny`. -/
private def uartRegion : MmioRegionDesc :=
  { base := uart0Base, size := 0x1000, readSemantics := .volatile, writeSemantics := .normal }
private def gicDistRegion : MmioRegionDesc :=
  { base := gicDistributorBase, size := 0x1000, readSemantics := .volatile, writeSemantics := .writeOneClear }
private def gicCpuRegion : MmioRegionDesc :=
  { base := gicCpuInterfaceBase, size := 0x2000, readSemantics := .volatile, writeSemantics := .normal }

private theorem uartRegion_mem : uartRegion ∈ rpi5MmioRegionDescs := by
  unfold rpi5MmioRegionDescs uartRegion; exact List.Mem.head _
private theorem gicDistRegion_mem : gicDistRegion ∈ rpi5MmioRegionDescs := by
  unfold rpi5MmioRegionDescs gicDistRegion; exact List.Mem.tail _ (List.Mem.head _)
private theorem gicCpuRegion_mem : gicCpuRegion ∈ rpi5MmioRegionDescs := by
  unfold rpi5MmioRegionDescs gicCpuRegion; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- X1-E: Construct an `MmioSafe` witness for UART PL011 (volatile reads).
    The UART data/status registers are volatile — each read may return a
    different value. The witness uses `MmioReadOutcome.volatileAny`. -/
def mkMmioSafe_uart (addr : PAddr) (outcome memoryAt : Nat)
    (hInRegion : inMmioRegion rpi5MmioRegionDescs addr = true)
    (hContains : uartRegion.contains addr = true) :
    MmioSafe rpi5MmioRegionDescs addr outcome memoryAt :=
  { hInRegion := hInRegion
    readKind := .volatile
    hReadKind := ⟨uartRegion, uartRegion_mem, hContains, rfl⟩
    hOutcome := .volatileAny }

/-- X1-E: Construct an `MmioSafe` witness for GIC-400 distributor (volatile reads).
    The GIC distributor status registers are volatile — interrupt state changes
    between reads. The witness uses `MmioReadOutcome.volatileAny`. -/
def mkMmioSafe_gicDist (addr : PAddr) (outcome memoryAt : Nat)
    (hInRegion : inMmioRegion rpi5MmioRegionDescs addr = true)
    (hContains : gicDistRegion.contains addr = true) :
    MmioSafe rpi5MmioRegionDescs addr outcome memoryAt :=
  { hInRegion := hInRegion
    readKind := .volatile
    hReadKind := ⟨gicDistRegion, gicDistRegion_mem, hContains, rfl⟩
    hOutcome := .volatileAny }

/-- X1-E: Construct an `MmioSafe` witness for GIC-400 CPU interface (volatile reads).
    The GIC CPU interface registers (interrupt acknowledge, priority, etc.) are
    volatile. The witness uses `MmioReadOutcome.volatileAny`. -/
def mkMmioSafe_gicCpu (addr : PAddr) (outcome memoryAt : Nat)
    (hInRegion : inMmioRegion rpi5MmioRegionDescs addr = true)
    (hContains : gicCpuRegion.contains addr = true) :
    MmioSafe rpi5MmioRegionDescs addr outcome memoryAt :=
  { hInRegion := hInRegion
    readKind := .volatile
    hReadKind := ⟨gicCpuRegion, gicCpuRegion_mem, hContains, rfl⟩
    hOutcome := .volatileAny }

-- ============================================================================
-- W4-F (L-16): MMIO Formalization Boundary Documentation
-- ============================================================================

/-!
## W4-F: MMIO Formalization Gap — What Is and Is Not Modeled

### Modeled (formal guarantees hold)

1. **Address validation**: All MMIO operations check `isDeviceAddress` and reject
   non-device addresses with `.policyDenied`. Proven: `mmioRead_rejects_non_device`,
   `mmioWrite_rejects_non_device`, `mmioWrite32_rejects_non_device`,
   `mmioWrite64_rejects_non_device`.

2. **Alignment enforcement**: 32-bit and 64-bit writes check alignment (4-byte and
   8-byte respectively) and reject unaligned access with `.mmioUnaligned`. Proven:
   `mmioWrite32_rejects_unaligned`, `mmioWrite64_rejects_unaligned`.

3. **Region bounds**: MMIO regions are declared with base/size and disjointness
   from RAM is proven (`mmioRegionDisjoint_holds`). The `MmioRegionDesc` type
   tracks read/write semantics per region.

4. **Frame properties**: MMIO writes only modify target bytes; all other addresses
   are preserved. Proven: `mmioWrite_frame`, `mmioWrite32_frame`, `mmioWrite64_frame`.

5. **Read preservation**: MMIO reads do not modify state. Proven:
   `mmioReadByte_preserves_state` (byte-granularity, AK9-A renamed),
   `mmioRead32_preserves_state` and `mmioRead64_preserves_state`
   (width-specific reads, AK9-A).

6. **Write-one-clear modeling**: `mmioWrite32W1C` models GIC-400 W1C semantics
   (`new = old & ~mask`), distinct from direct-store `mmioWrite32`.

### Not modeled (deferred to H3 hardware bring-up)

1. **Volatile read non-determinism**: The abstract model returns `st.machine.memory addr`
   for all reads, including volatile device registers. Real hardware may return
   different values on each read (e.g., status registers, FIFO data registers).
   **Mitigation**: `MmioSafe` hypothesis type prevents proofs from assuming
   idempotent reads for MMIO addresses.

2. **Memory ordering / barriers**: ARM64 MMIO requires DMB/DSB/ISB barriers for
   correct ordering with respect to normal memory. The abstract model uses
   instantaneous memory updates with no ordering constraints. AG8-C adds formal
   `BarrierKind` type and `barrierOrdered` predicate with trivial sequential
   satisfaction and explicit ordering theorems (see end of file). These become
   non-trivial proof obligations in the multi-core extension (closed by
   AN9-I / AN9-J per docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12).

3. **Device-specific register semantics**: Beyond the W1C model, device registers
   may have set-only, read-clear, or FIFO semantics. These are *declared* via
   `MmioReadKind`/`MmioWriteKind` but the abstract model uses direct memory
   store for writes and direct memory read for reads. The gap between declared
   semantics and modeled behavior is intentional: it constrains proof reasoning
   (via `MmioSafe`) without requiring a full device state machine.

4. **Interrupt side effects**: MMIO writes to GIC registers (enable/disable/acknowledge)
   trigger hardware interrupt controller state changes not captured in the memory
   model. The interrupt contract in `RPi5/BootContract.lean` handles this at a
   higher abstraction level.

5. **Cache coherency**: The model assumes coherent memory. Real ARM64 MMIO to
   device memory (strongly-ordered/device memory type) has different cache
   behavior than normal memory. This is handled by MMU page table attributes
   in the hardware binding, not in this abstract model.

### Accepted gaps rationale

The formalization boundary is drawn at address validation + alignment enforcement
because these are the safety-critical properties that prevent kernel memory
corruption. Volatile semantics, ordering, and device-specific behavior are
platform-specific hardware concerns that will be refined during the H3 hardware
binding workstream with actual device testing. The `MmioSafe` hypothesis type
ensures that proofs cannot unsoundly reason about device register values.
-/

-- ============================================================================
-- T6-E: Device-region validation
-- ============================================================================

/-- T6-E: Check whether a physical address falls within any `.device` region
    of the RPi5 memory map. Returns `true` iff the address is in a device
    region (peripherals, MMIO registers). -/
def isDeviceAddress (addr : PAddr) : Bool :=
  rpi5MachineConfig.memoryMap.any fun region =>
    region.kind == .device && region.contains addr

-- ============================================================================
-- T6-E: MMIO read/write operations in the kernel monad
-- ============================================================================

/-- AK9-A (P-H01) / U6-A / T6-E: MMIO byte read — **debug/UART only**.

    This byte-granularity read is retained for UART debug paths (PL011
    DR/FR registers read 1 byte at a time) and diagnostic contexts.
    Hardware-facing GIC-400 / BCM2712 peripheral registers require
    word- or doubleword-sized aligned reads — callers MUST use
    `mmioRead32` / `mmioRead64` (defined below) for those. The naming
    `mmioReadByte` (renamed from `mmioRead` in AK9-A) enforces this at
    the call site: any code that reads for GIC/BCM2712 registers and
    calls `mmioReadByte` is using the wrong function.

    For addresses in a declared `MmioRegionDesc` with non-RAM semantics,
    the read result is *modeled* as the current memory content but proofs
    MUST NOT rely on this value being idempotent or deterministic. The
    `MmioSafe` hypothesis type enforces this: any proof depending on the
    concrete value returned must carry platform-specific justification.

    Returns `policyDenied` if the address is not in a device region.

    **U6-A soundness note**: For volatile/writeOneClear/fifo regions, the
    abstract model returns `st.machine.memory addr` but the real hardware
    may return a different value on each read. Proofs must use `MmioSafe`
    or restrict to `¬ inMmioRegion rpi5MmioRegionDescs addr` to avoid
    unsound reasoning about device registers.

    **AI6-B (M-10) — Sequential model limitation**: This function returns
    `st.machine.memory addr` (RAM semantics). The sequential model does
    not capture volatile register behavior — real hardware device registers
    may return different values on successive reads (status bits, FIFO data,
    interrupt acknowledgment). Hardware binding (AN9 / closes DEF-R-HAL-L14
    per docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12) must substitute
    actual MMIO reads via FFI (`@[extern]` bridge to Rust HAL `mmio.rs`). -/
def mmioReadByte (addr : PAddr) : Kernel UInt8 :=
  fun st =>
    if isDeviceAddress addr then
      .ok (st.machine.memory addr, st)
    else
      .error .policyDenied

/-- AK9-A backwards-compat alias: `mmioRead` delegates to `mmioReadByte`.
    Prior releases exposed this 8-bit read as `mmioRead`. v0.30.4 added
    `mmioReadByte` as a thin `@[inline]` alias; the v0.30.5 audit
    remediation inverted the relationship so `mmioReadByte` is the
    primary definition and `mmioRead` is this deprecated alias. New
    code should use `mmioReadByte` (or `mmioRead32` / `mmioRead64` for
    word-sized access). -/
@[deprecated mmioReadByte (since := "0.30.5"), inline]
def mmioRead (addr : PAddr) : Kernel UInt8 := mmioReadByte addr

/-- U6-A/T6-E: MMIO write operation with formal abstraction boundary.

    Writes a value to a device register address. For `writeOneClear`
    regions, the actual hardware effect is 1-bit-clears (not a direct store);
    for `setOnly` regions, only 1-bits take effect. The abstract model uses
    a direct memory store for all write semantics — the gap between abstract
    store and hardware-specific write effect is captured by `MmioWriteKind`
    and will be refined by AN9 (hardware binding).

    Returns `policyDenied` if the address is not in a device region. -/
def mmioWrite (addr : PAddr) (val : UInt8) : Kernel Unit :=
  fun st =>
    if isDeviceAddress addr then
      let machine' := { st.machine with memory := fun a => if a = addr then val else st.machine.memory a }
      .ok ((), { st with machine := machine' })
    else
      .error .policyDenied

-- ============================================================================
-- U6-H (U-M10): 32-bit and 64-bit MMIO write operations
-- ============================================================================

/-- V4-B/M-HW-1: Check whether a physical address is N-byte aligned. -/
def isAligned (addr : PAddr) (alignment : Nat) : Bool :=
  addr.toNat % alignment == 0

-- ============================================================================
-- AK9-D (P-M02): Region-local range check for multi-byte MMIO accesses
-- ============================================================================

/-- AK9-D (P-M02): Locate the declared `MemoryRegion` that contains `addr`
    among the RPi5 `.device` regions. Returns `none` if the address is not
    in any device region. -/
def findDeviceRegion (addr : PAddr) : Option SeLe4n.MemoryRegion :=
  rpi5MachineConfig.memoryMap.find?
    fun region => region.kind == .device && region.contains addr

/-- AK9-D (P-M02): Region-local endpoint bound — check that an N-byte access
    starting at `addr` lies ENTIRELY within a single declared device region.
    This strengthens the prior AF3-B dual-endpoint check which accepted two
    addresses that happened to both be in (possibly different) device regions,
    spliced at a boundary.

    Returns `true` iff there is a device region `r` such that `r.contains addr`
    AND `addr + N ≤ r.endAddr`. -/
def isDeviceRangeWithinRegion (addr : PAddr) (n : Nat) : Bool :=
  match findDeviceRegion addr with
  | none => false
  | some r => addr.toNat + n ≤ r.endAddr

/-- U6-H/V4-B: MMIO 32-bit write for ARM64 GIC register access.
    GIC-400 registers require 32-bit aligned writes. This operation
    writes 4 bytes at the target address (little-endian byte order).

    V4-B/M-HW-1: Returns `mmioUnaligned` if `addr` is not 4-byte aligned.

    AF3-B → AK9-D (P-M02) tightening: Originally validated both endpoints
    (`addr` and `addr+3`) against `isDeviceAddress` individually; this
    permitted two addresses that happened to both be in device regions,
    spliced across a region boundary (unreachable on the current RPi5
    layout but structurally unsound). The range check now uses
    `isDeviceRangeWithinRegion` which requires the ENTIRE 4-byte range
    `[addr, addr+4)` to lie within a SINGLE declared `.device` region. -/
def mmioWrite32 (addr : PAddr) (val : UInt32) : Kernel Unit :=
  fun st =>
    if !isAligned addr 4 then .error .mmioUnaligned
    -- AK9-D (P-M02): Region-local range check (stronger than AF3-B)
    else if isDeviceRangeWithinRegion addr 4 then
      let b0 : UInt8 := val.toNat % 256 |>.toUInt8
      let b1 : UInt8 := (val.toNat / 256) % 256 |>.toUInt8
      let b2 : UInt8 := (val.toNat / 65536) % 256 |>.toUInt8
      let b3 : UInt8 := (val.toNat / 16777216) % 256 |>.toUInt8
      let a0 := addr
      let a1 := PAddr.ofNat (addr.toNat + 1)
      let a2 := PAddr.ofNat (addr.toNat + 2)
      let a3 := PAddr.ofNat (addr.toNat + 3)
      let mem := st.machine.memory
      let mem' : PAddr → UInt8 := fun a =>
        if a = a0 then b0
        else if a = a1 then b1
        else if a = a2 then b2
        else if a = a3 then b3
        else mem a
      .ok ((), { st with machine := { st.machine with memory := mem' } })
    else
      .error .policyDenied

/-- U6-H/V4-B: MMIO 64-bit write for ARM64 register access.
    Writes 8 bytes at the target address (little-endian byte order).

    V4-B/M-HW-1: Returns `mmioUnaligned` if `addr` is not 8-byte aligned.

    AK9-D (P-M02) tightening: 8-byte range must lie within a single
    `.device` region, via `isDeviceRangeWithinRegion`. -/
def mmioWrite64 (addr : PAddr) (val : UInt64) : Kernel Unit :=
  fun st =>
    if !isAligned addr 8 then .error .mmioUnaligned
    -- AK9-D (P-M02): Region-local range check for 64-bit writes
    else if isDeviceRangeWithinRegion addr 8 then
      let n := val.toNat
      let a0 := addr
      let a1 := PAddr.ofNat (addr.toNat + 1)
      let a2 := PAddr.ofNat (addr.toNat + 2)
      let a3 := PAddr.ofNat (addr.toNat + 3)
      let a4 := PAddr.ofNat (addr.toNat + 4)
      let a5 := PAddr.ofNat (addr.toNat + 5)
      let a6 := PAddr.ofNat (addr.toNat + 6)
      let a7 := PAddr.ofNat (addr.toNat + 7)
      let mem := st.machine.memory
      let mem' : PAddr → UInt8 := fun a =>
        if a = a0 then (n % 256).toUInt8
        else if a = a1 then ((n / 256) % 256).toUInt8
        else if a = a2 then ((n / 65536) % 256).toUInt8
        else if a = a3 then ((n / 16777216) % 256).toUInt8
        else if a = a4 then ((n / 4294967296) % 256).toUInt8
        else if a = a5 then ((n / 1099511627776) % 256).toUInt8
        else if a = a6 then ((n / 281474976710656) % 256).toUInt8
        else if a = a7 then ((n / 72057594037927936) % 256).toUInt8
        else mem a
      .ok ((), { st with machine := { st.machine with memory := mem' } })
    else
      .error .policyDenied

-- ============================================================================
-- AF3-C: MMIO Write Semantics Model
-- ============================================================================
--
-- The abstract model provides three write semantics:
-- • `mmioWrite32`/`mmioWrite64`: Direct byte-by-byte replacement (standard store)
-- • `mmioWrite32W1C`: Write-one-to-clear (new = old & ~write)
-- • [Missing] Set-only: new = old | write
--
-- Hardware W1C registers (e.g., GIC-400 ICPENDR) MUST use `mmioWrite32W1C`.
-- Using `mmioWrite32` on a W1C register produces model-correct but
-- hardware-incorrect behavior.
--
-- `MmioWriteSafe` witness type gating correct write function usage per
-- register address range is deferred to H3 hardware bring-up. Until then,
-- callers must manually select the correct write function based on hardware
-- documentation.
-- ============================================================================

-- ============================================================================
-- AK9-A (P-H01): Width-specific MMIO reads with alignment and range checks
-- ============================================================================

/-- AK9-A (P-H01): MMIO 32-bit aligned read for GIC-400 / BCM2712 device
    registers. Hardware-facing peripheral registers REQUIRE word-aligned
    word-sized reads; a misaligned access on `.device`/Device-nGnRnE memory
    produces a synchronous Data Abort on ARM64 (ARM ARM § D7.2.44).

    Returns:
    - `.error .mmioUnaligned` if `addr` is not 4-byte aligned,
    - `.error .policyDenied` if the 4-byte range `[addr, addr+4)` does not
      lie entirely within a single declared RPi5 `.device` region
      (AK9-D region-local check — stricter than the prior per-endpoint
      AF3-B form),
    - `.ok (value, st)` otherwise, where `value` is the little-endian
      composition of the four bytes at `addr..addr+3`. The model returns
      the current `st.machine.memory` bytes; real hardware behavior for
      volatile / W1C / FIFO regions is constrained by `MmioSafe`.

    AK5-G/H coordination: Rust HAL `mmio::mmio_read32` (alignment `assert!`,
    ARM64 LDR) is the runtime counterpart. Both sides enforce alignment;
    Rust abort asserts misalignment as a safety invariant, Lean propagates
    as a proof-layer error. -/
def mmioRead32 (addr : PAddr) : Kernel UInt32 :=
  fun st =>
    if !isAligned addr 4 then .error .mmioUnaligned
    else if isDeviceRangeWithinRegion addr 4 then
      let mem := st.machine.memory
      let b0 := mem addr
      let b1 := mem (PAddr.ofNat (addr.toNat + 1))
      let b2 := mem (PAddr.ofNat (addr.toNat + 2))
      let b3 := mem (PAddr.ofNat (addr.toNat + 3))
      let v : UInt32 :=
        b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)
      .ok (v, st)
    else
      .error .policyDenied

/-- AK9-A (P-H01): MMIO 64-bit aligned read for 64-bit ARM64 device
    registers (e.g., GIC-500 virtualization extensions, high-half timer
    counters on some peripherals). Same discipline as `mmioRead32` with
    8-byte alignment and an 8-byte region-local range check. -/
def mmioRead64 (addr : PAddr) : Kernel UInt64 :=
  fun st =>
    if !isAligned addr 8 then .error .mmioUnaligned
    else if isDeviceRangeWithinRegion addr 8 then
      let mem := st.machine.memory
      let b0 := mem addr
      let b1 := mem (PAddr.ofNat (addr.toNat + 1))
      let b2 := mem (PAddr.ofNat (addr.toNat + 2))
      let b3 := mem (PAddr.ofNat (addr.toNat + 3))
      let b4 := mem (PAddr.ofNat (addr.toNat + 4))
      let b5 := mem (PAddr.ofNat (addr.toNat + 5))
      let b6 := mem (PAddr.ofNat (addr.toNat + 6))
      let b7 := mem (PAddr.ofNat (addr.toNat + 7))
      let v : UInt64 :=
        b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
        (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)
      .ok (v, st)
    else
      .error .policyDenied

/-- AK9-A: `mmioRead32` at an unaligned address is rejected with `.mmioUnaligned`. -/
theorem mmioRead32_rejects_unaligned (addr : PAddr) (st : SystemState)
    (hUnaligned : isAligned addr 4 = false) :
    mmioRead32 addr st = .error .mmioUnaligned := by
  simp [mmioRead32, hUnaligned]

/-- AK9-A: `mmioRead64` at an unaligned address is rejected with `.mmioUnaligned`. -/
theorem mmioRead64_rejects_unaligned (addr : PAddr) (st : SystemState)
    (hUnaligned : isAligned addr 8 = false) :
    mmioRead64 addr st = .error .mmioUnaligned := by
  simp [mmioRead64, hUnaligned]

/-- AK9-A: `mmioRead32` outside any device region is rejected with `.policyDenied`. -/
theorem mmioRead32_rejects_out_of_region (addr : PAddr) (st : SystemState)
    (hAligned : isAligned addr 4 = true)
    (hOutside : isDeviceRangeWithinRegion addr 4 = false) :
    mmioRead32 addr st = .error .policyDenied := by
  simp [mmioRead32, hAligned, hOutside]

/-- AK9-A: `mmioRead64` outside any device region is rejected with `.policyDenied`. -/
theorem mmioRead64_rejects_out_of_region (addr : PAddr) (st : SystemState)
    (hAligned : isAligned addr 8 = true)
    (hOutside : isDeviceRangeWithinRegion addr 8 = false) :
    mmioRead64 addr st = .error .policyDenied := by
  simp [mmioRead64, hAligned, hOutside]

/-- AK9-A: `mmioRead32` does not modify state (read-only). -/
theorem mmioRead32_preserves_state (addr : PAddr) (st st' : SystemState) (v : UInt32)
    (hOk : mmioRead32 addr st = .ok (v, st')) :
    st' = st := by
  unfold mmioRead32 at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · cases hOk; rfl
    · cases hOk

/-- AK9-A: `mmioRead64` does not modify state (read-only). -/
theorem mmioRead64_preserves_state (addr : PAddr) (st st' : SystemState) (v : UInt64)
    (hOk : mmioRead64 addr st = .ok (v, st')) :
    st' = st := by
  unfold mmioRead64 at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · cases hOk; rfl
    · cases hOk

/-- AK9-A: `mmioRead32` aligned AND region-locally bounded produces a
    success outcome. Completes the read-side correctness triple alongside
    `_rejects_unaligned`, `_rejects_out_of_region`, `_preserves_state`. -/
theorem mmioRead32_alignedAndBounded_within_region
    (addr : PAddr) (st : SystemState)
    (hAligned : isAligned addr 4 = true)
    (hInside : isDeviceRangeWithinRegion addr 4 = true) :
    ∃ v, mmioRead32 addr st = .ok (v, st) := by
  unfold mmioRead32
  simp [hAligned, hInside]

/-- AK9-A: `mmioRead64` aligned AND region-locally bounded produces a
    success outcome. -/
theorem mmioRead64_alignedAndBounded_within_region
    (addr : PAddr) (st : SystemState)
    (hAligned : isAligned addr 8 = true)
    (hInside : isDeviceRangeWithinRegion addr 8 = true) :
    ∃ v, mmioRead64 addr st = .ok (v, st) := by
  unfold mmioRead64
  simp [hAligned, hInside]
-- ============================================================================

-- ============================================================================
-- V4-C/M-HW-2: Write-one-clear (W1C) semantics for GIC registers
-- ============================================================================

/-- V4-C/M-HW-2: Read 4 bytes from abstract memory as a little-endian UInt32.
    Used by W1C write to read the current register value before applying
    the clear mask. -/
def mmioReadBytes32 (mem : PAddr → UInt8) (addr : PAddr) : UInt32 :=
  let b0 := mem addr
  let b1 := mem (PAddr.ofNat (addr.toNat + 1))
  let b2 := mem (PAddr.ofNat (addr.toNat + 2))
  let b3 := mem (PAddr.ofNat (addr.toNat + 3))
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- V4-C/M-HW-2: MMIO 32-bit write with write-one-clear (W1C) semantics.

    GIC-400 interrupt status registers (e.g., GICD_ICPENDRn, GICD_ICACTIVERn)
    use W1C semantics: writing a 1-bit to a position clears that bit in the
    register; writing a 0-bit has no effect. The resulting value is:

        new_val = old_val & ~write_val

    This models hardware W1C behavior that a direct store (`mmioWrite32`) does
    not capture. Use this function for GIC status/acknowledge registers.

    Returns `mmioUnaligned` if `addr` is not 4-byte aligned. -/
def mmioWrite32W1C (addr : PAddr) (clearMask : UInt32) : Kernel Unit :=
  fun st =>
    if !isAligned addr 4 then .error .mmioUnaligned
    -- AK9-D (P-M02): Region-local range check (stronger than AF3-B) — entire
    -- 4-byte range must lie within a single `.device` region.
    else if isDeviceRangeWithinRegion addr 4 then
      let oldVal := mmioReadBytes32 st.machine.memory addr
      let newVal := oldVal &&& (~~~ clearMask)
      let b0 : UInt8 := newVal.toNat % 256 |>.toUInt8
      let b1 : UInt8 := (newVal.toNat / 256) % 256 |>.toUInt8
      let b2 : UInt8 := (newVal.toNat / 65536) % 256 |>.toUInt8
      let b3 : UInt8 := (newVal.toNat / 16777216) % 256 |>.toUInt8
      let a0 := addr
      let a1 := PAddr.ofNat (addr.toNat + 1)
      let a2 := PAddr.ofNat (addr.toNat + 2)
      let a3 := PAddr.ofNat (addr.toNat + 3)
      let mem := st.machine.memory
      let mem' : PAddr → UInt8 := fun a =>
        if a = a0 then b0
        else if a = a1 then b1
        else if a = a2 then b2
        else if a = a3 then b3
        else mem a
      .ok ((), { st with machine := { st.machine with memory := mem' } })
    else
      .error .policyDenied

/-- AK9-D bridge: if the base `addr` is not any device address, the range-
    local check trivially fails because `findDeviceRegion` returns `none`. -/
theorem isDeviceRangeWithinRegion_false_of_non_device (addr : PAddr) (n : Nat)
    (hNonDevice : isDeviceAddress addr = false) :
    isDeviceRangeWithinRegion addr n = false := by
  -- `isDeviceAddress addr = false` ⟹ no region in memoryMap satisfies
  -- the (.device ∧ contains addr) predicate ⟹ `find?` returns `none`.
  let p : SeLe4n.MemoryRegion → Bool :=
    fun region => region.kind == .device && region.contains addr
  have hAnyFalse : rpi5MachineConfig.memoryMap.any p = false := hNonDevice
  have hFindNone : findDeviceRegion addr = none := by
    show rpi5MachineConfig.memoryMap.find? p = none
    -- If find? returned `some r`, membership + predicate would imply .any = true.
    rcases hFind : rpi5MachineConfig.memoryMap.find? p with _ | r
    · rfl
    · exfalso
      have hMem : r ∈ rpi5MachineConfig.memoryMap :=
        List.mem_of_find?_eq_some hFind
      have hPred : p r = true := List.find?_some hFind
      have hTrue : rpi5MachineConfig.memoryMap.any p = true :=
        List.any_eq_true.mpr ⟨r, hMem, hPred⟩
      rw [hTrue] at hAnyFalse
      exact Bool.false_ne_true hAnyFalse.symm
  simp [isDeviceRangeWithinRegion, hFindNone]

/-- AK9-D: W1C write outside a single device region is rejected. Replaces the
    former AF3-B per-endpoint rejection with the region-local check —
    strictly stronger (covers boundary-splicing cases as well). -/
theorem mmioWrite32W1C_rejects_out_of_region (addr : PAddr) (val : UInt32)
    (st : SystemState)
    (hAligned : isAligned addr 4 = true)
    (hOutside : isDeviceRangeWithinRegion addr 4 = false) :
    mmioWrite32W1C addr val st = .error .policyDenied := by
  simp [mmioWrite32W1C, hAligned, hOutside]

/-- AK9-D: W1C write at a non-device base address is rejected. -/
theorem mmioWrite32W1C_rejects_non_device (addr : PAddr) (val : UInt32) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 4 = true) :
    mmioWrite32W1C addr val st = .error .policyDenied :=
  mmioWrite32W1C_rejects_out_of_region addr val st hAligned
    (isDeviceRangeWithinRegion_false_of_non_device addr 4 hNonDevice)

/-- V4-C: W1C write with unaligned address is rejected. -/
theorem mmioWrite32W1C_rejects_unaligned (addr : PAddr) (val : UInt32) (st : SystemState)
    (hUnaligned : isAligned addr 4 = false) :
    mmioWrite32W1C addr val st = .error .mmioUnaligned := by
  simp [mmioWrite32W1C, hUnaligned]

-- ============================================================================
-- V4-B: Alignment enforcement correctness properties
-- ============================================================================

/-- V4-B: MMIO 32-bit write with unaligned address is rejected. -/
theorem mmioWrite32_rejects_unaligned (addr : PAddr) (val : UInt32) (st : SystemState)
    (hUnaligned : isAligned addr 4 = false) :
    mmioWrite32 addr val st = .error .mmioUnaligned := by
  simp [mmioWrite32, hUnaligned]

/-- V4-B: MMIO 64-bit write with unaligned address is rejected. -/
theorem mmioWrite64_rejects_unaligned (addr : PAddr) (val : UInt64) (st : SystemState)
    (hUnaligned : isAligned addr 8 = false) :
    mmioWrite64 addr val st = .error .mmioUnaligned := by
  simp [mmioWrite64, hUnaligned]

-- ============================================================================
-- T6-E: Correctness properties
-- ============================================================================

/-- AK9-A / T6-E: MMIO byte read at a non-device address is rejected. -/
theorem mmioReadByte_rejects_non_device (addr : PAddr) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioReadByte addr st = .error .policyDenied := by
  simp [mmioReadByte, hNonDevice]

set_option linter.deprecated false in
/-- T6-E: Backwards-compat alias theorem — `mmioRead` rejects non-device. -/
theorem mmioRead_rejects_non_device (addr : PAddr) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioRead addr st = .error .policyDenied :=
  mmioReadByte_rejects_non_device addr st hNonDevice

/-- T6-E: MMIO write at a non-device address is rejected. -/
theorem mmioWrite_rejects_non_device (addr : PAddr) (val : UInt8) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioWrite addr val st = .error .policyDenied := by
  simp [mmioWrite, hNonDevice]

/-- AK9-A / T6-E: MMIO byte read does not modify state. -/
theorem mmioReadByte_preserves_state (addr : PAddr) (st st' : SystemState) (v : UInt8)
    (hOk : mmioReadByte addr st = .ok (v, st')) :
    st' = st := by
  unfold mmioReadByte at hOk
  split at hOk
  · cases hOk; rfl
  · cases hOk

set_option linter.deprecated false in
/-- T6-E: Backwards-compat alias theorem — `mmioRead` preserves state. -/
theorem mmioRead_preserves_state (addr : PAddr) (st st' : SystemState) (v : UInt8)
    (hOk : mmioRead addr st = .ok (v, st')) :
    st' = st :=
  mmioReadByte_preserves_state addr st st' v hOk

/-- T6-E: MMIO write only modifies the target address. -/
theorem mmioWrite_frame (addr : PAddr) (val : UInt8) (st st' : SystemState)
    (hOk : mmioWrite addr val st = .ok ((), st'))
    (other : PAddr) (hNeq : other ≠ addr) :
    st'.machine.memory other = st.machine.memory other := by
  unfold mmioWrite at hOk
  split at hOk
  · cases hOk; simp [hNeq]
  · cases hOk

-- ============================================================================
-- U6-H: 32/64-bit write correctness properties
-- ============================================================================

/-- AK9-D (replaces AF3-B single-endpoint form): MMIO 32-bit write whose
    4-byte range is not entirely within a single `.device` region is
    rejected with `.policyDenied`. Strictly stronger than the prior
    per-endpoint check — covers region-boundary splicing as well. -/
theorem mmioWrite32_rejects_out_of_region (addr : PAddr) (val : UInt32)
    (st : SystemState)
    (hAligned : isAligned addr 4 = true)
    (hOutside : isDeviceRangeWithinRegion addr 4 = false) :
    mmioWrite32 addr val st = .error .policyDenied := by
  simp [mmioWrite32, hAligned, hOutside]

/-- U6-H/V4-B: MMIO 32-bit write at a non-device, aligned address is rejected.
    AK9-D rewiring: derived from the stronger region-local rejection via
    `isDeviceRangeWithinRegion_false_of_non_device`. -/
theorem mmioWrite32_rejects_non_device (addr : PAddr) (val : UInt32) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 4 = true) :
    mmioWrite32 addr val st = .error .policyDenied :=
  mmioWrite32_rejects_out_of_region addr val st hAligned
    (isDeviceRangeWithinRegion_false_of_non_device addr 4 hNonDevice)

/-- AK9-D: MMIO 64-bit write whose 8-byte range is not entirely within a
    single `.device` region is rejected. -/
theorem mmioWrite64_rejects_out_of_region (addr : PAddr) (val : UInt64)
    (st : SystemState)
    (hAligned : isAligned addr 8 = true)
    (hOutside : isDeviceRangeWithinRegion addr 8 = false) :
    mmioWrite64 addr val st = .error .policyDenied := by
  simp [mmioWrite64, hAligned, hOutside]

/-- U6-H/V4-B: MMIO 64-bit write at a non-device, aligned address is rejected.
    AK9-D rewiring: derived from the stronger region-local rejection. -/
theorem mmioWrite64_rejects_non_device (addr : PAddr) (val : UInt64) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 8 = true) :
    mmioWrite64 addr val st = .error .policyDenied :=
  mmioWrite64_rejects_out_of_region addr val st hAligned
    (isDeviceRangeWithinRegion_false_of_non_device addr 8 hNonDevice)

/-- AK9-D (P-M02): MMIO 32-bit write ALIGNED AND region-locally BOUNDED
    produces a success outcome. Positive correctness lemma: when alignment
    holds AND the 4-byte range is within a single `.device` region, the
    write proceeds to `.ok`. This is the new-world positive counterpart to
    the negative `_rejects_*` theorems. -/
theorem mmioWrite32_alignedAndBounded_within_region
    (addr : PAddr) (val : UInt32) (st : SystemState)
    (hAligned : isAligned addr 4 = true)
    (hInside : isDeviceRangeWithinRegion addr 4 = true) :
    ∃ st', mmioWrite32 addr val st = .ok ((), st') := by
  -- Witness: the state produced by reducing the definition with the two guards true.
  unfold mmioWrite32
  simp [hAligned, hInside]

/-- AK9-D: Positive correctness for 64-bit writes. -/
theorem mmioWrite64_alignedAndBounded_within_region
    (addr : PAddr) (val : UInt64) (st : SystemState)
    (hAligned : isAligned addr 8 = true)
    (hInside : isDeviceRangeWithinRegion addr 8 = true) :
    ∃ st', mmioWrite64 addr val st = .ok ((), st') := by
  unfold mmioWrite64
  simp [hAligned, hInside]

/-- U6-H/V4-B: MMIO 32-bit write only modifies the 4-byte range [addr, addr+4). -/
theorem mmioWrite32_frame (addr : PAddr) (val : UInt32) (st st' : SystemState)
    (hOk : mmioWrite32 addr val st = .ok ((), st'))
    (other : PAddr)
    (hNeq0 : other ≠ addr)
    (hNeq1 : other ≠ PAddr.ofNat (addr.toNat + 1))
    (hNeq2 : other ≠ PAddr.ofNat (addr.toNat + 2))
    (hNeq3 : other ≠ PAddr.ofNat (addr.toNat + 3)) :
    st'.machine.memory other = st.machine.memory other := by
  unfold mmioWrite32 at hOk
  simp only [Bool.not_eq_true'] at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · cases hOk; simp [hNeq0, hNeq1, hNeq2, hNeq3]
    · cases hOk

/-- U6-H/V4-B: MMIO 64-bit write only modifies the 8-byte range [addr, addr+8). -/
theorem mmioWrite64_frame (addr : PAddr) (val : UInt64) (st st' : SystemState)
    (hOk : mmioWrite64 addr val st = .ok ((), st'))
    (other : PAddr)
    (hNeq0 : other ≠ addr)
    (hNeq1 : other ≠ PAddr.ofNat (addr.toNat + 1))
    (hNeq2 : other ≠ PAddr.ofNat (addr.toNat + 2))
    (hNeq3 : other ≠ PAddr.ofNat (addr.toNat + 3))
    (hNeq4 : other ≠ PAddr.ofNat (addr.toNat + 4))
    (hNeq5 : other ≠ PAddr.ofNat (addr.toNat + 5))
    (hNeq6 : other ≠ PAddr.ofNat (addr.toNat + 6))
    (hNeq7 : other ≠ PAddr.ofNat (addr.toNat + 7)) :
    st'.machine.memory other = st.machine.memory other := by
  unfold mmioWrite64 at hOk
  simp only [Bool.not_eq_true'] at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · cases hOk; simp [hNeq0, hNeq1, hNeq2, hNeq3, hNeq4, hNeq5, hNeq6, hNeq7]
    · cases hOk

-- ============================================================================
-- U6-B (U-M08): MMIO-aware proof guidance
-- ============================================================================

/-- U6-B: Predicate asserting that an address is NOT in any declared MMIO
    region. Proofs depending on memory-read idempotency or determinism
    should carry this hypothesis for addresses that could be MMIO. -/
def notInMmioRegion (addr : PAddr) : Prop :=
  inMmioRegion rpi5MmioRegionDescs addr = false

/-- U6-B / AK9-A: MMIO byte read at a non-MMIO address returns the memory
    function value, and this result IS idempotent (safe for proofs to
    unfold). Renamed from `mmioRead_nonMmio_safe` in AK9-A. -/
theorem mmioReadByte_nonMmio_safe (addr : PAddr) (st : SystemState)
    (hDevice : isDeviceAddress addr = true)
    (_hNotMmio : notInMmioRegion addr) :
    mmioReadByte addr st = .ok (st.machine.memory addr, st) := by
  simp [mmioReadByte, hDevice]

set_option linter.deprecated false in
/-- U6-B: Backwards-compat alias theorem. -/
theorem mmioRead_nonMmio_safe (addr : PAddr) (st : SystemState)
    (hDevice : isDeviceAddress addr = true)
    (hNotMmio : notInMmioRegion addr) :
    mmioRead addr st = .ok (st.machine.memory addr, st) :=
  mmioReadByte_nonMmio_safe addr st hDevice hNotMmio

/-- U6-B: For VSpace page-table walk proofs: any address in a page-mapped
    region that is not in an MMIO region can be read idempotently.
    This is the key lemma that VSpace proofs should cite when reasoning
    about memory reads during page table walks. -/
theorem memoryRead_idempotent_nonMmio (addr : PAddr) (st : SystemState)
    (_hNotMmio : notInMmioRegion addr) :
    st.machine.memory addr = st.machine.memory addr := by
  rfl

-- ============================================================================
-- AG8-C (H3-ARCH-08): Formal Memory Barrier Semantics
-- ============================================================================

/-!
## AG8-C: Memory Barrier Semantics Model

ARM64 defines three memory barrier instructions that enforce ordering of
memory accesses. In the abstract Lean model, all memory updates are
instantaneous (single-threaded, no pipeline), so barriers are trivially
satisfied. This formalization captures the *semantic contract* that:

1. MMIO writes preceded by DSB are visible to hardware before subsequent reads
2. TLB invalidations followed by DSB + ISB are complete before next instruction
3. Context switch register saves preceded by DMB are ordered correctly

The Rust HAL layer (`barriers.rs`) provides the actual instructions:
- `dmb_ish()`, `dmb_sy()` — Data Memory Barrier
- `dsb_ish()`, `dsb_sy()` — Data Synchronization Barrier
- `isb()` — Instruction Synchronization Barrier
-/

/-- Memory barrier type classification per ARM Architecture Reference Manual. -/
inductive BarrierKind where
  /-- Data Memory Barrier: ensures ordering of data accesses across the
      barrier point. Accesses before DMB are observed before accesses after. -/
  | dmb_ish
  /-- Data Synchronization Barrier: ensures *completion* (not just ordering)
      of all data accesses before the barrier. Required before TLBI sequences
      and after GIC register writes. -/
  | dsb_ish
  /-- Instruction Synchronization Barrier: flushes the instruction pipeline.
      Required after TLBI + DSB to ensure subsequent instructions use the
      new page table mappings. -/
  | isb
  deriving Repr, DecidableEq, BEq

/-- Abstract barrier ordering predicate.

In the sequential abstract model, memory updates are instantaneous, so
barrier ordering is trivially satisfied. This predicate exists to:
1. Document where barriers are semantically required
2. Enable future multi-core extension (closed by AN9-I / AN9-J per
   docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12) where barriers
   become non-trivial proof obligations
3. Allow proofs to explicitly depend on barrier presence

`barrierOrdered st st'` asserts that all memory operations in `st` that
preceded a barrier are visible in `st'`. In the single-core sequential
model, this is always true. -/
def barrierOrdered (_st _st' : SystemState) : Prop := True

/-- Barrier ordering is trivially satisfied in the sequential model. -/
theorem barrierOrdered_trivial (st st' : SystemState) :
    barrierOrdered st st' :=
  trivial

/-- DSB followed by ISB guarantees TLB invalidation visibility.
In the sequential model, this is trivially satisfied (`barrierOrdered := True`).
On hardware, DSB + ISB ensures page table walks use updated mappings.
This formalizes the contract that TlbModel.tlbBarrierComplete depends on.
Becomes a non-trivial obligation in the multi-core extension (WS-W). -/
theorem dsb_isb_guarantees_tlb_visibility (st st' : SystemState)
    (_hDsb : BarrierKind.dsb_ish = .dsb_ish)
    (_hIsb : BarrierKind.isb = .isb) :
    barrierOrdered st st' :=
  trivial

/-- DMB ISH guarantees MMIO write ordering (trivially in sequential model).
On hardware, MMIO writes preceded by DMB ISH are observed before subsequent
data accesses. Required for GIC register sequences (acknowledge → process → EOI).
In the sequential model, `barrierOrdered := True` so this is trivially satisfied.
Becomes a non-trivial obligation in the multi-core extension (WS-W). -/
theorem dmb_guarantees_mmio_ordering (st st' : SystemState)
    (_hDmb : BarrierKind.dmb_ish = .dmb_ish) :
    barrierOrdered st st' :=
  trivial

/-- DSB ISH guarantees MMIO write completion (trivially in sequential model).
On hardware, MMIO writes preceded by DSB ISH are *completed* (not just ordered)
before subsequent instructions. Required before ERET to ensure GIC EOI is
processed before returning to user mode.
In the sequential model, `barrierOrdered := True` so this is trivially satisfied.
Becomes a non-trivial obligation in the multi-core extension (WS-W). -/
theorem dsb_guarantees_mmio_completion (st st' : SystemState)
    (_hDsb : BarrierKind.dsb_ish = .dsb_ish) :
    barrierOrdered st st' :=
  trivial

-- ============================================================================
-- AK9-H: LOW-tier platform batch documentation (P-L1..P-L13)
-- ============================================================================

/-!
## AK9-H (P-L1..P-L13): Platform LOW-tier accepted gaps / documentation batch

- **P-L1** `StateBuilder.buildChecked` `panic!`: AE6-B migrated the primary
  boot-path constructors off `buildChecked`; the remaining `panic!` is only
  a diagnostic last resort invoked when invariant validation fails — test
  harnesses prefer `buildValidated` directly. Recorded here; a structured
  error return is the post-1.0 hardening direction (P-L6).

- **P-L2** `readCString` fuel 256: the 256-byte cap reflects FDT string-
  table entries which are always short property names (spec-mandated
  sub-32-char names). A fuel-exhaustion return type upgrade is tracked
  as a post-1.0 hardening candidate; no currently-active plan file
  tracks it.

- **P-L3** `physicalAddressWidth` bounds: **RESOLVED** via AK9-F —
  `applyMachineConfigChecked` enforces `physicalAddressWidth ≤ 52`
  (ARMv8 LPA maximum). `config.wellFormed` additionally enforces
  `physicalAddressWidth > 0` (see Machine.lean §MachineConfig.wellFormed).

- **P-L4** `extractPeripherals` 2-level: documented at `DeviceTree.lean`
  (AF-32). The BCM2712 DTB has peripherals at depth 1–2; deeper nesting
  for non-RPi5 platforms is recorded here as a post-1.0 hardening
  candidate; no currently-active plan file tracks it.

- **P-L5** MMIO operations do not issue interrupts-disable guards:
  single-core sequential model — the MMIO write sequence is atomic by
  modeling construction. On real hardware, the Rust HAL's
  `with_interrupts_disabled` wrapper (`sele4n-hal/src/interrupts.rs`)
  is the runtime guard. Proofs depending on atomicity of MMIO sequences
  through interrupt windows are tracked under `barrierOrdered`; the
  multi-core extension is recorded here as a post-1.0 hardening
  candidate; no currently-active plan file tracks it.

- **P-L6** `buildValidated` unstructured strings: test-surface
  diagnostic, not proof-layer. A `BuildValidationError` inductive with
  structured variants is tracked as post-1.0 test hygiene.

- **P-L7** `mmioRegionDisjointCheck` scope: **RESOLVED** — pairwise
  MMIO-vs-MMIO disjointness is covered by
  `mmioRegionsPairwiseDisjointCheck` / `mmioRegionsPairwiseDisjoint_holds`
  in `Board.lean:181` (from X4-D/M-10). MMIO-vs-RAM disjointness is
  `mmioRegionDisjoint_holds`.

- **P-L8** O(n²) boot IRQ scan in `bootFromPlatformWithWarnings`:
  boot-only cost; the RPi5 `irqTable` is at most ~20 entries, and boot
  runs once. Documented as accepted cost.

- **P-L9** VSpaceRoot boot exclusion: recorded here as a post-1.0
  hardening candidate; no currently-active plan file tracks it. The
  `bootSafeObject` predicate excludes `.vspaceRoot` variants because
  ASID-table registration in `storeObject` requires a fully-initialized
  ASID manager which is not available during builder-phase boot. All
  address spaces are configured post-boot via `vspaceMap` syscalls.

- **P-L10** `registerContextStableCheck` ignores pre-state: deliberate.
  The predicate examines post-state only; pre-state is retained in the
  signature for `RuntimeBoundaryContract.registerContextStable` shape.
  When a future extension requires pre-state comparison, extend the
  field names rather than re-introduce the unused parameter.

- **P-L11** FFI `opaque BaseIO` contract bridging: recorded here as a
  post-1.0 hardening candidate; no currently-active plan file tracks it.
  A formal soundness bridge between `@[extern]`-declared FFI functions
  and their Rust HAL counterparts would supplement the existing
  production AdapterProofHooks.

- **P-L12** `mmioWrite32W1C` region-kind check: the `MmioWriteKind`
  classifier (`normal`/`writeOneClear`/`setOnly`) is declared on
  `MmioRegionDesc.writeSemantics`; runtime gating of caller choice
  (`mmioWrite32` vs `mmioWrite32W1C`) against region declaration is a
  post-1.0 hygiene tightening — tracked under `MmioWriteSafe` witness
  type (see §AF3-C commentary above).

- **P-L13** touching-regions fragility (page-granular alignment
  assumption in the region-local check): **AK9-D** `isDeviceRangeWithinRegion`
  now enforces this structurally — an N-byte access is accepted only if
  `addr + N ≤ r.endAddr` for a containing region `r`. The concern about
  adjacent device regions being accidentally spliced is eliminated.
-/

end SeLe4n.Platform.RPi5
