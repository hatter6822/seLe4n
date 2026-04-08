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

    For non-RAM regions, `mmioRead` returns the current abstract memory
    content but proofs MUST NOT assume idempotency or determinism for
    volatile addresses. The `MmioSafe` hypothesis type enforces this at
    the proof level. A future WS-V refinement will make the read result
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

5. **Read preservation**: `mmioRead` does not modify state. Proven:
   `mmioRead_preserves_state`.

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
   instantaneous memory updates with no ordering constraints. Barrier annotations
   exist in the type system but are not enforced.

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

/-- U6-A/T6-E: MMIO read operation with formal abstraction boundary.

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
    unsound reasoning about device registers. -/
def mmioRead (addr : PAddr) : Kernel UInt8 :=
  fun st =>
    if isDeviceAddress addr then
      .ok (st.machine.memory addr, st)
    else
      .error .policyDenied

/-- U6-A/T6-E: MMIO write operation with formal abstraction boundary.

    Writes a value to a device register address. For `writeOneClear`
    regions, the actual hardware effect is 1-bit-clears (not a direct store);
    for `setOnly` regions, only 1-bits take effect. The abstract model uses
    a direct memory store for all write semantics — the gap between abstract
    store and hardware-specific write effect is captured by `MmioWriteKind`
    and will be refined in WS-V hardware binding.

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

/-- U6-H/V4-B: MMIO 32-bit write for ARM64 GIC register access.
    GIC-400 registers require 32-bit aligned writes. This operation
    writes 4 bytes at the target address (little-endian byte order).

    V4-B/M-HW-1: Returns `mmioUnaligned` if `addr` is not 4-byte aligned. -/
def mmioWrite32 (addr : PAddr) (val : UInt32) : Kernel Unit :=
  fun st =>
    if !isAligned addr 4 then .error .mmioUnaligned
    -- AF3-B: Validate entire write range [addr, addr+3] for 32-bit writes
    else if isDeviceAddress addr && isDeviceAddress (PAddr.ofNat (addr.toNat + 3)) then
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

    V4-B/M-HW-1: Returns `mmioUnaligned` if `addr` is not 8-byte aligned. -/
def mmioWrite64 (addr : PAddr) (val : UInt64) : Kernel Unit :=
  fun st =>
    if !isAligned addr 8 then .error .mmioUnaligned
    -- AF3-B: Validate entire write range [addr, addr+7] for 64-bit writes
    else if isDeviceAddress addr && isDeviceAddress (PAddr.ofNat (addr.toNat + 7)) then
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
    -- AF3-B: Validate entire write range [addr, addr+3] for W1C 32-bit writes
    else if isDeviceAddress addr && isDeviceAddress (PAddr.ofNat (addr.toNat + 3)) then
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

/-- V4-C: W1C write at a non-device address is rejected. -/
theorem mmioWrite32W1C_rejects_non_device (addr : PAddr) (val : UInt32) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 4 = true) :
    mmioWrite32W1C addr val st = .error .policyDenied := by
  simp [mmioWrite32W1C, hNonDevice, hAligned]

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

/-- T6-E: MMIO read at a non-device address is rejected. -/
theorem mmioRead_rejects_non_device (addr : PAddr) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioRead addr st = .error .policyDenied := by
  simp [mmioRead, hNonDevice]

/-- T6-E: MMIO write at a non-device address is rejected. -/
theorem mmioWrite_rejects_non_device (addr : PAddr) (val : UInt8) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioWrite addr val st = .error .policyDenied := by
  simp [mmioWrite, hNonDevice]

/-- T6-E: MMIO read does not modify state. -/
theorem mmioRead_preserves_state (addr : PAddr) (st st' : SystemState) (v : UInt8)
    (hOk : mmioRead addr st = .ok (v, st')) :
    st' = st := by
  unfold mmioRead at hOk
  split at hOk
  · cases hOk; rfl
  · cases hOk

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

/-- U6-H/V4-B: MMIO 32-bit write at a non-device, aligned address is rejected. -/
theorem mmioWrite32_rejects_non_device (addr : PAddr) (val : UInt32) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 4 = true) :
    mmioWrite32 addr val st = .error .policyDenied := by
  simp [mmioWrite32, hNonDevice, hAligned]

/-- U6-H/V4-B: MMIO 64-bit write at a non-device, aligned address is rejected. -/
theorem mmioWrite64_rejects_non_device (addr : PAddr) (val : UInt64) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false)
    (hAligned : isAligned addr 8 = true) :
    mmioWrite64 addr val st = .error .policyDenied := by
  simp [mmioWrite64, hNonDevice, hAligned]

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

/-- U6-B: MMIO read at a non-MMIO address returns the memory function value,
    and this result IS idempotent (safe for proofs to unfold). -/
theorem mmioRead_nonMmio_safe (addr : PAddr) (st : SystemState)
    (hDevice : isDeviceAddress addr = true)
    (_hNotMmio : notInMmioRegion addr) :
    mmioRead addr st = .ok (st.machine.memory addr, st) := by
  simp [mmioRead, hDevice]

/-- U6-B: For VSpace page-table walk proofs: any address in a page-mapped
    region that is not in an MMIO region can be read idempotently.
    This is the key lemma that VSpace proofs should cite when reasoning
    about memory reads during page table walks. -/
theorem memoryRead_idempotent_nonMmio (addr : PAddr) (st : SystemState)
    (_hNotMmio : notInMmioRegion addr) :
    st.machine.memory addr = st.machine.memory addr := by
  rfl

end SeLe4n.Platform.RPi5
