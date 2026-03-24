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
-- T6-H/M-NEW-8: Memory barrier types for ARM64
-- ============================================================================

/-- T6-H: ARM64 memory barrier instructions.
    These model the three barrier types available on ARMv8-A:
    - `dmb`: Data Memory Barrier — orders data memory accesses
    - `dsb`: Data Synchronization Barrier — ensures completion of accesses
    - `isb`: Instruction Synchronization Barrier — flushes pipeline -/
inductive MemoryBarrier where
  | dmb  -- Data Memory Barrier
  | dsb  -- Data Synchronization Barrier
  | isb  -- Instruction Synchronization Barrier
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- T6-E/M-NEW-7: MMIO operation types
-- ============================================================================

/-- T6-E: MMIO operation descriptor. Encodes the type of device register
    access (read/write, 32/64-bit) along with the target address, value,
    and required memory barriers.

    **Barrier convention for ARM64 MMIO**:
    - Reads: `barrierAfter := some .dmb` (ensure read completes before
      subsequent accesses observe the value)
    - Writes: `barrierBefore := some .dsb` (ensure prior writes complete
      before the device register write)
    - Configuration writes: `barrierAfter := some .isb` (flush pipeline
      after modifying system registers) -/
inductive MmioOpKind where
  | read32   -- 32-bit device register read
  | write32  -- 32-bit device register write
  | read64   -- 64-bit device register read
  | write64  -- 64-bit device register write
  deriving Repr, DecidableEq

/-- T6-E/H: Complete MMIO operation with address, value, and barrier annotations. -/
structure MmioOp where
  /-- The kind of MMIO operation. -/
  kind : MmioOpKind
  /-- Target device register physical address. -/
  addr : PAddr
  /-- Value to write (for write ops) or expected value (for read ops, ignored). -/
  value : Nat := 0
  /-- Memory barrier to execute before the MMIO operation. -/
  barrierBefore : Option MemoryBarrier := none
  /-- Memory barrier to execute after the MMIO operation. -/
  barrierAfter : Option MemoryBarrier := none
  deriving Repr

-- ============================================================================
-- T6-E: Device-region validation
-- ============================================================================

/-- T6-E: Check whether a physical address falls within any `.device` region
    of the RPi5 memory map. Returns `true` iff the address is in a device
    region (peripherals, MMIO registers). -/
def isDeviceAddress (addr : PAddr) : Bool :=
  rpi5MachineConfig.memoryMap.any fun region =>
    region.kind == .device && region.contains addr

/-- T6-E: Check whether a physical address falls within a known MMIO
    peripheral region. This is a tighter check than `isDeviceAddress` —
    it validates against the specific peripheral register spaces. -/
def isMmioPeripheralAddress (addr : PAddr) : Bool :=
  mmioRegions.any fun region => region.contains addr

-- ============================================================================
-- T6-E: MMIO read/write operations in the kernel monad
-- ============================================================================

/-- T6-E/M-NEW-7: MMIO read operation. Reads a value from a device register
    address after validating that the address is in a `.device` memory region.

    Returns `policyDenied` if the address is not in a device region.
    The read value is modeled as the current memory content at that address
    (in the abstract model, device registers are part of the memory function).

    **Note**: In the abstract model, MMIO reads return the memory function's
    value at the address. On real hardware, device registers have side effects
    (reading clears status bits, etc.). This gap is documented and will be
    addressed in WS-U with a device register state model. -/
def mmioRead (addr : PAddr) : Kernel UInt8 :=
  fun st =>
    if isDeviceAddress addr then
      .ok (st.machine.memory addr, st)
    else
      .error .policyDenied

/-- T6-E/M-NEW-7: MMIO write operation. Writes a value to a device register
    address after validating that the address is in a `.device` memory region.

    Returns `policyDenied` if the address is not in a device region.
    The write updates the memory function at the target address.

    **Note**: Same abstract model limitation as `mmioRead` — device register
    side effects (write-triggers, clear-on-write bits) are not modeled. -/
def mmioWrite (addr : PAddr) (val : UInt8) : Kernel Unit :=
  fun st =>
    if isDeviceAddress addr then
      let machine' := { st.machine with memory := fun a => if a = addr then val else st.machine.memory a }
      .ok ((), { st with machine := machine' })
    else
      .error .policyDenied

-- ============================================================================
-- T6-E: MMIO operation validation and execution
-- ============================================================================

/-- T6-E: Validate that an MMIO operation targets a valid device address.
    Returns `true` iff the operation's address is in a `.device` region. -/
def MmioOp.isValid (op : MmioOp) : Bool :=
  isDeviceAddress op.addr

/-- T6-E: Validate that an MMIO operation has appropriate barriers for its kind.
    ARM64 convention:
    - Reads should have `barrierAfter` (DMB to ensure ordering)
    - Writes should have `barrierBefore` (DSB to ensure completion) -/
def MmioOp.hasAppropriateBarriers (op : MmioOp) : Bool :=
  match op.kind with
  | .read32 | .read64 => op.barrierAfter.isSome
  | .write32 | .write64 => op.barrierBefore.isSome

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

end SeLe4n.Platform.RPi5
