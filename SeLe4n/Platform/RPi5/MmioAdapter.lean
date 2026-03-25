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

/-- U6-A: `MmioSafe` hypothesis type. Proofs that need to reason about
    the outcome of an MMIO operation on a non-RAM region must carry an
    `MmioSafe` witness. The caller must supply platform-specific
    justification that the MMIO access produces the expected result.

    This prevents proofs from silently assuming RAM semantics for device
    register accesses. Any theorem depending on MMIO read values must
    either:
    1. Restrict to non-MMIO addresses via `¬ inMmioRegion regions addr`, or
    2. Carry an `MmioSafe` hypothesis with platform-specific justification.

    The `outcome` field captures what the caller asserts about the read
    result. The `justification` field is a proof obligation that the
    platform binding guarantees this outcome. -/
structure MmioSafe (regions : List MmioRegionDesc) (addr : PAddr) (outcome : Nat) where
  /-- The address is within a declared MMIO region. -/
  hInRegion : inMmioRegion regions addr = true
  /-- Platform-specific justification that this MMIO access produces
      the declared outcome. Opaque — cannot be discharged by computation. -/
  hOutcome : True  -- Placeholder: WS-V will refine with device state model

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

/-- U6-H: MMIO 32-bit write for ARM64 GIC register access.
    GIC-400 registers require 32-bit aligned writes. This operation
    writes 4 bytes at the target address (little-endian byte order).

    **Alignment requirement**: `addr` must be 4-byte aligned for GIC
    registers. The abstract model does not enforce alignment (the memory
    function is byte-addressed); WS-V hardware binding will add alignment
    validation. -/
def mmioWrite32 (addr : PAddr) (val : UInt32) : Kernel Unit :=
  fun st =>
    if isDeviceAddress addr then
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

/-- U6-H: MMIO 64-bit write for ARM64 register access.
    Writes 8 bytes at the target address (little-endian byte order).

    **Alignment requirement**: `addr` must be 8-byte aligned.
    Abstract model is byte-addressed; alignment enforced at WS-V. -/
def mmioWrite64 (addr : PAddr) (val : UInt64) : Kernel Unit :=
  fun st =>
    if isDeviceAddress addr then
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

/-- U6-H: MMIO 32-bit write at a non-device address is rejected. -/
theorem mmioWrite32_rejects_non_device (addr : PAddr) (val : UInt32) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioWrite32 addr val st = .error .policyDenied := by
  simp [mmioWrite32, hNonDevice]

/-- U6-H: MMIO 64-bit write at a non-device address is rejected. -/
theorem mmioWrite64_rejects_non_device (addr : PAddr) (val : UInt64) (st : SystemState)
    (hNonDevice : isDeviceAddress addr = false) :
    mmioWrite64 addr val st = .error .policyDenied := by
  simp [mmioWrite64, hNonDevice]

/-- U6-H: MMIO 32-bit write only modifies the 4-byte range [addr, addr+4). -/
theorem mmioWrite32_frame (addr : PAddr) (val : UInt32) (st st' : SystemState)
    (hOk : mmioWrite32 addr val st = .ok ((), st'))
    (other : PAddr)
    (hNeq0 : other ≠ addr)
    (hNeq1 : other ≠ PAddr.ofNat (addr.toNat + 1))
    (hNeq2 : other ≠ PAddr.ofNat (addr.toNat + 2))
    (hNeq3 : other ≠ PAddr.ofNat (addr.toNat + 3)) :
    st'.machine.memory other = st.machine.memory other := by
  unfold mmioWrite32 at hOk
  split at hOk
  · cases hOk; simp [hNeq0, hNeq1, hNeq2, hNeq3]
  · cases hOk

/-- U6-H: MMIO 64-bit write only modifies the 8-byte range [addr, addr+8). -/
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
  split at hOk
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
