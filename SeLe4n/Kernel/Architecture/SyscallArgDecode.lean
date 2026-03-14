/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # Per-Syscall Argument Decode Layer (WS-K-B)

This module implements the second layer of the two-layer syscall argument
decode architecture:

1. **Layer 1** (`RegisterDecode.lean`): Converts raw register file values into
   a flat `SyscallDecodeResult` containing `capAddr`, `msgInfo`, `syscallId`,
   and `msgRegs : Array RegValue`.

2. **Layer 2** (this module): Converts the `msgRegs` array within a
   `SyscallDecodeResult` into per-syscall typed argument structures. Each
   syscall family gets a dedicated structure and total decode function.

**Dependencies:** Only `Model.State` (for types). Does not import any kernel
subsystem module, maintaining the same dependency discipline as
`RegisterDecode.lean`.

**Key properties:**
- All decode functions are total with explicit `Except KernelError` returns.
- Shared `requireMsgReg` provides bounds-checked array indexing.
- Determinism theorems: each decode is a pure function of its input.
- Error-exclusivity theorems: decode fails iff register count insufficient.
-/

namespace SeLe4n.Kernel.Architecture.SyscallArgDecode

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- Shared infrastructure
-- ============================================================================

/-- Bounds-checked message register access. Returns `invalidMessageInfo` if
    the index exceeds the array size. All per-syscall decode functions
    delegate to this, avoiding duplicated bounds logic. -/
@[inline] def requireMsgReg (regs : Array RegValue) (idx : Nat)
    : Except KernelError RegValue :=
  if h : idx < regs.size then .ok regs[idx]
  else .error .invalidMessageInfo

/-- Determinism: `requireMsgReg` is pure. -/
theorem requireMsgReg_deterministic (regs : Array RegValue) (idx : Nat) :
    requireMsgReg regs idx = requireMsgReg regs idx := rfl

/-- Error exclusivity: `requireMsgReg` fails iff the index is out of bounds. -/
theorem requireMsgReg_error_iff (regs : Array RegValue) (idx : Nat) :
    requireMsgReg regs idx = .error .invalidMessageInfo ↔ ¬(idx < regs.size) := by
  unfold requireMsgReg
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp at h; simp [h]

/-- Success exclusivity: `requireMsgReg` succeeds iff the index is in bounds. -/
theorem requireMsgReg_ok_iff (regs : Array RegValue) (idx : Nat) :
    (∃ v, requireMsgReg regs idx = .ok v) ↔ idx < regs.size := by
  unfold requireMsgReg
  constructor
  · intro ⟨v, hv⟩; split at hv <;> simp_all
  · intro h; exact ⟨regs[idx], by simp [h]⟩

-- ============================================================================
-- CSpace argument structures
-- ============================================================================

/-- Per-syscall argument structure for `cspaceMint`.
    Register mapping: x2=srcSlot, x3=dstSlot, x4=rights bitmask, x5=badge. -/
structure CSpaceMintArgs where
  srcSlot : Slot
  dstSlot : Slot
  rights  : AccessRightSet
  badge   : Badge
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceCopy`.
    Register mapping: x2=srcSlot, x3=dstSlot. -/
structure CSpaceCopyArgs where
  srcSlot : Slot
  dstSlot : Slot
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceMove`.
    Register mapping: x2=srcSlot, x3=dstSlot. -/
structure CSpaceMoveArgs where
  srcSlot : Slot
  dstSlot : Slot
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceDelete`.
    Register mapping: x2=targetSlot. -/
structure CSpaceDeleteArgs where
  targetSlot : Slot
  deriving Repr, DecidableEq

-- ============================================================================
-- Lifecycle and VSpace argument structures
-- ============================================================================

/-- Per-syscall argument structure for `lifecycleRetype`.
    Register mapping: x2=targetObj, x3=newType tag, x4=size hint. -/
structure LifecycleRetypeArgs where
  targetObj : ObjId
  newType   : Nat
  size      : Nat
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `vspaceMap`.
    Register mapping: x2=asid, x3=vaddr, x4=paddr, x5=perms word. -/
structure VSpaceMapArgs where
  asid  : ASID
  vaddr : VAddr
  paddr : PAddr
  perms : Nat
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `vspaceUnmap`.
    Register mapping: x2=asid, x3=vaddr. -/
structure VSpaceUnmapArgs where
  asid  : ASID
  vaddr : VAddr
  deriving Repr, DecidableEq

-- ============================================================================
-- CSpace decode functions
-- ============================================================================

/-- Decode CSpace mint arguments from message registers.
    Requires 4 message registers (srcSlot, dstSlot, rights, badge). -/
def decodeCSpaceMintArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMintArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  pure { srcSlot := Slot.ofNat r0.val
         dstSlot := Slot.ofNat r1.val
         rights  := ⟨r2.val⟩
         badge   := Badge.ofNat r3.val }

/-- Decode CSpace copy arguments from message registers.
    Requires 2 message registers (srcSlot, dstSlot). -/
def decodeCSpaceCopyArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceCopyArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { srcSlot := Slot.ofNat r0.val, dstSlot := Slot.ofNat r1.val }

/-- Decode CSpace move arguments from message registers.
    Requires 2 message registers (srcSlot, dstSlot). -/
def decodeCSpaceMoveArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMoveArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { srcSlot := Slot.ofNat r0.val, dstSlot := Slot.ofNat r1.val }

/-- Decode CSpace delete arguments from message registers.
    Requires 1 message register (targetSlot). -/
def decodeCSpaceDeleteArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceDeleteArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { targetSlot := Slot.ofNat r0.val }

-- ============================================================================
-- Lifecycle and VSpace decode functions
-- ============================================================================

/-- Decode lifecycle retype arguments from message registers.
    Requires 3 message registers (targetObj, newType tag, size hint). -/
def decodeLifecycleRetypeArgs (decoded : SyscallDecodeResult)
    : Except KernelError LifecycleRetypeArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  pure { targetObj := ObjId.ofNat r0.val
         newType   := r1.val
         size      := r2.val }

/-- Decode VSpace map arguments from message registers.
    Requires 4 message registers (asid, vaddr, paddr, perms word). -/
def decodeVSpaceMapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceMapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  pure { asid  := ASID.ofNat r0.val
         vaddr := VAddr.ofNat r1.val
         paddr := PAddr.ofNat r2.val
         perms := r3.val }

/-- Decode VSpace unmap arguments from message registers.
    Requires 2 message registers (asid, vaddr). -/
def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceUnmapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { asid  := ASID.ofNat r0.val
         vaddr := VAddr.ofNat r1.val }

-- ============================================================================
-- Determinism theorems
-- ============================================================================

theorem decodeCSpaceMintArgs_deterministic (d : SyscallDecodeResult) :
    decodeCSpaceMintArgs d = decodeCSpaceMintArgs d := rfl

theorem decodeCSpaceCopyArgs_deterministic (d : SyscallDecodeResult) :
    decodeCSpaceCopyArgs d = decodeCSpaceCopyArgs d := rfl

theorem decodeCSpaceMoveArgs_deterministic (d : SyscallDecodeResult) :
    decodeCSpaceMoveArgs d = decodeCSpaceMoveArgs d := rfl

theorem decodeCSpaceDeleteArgs_deterministic (d : SyscallDecodeResult) :
    decodeCSpaceDeleteArgs d = decodeCSpaceDeleteArgs d := rfl

theorem decodeLifecycleRetypeArgs_deterministic (d : SyscallDecodeResult) :
    decodeLifecycleRetypeArgs d = decodeLifecycleRetypeArgs d := rfl

theorem decodeVSpaceMapArgs_deterministic (d : SyscallDecodeResult) :
    decodeVSpaceMapArgs d = decodeVSpaceMapArgs d := rfl

theorem decodeVSpaceUnmapArgs_deterministic (d : SyscallDecodeResult) :
    decodeVSpaceUnmapArgs d = decodeVSpaceUnmapArgs d := rfl

-- ============================================================================
-- Error-exclusivity theorems
-- ============================================================================

/-- Helper: unfold requireMsgReg in a goal and simplify dite. -/
private theorem requireMsgReg_unfold_ok (regs : Array RegValue) (idx : Nat) (h : idx < regs.size) :
    requireMsgReg regs idx = .ok regs[idx] := by simp [requireMsgReg, dif_pos h]

private theorem requireMsgReg_unfold_err (regs : Array RegValue) (idx : Nat) (h : ¬(idx < regs.size)) :
    requireMsgReg regs idx = .error .invalidMessageInfo := by simp [requireMsgReg, dif_neg h]

/-- CSpace mint decode fails iff fewer than 4 message registers. -/
theorem decodeCSpaceMintArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceMintArgs d = .error e) ↔ d.msgRegs.size < 4 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 4
    · exact hlt
    · exfalso
      simp only [decodeCSpaceMintArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeCSpaceMintArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        by_cases h2 : 2 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h2]; simp
          rw [requireMsgReg_unfold_err _ _ (by omega)]
        · rw [requireMsgReg_unfold_err _ _ h2]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- CSpace copy decode fails iff fewer than 2 message registers. -/
theorem decodeCSpaceCopyArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceCopyArgs d = .error e) ↔ d.msgRegs.size < 2 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 2
    · exact hlt
    · exfalso
      simp only [decodeCSpaceCopyArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeCSpaceCopyArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      rw [requireMsgReg_unfold_err _ _ (by omega)]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- CSpace move decode fails iff fewer than 2 message registers. -/
theorem decodeCSpaceMoveArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceMoveArgs d = .error e) ↔ d.msgRegs.size < 2 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 2
    · exact hlt
    · exfalso
      simp only [decodeCSpaceMoveArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeCSpaceMoveArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      rw [requireMsgReg_unfold_err _ _ (by omega)]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- CSpace delete decode fails iff fewer than 1 message register. -/
theorem decodeCSpaceDeleteArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceDeleteArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeCSpaceDeleteArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeCSpaceDeleteArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- Lifecycle retype decode fails iff fewer than 3 message registers. -/
theorem decodeLifecycleRetypeArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeLifecycleRetypeArgs d = .error e) ↔ d.msgRegs.size < 3 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 3
    · exact hlt
    · exfalso
      simp only [decodeLifecycleRetypeArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeLifecycleRetypeArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        rw [requireMsgReg_unfold_err _ _ (by omega)]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- VSpace map decode fails iff fewer than 4 message registers. -/
theorem decodeVSpaceMapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceMapArgs d = .error e) ↔ d.msgRegs.size < 4 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 4
    · exact hlt
    · exfalso
      simp only [decodeVSpaceMapArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeVSpaceMapArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        by_cases h2 : 2 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h2]; simp
          rw [requireMsgReg_unfold_err _ _ (by omega)]
        · rw [requireMsgReg_unfold_err _ _ h2]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- VSpace unmap decode fails iff fewer than 2 message registers. -/
theorem decodeVSpaceUnmapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceUnmapArgs d = .error e) ↔ d.msgRegs.size < 2 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 2
    · exact hlt
    · exfalso
      simp only [decodeVSpaceUnmapArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeVSpaceUnmapArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      rw [requireMsgReg_unfold_err _ _ (by omega)]
    · rw [requireMsgReg_unfold_err _ _ h0]

end SeLe4n.Kernel.Architecture.SyscallArgDecode
