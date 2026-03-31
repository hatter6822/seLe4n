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
    Register mapping: x2=targetObj, x3=newType tag, x4=size hint.
    R7-E/L-10: `newType` is typed as `KernelObjectType` instead of raw `Nat`,
    ensuring only valid object types are accepted at the decode boundary. -/
structure LifecycleRetypeArgs where
  targetObj : ObjId
  newType   : KernelObjectType
  size      : Nat
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `vspaceMap`.
    Register mapping: x2=asid, x3=vaddr, x4=paddr, x5=perms word.
    T6-C/M-ARCH-1: `perms` is typed as `PagePermissions` instead of raw `Nat`.
    Validation occurs at decode time via `PagePermissions.ofNat?`, rejecting
    values outside the valid 5-bit range (0–31). -/
structure VSpaceMapArgs where
  asid  : ASID
  vaddr : VAddr
  paddr : PAddr
  perms : PagePermissions
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
         rights  := AccessRightSet.ofNat r2.val  -- Mask to valid 5-bit range at decode boundary
         badge   := Badge.ofNatMasked r3.val }

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
    Requires 3 message registers (targetObj, newType tag, size hint).
    R7-E/L-10: The raw `newType` tag is validated through `KernelObjectType.ofNat?`,
    rejecting unrecognized type tags at the decode boundary. -/
def decodeLifecycleRetypeArgs (decoded : SyscallDecodeResult)
    : Except KernelError LifecycleRetypeArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  match KernelObjectType.ofNat? r1.val with
  | some objType =>
    pure { targetObj := ObjId.ofNat r0.val
           newType   := objType
           size      := r2.val }
  | none => .error .invalidTypeTag

/-- Decode VSpace map arguments from message registers.
    Requires 4 message registers (asid, vaddr, paddr, perms word).
    T6-C/M-ARCH-1: Validates the permissions word at decode time via
    `PagePermissions.ofNat?`. Returns `invalidArgument` for values ≥ 32
    (undefined permission bits set — U5-E/U-M07: decode error, not policy).
    U2-B/U-H06: Validates VAddr lies within ARM64 48-bit canonical range.
    Returns `addressOutOfBounds` for VAddr ≥ 2^48. -/
def decodeVSpaceMapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceMapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  -- U2-G/U-H08: Validate ASID within 16-bit range (ARM64 standard: maxASID = 65536)
  let asid := ASID.ofNat r0.val
  if !asid.isValidForConfig 65536 then .error .asidNotBound
  else
  -- U2-B/U-H06: Validate VAddr lies within ARM64 48-bit canonical address range
  let vaddr := VAddr.ofNat r1.val
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else
    match PagePermissions.ofNat? r3.val with
    | some perms =>
      pure { asid  := asid
             vaddr := vaddr
             paddr := PAddr.ofNat r2.val
             perms := perms }
    -- U5-E/U-M07: Invalid permission bits are a decode error, not a policy violation.
    -- Prior to U5-E this incorrectly returned `.policyDenied`.
    -- X5-E/M-11: Use `invalidSyscallArgument` for syscall-specific decode context.
    | none => .error .invalidSyscallArgument

/-- Decode VSpace unmap arguments from message registers.
    Requires 2 message registers (asid, vaddr). -/
def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceUnmapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  -- U2-G/U-H08: Validate ASID within 16-bit range
  let asid := ASID.ofNat r0.val
  if !asid.isValidForConfig 65536 then .error .asidNotBound
  else
  pure { asid  := asid
         vaddr := VAddr.ofNat r1.val }

-- ============================================================================
-- V4-F/M-HW-5: MemoryKind cross-check for VSpace permissions
-- ============================================================================

/-- V4-F/M-HW-5: Post-decode validation that cross-checks VSpace permissions
    against the target physical address's `MemoryKind`. Device regions must not
    receive execute permission (execute-from-device is undefined on ARM64).

    This validation occurs after `decodeVSpaceMapArgs` because the memory map
    is not available at the register-decode layer. Callers (API dispatch) should
    invoke this check before passing arguments to `vspaceMapPageWithFlush`. -/
def validateVSpaceMapPermsForMemoryKind
    (args : VSpaceMapArgs) (memoryMap : List MemoryRegion) : Except KernelError VSpaceMapArgs :=
  let regionKind := memoryMap.find? (fun r => r.contains args.paddr)
    |>.map (fun r => r.kind)
  match regionKind with
  | some MemoryKind.device =>
    -- Device regions must not have execute permission
    if args.perms.execute then .error .policyDenied
    else .ok args
  | _ => .ok args

/-- V4-F: Device regions with execute permission are rejected. -/
theorem validateVSpaceMapPermsForMemoryKind_device_noexec
    (args : VSpaceMapArgs) (memoryMap : List MemoryRegion)
    (hFind : memoryMap.find? (fun r => r.contains args.paddr) = some region)
    (hDevice : region.kind = .device)
    (hExec : args.perms.execute = true) :
    ∃ e, validateVSpaceMapPermsForMemoryKind args memoryMap = .error e := by
  simp [validateVSpaceMapPermsForMemoryKind, hFind, hDevice, hExec]

-- ============================================================================
-- Encode functions (inverse of decode, for round-trip proofs)
-- ============================================================================

/-- Encode CSpace mint arguments into message registers.
    Inverse of `decodeCSpaceMintArgs`. -/
@[inline] def encodeCSpaceMintArgs (args : CSpaceMintArgs) : Array RegValue :=
  #[⟨args.srcSlot.toNat⟩, ⟨args.dstSlot.toNat⟩, ⟨args.rights.bits⟩, ⟨args.badge.toNat⟩]

/-- Encode CSpace copy arguments into message registers.
    Inverse of `decodeCSpaceCopyArgs`. -/
@[inline] def encodeCSpaceCopyArgs (args : CSpaceCopyArgs) : Array RegValue :=
  #[⟨args.srcSlot.toNat⟩, ⟨args.dstSlot.toNat⟩]

/-- Encode CSpace move arguments into message registers.
    Inverse of `decodeCSpaceMoveArgs`. -/
@[inline] def encodeCSpaceMoveArgs (args : CSpaceMoveArgs) : Array RegValue :=
  #[⟨args.srcSlot.toNat⟩, ⟨args.dstSlot.toNat⟩]

/-- Encode CSpace delete arguments into message registers.
    Inverse of `decodeCSpaceDeleteArgs`. -/
@[inline] def encodeCSpaceDeleteArgs (args : CSpaceDeleteArgs) : Array RegValue :=
  #[⟨args.targetSlot.toNat⟩]

/-- Encode lifecycle retype arguments into message registers.
    Inverse of `decodeLifecycleRetypeArgs`. -/
@[inline] def encodeLifecycleRetypeArgs (args : LifecycleRetypeArgs) : Array RegValue :=
  #[⟨args.targetObj.toNat⟩, ⟨args.newType.toNat⟩, ⟨args.size⟩]

/-- Encode VSpace map arguments into message registers.
    Inverse of `decodeVSpaceMapArgs`. T6-C: encodes PagePermissions via toNat. -/
@[inline] def encodeVSpaceMapArgs (args : VSpaceMapArgs) : Array RegValue :=
  #[⟨args.asid.toNat⟩, ⟨args.vaddr.toNat⟩, ⟨args.paddr.toNat⟩, ⟨args.perms.toNat⟩]

/-- Encode VSpace unmap arguments into message registers.
    Inverse of `decodeVSpaceUnmapArgs`. -/
@[inline] def encodeVSpaceUnmapArgs (args : VSpaceUnmapArgs) : Array RegValue :=
  #[⟨args.asid.toNat⟩, ⟨args.vaddr.toNat⟩]

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

/-- R7-E/L-10: Lifecycle retype decode fails if fewer than 3 message registers. -/
theorem decodeLifecycleRetypeArgs_error_of_insufficient_regs (d : SyscallDecodeResult)
    (h : d.msgRegs.size < 3) :
    ∃ e, decodeLifecycleRetypeArgs d = .error e := by
  refine ⟨.invalidMessageInfo, ?_⟩
  simp only [decodeLifecycleRetypeArgs, bind, Except.bind]
  by_cases h0 : 0 < d.msgRegs.size
  · rw [requireMsgReg_unfold_ok _ _ h0]; simp
    by_cases h1 : 1 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h1]; simp
      rw [requireMsgReg_unfold_err _ _ (by omega)]
    · rw [requireMsgReg_unfold_err _ _ h1]
  · rw [requireMsgReg_unfold_err _ _ h0]

/-- R7-E/L-10: Lifecycle retype decode fails if the type tag is unrecognized. -/
theorem decodeLifecycleRetypeArgs_error_of_invalid_type (d : SyscallDecodeResult)
    (hSize : 3 ≤ d.msgRegs.size)
    (hTag : KernelObjectType.ofNat? d.msgRegs[1].val = none) :
    ∃ e, decodeLifecycleRetypeArgs d = .error e := by
  refine ⟨.invalidTypeTag, ?_⟩
  simp only [decodeLifecycleRetypeArgs, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega), hTag]

/-- T6-C/D: VSpace map decode fails if fewer than 4 message registers. -/
theorem decodeVSpaceMapArgs_error_of_insufficient_regs (d : SyscallDecodeResult)
    (h : d.msgRegs.size < 4) :
    ∃ e, decodeVSpaceMapArgs d = .error e := by
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

/-- U2-B: VSpace map decode fails if VAddr is non-canonical (≥ 2^48). -/
theorem decodeVSpaceMapArgs_error_of_noncanonical_vaddr (d : SyscallDecodeResult)
    (hSize : 4 ≤ d.msgRegs.size)
    (hVAddr : (VAddr.ofNat d.msgRegs[1].val).isCanonical = false) :
    ∃ e, decodeVSpaceMapArgs d = .error e := by
  simp only [decodeVSpaceMapArgs, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega)]
  split
  · -- ASID invalid → error (asidNotBound)
    exact ⟨.asidNotBound, rfl⟩
  · -- ASID valid → VAddr check fails
    exact ⟨.addressOutOfBounds, by simp [hVAddr]⟩

/-- T6-D/M-ARCH-1: VSpace map decode fails if the permissions word is invalid (≥ 32). -/
theorem decodeVSpaceMapArgs_error_of_invalid_perms (d : SyscallDecodeResult)
    (hSize : 4 ≤ d.msgRegs.size)
    (hPerms : PagePermissions.ofNat? d.msgRegs[3].val = none) :
    ∃ e, decodeVSpaceMapArgs d = .error e := by
  simp only [decodeVSpaceMapArgs, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega)]
  split
  · -- ASID invalid → error
    exact ⟨.asidNotBound, rfl⟩
  · -- ASID valid → check VAddr
    split
    · -- VAddr not canonical → error
      exact ⟨.addressOutOfBounds, rfl⟩
    · -- VAddr canonical → perms check fails
      exact ⟨.invalidSyscallArgument, by simp [hPerms]⟩

/-- VSpace map decode fails iff fewer than 4 message registers,
    ASID is invalid, VAddr is non-canonical, or the permissions word is invalid.
    Four failure modes:
    1. `msgRegs.size < 4` → `requireMsgReg` returns error
    2. ASID (msgRegs[0]) ≥ 65536 → asidNotBound
    3. VAddr (msgRegs[1]) ≥ 2^48 → addressOutOfBounds
    4. `msgRegs.size ≥ 4`, ASID valid, VAddr canonical, but `PagePermissions.ofNat?` returns none → invalidSyscallArgument (X5-E) -/
theorem decodeVSpaceMapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceMapArgs d = .error e) ↔
    (d.msgRegs.size < 4 ∨
     (∃ (h : 3 < d.msgRegs.size), (ASID.ofNat (d.msgRegs[0]'(by omega)).val).isValidForConfig 65536 = false) ∨
     (∃ (h : 3 < d.msgRegs.size), (VAddr.ofNat (d.msgRegs[1]'(by omega)).val).isCanonical = false) ∨
     (∃ (h : 3 < d.msgRegs.size), PagePermissions.ofNat? (d.msgRegs[3]'h).val = none)) := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 4
    · exact .inl hlt
    · have h3 : 3 < d.msgRegs.size := by omega
      simp only [decodeVSpaceMapArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega)] at he
      split at he
      · -- ASID invalid
        rename_i hAsidInvalid
        right; left
        exact ⟨h3, by
          simp only [Bool.not_eq_true'] at hAsidInvalid
          cases hc : (ASID.ofNat d.msgRegs[0].val).isValidForConfig 65536
          · rfl
          · rw [hc] at hAsidInvalid; simp at hAsidInvalid⟩
      · -- ASID valid → check VAddr
        split at he
        · -- VAddr not canonical
          rename_i hNotCanon
          right; right; left
          exact ⟨h3, by
            simp only [Bool.not_eq_true'] at hNotCanon
            cases hc : (VAddr.ofNat d.msgRegs[1].val).isCanonical
            · rfl
            · rw [hc] at hNotCanon; simp at hNotCanon⟩
        · -- VAddr canonical → check perms
          right; right; right
          exact ⟨h3, by
            split at he
            · -- some perms case: decode succeeded → contradicts error assumption
              nomatch he
            · -- none case: perms invalid
              assumption⟩
  · intro h
    match h with
    | .inl hLt => exact decodeVSpaceMapArgs_error_of_insufficient_regs d hLt
    | .inr (.inl ⟨h3, hAsid⟩) =>
      exact ⟨.asidNotBound, by
        simp only [decodeVSpaceMapArgs, bind, Except.bind,
          requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
          dif_pos (show 1 < d.msgRegs.size by omega),
          dif_pos (show 2 < d.msgRegs.size by omega),
          dif_pos (show 3 < d.msgRegs.size by omega)]
        have : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig 65536) = true := by
          rw [hAsid]; rfl
        simp [this]⟩
    | .inr (.inr (.inl ⟨h3, hVAddr⟩)) =>
      exact decodeVSpaceMapArgs_error_of_noncanonical_vaddr d (by omega) hVAddr
    | .inr (.inr (.inr ⟨h3, hPerms⟩)) =>
      exact decodeVSpaceMapArgs_error_of_invalid_perms d (by omega) hPerms

/-- VSpace unmap decode fails iff fewer than 2 message registers or ASID invalid. -/
theorem decodeVSpaceUnmapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceUnmapArgs d = .error e) ↔
    (d.msgRegs.size < 2 ∨
     (∃ (h : 1 < d.msgRegs.size), (ASID.ofNat (d.msgRegs[0]'(by omega)).val).isValidForConfig 65536 = false)) := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 2
    · exact .inl hlt
    · have h1 : 1 < d.msgRegs.size := by omega
      simp only [decodeVSpaceUnmapArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega)] at he
      split at he
      · -- ASID invalid
        rename_i hAsidInvalid
        right
        exact ⟨h1, by
          simp only [Bool.not_eq_true'] at hAsidInvalid
          cases hc : (ASID.ofNat d.msgRegs[0].val).isValidForConfig 65536
          · rfl
          · rw [hc] at hAsidInvalid; simp at hAsidInvalid⟩
      · -- ASID valid → pure succeeds → contradiction
        nomatch he
  · intro h
    match h with
    | .inl hLt =>
      refine ⟨.invalidMessageInfo, ?_⟩
      simp only [decodeVSpaceUnmapArgs, bind, Except.bind]
      by_cases h0 : 0 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h0]; simp
        rw [requireMsgReg_unfold_err _ _ (by omega)]
      · rw [requireMsgReg_unfold_err _ _ h0]
    | .inr ⟨h1, hAsid⟩ =>
      exact ⟨.asidNotBound, by
        simp only [decodeVSpaceUnmapArgs, bind, Except.bind,
          requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
          dif_pos (show 1 < d.msgRegs.size by omega)]
        have : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig 65536) = true := by
          rw [hAsid]; rfl
        simp [this]⟩

-- ============================================================================
-- Round-trip proofs: encode then decode recovers the original
-- ============================================================================

/-- Helper: a `SyscallDecodeResult` stub with given message registers.
    Used exclusively for round-trip proof statements. -/
private def stubDecoded (regs : Array RegValue) : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := regs }

/-- Round-trip: encoding then decoding CSpaceMintArgs recovers the original
    when the rights are valid (bits < 32) and the badge is word-bounded.
    R6-B: `ofNatMasked` decode requires the badge to fit in one machine word
    for lossless roundtrip. Y1-D: `ofNat` decode masks to 5-bit range, so
    lossless roundtrip requires `args.rights.valid`. -/
theorem decodeCSpaceMintArgs_roundtrip (args : CSpaceMintArgs)
    (hRights : args.rights.valid) (hBadge : args.badge.valid) :
    decodeCSpaceMintArgs (stubDecoded (encodeCSpaceMintArgs args)) = .ok args := by
  rcases args with ⟨s, d, r, ⟨bv⟩⟩
  simp only [Badge.valid, machineWordMax, machineWordBits] at hBadge
  have hModBadge : bv % 18446744073709551616 = bv := Nat.mod_eq_of_lt hBadge
  have hModRights : AccessRightSet.ofNat r.bits = r := AccessRightSet.ofNat_idempotent r hRights
  show Except.ok (⟨Slot.ofNat s.toNat, Slot.ofNat d.toNat, AccessRightSet.ofNat r.bits, ⟨bv % 18446744073709551616⟩⟩ : CSpaceMintArgs) = Except.ok ⟨s, d, r, ⟨bv⟩⟩
  simp only [Slot.ofNat, Slot.toNat, hModRights, hModBadge]

/-- Round-trip: encoding then decoding CSpaceCopyArgs recovers the original. -/
theorem decodeCSpaceCopyArgs_roundtrip (args : CSpaceCopyArgs) :
    decodeCSpaceCopyArgs (stubDecoded (encodeCSpaceCopyArgs args)) = .ok args := by
  rcases args with ⟨s, d⟩; rfl

/-- Round-trip: encoding then decoding CSpaceMoveArgs recovers the original. -/
theorem decodeCSpaceMoveArgs_roundtrip (args : CSpaceMoveArgs) :
    decodeCSpaceMoveArgs (stubDecoded (encodeCSpaceMoveArgs args)) = .ok args := by
  rcases args with ⟨s, d⟩; rfl

/-- Round-trip: encoding then decoding CSpaceDeleteArgs recovers the original. -/
theorem decodeCSpaceDeleteArgs_roundtrip (args : CSpaceDeleteArgs) :
    decodeCSpaceDeleteArgs (stubDecoded (encodeCSpaceDeleteArgs args)) = .ok args := by
  rcases args with ⟨t⟩; rfl

/-- Round-trip: encoding then decoding LifecycleRetypeArgs recovers the original.
    R7-E/L-10: The proof case-splits on `KernelObjectType` — each variant reduces
    to `rfl` because `ofNat?` and `toNat` are definitional inverses per case. -/
theorem decodeLifecycleRetypeArgs_roundtrip (args : LifecycleRetypeArgs) :
    decodeLifecycleRetypeArgs (stubDecoded (encodeLifecycleRetypeArgs args)) = .ok args := by
  rcases args with ⟨o, t, s⟩
  simp only [decodeLifecycleRetypeArgs, encodeLifecycleRetypeArgs, stubDecoded,
    requireMsgReg, KernelObjectType.toNat]
  cases t <;> rfl

/-- T6-C: Round-trip requires that the permissions encode to a valid range.
    `PagePermissions.toNat` always produces values < 32 (5-bit bitfield). -/
private theorem pagePermissions_toNat_lt_32 (p : PagePermissions) :
    p.toNat < 32 := by
  rcases p with ⟨r, w, e, u, c⟩
  cases r <;> cases w <;> cases e <;> cases u <;> cases c <;> decide

private theorem pagePermissions_ofNat?_toNat (p : PagePermissions)
    (hWx : p.wxCompliant = true) :
    PagePermissions.ofNat? p.toNat = some (PagePermissions.ofNat p.toNat) := by
  have hLt := pagePermissions_toNat_lt_32 p
  have hWxRt : (PagePermissions.ofNat p.toNat).wxCompliant = true := by
    rw [PagePermissions.ofNat_toNat_roundtrip]; exact hWx
  simp [PagePermissions.ofNat?, hLt, hWxRt]

/-- U2-B/U2-G/V4-K: Round-trip requires VAddr is canonical (within 48-bit range),
    ASID is valid for config 65536, and permissions are W^X compliant.
    V4-K: W^X compliance is now enforced at decode time by `ofNat?`. -/
theorem decodeVSpaceMapArgs_roundtrip (args : VSpaceMapArgs)
    (hAsid : args.asid.isValidForConfig 65536 = true)
    (hVAddr : args.vaddr.isCanonical = true)
    (hWx : args.perms.wxCompliant = true) :
    decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs args)) = .ok args := by
  rcases args with ⟨a, v, p, perms⟩
  show decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs ⟨a, v, p, perms⟩)) = .ok ⟨a, v, p, perms⟩
  -- U2-G: The ASID validity check needs to pass; derive that from hAsid
  have hAsidValid : (ASID.ofNat a.toNat).isValidForConfig 65536 = true := by
    simp only [ASID.ofNat, ASID.toNat]; exact hAsid
  have hAsidNotFalse : (!(ASID.ofNat a.toNat).isValidForConfig 65536) = false := by
    rw [hAsidValid]; rfl
  -- U2-B: The VAddr canonical check needs to pass; derive that from hVAddr
  have hCanon : (VAddr.ofNat v.toNat).isCanonical = true := by
    simp only [VAddr.ofNat, VAddr.toNat]; exact hVAddr
  have hNotCanonFalse : (!(VAddr.ofNat v.toNat).isCanonical) = false := by
    rw [hCanon]; rfl
  rcases perms with ⟨r, w, e, u, c⟩
  have hA : a.isValidForConfig 65536 = true := hAsid
  have hV : v.isCanonical = true := hVAddr
  -- V4-K: W^X cases (write=true, execute=true) are excluded by hWx
  cases r <;> cases w <;> cases e <;> cases u <;> cases c <;>
    simp_all [decodeVSpaceMapArgs, encodeVSpaceMapArgs, stubDecoded,
      bind, Except.bind, requireMsgReg, PagePermissions.wxCompliant,
      PagePermissions.toNat, PagePermissions.ofNat?, PagePermissions.ofNat,
      ASID.ofNat_toNat, VAddr.ofNat_toNat, PAddr.ofNat_toNat, pure, Except.pure]

/-- Round-trip: encoding then decoding VSpaceUnmapArgs recovers the original.
    U2-G: Requires ASID is valid for config 65536. -/
theorem decodeVSpaceUnmapArgs_roundtrip (args : VSpaceUnmapArgs)
    (hAsid : args.asid.isValidForConfig 65536 = true) :
    decodeVSpaceUnmapArgs (stubDecoded (encodeVSpaceUnmapArgs args)) = .ok args := by
  rcases args with ⟨a, v⟩
  simp [decodeVSpaceUnmapArgs, encodeVSpaceUnmapArgs, stubDecoded,
    bind, Except.bind, requireMsgReg, ASID.ofNat_toNat, VAddr.ofNat_toNat,
    pure, Except.pure, hAsid]

-- ============================================================================
-- WS-Q1-D: Service argument structures
-- ============================================================================

/-- Per-syscall argument structure for `serviceRegister`.
    Register mapping: x2=interfaceId, x3=methodCount, x4=maxMessageSize,
    x5=maxResponseSize, x6=requiresGrant (0 or 1). -/
structure ServiceRegisterArgs where
  interfaceId    : InterfaceId
  methodCount    : Nat
  maxMessageSize : Nat
  maxResponseSize : Nat
  requiresGrant  : Bool
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `serviceRevoke`.
    Register mapping: x2=serviceId. -/
structure ServiceRevokeArgs where
  targetService : ServiceId
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `serviceQuery`.
    No additional message registers required — the endpoint object ID comes
    from the capability target, not from message registers. -/
structure ServiceQueryArgs where
  deriving Repr, DecidableEq

-- ============================================================================
-- WS-Q1-D: Service decode functions
-- ============================================================================

/-- Decode service register arguments from message registers.
    Requires 5 message registers (interfaceId, methodCount, maxMessageSize,
    maxResponseSize, requiresGrant). -/
def decodeServiceRegisterArgs (decoded : SyscallDecodeResult)
    : Except KernelError ServiceRegisterArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  let r4 ← requireMsgReg decoded.msgRegs 4
  pure { interfaceId    := InterfaceId.ofNat r0.val
         methodCount    := r1.val
         maxMessageSize := r2.val
         maxResponseSize := r3.val
         requiresGrant  := r4.val != 0 }

/-- Decode service revoke arguments from message registers.
    Requires 1 message register (serviceId). -/
def decodeServiceRevokeArgs (decoded : SyscallDecodeResult)
    : Except KernelError ServiceRevokeArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { targetService := ⟨r0.val⟩ }

-- ============================================================================
-- WS-Q1-D: Service encode functions
-- ============================================================================

/-- Encode service register arguments into message registers.
    Inverse of `decodeServiceRegisterArgs`. -/
@[inline] def encodeServiceRegisterArgs (args : ServiceRegisterArgs) : Array RegValue :=
  #[⟨args.interfaceId.toNat⟩, ⟨args.methodCount⟩, ⟨args.maxMessageSize⟩,
    ⟨args.maxResponseSize⟩, ⟨if args.requiresGrant then 1 else 0⟩]

/-- Encode service revoke arguments into message registers.
    Inverse of `decodeServiceRevokeArgs`. -/
@[inline] def encodeServiceRevokeArgs (args : ServiceRevokeArgs) : Array RegValue :=
  #[⟨args.targetService.toNat⟩]

-- ============================================================================
-- WS-Q1-D: Service error-exclusivity theorems
-- ============================================================================

/-- Service register decode fails iff fewer than 5 message registers. -/
theorem decodeServiceRegisterArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeServiceRegisterArgs d = .error e) ↔ d.msgRegs.size < 5 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 5
    · exact hlt
    · exfalso
      simp only [decodeServiceRegisterArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega),
        dif_pos (show 4 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeServiceRegisterArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        by_cases h2 : 2 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h2]; simp
          by_cases h3 : 3 < d.msgRegs.size
          · rw [requireMsgReg_unfold_ok _ _ h3]; simp
            rw [requireMsgReg_unfold_err _ _ (by omega)]
          · rw [requireMsgReg_unfold_err _ _ h3]
        · rw [requireMsgReg_unfold_err _ _ h2]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- Service revoke decode fails iff fewer than 1 message register. -/
theorem decodeServiceRevokeArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeServiceRevokeArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeServiceRevokeArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeServiceRevokeArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

-- ============================================================================
-- WS-Q1-D: Service round-trip theorems
-- ============================================================================

/-- Round-trip: encoding then decoding ServiceRegisterArgs recovers the original. -/
theorem decodeServiceRegisterArgs_roundtrip (args : ServiceRegisterArgs) :
    decodeServiceRegisterArgs (stubDecoded (encodeServiceRegisterArgs args)) = .ok args := by
  rcases args with ⟨iid, mc, mms, mrs, rg⟩
  simp [decodeServiceRegisterArgs, encodeServiceRegisterArgs, stubDecoded,
        requireMsgReg, bind, Except.bind, pure, Except.pure,
        InterfaceId.ofNat, InterfaceId.toNat]
  cases rg <;> simp

/-- Round-trip: encoding then decoding ServiceRevokeArgs recovers the original. -/
theorem decodeServiceRevokeArgs_roundtrip (args : ServiceRevokeArgs) :
    decodeServiceRevokeArgs (stubDecoded (encodeServiceRevokeArgs args)) = .ok args := by
  rcases args with ⟨s⟩; rfl

-- ============================================================================
-- V2-I: Notification and ReplyRecv argument structures
-- ============================================================================

/-- V2-A/V2-I: Per-syscall argument structure for `notificationSignal`.
    Register mapping: x2=badge value.
    The notification object is resolved from the capability target (no MR decode). -/
structure NotificationSignalArgs where
  badge : Badge
  deriving Repr, DecidableEq

/-- V2-A/V2-I: Per-syscall argument structure for `notificationWait`.
    No message registers needed — the notification object is resolved from the
    capability target. The waiter thread ID comes from the current thread. -/
structure NotificationWaitArgs where
  deriving Repr, DecidableEq

/-- V2-C/V2-I: Per-syscall argument structure for `replyRecv`.
    Register mapping: x2=replyTarget thread ID.
    The endpoint is resolved from the capability target. Message body comes
    from the standard message registers (same as send). -/
structure ReplyRecvArgs where
  replyTarget : ThreadId
  deriving Repr, DecidableEq

/-- V2-I: Decode notification signal arguments from message registers.
    Requires 1 message register (badge). -/
def decodeNotificationSignalArgs (decoded : SyscallDecodeResult)
    : Except KernelError NotificationSignalArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { badge := Badge.ofNatMasked r0.val }

/-- V2-I: Decode notification wait arguments. No message registers needed. -/
def decodeNotificationWaitArgs (_decoded : SyscallDecodeResult)
    : Except KernelError NotificationWaitArgs :=
  pure {}

/-- V2-I: Decode replyRecv arguments from message registers.
    Requires 1 message register (reply target thread ID). -/
def decodeReplyRecvArgs (decoded : SyscallDecodeResult)
    : Except KernelError ReplyRecvArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { replyTarget := ThreadId.ofNat r0.val }

-- ============================================================================
-- Z5-A/B/C: SchedContext argument structures
-- ============================================================================

/-- Z5-A: Per-syscall argument structure for `schedContextConfigure`.
    Register mapping: x2=budget, x3=period, x4=priority, x5=deadline, x6=domain. -/
structure SchedContextConfigureArgs where
  budget   : Nat
  period   : Nat
  priority : Nat
  deadline : Nat
  domain   : Nat
  deriving Repr, DecidableEq

/-- Z5-B: Per-syscall argument structure for `schedContextBind`.
    Register mapping: x2=threadId (thread to bind to this SchedContext). -/
structure SchedContextBindArgs where
  threadId : Nat
  deriving Repr, DecidableEq

/-- Z5-C: Per-syscall argument structure for `schedContextUnbind`.
    No additional arguments — the SchedContext comes from the capability target. -/
structure SchedContextUnbindArgs where
  deriving Repr, DecidableEq

-- ============================================================================
-- Z5-A/B/C: SchedContext decode functions
-- ============================================================================

/-- Z5-A: Decode schedContextConfigure arguments from message registers.
    Requires 5 message registers (budget, period, priority, deadline, domain). -/
def decodeSchedContextConfigureArgs (decoded : SyscallDecodeResult)
    : Except KernelError SchedContextConfigureArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  let r4 ← requireMsgReg decoded.msgRegs 4
  pure { budget := r0.val, period := r1.val, priority := r2.val,
         deadline := r3.val, domain := r4.val }

/-- Z5-B: Decode schedContextBind arguments from message registers.
    Requires 1 message register (threadId). -/
def decodeSchedContextBindArgs (decoded : SyscallDecodeResult)
    : Except KernelError SchedContextBindArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { threadId := r0.val }

/-- Z5-C: Decode schedContextUnbind arguments. No message registers needed. -/
def decodeSchedContextUnbindArgs (_decoded : SyscallDecodeResult)
    : Except KernelError SchedContextUnbindArgs :=
  pure {}

-- ============================================================================
-- Z5-A/B/C: SchedContext encode functions
-- ============================================================================

/-- Z5-A: Encode schedContextConfigure arguments into message registers. -/
@[inline] def encodeSchedContextConfigureArgs (args : SchedContextConfigureArgs) : Array RegValue :=
  #[⟨args.budget⟩, ⟨args.period⟩, ⟨args.priority⟩, ⟨args.deadline⟩, ⟨args.domain⟩]

/-- Z5-B: Encode schedContextBind arguments into message registers. -/
@[inline] def encodeSchedContextBindArgs (args : SchedContextBindArgs) : Array RegValue :=
  #[⟨args.threadId⟩]

/-- Z5-C: Encode schedContextUnbind arguments (empty — no message registers). -/
@[inline] def encodeSchedContextUnbindArgs (_args : SchedContextUnbindArgs) : Array RegValue :=
  #[]

-- ============================================================================
-- Z5-A/B/C: SchedContext round-trip proofs
-- ============================================================================

/-- Z5-A: SchedContextConfigureArgs decode round-trip. -/
theorem decodeSchedContextConfigureArgs_roundtrip (args : SchedContextConfigureArgs) :
    decodeSchedContextConfigureArgs (stubDecoded (encodeSchedContextConfigureArgs args)) = .ok args := by
  rcases args with ⟨b, p, pr, d, dm⟩; rfl

/-- Z5-B: SchedContextBindArgs decode round-trip. -/
theorem decodeSchedContextBindArgs_roundtrip (args : SchedContextBindArgs) :
    decodeSchedContextBindArgs (stubDecoded (encodeSchedContextBindArgs args)) = .ok args := by
  rcases args with ⟨t⟩; rfl

/-- Z5-C: SchedContextUnbindArgs decode round-trip (trivial). -/
theorem decodeSchedContextUnbindArgs_roundtrip (args : SchedContextUnbindArgs) :
    decodeSchedContextUnbindArgs (stubDecoded (encodeSchedContextUnbindArgs args)) = .ok args := by
  rcases args; rfl

/-- V2-I: Encode notification signal arguments into message registers. -/
@[inline] def encodeNotificationSignalArgs (args : NotificationSignalArgs) : Array RegValue :=
  #[⟨args.badge.val⟩]

/-- V2-I: Encode notification wait arguments (empty — no message registers). -/
@[inline] def encodeNotificationWaitArgs (_args : NotificationWaitArgs) : Array RegValue :=
  #[]

/-- V2-I: Encode replyRecv arguments into message registers. -/
@[inline] def encodeReplyRecvArgs (args : ReplyRecvArgs) : Array RegValue :=
  #[⟨args.replyTarget.toNat⟩]

/-- V2-I: NotificationSignalArgs decode round-trip.
    Requires badge validity for lossless round-trip through `ofNatMasked`. -/
theorem decodeNotificationSignalArgs_roundtrip (args : NotificationSignalArgs)
    (hBadge : args.badge.valid) :
    decodeNotificationSignalArgs (stubDecoded (encodeNotificationSignalArgs args)) = .ok args := by
  rcases args with ⟨b⟩
  simp [decodeNotificationSignalArgs, encodeNotificationSignalArgs, stubDecoded,
        requireMsgReg, bind, Except.bind, pure, Except.pure]
  exact Badge.ofNatMasked_toNat b hBadge

/-- V2-I: NotificationWaitArgs decode round-trip (trivial — no MR decode). -/
theorem decodeNotificationWaitArgs_roundtrip (args : NotificationWaitArgs) :
    decodeNotificationWaitArgs (stubDecoded (encodeNotificationWaitArgs args)) = .ok args := by
  rcases args; rfl

/-- V2-I: ReplyRecvArgs decode round-trip. -/
theorem decodeReplyRecvArgs_roundtrip (args : ReplyRecvArgs) :
    decodeReplyRecvArgs (stubDecoded (encodeReplyRecvArgs args)) = .ok args := by
  rcases args with ⟨t⟩; rfl

/-- Composed round-trip: all 15 argument structures satisfy the encode-decode
    round-trip property. R6-B: CSpaceMintArgs and NotificationSignalArgs require
    badge validity for lossless roundtrip through `ofNatMasked`. Y1-D:
    CSpaceMintArgs additionally requires rights validity for lossless roundtrip
    through `AccessRightSet.ofNat`. Parallel to `decode_components_roundtrip`
    in `RegisterDecode.lean`. -/
theorem decode_layer2_roundtrip_all :
    (∀ args, args.rights.valid → args.badge.valid →
      decodeCSpaceMintArgs (stubDecoded (encodeCSpaceMintArgs args)) = .ok args) ∧
    (∀ args, decodeCSpaceCopyArgs (stubDecoded (encodeCSpaceCopyArgs args)) = .ok args) ∧
    (∀ args, decodeCSpaceMoveArgs (stubDecoded (encodeCSpaceMoveArgs args)) = .ok args) ∧
    (∀ args, decodeCSpaceDeleteArgs (stubDecoded (encodeCSpaceDeleteArgs args)) = .ok args) ∧
    (∀ args, decodeLifecycleRetypeArgs (stubDecoded (encodeLifecycleRetypeArgs args)) = .ok args) ∧
    (∀ args, args.asid.isValidForConfig 65536 = true → args.vaddr.isCanonical = true →
      args.perms.wxCompliant = true →
      decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs args)) = .ok args) ∧
    (∀ args, args.asid.isValidForConfig 65536 = true →
      decodeVSpaceUnmapArgs (stubDecoded (encodeVSpaceUnmapArgs args)) = .ok args) ∧
    (∀ args, decodeServiceRegisterArgs (stubDecoded (encodeServiceRegisterArgs args)) = .ok args) ∧
    (∀ args, decodeServiceRevokeArgs (stubDecoded (encodeServiceRevokeArgs args)) = .ok args) ∧
    (∀ args, args.badge.valid →
      decodeNotificationSignalArgs (stubDecoded (encodeNotificationSignalArgs args)) = .ok args) ∧
    (∀ args, decodeNotificationWaitArgs (stubDecoded (encodeNotificationWaitArgs args)) = .ok args) ∧
    (∀ args, decodeReplyRecvArgs (stubDecoded (encodeReplyRecvArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextConfigureArgs (stubDecoded (encodeSchedContextConfigureArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextBindArgs (stubDecoded (encodeSchedContextBindArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextUnbindArgs (stubDecoded (encodeSchedContextUnbindArgs args)) = .ok args) :=
  ⟨fun args hR hB => decodeCSpaceMintArgs_roundtrip args hR hB,
   decodeCSpaceCopyArgs_roundtrip,
   decodeCSpaceMoveArgs_roundtrip,
   decodeCSpaceDeleteArgs_roundtrip,
   decodeLifecycleRetypeArgs_roundtrip,
   fun args hA hV hWx => decodeVSpaceMapArgs_roundtrip args hA hV hWx,
   fun args hA => decodeVSpaceUnmapArgs_roundtrip args hA,
   decodeServiceRegisterArgs_roundtrip,
   decodeServiceRevokeArgs_roundtrip,
   fun args h => decodeNotificationSignalArgs_roundtrip args h,
   decodeNotificationWaitArgs_roundtrip,
   decodeReplyRecvArgs_roundtrip,
   decodeSchedContextConfigureArgs_roundtrip,
   decodeSchedContextBindArgs_roundtrip,
   decodeSchedContextUnbindArgs_roundtrip⟩

/-- V2-I: NotificationSignalArgs error exclusivity. -/
theorem decodeNotificationSignalArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeNotificationSignalArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeNotificationSignalArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeNotificationSignalArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- V2-I: ReplyRecvArgs error exclusivity. -/
theorem decodeReplyRecvArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeReplyRecvArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeReplyRecvArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeReplyRecvArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

-- ============================================================================
-- Z8-B: SchedContext error-exclusivity theorems
-- ============================================================================

/-- Z8-B: SchedContextConfigureArgs decode fails iff fewer than 5 message registers. -/
theorem decodeSchedContextConfigureArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeSchedContextConfigureArgs d = .error e) ↔ d.msgRegs.size < 5 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 5
    · exact hlt
    · exfalso
      simp only [decodeSchedContextConfigureArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega),
        dif_pos (show 4 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeSchedContextConfigureArgs, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        by_cases h2 : 2 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h2]; simp
          by_cases h3 : 3 < d.msgRegs.size
          · rw [requireMsgReg_unfold_ok _ _ h3]; simp
            rw [requireMsgReg_unfold_err _ _ (by omega)]
          · rw [requireMsgReg_unfold_err _ _ h3]
        · rw [requireMsgReg_unfold_err _ _ h2]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- Z8-B: SchedContextBindArgs decode fails iff fewer than 1 message register. -/
theorem decodeSchedContextBindArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeSchedContextBindArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeSchedContextBindArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeSchedContextBindArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- Z8-B: SchedContextUnbindArgs decode never fails (no message registers required). -/
theorem decodeSchedContextUnbindArgs_error_iff (d : SyscallDecodeResult) :
    ¬(∃ e, decodeSchedContextUnbindArgs d = .error e) := by
  intro ⟨e, he⟩
  simp only [decodeSchedContextUnbindArgs, pure, Except.pure] at he
  nomatch he

-- ============================================================================
-- IPC extra capability address decode (M-D01)
-- ============================================================================

/-- M-D01: Decode extra capability addresses from message registers.

seL4 convention: extra cap addresses are packed into the message registers
immediately after the message body. The `msgInfo.extraCaps` field (0..3)
specifies how many extra cap addresses follow. Each extra cap address is
a single register value interpreted as a CPtr.

Returns an array of CPtrs (length ≤ 3). If a register index is out of
bounds, the corresponding cap address is silently dropped (seL4 behavior:
truncate to available registers). -/
def decodeExtraCapAddrs (decoded : SyscallDecodeResult) :
    Array SeLe4n.CPtr :=
  let startIdx := decoded.msgInfo.length
  let count := min decoded.msgInfo.extraCaps maxExtraCaps
  (Array.range count).filterMap fun i =>
    decoded.msgRegs[startIdx + i]?.map fun rv => ⟨rv.val⟩

-- ============================================================================
-- X4-F/M-8: Platform-specific regCount validation
-- ============================================================================

/-- X4-F/M-8: ARM64 register count correctness.
    Confirms that the default `regCount := 32` used by `decodeSyscallArgs`
    matches the architectural GPR count defined in `Machine.lean`.
    ARM64 AAPCS64: x0–x30 (31 general-purpose) + xzr (zero register) = 32 indices.
    Register index 31 (xzr) is the last valid index; index 32 is correctly
    rejected by `validateRegBound`.

    If targeting a non-ARM64 platform with a different register file width,
    `regCount` must be updated to match `RegName.arm64GPRCount` (or its
    platform-specific equivalent) and this theorem must be re-proven. -/
theorem arm64_regCount_valid :
    32 = RegName.arm64GPRCount := rfl

/-- X4-F/M-8: The `MachineConfig.registerCount` default value equals the
    ARM64 GPR count, ensuring configuration-level consistency.
    Any `MachineConfig` using the default `registerCount` field is aligned
    with the ARM64 architecture. -/
theorem machineConfig_registerCount_default_eq_arm64GPRCount :
    ({ registerWidth := 64, virtualAddressWidth := 48,
       physicalAddressWidth := 44, pageSize := 4096,
       maxASID := 65536, memoryMap := [] } : MachineConfig).registerCount
    = RegName.arm64GPRCount := rfl

end SeLe4n.Kernel.Architecture.SyscallArgDecode
