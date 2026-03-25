/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # Register Decode Layer

This module provides total, deterministic decode functions that convert raw
register values from the machine register file into typed kernel references.
It models the syscall argument decode path that real hardware mandates: on
ARM64, syscall arguments arrive in general-purpose registers x0–x7, and the
kernel must decode raw register words into typed kernel references before any
authority check can proceed.

**Dependencies:** Only `Machine.lean` (via `Model.State`) and
`Model/Object/Types.lean`. Does not import any kernel subsystem module.
Subsystems consume decoded results, not this module.

**Key properties:**
- All decode functions are total with explicit `Except KernelError` returns.
- Round-trip lemmas prove encode-then-decode recovers the original value.
- Determinism theorem proves decode of identical inputs produces identical results.
-/

namespace SeLe4n.Kernel.Architecture.RegisterDecode

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- Encoding helpers (for round-trip proofs)
-- ============================================================================

/-- Encode a capability pointer as a register value. -/
@[inline] def encodeCapPtr (c : CPtr) : RegValue := ⟨c.toNat⟩

/-- Encode a message info structure as a register value. -/
@[inline] def encodeMsgInfo (mi : MessageInfo) : RegValue := ⟨mi.encode⟩

/-- Encode a syscall identifier as a register value. -/
@[inline] def encodeSyscallId (s : SyscallId) : RegValue := ⟨s.toNat⟩

/-- Encode message register values (identity in the abstract model).
    Stated explicitly for proof-surface completeness and round-trip symmetry
    with the other `encode*` helpers. -/
@[inline] def encodeMsgRegs (regs : Array RegValue) : Array RegValue := regs

/-- Extract message register values for IPC message population.
    Converts `RegValue` wrappers to raw `Nat` values and limits the result
    to `min info.length (min maxMessageRegisters msgRegs.size)` entries.

    The length is bounded three ways:
    1. `info.length` — the sender's declared message length.
    2. `maxMessageRegisters` (120) — the seL4 protocol maximum.
    3. `msgRegs.size` — the platform's inline register count (4 on ARM64).

    S4-D: Returns `Array RegValue` to match `IpcMessage.registers : Array RegValue`.
    Previously returned `Array Nat` via `.map RegValue.val`; now preserves the
    typed wrapper throughout the IPC pipeline. -/
@[inline] def extractMessageRegisters (msgRegs : Array RegValue)
    (info : MessageInfo) : Array RegValue :=
  let count := min info.length (min maxMessageRegisters msgRegs.size)
  msgRegs.extract 0 count

-- ============================================================================
-- Decode functions — total with explicit error returns
-- ============================================================================

/-- Decode a raw register value into a capability pointer.

    S4-K: Returns `invalidCapPtr` for register values exceeding 64-bit word
    bounds (`rv.val ≥ 2^64`). In the abstract model with unbounded `Nat`, this
    rejects values that cannot be represented in a hardware register. On real
    ARM64 hardware, all register values are inherently 64-bit and this check
    is always satisfied. The bounds check ensures model-level consistency:
    proofs about CPtr values hold for the hardware word size. -/
@[inline] def decodeCapPtr (rv : RegValue) : Except KernelError CPtr :=
  if isWord64Dec rv.val then .ok (CPtr.ofNat rv.val)
  else .error .invalidCapPtr

/-- Decode a raw register value into a message info word.
    Extracts length, extra caps count, and label from bit fields.
    Returns `invalidMessageInfo` if length or extraCaps exceed bounds. -/
@[inline] def decodeMsgInfo (rv : RegValue) : Except KernelError MessageInfo :=
  match MessageInfo.decode rv.val with
  | some mi => .ok mi
  | none    => .error .invalidMessageInfo

/-- Decode the syscall number register into a typed syscall identifier.
    Returns `invalidSyscallNumber` if the value is not in the modeled set. -/
@[inline] def decodeSyscallId (rv : RegValue) : Except KernelError SyscallId :=
  match SyscallId.ofNat? rv.val with
  | some sid => .ok sid
  | none     => .error .invalidSyscallNumber

/-- Validate that a register name is within architectural bounds.
    Returns `invalidRegister` if the index exceeds `registerCount`. -/
@[inline] def validateRegBound (r : RegName) (bound : Nat) : Except KernelError Unit :=
  if r.val < bound then .ok () else .error .invalidRegister

/-- Extract typed syscall arguments from the current thread's register file
    using the platform's register layout convention.
    This is the single authoritative decode entry point.

    Message register values (x2–x5 on ARM64) are validated for bounds and
    read in a single pass via `Array.mapM`. The resulting `msgRegs` array
    has the same length as `layout.msgRegs` (proved by `decodeMsgRegs_length`). -/
@[inline] def decodeSyscallArgs
    (layout : SyscallRegisterLayout)
    (regs : RegisterFile)
    (regCount : Nat := 32) : Except KernelError SyscallDecodeResult := do
  -- Validate register bounds for fixed-position registers
  validateRegBound layout.capPtrReg regCount
  validateRegBound layout.msgInfoReg regCount
  validateRegBound layout.syscallNumReg regCount
  -- Validate and read message registers in a single pass
  let msgRegVals ← layout.msgRegs.mapM fun r => do
    validateRegBound r regCount
    pure (readReg regs r)
  -- Read and decode fixed-position registers
  let capAddr ← decodeCapPtr (readReg regs layout.capPtrReg)
  let msgInfo ← decodeMsgInfo (readReg regs layout.msgInfoReg)
  let syscallId ← decodeSyscallId (readReg regs layout.syscallNumReg)
  pure { capAddr, msgInfo, syscallId, msgRegs := msgRegVals }

-- ============================================================================
-- Round-trip lemmas
-- ============================================================================

/-- Round-trip: encoding then decoding a CPtr recovers the original,
    provided the CPtr value fits in a 64-bit word.

    S4-K: The `isWord64` precondition is required because `decodeCapPtr` now
    rejects out-of-range values. On real ARM64 hardware, all register values
    are inherently 64-bit, so `hBound` is trivially satisfied. -/
theorem decodeCapPtr_roundtrip (c : CPtr) (hBound : isWord64 c.toNat) :
    decodeCapPtr (encodeCapPtr c) = .ok c := by
  unfold decodeCapPtr encodeCapPtr CPtr.toNat at *
  have h64 : isWord64Dec c.val = true := (SeLe4n.isWord64Dec_iff c.val).mpr hBound
  simp [h64, CPtr.ofNat]

/-- Round-trip: encoding then decoding a SyscallId recovers the original. -/
theorem decodeSyscallId_roundtrip (s : SyscallId) :
    decodeSyscallId (encodeSyscallId s) = .ok s := by
  simp [decodeSyscallId, encodeSyscallId]
  rw [SyscallId.ofNat_toNat s]

/-- Round-trip: encoding then decoding a MessageInfo recovers the original,
    provided the fields satisfy seL4 message-info bounds.
    Completes the round-trip proof surface for all three decode components. -/
theorem decodeMsgInfo_roundtrip (mi : MessageInfo)
    (hLen : mi.length ≤ maxMessageRegisters)
    (hCaps : mi.extraCaps ≤ maxExtraCaps)
    (hLabel : mi.label ≤ MessageInfo.maxLabel := by omega) :
    decodeMsgInfo (encodeMsgInfo mi) = .ok mi := by
  simp only [decodeMsgInfo, encodeMsgInfo]
  have h := MessageInfo.encode_decode_roundtrip mi hLen hCaps hLabel
  simp only [h]

/-- Round-trip: encoding then decoding message register values is identity. -/
theorem decodeMsgRegs_roundtrip (vals : Array RegValue) :
    encodeMsgRegs vals = vals := rfl

/-- All four per-component round-trips compose: given a well-formed
    `SyscallDecodeResult`, encoding each field then decoding recovers
    the original. Includes `msgRegs` identity round-trip.
    Stated as individual component equalities that can be composed at the
    call site for any register layout. -/
theorem decode_components_roundtrip (decoded : SyscallDecodeResult)
    (hLen : decoded.msgInfo.length ≤ maxMessageRegisters)
    (hCaps : decoded.msgInfo.extraCaps ≤ maxExtraCaps)
    (hLabel : decoded.msgInfo.label ≤ MessageInfo.maxLabel := by omega)
    (hCapBound : isWord64 decoded.capAddr.toNat) :
    decodeCapPtr (encodeCapPtr decoded.capAddr) = .ok decoded.capAddr ∧
    decodeMsgInfo (encodeMsgInfo decoded.msgInfo) = .ok decoded.msgInfo ∧
    decodeSyscallId (encodeSyscallId decoded.syscallId) = .ok decoded.syscallId ∧
    encodeMsgRegs decoded.msgRegs = decoded.msgRegs :=
  ⟨decodeCapPtr_roundtrip decoded.capAddr hCapBound,
   decodeMsgInfo_roundtrip decoded.msgInfo hLen hCaps hLabel,
   decodeSyscallId_roundtrip decoded.syscallId,
   decodeMsgRegs_roundtrip decoded.msgRegs⟩

-- ============================================================================
-- Message register extraction lemmas
-- ============================================================================

/-- The extracted message register array has at most `maxMessageRegisters`
    entries. This guarantees `IpcMessage.bounded` for the registers component
    when the message is constructed from the extraction result. -/
theorem extractMessageRegisters_length (msgRegs : Array RegValue)
    (info : MessageInfo) :
    (extractMessageRegisters msgRegs info).size ≤ maxMessageRegisters := by
  unfold extractMessageRegisters
  simp [Array.size_extract]
  omega

/-- An IpcMessage constructed from extracted registers with empty caps
    satisfies `IpcMessage.bounded`. -/
theorem extractMessageRegisters_ipc_bounded (msgRegs : Array RegValue)
    (info : MessageInfo) (badge : Option SeLe4n.Badge) :
    IpcMessage.bounded {
      registers := extractMessageRegisters msgRegs info,
      caps := #[],
      badge := badge } := by
  unfold IpcMessage.bounded
  constructor
  · exact extractMessageRegisters_length msgRegs info
  · simp [maxExtraCaps, Array.size]

/-- S4-D: Round-trip — extracting message registers from an array whose size
    matches the message info length recovers the original array, provided the
    size is within bounds. -/
theorem extractMessageRegisters_roundtrip
    (vals : Array RegValue)
    (info : MessageInfo)
    (hLen : info.length = vals.size)
    (hBound : vals.size ≤ maxMessageRegisters) :
    extractMessageRegisters vals info = vals := by
  unfold extractMessageRegisters
  have hCount : min info.length (min maxMessageRegisters vals.size)
      = vals.size := by omega
  ext i
  · simp [Array.size_extract]; omega
  · simp [Array.getElem_extract]

-- ============================================================================
-- Error exclusivity — each error variant maps to exactly one failure mode
-- ============================================================================

/-- If decodeSyscallId fails, the register value was not a valid syscall number. -/
theorem decodeSyscallId_error_iff (rv : RegValue) :
    decodeSyscallId rv = .error .invalidSyscallNumber ↔
    SyscallId.ofNat? rv.val = none := by
  simp [decodeSyscallId]
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp [h]

/-- If decodeMsgInfo fails, the register value had invalid length or extraCaps. -/
theorem decodeMsgInfo_error_iff (rv : RegValue) :
    decodeMsgInfo rv = .error .invalidMessageInfo ↔
    MessageInfo.decode rv.val = none := by
  simp [decodeMsgInfo]
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp [h]

/-- S4-K: decodeCapPtr succeeds iff the register value is word64-bounded. -/
theorem decodeCapPtr_ok_iff (rv : RegValue) :
    (∃ c, decodeCapPtr rv = .ok c) ↔ isWord64Dec rv.val = true := by
  unfold decodeCapPtr
  constructor
  · intro ⟨c, h⟩; split at h <;> simp_all
  · intro h; exact ⟨CPtr.ofNat rv.val, by simp [h]⟩

/-- S4-K: decodeCapPtr succeeds for word64-bounded values. -/
theorem decodeCapPtr_ok_of_word64 (rv : RegValue) (h : isWord64Dec rv.val = true) :
    decodeCapPtr rv = .ok (CPtr.ofNat rv.val) := by
  unfold decodeCapPtr; simp [h]

/-- Register bound validation succeeds iff the index is within bounds. -/
theorem validateRegBound_ok_iff (r : RegName) (bound : Nat) :
    validateRegBound r bound = .ok () ↔ r.val < bound := by
  unfold validateRegBound
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp [h]

/-- Register bound validation fails iff the index is out of bounds. -/
theorem validateRegBound_error_iff (r : RegName) (bound : Nat) :
    validateRegBound r bound = .error .invalidRegister ↔ ¬(r.val < bound) := by
  unfold validateRegBound
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp at h; simp [h]

-- ============================================================================
-- Message register length invariant
-- ============================================================================

/-- Helper: `List.mapM` with `Except` preserves list length on success. -/
private theorem list_mapM_except_length {α β ε : Type}
    (f : α → Except ε β) (xs : List α) (ys : List β)
    (h : List.mapM f xs = Except.ok ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h
    subst h; rfl
  | cons a as ih =>
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i b hb
      split at h
      · simp at h
      · rename_i bs hbs
        simp only [pure, Except.pure] at h
        have hEq : ys = b :: bs := Except.ok.inj h.symm
        rw [hEq, List.length_cons, List.length_cons]
        congr 1
        exact ih bs hbs

/-- Helper: `Array.mapM` with `Except` preserves array size on success.
    Proved via `List.mapM` length preservation and `Array.toList_mapM`. -/
private theorem array_mapM_except_size {α β ε : Type}
    (f : α → Except ε β) (arr : Array α) (result : Array β)
    (h : arr.mapM f = Except.ok result) :
    result.size = arr.size := by
  have hList := Array.toList_mapM (f := f) (xs := arr)
  rw [h] at hList
  simp only [Functor.map, Except.map] at hList
  have hLen := list_mapM_except_length f arr.toList result.toList hList.symm
  rw [Array.size, Array.size]
  exact hLen

/-- When `decodeSyscallArgs` succeeds, the `msgRegs` array in the result has
    the same size as the layout's `msgRegs` array. This guarantees that
    per-syscall decode functions (WS-K-B) can rely on the array length matching
    the platform convention (4 for ARM64). -/
theorem decodeMsgRegs_length
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded : SyscallDecodeResult)
    (hOk : decodeSyscallArgs layout regs regCount = .ok decoded) :
    decoded.msgRegs.size = layout.msgRegs.size := by
  unfold decodeSyscallArgs at hOk
  simp only [bind, Except.bind] at hOk
  -- Each `split at hOk` case-splits on a validateRegBound/mapM/decode result.
  -- The `.error` branch contradicts `hOk = .ok decoded`.
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · rename_i msgRegVals hMapM
          split at hOk
          · simp at hOk
          · split at hOk
            · simp at hOk
            · split at hOk
              · simp at hOk
              · simp only [pure, Except.pure] at hOk
                have hEq := Except.ok.inj hOk
                have hMsgRegs : decoded.msgRegs = msgRegVals :=
                  (congrArg SyscallDecodeResult.msgRegs hEq).symm
                rw [hMsgRegs]
                exact array_mapM_except_size _ _ _ hMapM

end SeLe4n.Kernel.Architecture.RegisterDecode
