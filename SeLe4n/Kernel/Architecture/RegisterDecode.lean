-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.IpcBufferRead

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
  -- AK4-A.2: Populate inlineCount/overflowCount with inline-only accounting.
  -- Legacy register-only decoder — `overflowCount` is always 0; callers that
  -- require IPC-buffer merge must use `decodeSyscallArgsFromState` instead.
  pure { capAddr, msgInfo, syscallId, msgRegs := msgRegVals,
         inlineCount := msgRegVals.size, overflowCount := 0 }

-- ============================================================================
-- AK4-A.3: State-aware decode with IPC-buffer overflow merge (R-ABI-C01)
-- ============================================================================

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- One overflow message word from the caller's IPC buffer, any internal
    error collapsed to `.invalidMessageInfo` (matches seL4 convention). -/
def readOverflowWord (st : SystemState) (tid : ThreadId) (i : Nat) :
    Except KernelError UInt64 :=
  match ipcBufferReadMr st tid i with
  | .ok v => .ok v
  | .error _ => .error .invalidMessageInfo

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- AK4-A.3 (R-ABI-C01 / CRITICAL): Extended decode that merges IPC-buffer
    overflow slots into `msgRegs` for syscalls whose `msgInfo.length >
    inlineCount`.

    **Two-stage pipeline:**
    1. Run `decodeSyscallArgs` to obtain the base result (inline regs only).
    2. If `msgInfo.length > inline.size`, read the remaining overflow slots
       from the caller's IPC buffer and append them to `msgRegs`.

    **Why this exists:** `arm64DefaultLayout.msgRegs` provides 4 inline
    positions (x2..x5). Syscalls with 5+ message registers (e.g.,
    `serviceRegister`, `schedContextConfigure`) encode the overflow into the
    thread's IPC buffer. Without this merge step, the Lean kernel would
    reject every such Rust-encoded syscall — the critical `R-ABI-C01`
    finding.

    **Failure propagation:** Any `IpcBufferReadError` (missing TCB, unmapped
    VAddr, out-of-range index) collapses to `KernelError.invalidMessageInfo`,
    matching seL4 ABI behaviour where the caller sees a single error kind.

    **Purity:** This function is read-only on `SystemState` — only the base
    `decodeSyscallArgs` result and the IPC-buffer word reads are consulted. -/
def decodeSyscallArgsFromState
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : Except KernelError SyscallDecodeResult := do
  let base ← decodeSyscallArgs layout regs regCount
  let inlineSize := base.msgRegs.size
  let totalLen := base.msgInfo.length
  if totalLen ≤ inlineSize then
    -- Short path: `msgInfo.length` fits within inline register count.
    -- Preserve all inline regs (matches ARM64 hardware semantics — x2..x5
    -- are read unconditionally at decode time; `msgInfo.length` only
    -- governs how many registers downstream IPC transfer will propagate).
    -- Per-syscall decoders use `requireMsgReg` for bounds checking.
    pure { base with
             msgRegs       := base.msgRegs,
             inlineCount   := inlineSize,
             overflowCount := 0 }
  else
    -- Merge overflow slots from the caller's IPC buffer.
    let overflowNeeded := totalLen - inlineSize
    let overflowNats ← (List.range overflowNeeded).mapM (readOverflowWord st tid)
    let overflowRegs : Array RegValue :=
      (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
    pure { base with
             msgRegs       := base.msgRegs ++ overflowRegs,
             inlineCount   := inlineSize,
             overflowCount := overflowNeeded }

/-- WS-ZA ZA4.7: **the same two-stage decode, with the overflow read
supplied.**  The reader is the only state the decode consults, so a surface that keeps
the IPC buffer elsewhere (the frozen store) decodes a saved frame through this
with its own reader, and `decodeSyscallArgsFromState_eq_with` pins the live
decode to it. -/
def decodeSyscallArgsWith (readOverflow : Nat → Except KernelError UInt64)
    (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : Except KernelError SyscallDecodeResult := do
  let base ← decodeSyscallArgs layout regs regCount
  let inlineSize := base.msgRegs.size
  let totalLen := base.msgInfo.length
  if totalLen ≤ inlineSize then
    pure { base with
             msgRegs       := base.msgRegs,
             inlineCount   := inlineSize,
             overflowCount := 0 }
  else
    let overflowNeeded := totalLen - inlineSize
    let overflowNats ← (List.range overflowNeeded).mapM readOverflow
    let overflowRegs : Array RegValue :=
      (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
    pure { base with
             msgRegs       := base.msgRegs ++ overflowRegs,
             inlineCount   := inlineSize,
             overflowCount := overflowNeeded }

/-- WS-ZA ZA4.7: the live decode is `decodeSyscallArgsWith` over the live IPC
buffer read. -/
theorem decodeSyscallArgsFromState_eq_with (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat) :
    decodeSyscallArgsFromState st tid layout regs regCount =
      decodeSyscallArgsWith (readOverflowWord st tid) layout regs regCount := rfl

/-- Bound-checking the message registers in one `mapM` pass refuses with
    `.invalidRegister` exactly when some register is out of bounds, and
    otherwise reads them all. -/
theorem listMapM_validateRegBound (rs : List RegName) (regs : RegisterFile)
    (regCount : Nat) :
    rs.mapM (fun r => (do validateRegBound r regCount; pure (readReg regs r) :
        Except KernelError RegValue)) =
      if rs.all (·.val < regCount) then .ok (rs.map (readReg regs))
      else .error .invalidRegister := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.mapM_cons, List.all_cons, List.map_cons]
    rw [ih]
    by_cases h : r.val < regCount
    · simp only [validateRegBound, h, ↓reduceIte, decide_true, Bool.true_and]
      split <;> rfl
    · simp [validateRegBound, h, bind, Except.bind]

/-- `listMapM_validateRegBound` over an array. -/
theorem arrayMapM_validateRegBound (rs : Array RegName) (regs : RegisterFile)
    (regCount : Nat) :
    rs.mapM (fun r => (do validateRegBound r regCount; pure (readReg regs r) :
        Except KernelError RegValue)) =
      if rs.all (·.val < regCount) then .ok (rs.map (readReg regs))
      else .error .invalidRegister := by
  rcases rs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList]
  have hAll : (Array.mk l).all (·.val < regCount) = l.all (·.val < regCount) :=
    List.all_toArray ..
  rw [hAll, listMapM_validateRegBound]
  split <;> simp [Functor.map, Except.map]

/-- `decodeSyscallArgsFromState`'s overflow merge, from the inline decode. -/
def mergeOverflowWords (st : SystemState) (tid : ThreadId)
    (base : SyscallDecodeResult) : Except KernelError SyscallDecodeResult := do
  let inlineSize := base.msgRegs.size
  let overflowNeeded := base.msgInfo.length - inlineSize
  let overflowNats ← (List.range overflowNeeded).mapM (readOverflowWord st tid)
  let overflowRegs : Array RegValue :=
    (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
  pure { base with
           msgRegs       := base.msgRegs ++ overflowRegs,
           inlineCount   := inlineSize,
           overflowCount := overflowNeeded }

/-- `decodeSyscallArgsFromState`, building nothing a caller does not use.  The
    register bounds are one test rather than a `mapM` pass that copies the
    layout's register array, and the result is inlined, so a caller that reads
    only some fields of the decode (the signal reads the operand, the syscall
    number and the message length) builds neither the record nor the message
    array (WS-ZA).  Proven equal by `decodeSyscallArgsFromState_eq_impl`. -/
@[inline] def decodeSyscallArgsFromStateImpl
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : Except KernelError SyscallDecodeResult :=
  if layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true then
    match decodeCapPtr (readReg regs layout.capPtrReg) with
    | .error e => .error e
    | .ok capAddr =>
    match decodeMsgInfo (readReg regs layout.msgInfoReg) with
    | .error e => .error e
    | .ok msgInfo =>
    match decodeSyscallId (readReg regs layout.syscallNumReg) with
    | .error e => .error e
    | .ok syscallId =>
      let base : SyscallDecodeResult :=
        { capAddr, msgInfo, syscallId, msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 }
      if msgInfo.length ≤ layout.msgRegs.size then .ok base
      else mergeOverflowWords st tid base
  else .error .invalidRegister

@[csimp] theorem decodeSyscallArgsFromState_eq_impl :
    @decodeSyscallArgsFromState = @decodeSyscallArgsFromStateImpl := by
  funext st tid layout regs regCount
  simp only [decodeSyscallArgsFromState, decodeSyscallArgsFromStateImpl, decodeSyscallArgs,
    arrayMapM_validateRegBound]
  by_cases h1 : layout.capPtrReg.val < regCount <;>
  by_cases h2 : layout.msgInfoReg.val < regCount <;>
  by_cases h3 : layout.syscallNumReg.val < regCount <;>
  by_cases h4 : layout.msgRegs.all (·.val < regCount) = true <;>
  simp only [validateRegBound, h1, h2, h3, h4, ↓reduceIte, and_self, and_true,
    and_false, bind, Except.bind, pure, Except.pure, Bool.false_eq_true] <;>
  try rfl
  rcases decodeCapPtr (readReg regs layout.capPtrReg) with e | capAddr
  · rfl
  rcases decodeMsgInfo (readReg regs layout.msgInfoReg) with e | msgInfo
  · rfl
  rcases decodeSyscallId (readReg regs layout.syscallNumReg) with e | syscallId
  · rfl
  simp only [Array.size_map]
  split
  · rfl
  · simp only [mergeOverflowWords, Array.size_map, bind, Except.bind, pure, Except.pure]

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
  have h64 : isWord64Dec c.toNat = true := (SeLe4n.isWord64Dec_iff c.toNat).mpr hBound
  unfold decodeCapPtr encodeCapPtr
  simp only [h64, if_true, CPtr.ofNat_toNat]

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

/-- All three per-component round-trips compose: given a well-formed
    `SyscallDecodeResult`, encoding each field then decoding recovers
    the original. Message registers need no round-trip (identity in the
    abstract model). -/
theorem decode_components_roundtrip (decoded : SyscallDecodeResult)
    (hLen : decoded.msgInfo.length ≤ maxMessageRegisters)
    (hCaps : decoded.msgInfo.extraCaps ≤ maxExtraCaps)
    (hLabel : decoded.msgInfo.label ≤ MessageInfo.maxLabel := by omega)
    (hCapBound : isWord64 decoded.capAddr.toNat) :
    decodeCapPtr (encodeCapPtr decoded.capAddr) = .ok decoded.capAddr ∧
    decodeMsgInfo (encodeMsgInfo decoded.msgInfo) = .ok decoded.msgInfo ∧
    decodeSyscallId (encodeSyscallId decoded.syscallId) = .ok decoded.syscallId :=
  ⟨decodeCapPtr_roundtrip decoded.capAddr hCapBound,
   decodeMsgInfo_roundtrip decoded.msgInfo hLen hCaps hLabel,
   decodeSyscallId_roundtrip decoded.syscallId⟩

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

/-- An IpcMessage constructed from extracted registers satisfies
    `IpcMessage.bounded`. -/
theorem extractMessageRegisters_ipc_bounded (msgRegs : Array RegValue)
    (info : MessageInfo) (badge : Option SeLe4n.Badge) :
    IpcMessage.bounded {
      registers := extractMessageRegisters msgRegs info,
      badge := badge } :=
  extractMessageRegisters_length msgRegs info

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

-- ============================================================================
-- AK4-A.4 / AK4-A.5: State-aware decode correctness + NI properties
-- ============================================================================

/-- AK4-A.4: The failure-to-decode-base predicate — if the legacy register-only
    `decodeSyscallArgs` fails, the state-aware wrapper propagates the same
    error (IPC-buffer merge is never attempted before base decode succeeds). -/
theorem decodeSyscallArgsFromState_base_error_propagates
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (e : KernelError)
    (hErr : decodeSyscallArgs layout regs regCount = .error e) :
    decodeSyscallArgsFromState st tid layout regs regCount = .error e := by
  unfold decodeSyscallArgsFromState
  simp [bind, Except.bind, hErr]

/-- AK4-A.4: Success implies base decode succeeded. The merge wrapper does
    not create `ok` results from `error` bases. -/
theorem decodeSyscallArgsFromState_ok_implies_base_ok
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded : SyscallDecodeResult)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    ∃ base, decodeSyscallArgs layout regs regCount = .ok base := by
  unfold decodeSyscallArgsFromState at hOk
  simp only [bind, Except.bind] at hOk
  cases hBase : decodeSyscallArgs layout regs regCount with
  | error e => rw [hBase] at hOk; simp at hOk
  | ok base => exact ⟨base, rfl⟩

/-- AK4-A.4: Every successful state-aware decode preserves `capAddr`,
    `msgInfo`, and `syscallId` from the base decode. The merge stage only
    extends `msgRegs` and sets the count fields; the authoritative
    register-word fields remain untouched. -/
theorem decodeSyscallArgsFromState_header_preserved
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded base : SyscallDecodeResult)
    (hBase : decodeSyscallArgs layout regs regCount = .ok base)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    decoded.capAddr = base.capAddr ∧
    decoded.msgInfo = base.msgInfo ∧
    decoded.syscallId = base.syscallId := by
  unfold decodeSyscallArgsFromState at hOk
  rw [hBase] at hOk
  simp only [bind, Except.bind] at hOk
  split at hOk
  · simp only [pure, Except.pure, Except.ok.injEq] at hOk
    refine ⟨?_, ?_, ?_⟩ <;> (rw [← hOk])
  · split at hOk
    · simp at hOk
    · simp only [pure, Except.pure, Except.ok.injEq] at hOk
      refine ⟨?_, ?_, ?_⟩ <;> (rw [← hOk])

/-- AK4-A.4: `capAddr` is preserved through IPC-buffer merge. -/
theorem decodeSyscallArgsFromState_capAddr_eq
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded base : SyscallDecodeResult)
    (hBase : decodeSyscallArgs layout regs regCount = .ok base)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    decoded.capAddr = base.capAddr :=
  (decodeSyscallArgsFromState_header_preserved
    st tid layout regs regCount decoded base hBase hOk).1

/-- AK4-A.4: `msgInfo` is preserved through IPC-buffer merge. -/
theorem decodeSyscallArgsFromState_msgInfo_eq
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded base : SyscallDecodeResult)
    (hBase : decodeSyscallArgs layout regs regCount = .ok base)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    decoded.msgInfo = base.msgInfo :=
  (decodeSyscallArgsFromState_header_preserved
    st tid layout regs regCount decoded base hBase hOk).2.1

/-- AK4-A.4: `syscallId` is preserved through IPC-buffer merge. -/
theorem decodeSyscallArgsFromState_syscallId_eq
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded base : SyscallDecodeResult)
    (hBase : decodeSyscallArgs layout regs regCount = .ok base)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    decoded.syscallId = base.syscallId :=
  (decodeSyscallArgsFromState_header_preserved
    st tid layout regs regCount decoded base hBase hOk).2.2

/-- AK4-A.5 (NI): The decode wrapper's read scope on `SystemState` is
    exclusively what `ipcBufferReadMr` consults for each `tid`. If two
    states agree on the caller's TCB (via `tid.toObjId`), the caller's
    VSpaceRoot object, the full memory function and the synced words, the decode result
    is identical.

    This is the top-level NI witness for Phase AK4 — it lifts the
    `ipcBufferReadMr_reads_only_caller_tcb` witness from `IpcBufferRead.lean`
    to the decode wrapper consumed by `syscallEntry` /
    `syscallEntryChecked`. Together with the fact that `decodeSyscallArgs`
    depends only on `regs`, this proves the decode path has no
    cross-domain channel beyond the caller's own thread state. -/
theorem decodeSyscallArgsFromState_reads_only_caller
    (st st' : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (hTcb  : st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?)
    (hVs   : ∀ vs : SeLe4n.ObjId,
              (st.objects[tid.toObjId]?).bind
                 (fun o => match o with | .tcb t => some t.vspaceRoot | _ => none)
                 = some vs →
              st'.objects[vs]? = st.objects[vs]?)
    (hMem  : st'.machine.memory = st.machine.memory)
    (hBytes : st'.machine.entryWordBytes = st.machine.entryWordBytes)
    (hCount : st'.machine.entryWordCount = st.machine.entryWordCount) :
    decodeSyscallArgsFromState st' tid layout regs regCount
      = decodeSyscallArgsFromState st tid layout regs regCount := by
  -- The only places where `decodeSyscallArgsFromState` reads `SystemState`
  -- are via `ipcBufferReadMr st tid i` calls inside the overflow branch.
  -- Rewriting each such call to use `st` instead of `st'` makes the two
  -- expressions definitionally equal.
  have hRead : ∀ i,
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st' tid i
        = SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid i := by
    intro i
    exact SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr_reads_only_caller_tcb
            st st' tid i hTcb hVs hMem hBytes hCount
  have hWord : readOverflowWord st' tid = readOverflowWord st tid := by
    funext i; simp only [readOverflowWord, hRead]
  unfold decodeSyscallArgsFromState
  simp only [hWord]

/-- AK4-A.4: Size invariant — `msgRegs.size = inlineCount + overflowCount`
    on any successful state-aware decode. This is the downstream contract
    required by per-syscall argument decoders using `requireMsgReg`. -/
theorem decodeSyscallArgsFromState_size_invariant
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded : SyscallDecodeResult)
    (hOk : decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded) :
    decoded.msgRegs.size = decoded.inlineCount + decoded.overflowCount := by
  unfold decodeSyscallArgsFromState at hOk
  cases hBase : decodeSyscallArgs layout regs regCount with
  | error e => rw [hBase] at hOk; simp [bind, Except.bind] at hOk
  | ok base =>
    rw [hBase] at hOk
    simp only [bind, Except.bind] at hOk
    split at hOk
    · -- Short path
      simp only [pure, Except.pure, Except.ok.injEq] at hOk
      have h1 : decoded.msgRegs.size = base.msgRegs.size := by rw [← hOk]
      have h2 : decoded.inlineCount = base.msgRegs.size := by rw [← hOk]
      have h3 : decoded.overflowCount = 0 := by rw [← hOk]
      rw [h1, h2, h3]; omega
    · -- Overflow path
      split at hOk
      · simp at hOk
      · rename_i overflowNats hOverflowOk
        simp only [pure, Except.pure, Except.ok.injEq] at hOk
        have hMapLen : overflowNats.length
            = base.msgInfo.length - base.msgRegs.size := by
          have h := list_mapM_except_length _ _ _ hOverflowOk
          simpa [List.length_range] using h
        have hSize : decoded.msgRegs.size
            = base.msgRegs.size + overflowNats.length := by
          rw [← hOk]
          simp [Array.size_append, List.size_toArray, List.length_map]
        have hInline : decoded.inlineCount = base.msgRegs.size := by rw [← hOk]
        have hOver : decoded.overflowCount
            = base.msgInfo.length - base.msgRegs.size := by rw [← hOk]
        rw [hSize, hInline, hOver, hMapLen]


/-- The syscalls the entry routes on the register file itself, before any
    decode record or message array exists, with the operands each reads
    there.  Every other call goes through the decode (`viaDecode`). -/
inductive RegisterRoutedSyscall where
  /-- A signal: its operand address and the badge in the first message
      register. -/
  | signal (capAddr : CPtr) (badge : Badge)
  /-- A wait: its operand address. -/
  | wait (capAddr : CPtr)
  /-- WS-ZA ZA4.3: a yield, which reads no operand. -/
  | yield
  /-- WS-ZA ZA4.7: a send with no capabilities to transfer and no overflow
      words: its operand address and its message info; the words are the
      inline message registers. -/
  | send (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- WS-ZA ZA4.7: a call with no capabilities to transfer and no overflow
      words: its operand address and its message info; the words are the
      inline message registers. -/
  | call (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- WS-ZA ZA4.7: a reply with no overflow words: its operand address and
      its message info; the words are the inline message registers. -/
  | reply (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- WS-ZA ZA4.7: a receive: its operand address, its message length and,
      when the length is nonzero, the first message register (the reply
      object's capability address), read as the decode reads it but as the
      word (WS-ZA ZA4.8), so an address `≥ 2^63` builds no heap number. -/
  | receive (capAddr : CPtr) (len : Nat) (replyAddr : CPtr)
  /-- WS-ZA ZA4.7: a reply-receive with no overflow words: its endpoint
      capability's address and its message info; the reply capability's
      address is the first message register and the reply's words the rest. -/
  | replyRecv (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- WS-ZA ZA5.1: a capability invocation the IPC forms do not route
      (`routedInvocation`), with no overflow words: the syscall and its
      operand address; its arguments are the layout's message registers. -/
  | invoke (sid : SyscallId) (capAddr : CPtr)
  /-- WS-ZA ZA5.2, ZA5.5: a capability invocation with exactly one overflow
      word (`routedOverflowOne`: the scheduling-context configure, whose fifth
      argument is the domain, and the service register, whose fifth is whether
      the interface needs the grant right): the syscall and its operand
      address; its first four arguments are the layout's message registers and
      the fifth is overflow slot 0 of the caller's IPC buffer. -/
  | overflowOne (sid : SyscallId) (capAddr : CPtr)
  /-- WS-ZA ZA5.13: a declassification or an audit call (`routedAudited`) with
      no overflow words: the syscall and its operand address; its arguments
      are the layout's message registers. -/
  | audited (sid : SyscallId) (capAddr : CPtr)
  | viaDecode

/-- WS-ZA ZA5.1: the capability invocations the register file routes as
`invoke`: every invocation whose arguments fit the layout's message registers,
whose taint step is the identity and whose rights are checked in the classic
order.  The scheduling-context configure and the service register carry one
argument word more and are routed as `overflowOne` (`routedOverflowOne`); the
declassification and audit calls, whose taint steps are not the identity or
whose targets are checked first, are routed as `audited` (`routedAudited`). -/
def routedInvocation : SyscallId → Bool
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .mintReplyCap | .untypedRetype | .untypedReset
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRevoke | .serviceQuery | .schedContextBind | .schedContextUnbind | .schedContextConsumed
  | .tcbBindNotification | .tcbUnbindNotification | .tcbSuspend | .tcbResume
  | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer | .tcbSetAffinity
  | .tcbSetFaultHandler | .tcbSetSpace | .pageTableMap | .pageTableUnmap => true
  | _ => false

/-- The routed invocation syscall number `n` names, if any. -/
@[inline] def routedInvocationSid? (n : Nat) : Option SyscallId :=
  match SyscallId.ofNat? n with
  | some sid => if routedInvocation sid then some sid else none
  | none => none

theorem routedInvocationSid?_some {n : Nat} {sid : SyscallId}
    (h : routedInvocationSid? n = some sid) :
    routedInvocation sid = true ∧ n = sid.toNat := by
  unfold routedInvocationSid? at h
  split at h
  · next sid' hOf =>
    split at h
    · next hR =>
      cases h
      exact ⟨hR, (SyscallId.toNat_ofNat hOf).symm⟩
    · cases h
  · cases h

/-- WS-ZA ZA5.2, ZA5.5: the capability invocations the register file routes as
`overflowOne`: those whose arguments are the layout's message registers and one
overflow word, whose taint step is the identity and whose rights are checked in
the classic order. -/
def routedOverflowOne : SyscallId → Bool
  | .schedContextConfigure | .serviceRegister => true
  | _ => false

/-- The one-overflow-word invocation syscall number `n` names, if any. -/
@[inline] def routedOverflowOneSid? (n : Nat) : Option SyscallId :=
  match SyscallId.ofNat? n with
  | some sid => if routedOverflowOne sid then some sid else none
  | none => none

theorem routedOverflowOneSid?_some {n : Nat} {sid : SyscallId}
    (h : routedOverflowOneSid? n = some sid) :
    routedOverflowOne sid = true ∧ n = sid.toNat := by
  unfold routedOverflowOneSid? at h
  split at h
  · next sid' hOf =>
    split at h
    · next hR =>
      cases h
      exact ⟨hR, (SyscallId.toNat_ofNat hOf).symm⟩
    · cases h
  · cases h

/-- WS-ZA ZA5.13: the calls the register file routes as `audited`: the two
declassifications, which record into the audit trail and carry a taint step,
and the audit read and drain, which check their target before their right. -/
def routedAudited : SyscallId → Bool
  | .declassify | .declassifySignal | .auditRead | .auditDrain => true
  | _ => false

/-- The audited syscall number `n` names, if any. -/
@[inline] def routedAuditedSid? (n : Nat) : Option SyscallId :=
  match SyscallId.ofNat? n with
  | some sid => if routedAudited sid then some sid else none
  | none => none

theorem routedAuditedSid?_some {n : Nat} {sid : SyscallId}
    (h : routedAuditedSid? n = some sid) :
    routedAudited sid = true ∧ n = sid.toNat := by
  unfold routedAuditedSid? at h
  split at h
  · next sid' hOf =>
    split at h
    · next hR =>
      cases h
      exact ⟨hR, (SyscallId.toNat_ofNat hOf).symm⟩
    · cases h
  · cases h

/-- WS-ZA ZA4.8: a register's capability address always decodes, to the
address its word names — read as the word, an address `≥ 2^63` builds no
heap number. -/
theorem decodeCapPtr_readReg (rf : RegisterFile) (r : RegName) :
    decodeCapPtr (readReg rf r) = .ok (CPtr.ofWord (readRegWord rf r)) := by
  have hLt : (readRegWord rf r).toNat < machineWordMax := by
    unfold machineWordMax machineWordBits
    exact (readRegWord rf r).toNat_lt
  unfold decodeCapPtr
  rw [readReg_val_eq_word, if_pos (by simpa [isWord64Dec] using hLt), CPtr.ofWord_eq_ofNat]

/-- The routed syscall a register file names, read straight from the
    registers: `signal`/`wait` only when the decode succeeds as that syscall
    with no overflow words merged, and carries the same operands
    (`decodeSyscallArgsFromState_of_routedSignal`,
    `decodeSyscallArgsFromState_of_routedWait`).  Inlined and matched at once,
    it builds nothing. -/
@[inline] def registerRoutedSyscall (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : RegisterRoutedSyscall :=
  if layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true then
    let capAddr := CPtr.ofWord (readRegWord regs layout.capPtrReg)
    match decodeMsgInfo (readReg regs layout.msgInfoReg) with
    | .error _ => .viaDecode
    | .ok msgInfo =>
      if msgInfo.length ≤ layout.msgRegs.size then
        if (readReg regs layout.syscallNumReg).val = SyscallId.notificationSignal.toNat then
          if h0 : 0 < layout.msgRegs.size then
            .signal capAddr (Badge.ofWord (readRegWord regs layout.msgRegs[0]))
          else .viaDecode
        else if (readReg regs layout.syscallNumReg).val = SyscallId.notificationWait.toNat then
          .wait capAddr
        else if (readReg regs layout.syscallNumReg).val = SyscallId.yield.toNat then
          .yield
        else if (readReg regs layout.syscallNumReg).val = SyscallId.send.toNat ∧
            msgInfo.extraCaps = 0 then
          .send capAddr msgInfo
        else if (readReg regs layout.syscallNumReg).val = SyscallId.call.toNat ∧
            msgInfo.extraCaps = 0 then
          .call capAddr msgInfo
        else if (readReg regs layout.syscallNumReg).val = SyscallId.reply.toNat then
          .reply capAddr msgInfo
        else if (readReg regs layout.syscallNumReg).val = SyscallId.receive.toNat then
          if h0 : 0 < layout.msgRegs.size then
            .receive capAddr msgInfo.length (CPtr.ofWord (readRegWord regs layout.msgRegs[0]))
          else .receive capAddr msgInfo.length (CPtr.ofWord 0)
        else if (readReg regs layout.syscallNumReg).val = SyscallId.replyRecv.toNat then
          .replyRecv capAddr msgInfo
        else
          match routedInvocationSid? (readReg regs layout.syscallNumReg).val with
          | some sid => .invoke sid capAddr
          | none =>
            match routedAuditedSid? (readReg regs layout.syscallNumReg).val with
            | some sid => .audited sid capAddr
            | none => .viaDecode
      else if msgInfo.length = layout.msgRegs.size + 1 then
        match routedOverflowOneSid? (readReg regs layout.syscallNumReg).val with
        | some sid => .overflowOne sid capAddr
        | none => .viaDecode
      else .viaDecode
  else .viaDecode

/-- What a routed read pins about the decode: it succeeds, as `sid`, at
    `capAddr`, with no overflow words; the decoded registers are the mapped
    layout registers. -/
private theorem decodeSyscallArgsFromState_of_routed
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hC : decodeCapPtr (readReg regs layout.capPtrReg) = .ok capAddr)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hLen : msgInfo.length ≤ layout.msgRegs.size)
    (hS : (readReg regs layout.syscallNumReg).val = sid.toNat) :
    decodeSyscallArgsFromState st tid layout regs regCount =
      .ok { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  rw [decodeSyscallArgsFromState_eq_impl]
  unfold decodeSyscallArgsFromStateImpl
  rw [if_pos hB]
  have hId : decodeSyscallId (readReg regs layout.syscallNumReg) = .ok sid := by
    simp only [decodeSyscallId, hS, SyscallId.ofNat_toNat]
  simp only [hC, hM, hId, hLen, ↓reduceIte]

theorem decodeSyscallArgsFromState_of_routedSignal
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (badge : Badge)
    (h : registerRoutedSyscall layout regs regCount = .signal capAddr badge) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationSignal ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      ∃ h0 : 0 < decoded.msgRegs.size,
        badge = Badge.ofNatMasked (decoded.msgRegs[0]'h0).val := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      refine ⟨_, hD .notificationSignal ‹_›, rfl, rfl, rfl,
        by simpa only [Array.size_map] using ‹0 < layout.msgRegs.size›,
        by simp only [Array.getElem_map, readReg_val_eq_word, Badge.ofWord_eq_ofNatMasked]⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

theorem decodeSyscallArgsFromState_of_routedWait
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .wait capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationWait ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .notificationWait ‹_›, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.3: what a routed yield pins about the decode — it succeeds, as
`.yield`, with no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedYield
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (h : registerRoutedSyscall layout regs regCount = .yield) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .yield ∧ decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      exact ⟨_, hD .yield ‹_›, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed send pins about the decode — it succeeds, as
`.send`, at `capAddr`, with `msgInfo`, no overflow words and no extra
capabilities; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedSend
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .send capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .send ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .send ‹_ = SyscallId.send.toNat ∧ _›.1, rfl, rfl, rfl, rfl,
        ‹_ = SyscallId.send.toNat ∧ _›.2, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed call pins about the decode — it succeeds, as
`.call`, at `capAddr`, with the routed message info, no capabilities and no
overflow words; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedCall
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .call capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .call ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .call ‹_ = SyscallId.call.toNat ∧ _›.1, rfl, rfl, rfl, rfl,
        ‹_ = SyscallId.call.toNat ∧ _›.2, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed reply pins about the decode — it succeeds, as
`.reply`, at `capAddr`, with no overflow words, its message info `msgInfo` and
its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReply
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .reply capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .reply ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .reply ‹_ = SyscallId.reply.toNat›, rfl, rfl, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed receive pins about the decode — it succeeds, as
`.receive`, at `capAddr`, with message length 0 and no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedReceive
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (len : Nat) (replyAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .receive capAddr len replyAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .receive ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo.length = len ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      (len ≠ 0 → decoded.msgRegs[0]? = some ⟨replyAddr.toNat⟩) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      all_goals
        cases h
        refine ⟨_, hD .receive ‹_›, rfl, rfl, rfl, rfl, rfl, fun hN => ?_⟩
      · simp only [Array.getElem?_map, Array.getElem?_eq_getElem ‹0 < layout.msgRegs.size›,
          Option.map_some, CPtr.ofWord_toNat, ← readReg_val_eq_word]
      · exact absurd (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hN) hLen) ‹¬0 < layout.msgRegs.size›
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed reply-receive pins about the decode — it
succeeds, as `.replyRecv`, at `capAddr`, with no overflow words, its message
info `msgInfo` and its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReplyRecv
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .replyRecv capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .replyRecv ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .replyRecv ‹_ = SyscallId.replyRecv.toNat›, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.1: what a routed invocation pins about the decode: it succeeds,
as `sid`, a routed invocation, at `capAddr`, with no overflow words, its words
the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedInvoke
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .invoke sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedInvocation sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      next sid' hSid =>
        cases h
        obtain ⟨hR, hN⟩ := routedInvocationSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.13: what a routed declassification or audit call pins about the
decode: it succeeds, as `sid`, one of `routedAudited`, at `capAddr`, with no
overflow words, its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedAudited
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .audited sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedAudited sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      next sid' hSid =>
        cases h
        obtain ⟨hR, hN⟩ := routedAuditedSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.2, ZA5.5: what a routed one-overflow-word invocation pins about
the decode: as `sid`, one of `routedOverflowOne`, at `capAddr`, with one
overflow word, its words the layout's message registers and then overflow slot
0; it refuses exactly when that slot's read does. -/
theorem decodeSyscallArgsFromState_of_routedOverflowOne
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .overflowOne sid capAddr) :
    routedOverflowOne sid = true ∧
    ∃ msgInfo, decodeSyscallArgsFromState st tid layout regs regCount =
      match readOverflowWord st tid 0 with
      | .error e => .error e
      | .ok w => .ok { capAddr, msgInfo, syscallId := sid,
                       msgRegs := layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)],
                       inlineCount := layout.msgRegs.size, overflowCount := 1 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · repeat' (first | (cases h; done) | split at h)
    · next hLen =>
      split at h
      · next hLen1 =>
        split at h
        · next sid' hSid =>
          cases h
          obtain ⟨hR, hN⟩ := routedOverflowOneSid?_some hSid
          refine ⟨hR, mi, ?_⟩
          rw [decodeSyscallArgsFromState_eq_impl]
          unfold decodeSyscallArgsFromStateImpl
          rw [if_pos hB]
          have hId : decodeSyscallId (readReg regs layout.syscallNumReg) = .ok sid := by
            simp only [decodeSyscallId, hN, SyscallId.ofNat_toNat]
          simp only [hC, hM, hId, hLen1, Nat.not_succ_le_self, ↓reduceIte, mergeOverflowWords,
            Array.size_map, Nat.add_sub_cancel_left, List.range_one, List.mapM_cons,
            List.mapM_nil, bind, Except.bind, pure, Except.pure]
          cases readOverflowWord st tid 0 <;> rfl
        · cases h
      · cases h
  · cases h

end SeLe4n.Kernel.Architecture.RegisterDecode
