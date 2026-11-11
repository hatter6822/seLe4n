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
import SeLe4n.Kernel.Architecture.SyscallArgDecode

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
open SeLe4n.Kernel.Architecture.SyscallArgDecode (truncationMinimum)

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

/-- `decodeMsgInfo` read off the register's machine word: the fields are word
    operations, each small enough to be a scalar, so a word `≥ 2^63` builds no
    heap number (`decodeMsgInfoWord_eq`). -/
@[inline] def decodeMsgInfoWord (w : UInt64) : Except KernelError MessageInfo :=
  if (w &&& 0x7F) ≤ 120 && ((w >>> 7) &&& 3) ≤ 3 && (w >>> 12) ≤ 0xFFFFFFFFFFFFF then
    .ok { length := (w &&& 0x7F).toNat, extraCaps := ((w >>> 7) &&& 3).toNat,
          label := (w >>> 12).toNat, capsUnwrapped := ((w >>> 9) &&& 7).toNat }
  else .error .invalidMessageInfo

theorem decodeMsgInfoWord_eq (w : UInt64) :
    decodeMsgInfoWord w = decodeMsgInfo ⟨w.toNat⟩ := by
  unfold decodeMsgInfoWord decodeMsgInfo MessageInfo.decode
  have h1 : (w &&& 0x7F).toNat = w.toNat &&& 0x7F := by simp [UInt64.toNat_and]
  have h2 : ((w >>> 7) &&& 3).toNat = (w.toNat >>> 7) &&& 0x3 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h3 : (w >>> 12).toNat = w.toNat >>> 12 := by simp [UInt64.toNat_shiftRight]
  have h4 : ((w >>> 9) &&& 7).toNat = (w.toNat >>> 9) &&& 0x7 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight]
  simp only [UInt64.le_iff_toNat_le, h1, h2, h3, h4]
  simp only [maxMessageRegisters, Model.maxExtraCaps, MessageInfo.maxLabel]
  by_cases hc : ((w.toNat &&& 127 ≤ 120 ∧ w.toNat >>> 7 &&& 3 ≤ 3) ∧ w.toNat >>> 12 ≤ 4503599627370495)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    simp [hc]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    simp [hc]

/-- A register's message info, decoded off its word, is its decode. -/
theorem decodeMsgInfoWord_readReg (rf : RegisterFile) (r : RegName) :
    decodeMsgInfoWord (readRegWord rf r) = decodeMsgInfo (readReg rf r) := by
  rw [decodeMsgInfoWord_eq]
  congr 1
  cases h : readReg rf r with
  | mk v =>
    have := readReg_val_eq_word rf r
    rw [h] at this
    simp only at this
    rw [this]

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

/-- **Whether a syscall reads the message words past the inline registers.**
seL4 reads a word of the caller's IPC buffer only where a transfer copies it
(`copyMRs`, for the send, the call, the reply and the reply-receive's reply)
or a decoder reads an argument past the registers (`getSyscallArg`); the
model's decoders read at most four words except the scheduling-context
configure's and the service register's five (`truncationMinimum`).  Every
other syscall reads none: the receive, the wait and the yield read no message
(`handleRecv`, `handleYield`), the signal and the declassified signal take the
capability's badge, and every other invocation's arguments are its registers.
A long message-info word on one of those reads no IPC-buffer word and cannot be
refused or clamped by the buffer.  No wildcard: a new syscall states its
answer. -/
def syscallReadsOverflow : SyscallId → Bool
  | .send | .call | .reply | .replyRecv | .schedContextConfigure | .serviceRegister => true
  | .notificationSignal | .declassifySignal | .receive | .notificationWait | .yield
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke | .untypedRetype
  | .untypedReset | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction | .declassify
  | .auditRead | .auditDrain | .serviceRevoke | .serviceQuery | .schedContextBind
  | .schedContextUnbind | .tcbSuspend | .tcbResume | .tcbSetPriority | .tcbSetMCPriority
  | .tcbSetIPCBuffer | .tcbSetAffinity | .tcbSetFaultHandler | .tcbSetSpace | .pageTableMap
  | .pageTableUnmap | .schedContextConsumed | .schedContextYieldTo | .irqHandlerAck
  | .irqControlGet | .irqHandlerSetNotification | .irqHandlerClear | .tcbBindNotification
  | .tcbUnbindNotification | .mintReplyCap => false

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
  else if syscallReadsOverflow base.syscallId then
    -- Merge overflow slots from the caller's IPC buffer.
    let overflowNeeded := totalLen - inlineSize
    let overflowNats ← (List.range overflowNeeded).mapM (readOverflowWord st tid)
    let overflowRegs : Array RegValue :=
      (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
    pure { base with
             msgRegs       := base.msgRegs ++ overflowRegs,
             inlineCount   := inlineSize,
             overflowCount := overflowNeeded }
  else
    -- A syscall that reads no word past the inline registers (the signals,
    -- `syscallReadsOverflow`) reads none from the IPC buffer, however long
    -- its message-info word says the message is.
    pure { base with
             msgRegs       := base.msgRegs,
             inlineCount   := inlineSize,
             overflowCount := 0 }

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
  else if syscallReadsOverflow base.syscallId then
    let overflowNeeded := totalLen - inlineSize
    let overflowNats ← (List.range overflowNeeded).mapM readOverflow
    let overflowRegs : Array RegValue :=
      (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
    pure { base with
             msgRegs       := base.msgRegs ++ overflowRegs,
             inlineCount   := inlineSize,
             overflowCount := overflowNeeded }
  else
    pure { base with
             msgRegs       := base.msgRegs,
             inlineCount   := inlineSize,
             overflowCount := 0 }

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

/-- `decodeSyscallArgsFromState`'s overflow merge, from the inline decode: the
words past the inline registers, for a syscall that reads them
(`syscallReadsOverflow`); none, for one that does not. -/
def mergeOverflowWords (st : SystemState) (tid : ThreadId)
    (base : SyscallDecodeResult) : Except KernelError SyscallDecodeResult :=
  if syscallReadsOverflow base.syscallId then do
    let inlineSize := base.msgRegs.size
    let overflowNeeded := base.msgInfo.length - inlineSize
    let overflowNats ← (List.range overflowNeeded).mapM (readOverflowWord st tid)
    let overflowRegs : Array RegValue :=
      (overflowNats.map (fun w => (⟨w.toNat⟩ : RegValue))).toArray
    pure { base with
             msgRegs       := base.msgRegs ++ overflowRegs,
             inlineCount   := inlineSize,
             overflowCount := overflowNeeded }
  else
    pure { base with
             msgRegs       := base.msgRegs,
             inlineCount   := base.msgRegs.size,
             overflowCount := 0 }

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

/-- `decodeSyscallArgsFromState`, building nothing a caller does not use.  The
    register bounds are one test rather than a `mapM` pass that copies the
    layout's register array, and the result is inlined, so a caller that reads
    only some fields of the decode (the signal reads the operand, the syscall
    number and the message length) builds neither the record nor the message
    array (WS-ZA).  The capability address is read as its register's word
    (`decodeCapPtr_readReg`), so an address `≥ 2^63` builds no heap number.
    Proven equal by `decodeSyscallArgsFromState_eq_impl`. -/
@[inline] def decodeSyscallArgsFromStateImpl
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : Except KernelError SyscallDecodeResult :=
  if layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true then
    let capAddr := CPtr.ofWord (readRegWord regs layout.capPtrReg)
    match decodeMsgInfoWord (readRegWord regs layout.msgInfoReg) with
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
  rw [decodeCapPtr_readReg, decodeMsgInfoWord_readReg]
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
    (hLabel : mi.label ≤ MessageInfo.maxLabel := by omega)
    (hUnw : mi.capsUnwrapped ≤ MessageInfo.maxCapsUnwrapped := by omega) :
    decodeMsgInfo (encodeMsgInfo mi) = .ok mi := by
  simp only [decodeMsgInfo, encodeMsgInfo]
  have h := MessageInfo.encode_decode_roundtrip mi hLen hCaps hLabel hUnw
  simp only [h]

/-- All three per-component round-trips compose: given a well-formed
    `SyscallDecodeResult`, encoding each field then decoding recovers
    the original. Message registers need no round-trip (identity in the
    abstract model). -/
theorem decode_components_roundtrip (decoded : SyscallDecodeResult)
    (hLen : decoded.msgInfo.length ≤ maxMessageRegisters)
    (hCaps : decoded.msgInfo.extraCaps ≤ maxExtraCaps)
    (hLabel : decoded.msgInfo.label ≤ MessageInfo.maxLabel := by omega)
    (hUnw : decoded.msgInfo.capsUnwrapped ≤ MessageInfo.maxCapsUnwrapped := by omega)
    (hCapBound : isWord64 decoded.capAddr.toNat) :
    decodeCapPtr (encodeCapPtr decoded.capAddr) = .ok decoded.capAddr ∧
    decodeMsgInfo (encodeMsgInfo decoded.msgInfo) = .ok decoded.msgInfo ∧
    decodeSyscallId (encodeSyscallId decoded.syscallId) = .ok decoded.syscallId :=
  ⟨decodeCapPtr_roundtrip decoded.capAddr hCapBound,
   decodeMsgInfo_roundtrip decoded.msgInfo hLen hCaps hLabel hUnw,
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
    · split at hOk
      · simp at hOk
      · simp only [pure, Except.pure, Except.ok.injEq] at hOk
        refine ⟨?_, ?_, ?_⟩ <;> (rw [← hOk])
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
    · split at hOk
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
      · -- A syscall that reads no overflow word: the inline registers alone
        simp only [pure, Except.pure, Except.ok.injEq] at hOk
        have h1 : decoded.msgRegs.size = base.msgRegs.size := by rw [← hOk]
        have h2 : decoded.inlineCount = base.msgRegs.size := by rw [← hOk]
        have h3 : decoded.overflowCount = 0 := by rw [← hOk]
        rw [h1, h2, h3]; omega


/-- **A syscall that reads no overflow word reads no IPC buffer**: its decode
is the inline decode whatever the message length and whatever the state holds
(`syscallReadsOverflow`), so a long signal cannot be refused by an unmapped
buffer, as seL4's `seL4_Signal` reads no message. -/
theorem decodeSyscallArgsFromState_of_no_overflow
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (base : SyscallDecodeResult)
    (hBase : decodeSyscallArgs layout regs regCount = .ok base)
    (hNo : syscallReadsOverflow base.syscallId = false) :
    decodeSyscallArgsFromState st tid layout regs regCount =
      .ok { base with inlineCount := base.msgRegs.size, overflowCount := 0 } := by
  unfold decodeSyscallArgsFromState
  rw [hBase]
  simp only [bind, Except.bind, hNo, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

/-- The syscalls the entry routes on the register file itself, before any
    decode record or message array exists, with the operands each reads
    there.  Every other call goes through the decode (`viaDecode`). -/
inductive RegisterRoutedSyscall where
  /-- A signal: its operand address, and nothing else — the badge it ORs in
      is the capability's (`Capability.signalBadge`), so no message register
      is read, as seL4's `sendSignal` reads none. -/
  | signal (capAddr : CPtr)
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
  /-- A send with no capabilities to transfer whose message runs past the
      layout's message registers: its operand address and its message info;
      the first words are the inline message registers and the rest the
      overflow slots of the sender's IPC buffer, as the decode reads them. -/
  | sendLong (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- A call with no capabilities to transfer whose message runs past the
      layout's message registers: its operand address and its message info;
      the first words are the inline message registers and the rest the
      overflow slots of the caller's IPC buffer, as the decode reads them. -/
  | callLong (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- A reply whose message runs past the layout's message registers: its
      operand address and its message info; the first words are the inline
      message registers and the rest the overflow slots of the replier's IPC
      buffer, as the decode reads them. -/
  | replyLong (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- A reply-receive whose reply message runs past the layout's message
      registers: its operand address and its message info, the words read as
      `replyLong`'s are. -/
  | replyRecvLong (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- A send or a call (`sid`) that transfers capabilities, of any length:
      its operand address and its message info.  Its message is read as the
      send's or the call's is; the capabilities are looked up at the
      rendezvous. -/
  | transferring (sid : SyscallId) (capAddr : CPtr) (msgInfo : MessageInfo)
  /-- WS-ZA ZA5.13: a declassification or an audit call (`routedAudited`) with
      no overflow words: the syscall and its operand address; its arguments
      are the layout's message registers. -/
  | audited (sid : SyscallId) (capAddr : CPtr)
  /-- A call whose dispatch reads no word past overflow slot 0
      (`routedOverflowed`) and whose message runs past the layout's message
      registers: the syscall, its operand address and its message length.
      The decode reads its overflow slots, and the dispatch reads only the
      inline words and, for a five-word invocation, slot 0.  It carries the
      length alone, a number, so the route builds no message info. -/
  | overflowed (sid : SyscallId) (capAddr : CPtr) (len : Nat)
  /-- A five-word invocation (`routedOverflowOne`) whose message fits the
      layout's message registers: the syscall and its operand address.  Its
      fifth argument is missing, so the decode of its arguments refuses once
      the capability is found. -/
  | shortArgs (sid : SyscallId) (capAddr : CPtr)
  /-- A message-info word the decode refuses: the decode's refusal, before
      anything else is read. -/
  | refused (e : KernelError)
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
  | .schedContextYieldTo | .irqHandlerAck | .irqControlGet | .irqHandlerSetNotification | .irqHandlerClear
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

/-- The syscalls a message past the layout's registers and its first overflow
word routes as `overflowed`: the five-word invocations, whose fifth argument is
overflow slot 0 and whose decode reads every word the message names.  Every
other syscall past the registers either has a route of its own (the IPC calls)
or reads no overflow word and takes its short route (`syscallReadsOverflow`). -/
def routedOverflowed : SyscallId → Bool
  | .schedContextConfigure | .serviceRegister => true
  | _ => false

/-- The overflowed syscall number `n` names, if any. -/
@[inline] def routedOverflowedSid? (n : Nat) : Option SyscallId :=
  match SyscallId.ofNat? n with
  | some sid => if routedOverflowed sid then some sid else none
  | none => none

theorem routedOverflowedSid?_some {n : Nat} {sid : SyscallId}
    (h : routedOverflowedSid? n = some sid) :
    routedOverflowed sid = true ∧ n = sid.toNat := by
  unfold routedOverflowedSid? at h
  split at h
  · next sid' hOf =>
    split at h
    · next hR =>
      cases h
      exact ⟨hR, (SyscallId.toNat_ofNat hOf).symm⟩
    · cases h
  · cases h

/-- The route of a call no other route names: a syscall number the decode
refuses is refused as the decode refuses it, before anything else is read; any
other takes the decode. -/
@[inline] def unroutedSyscall (n : Nat) : RegisterRoutedSyscall :=
  match SyscallId.ofNat? n with
  | some _ => .viaDecode
  | none => .refused .invalidSyscallNumber

theorem unroutedSyscall_eq {n : Nat} {r : RegisterRoutedSyscall} (h : unroutedSyscall n = r) :
    r = .viaDecode ∨ (r = .refused .invalidSyscallNumber ∧ SyscallId.ofNat? n = none) := by
  unfold unroutedSyscall at h
  split at h
  · exact .inl h.symm
  · next hN => exact .inr ⟨h.symm, hN⟩

/-- The short message's route past the named syscalls, read off one decode of
the syscall number: `registerRoutedSyscallOf`'s tail, equal to reading it once per
route (`routedShortTail_eq`). -/
@[inline] def routedShortTail (capAddr : CPtr) (len n : Nat) : RegisterRoutedSyscall :=
  match SyscallId.ofNat? n with
  | some sid =>
    if routedInvocation sid then
      if len < truncationMinimum sid then .shortArgs sid capAddr else .invoke sid capAddr
    else if routedAudited sid then .audited sid capAddr
    else if routedOverflowOne sid then
      if len < truncationMinimum sid then .shortArgs sid capAddr else .viaDecode
    else .viaDecode
  | none => .refused .invalidSyscallNumber

theorem routedShortTail_eq (capAddr : CPtr) (len n : Nat) :
    routedShortTail capAddr len n =
      match routedInvocationSid? n with
      | some sid =>
        if len < truncationMinimum sid then .shortArgs sid capAddr else .invoke sid capAddr
      | none =>
        match routedAuditedSid? n with
        | some sid => .audited sid capAddr
        | none =>
          match routedOverflowOneSid? n with
          | some sid =>
            if len < truncationMinimum sid then .shortArgs sid capAddr else .viaDecode
          | none => unroutedSyscall n := by
  unfold routedShortTail routedInvocationSid? routedAuditedSid? routedOverflowOneSid?
    unroutedSyscall
  cases SyscallId.ofNat? n with
  | none => rfl
  | some sid => cases sid <;> rfl

/-- Whether syscall number `n` reads a message word past the inline registers
(`syscallReadsOverflow`); a number the decode refuses is routed as a long
message, whose tail refuses it as the short one's does. -/
@[inline] def syscallNumberReadsOverflow (n : Nat) : Bool :=
  match SyscallId.ofNat? n with
  | some sid => syscallReadsOverflow sid
  | none => true

/-- A syscall that reads its overflow words is one the router routes past the
inline registers: an IPC call or a five-word invocation. -/
theorem syscallReadsOverflow_eq_true_iff (sid : SyscallId) :
    syscallReadsOverflow sid = true ↔
      sid = .send ∨ sid = .call ∨ sid = .reply ∨ sid = .replyRecv ∨
        routedOverflowOne sid = true := by
  cases sid <;> decide

/-- A one-overflow-word invocation reads its overflow word. -/
theorem syscallReadsOverflow_of_routedOverflowOne {sid : SyscallId}
    (h : routedOverflowOne sid = true) : syscallReadsOverflow sid = true := by
  cases sid <;> first | rfl | (simp [routedOverflowOne] at h)

/-- A syscall the long message routes `overflowed` reads its overflow words. -/
theorem syscallReadsOverflow_of_routedOverflowed {sid : SyscallId}
    (h : routedOverflowed sid = true) : syscallReadsOverflow sid = true := by
  cases sid <;> first | rfl | (simp [routedOverflowed] at h)

/-- The overflowed route's syscalls are the five-word invocations. -/
theorem routedOverflowed_of_routedOverflowOne {sid : SyscallId}
    (h : routedOverflowOne sid = true) : routedOverflowed sid = true := by
  cases sid <;> first | rfl | (simp [routedOverflowOne] at h)

/-- The long message's route past the IPC calls, read off one decode of the
syscall number: `registerRoutedSyscallOf`'s tail (`routedLongTail_eq`).  Only a
syscall that reads its overflow words reaches it (`syscallNumberReadsOverflow`):
a five-word invocation, `overflowOne` at five words and `overflowed` past
them. -/
@[inline] def routedLongTail (capAddr : CPtr) (len size n : Nat) : RegisterRoutedSyscall :=
  match SyscallId.ofNat? n with
  | some sid =>
    if routedOverflowOne sid then
      if len = size + 1 then .overflowOne sid capAddr else .overflowed sid capAddr len
    else .viaDecode
  | none => .refused .invalidSyscallNumber

theorem routedLongTail_eq (capAddr : CPtr) (len size n : Nat) :
    routedLongTail capAddr len size n =
      match routedOverflowOneSid? n with
      | some sid => if len = size + 1 then .overflowOne sid capAddr else .overflowed sid capAddr len
      | none => unroutedSyscall n := by
  unfold routedLongTail routedOverflowOneSid? unroutedSyscall
  cases SyscallId.ofNat? n with
  | none => rfl
  | some sid => cases sid <;> rfl

/-- The routed syscall a register file names once its registers are in bounds
    (`registerRoutedSyscall`). -/
@[inline] def registerRoutedSyscallOf (layout : SyscallRegisterLayout) (regs : RegisterFile) :
    RegisterRoutedSyscall :=
  let capAddr := CPtr.ofWord (readRegWord regs layout.capPtrReg)
  match decodeMsgInfoWord (readRegWord regs layout.msgInfoReg) with
  | .error e => .refused e
  | .ok msgInfo =>
    if msgInfo.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow (readReg regs layout.syscallNumReg).val = false then
      if (readReg regs layout.syscallNumReg).val = SyscallId.notificationSignal.toNat then
        .signal capAddr
      else if (readReg regs layout.syscallNumReg).val = SyscallId.notificationWait.toNat then
        .wait capAddr
      else if (readReg regs layout.syscallNumReg).val = SyscallId.yield.toNat then
        .yield
      else if (readReg regs layout.syscallNumReg).val = SyscallId.send.toNat then
        if msgInfo.extraCaps = 0 then .send capAddr msgInfo
        else .transferring .send capAddr msgInfo
      else if (readReg regs layout.syscallNumReg).val = SyscallId.call.toNat then
        if msgInfo.extraCaps = 0 then .call capAddr msgInfo
        else .transferring .call capAddr msgInfo
      else if (readReg regs layout.syscallNumReg).val = SyscallId.reply.toNat then
        .reply capAddr msgInfo
      else if (readReg regs layout.syscallNumReg).val = SyscallId.receive.toNat then
        if h0 : 0 < layout.msgRegs.size then
          .receive capAddr msgInfo.length (CPtr.ofWord (readRegWord regs layout.msgRegs[0]))
        else .viaDecode
      else if (readReg regs layout.syscallNumReg).val = SyscallId.replyRecv.toNat then
        .replyRecv capAddr msgInfo
      else
        routedShortTail capAddr msgInfo.length (readReg regs layout.syscallNumReg).val
    else if (readReg regs layout.syscallNumReg).val = SyscallId.send.toNat then
      if msgInfo.extraCaps = 0 then .sendLong capAddr msgInfo
      else .transferring .send capAddr msgInfo
    else if (readReg regs layout.syscallNumReg).val = SyscallId.call.toNat then
      if msgInfo.extraCaps = 0 then .callLong capAddr msgInfo
      else .transferring .call capAddr msgInfo
    else if (readReg regs layout.syscallNumReg).val = SyscallId.reply.toNat then
      .replyLong capAddr msgInfo
    else if (readReg regs layout.syscallNumReg).val = SyscallId.replyRecv.toNat then
      .replyRecvLong capAddr msgInfo
    else
      routedLongTail capAddr msgInfo.length layout.msgRegs.size
        (readReg regs layout.syscallNumReg).val

/-- The routed syscall a register file names, read straight from the
    registers: `signal`/`wait` only when the decode succeeds as that syscall
    with no overflow words merged, and carries the same operands
    (`decodeSyscallArgsFromState_of_routedSignal`,
    `decodeSyscallArgsFromState_of_routedWait`).  Inlined and matched at once,
    it builds nothing.  Its registers out of bounds, it takes the decode. -/
@[inline] def registerRoutedSyscall (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (regCount : Nat := 32) : RegisterRoutedSyscall :=
  if layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true then
    registerRoutedSyscallOf layout regs
  else .viaDecode

/-- On the default layout every register the router reads is in bounds, so the
router is its body (`registerRoutedSyscallOf`): an arm matching on the body
reads no bounds check. -/
theorem registerRoutedSyscall_default (rf : RegisterFile) :
    registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      registerRoutedSyscallOf SeLe4n.arm64DefaultLayout rf := by
  unfold registerRoutedSyscall
  rw [if_pos ⟨by decide, by decide, by decide, by simp [SeLe4n.arm64DefaultLayout]⟩]

/-- **The router hands the decode nothing**, for the default layout: every
register file is routed to an arm of its own or refused as the decode refuses
it -- a send or a call transferring capabilities included (`.transferring`)
-- so the entry's decoded arm (`.viaDecode`) is unreachable from the ABI.  It
stays for a layout whose registers lie out of bounds or which has no message
register. -/
theorem registerRoutedSyscall_viaDecode (rf : RegisterFile) :
    registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 ≠ .viaDecode := by
  intro h
  unfold registerRoutedSyscall at h
  split at h
  case isFalse hB =>
    exact absurd ⟨by decide, by decide, by decide, by simp [SeLe4n.arm64DefaultLayout]⟩ hB
  unfold registerRoutedSyscallOf at h
  rw [decodeMsgInfoWord_readReg] at h
  cases hM : decodeMsgInfo (readReg rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
  | error e => simp only [hM] at h; cases h
  | ok mi =>
  simp only [hM] at h
  generalize hN : (readReg rf SeLe4n.arm64DefaultLayout.syscallNumReg).val = n at h
  cases hS : SyscallId.ofNat? n with
  | none =>
    have hNe : ∀ s : SyscallId, n ≠ s.toNat := by
      intro s hs; subst hs; rw [SyscallId.ofNat_toNat] at hS; cases hS
    simp only [hNe, if_false, routedShortTail, routedLongTail, hS] at h
    split at h <;> cases h
  | some sid =>
  have hn := SyscallId.toNat_ofNat hS
  subst hn
  cases sid <;> simp only [routedShortTail, routedLongTail, SyscallId.ofNat_toNat] at h <;>
    simp (config := { decide := true }) at h <;>
    (repeat' split at h) <;>
    first
      | (cases h; done)
      | (simp_all; done)
      | omega
      | (have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := by decide
         simp only [truncationMinimum] at *; omega)
end SeLe4n.Kernel.Architecture.RegisterDecode

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The message length a register-routed frame names: bits 0–6 of its
message-info word (`decodeMsgInfoWord`), read as a word so an arm that reads
it builds no message info. -/
@[inline] def routedLength (rf : SeLe4n.RegisterFile) : Nat :=
  (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg &&& 0x7F).toNat

/-- The length a decoded message info carries is the frame's `routedLength`. -/
theorem routedLength_of_decodeWord {rf : SeLe4n.RegisterFile} {mi : MessageInfo}
    (h : Architecture.RegisterDecode.decodeMsgInfoWord
      (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) = .ok mi) :
    routedLength rf = mi.length := by
  unfold Architecture.RegisterDecode.decodeMsgInfoWord at h
  split at h
  · cases h; rfl
  · cases h

theorem routedLength_of_decode {rf : SeLe4n.RegisterFile} {mi : MessageInfo}
    (h : Architecture.RegisterDecode.decodeMsgInfo
      (readReg rf SeLe4n.arm64DefaultLayout.msgInfoReg) = .ok mi) :
    routedLength rf = mi.length := by
  rw [← Architecture.RegisterDecode.decodeMsgInfoWord_readReg] at h
  exact routedLength_of_decodeWord h

end SeLe4n.Kernel
