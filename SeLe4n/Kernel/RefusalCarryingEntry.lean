-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.RefusalCarryingOverflowed
import SeLe4n.Kernel.RefusalCarryingReplyRecv
import SeLe4n.Kernel.RefusalCarryingInvocation
import SeLe4n.Kernel.RefusalCarryingDeclassification
import SeLe4n.Kernel.Architecture.RoutedRegisterDecode

/-!
# The checked syscall entry, refusing in the state it was refused in

WS-ZA ZA1.3.  `syscallEntryCheckedR` is `syscallEntryChecked` in the
`RefusalCarrying` form (`syscallEntryCheckedR_eq`): the syscalls whose
arguments all sit in registers and whose checks all precede their first write
are routed on the register file to the dispatches of `RefusalCarryingDispatch`,
`RefusalCarryingEndpoint`, `RefusalCarryingReplyRecv`, `RefusalCarryingInvocation`
and `RefusalCarryingDeclassification`; every other call takes
`RefusalCarrying.ofKernel` of the specification.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Architecture.RegisterDecode (clampedFrameDecode
  truncationMinimum_of_routedOverflowOne)

/-- **How many extra capabilities a routed frame's syscall `sid` looks up**
(`syscallExtraCapCount`): bits 7..8 of its message-info word, read as the word
so the entry builds no message info; none on a receive-phase syscall. -/
@[inline] def routedExtraCapCount (sid : SyscallId) (rf : SeLe4n.RegisterFile) : Nat :=
  syscallExtraCapCount sid
    ((SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg >>> 7) &&& 3).toNat

/-- A routed frame's count is that of any decode of its frame. -/
theorem routedExtraCapCount_of_msgInfo {st : SystemState} {tid : SeLe4n.ThreadId}
    {rf : SeLe4n.RegisterFile} {sid : SyscallId} {n : Nat}
    (h : ∃ decoded, SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout rf 32 = .ok decoded ∧ decoded.msgInfo.extraCaps = n) :
    routedExtraCapCount sid rf = syscallExtraCapCount sid n := by
  obtain ⟨decoded, hDec, rfl⟩ := h
  obtain ⟨mi, hM, hX, -⟩ := decodeSyscallArgsFromState_msgInfo hDec
  rw [← SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfoWord_readReg] at hM
  rw [hX, decodeMsgInfoWord_extraCaps hM]
  rfl

/-- A routed frame's count is its decode's. -/
theorem routedExtraCapCount_eq {st : SystemState} {tid : SeLe4n.ThreadId}
    {rf : SeLe4n.RegisterFile} {decoded : SyscallDecodeResult} {sid : SyscallId}
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout rf 32 = .ok decoded)
    (hSid : decoded.syscallId = sid) :
    routedExtraCapCount sid rf =
      syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps := by
  obtain ⟨mi, hM, hX, -⟩ := decodeSyscallArgsFromState_msgInfo hDec
  rw [← SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfoWord_readReg] at hM
  rw [hSid, hX, decodeMsgInfoWord_extraCaps hM]
  rfl

/-- A route that carries a message info counts its extra capabilities as the
routed frame does: the arm reads the count off the route's message info, the
entry's specification off the register word. -/
theorem routedExtraCapCount_of_route {rf : SeLe4n.RegisterFile}
    {r : SeLe4n.Kernel.Architecture.RegisterDecode.RegisterRoutedSyscall} {capAddr : SeLe4n.CPtr}
    {msgInfo : MessageInfo} (sid : SyscallId)
    (h : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout rf 32 = r)
    (hr : r = .send capAddr msgInfo ∨ r = .call capAddr msgInfo ∨ r = .reply capAddr msgInfo ∨
      r = .replyRecv capAddr msgInfo ∨ r = .sendLong capAddr msgInfo ∨
      r = .callLong capAddr msgInfo ∨ r = .replyLong capAddr msgInfo ∨
      r = .replyRecvLong capAddr msgInfo ∨ ∃ sid, r = .transferring sid capAddr msgInfo) :
    syscallExtraCapCount sid msgInfo.extraCaps = routedExtraCapCount sid rf := by
  unfold routedExtraCapCount
  rw [decodeMsgInfoWord_extraCaps
    (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall_msgInfo_decode _ _ _ h hr)]

/-- A receive looks no extra capability up. -/
theorem routedExtraCapCount_receive (rf : SeLe4n.RegisterFile) :
    routedExtraCapCount .receive rf = 0 := rfl

/-- `syscallEntryChecked`, refusing in the state it was handed
(`syscallEntryCheckedR_eq`), on the hardware's register layout
(`arm64DefaultLayout`, 32 registers).  A signal, wait, yield, capability-free send or call,
reply, receive, capability invocation (`routedInvocation`), or declassification or
audit call (`routedAudited`) whose arguments all sit in registers is routed on the
register file
itself (`registerRoutedSyscall`),
before any decode record exists: the decode writes nothing, so its dispatch is
handed the entry's own state and refuses in it.  Every other call keeps the
specification's form.

A specification: the compiled entry runs the continued form
(`syscallEntryCheckedK`, compiled as `syscallEntryRoutedK`), so no code is
generated for it. -/
noncomputable def syscallEntryCheckedR (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if isInsecureDefaultContext ctx then .error (.policyDenied, st)
    else
    match st.scheduler.currentOnCore executingCore with
    | none => .error (.illegalState, st)
    | some tid =>
      -- `lookupThreadRegisterContext`, read in place: its `.ok (regs, st)` is
      -- two cells this match never needs.
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
                SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
        | .signal capAddr =>
          dispatchSignalCheckedR ctx capAddr tid executingCore (routedExtraCapCount .notificationSignal tcb.registerContext) st
        | .wait capAddr =>
          dispatchWaitCheckedR ctx capAddr tid executingCore (routedExtraCapCount .notificationWait tcb.registerContext) st
        -- WS-ZA ZA4.3: a yield reads no operand and checks nothing a write
        -- precedes, so a refusal is in the entry's own state.
        | .yield =>
          match yieldOnCoreR st executingCore with
          | .error r => .error r
          | .ok st' => .ok ((), st')
        -- WS-ZA ZA4.7: a send with no capabilities to transfer checks
        -- everything before its first write.
        | .send capAddr msgInfo =>
          dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            tid executingCore (routedExtraCapCount .send tcb.registerContext) st
        -- WS-ZA ZA4.7: a call with no capabilities to transfer.
        | .call capAddr msgInfo =>
          dispatchCallCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            tid executingCore (routedExtraCapCount .call tcb.registerContext) st
        -- WS-ZA ZA4.7: a reply; one whose checks all pass before its first
        -- write writes in place.
        | .reply capAddr msgInfo =>
          dispatchReplyCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .reply tcb.registerContext) st
        -- WS-ZA ZA4.7: a receive, with or without a reply object; one that
        -- blocks checks everything, the reply object included, before its
        -- first write.
        | .receive capAddr len replyAddr =>
          dispatchReceiveCheckedR ctx capAddr len replyAddr tid executingCore (routedExtraCapCount .receive tcb.registerContext) st
        -- WS-ZA ZA4.7: a reply-receive; one that answers a caller blocked on
        -- this server and then blocks writes in place, after every check.
        | .replyRecv capAddr msgInfo =>
          dispatchReplyRecvCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext) st
        -- WS-ZA ZA5.1: a capability invocation outside IPC, its arguments
        -- read from the caller's registers.
        | .invoke sid capAddr =>
          dispatchInvocationCheckedR ctx sid capAddr tcb.registerContext tid executingCore (routedExtraCapCount sid tcb.registerContext) st
        -- WS-ZA ZA5.2, ZA5.5: a scheduling-context configure or a service
        -- register, its fifth word read from overflow slot 0 of the caller's
        -- IPC buffer.  The read writes nothing, so the dispatch is handed the
        -- entry's own state.
        | .overflowOne sid capAddr =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
            (fun _ => dispatchShortArgsCheckedR sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) st)
            (fun w =>
              dispatchOverflowOneCheckedR ctx sid capAddr tcb.registerContext w tid executingCore (routedExtraCapCount sid tcb.registerContext) st)
        -- WS-ZA ZA6.35: a send of more than four words.  Its overflow slots lie
        -- in the frame of the caller's IPC buffer (`lookupIPCBuffer`), so the
        -- decode reads them all exactly when it reads slot 0
        -- (`ipcBufferOverflowReadable`), and the send's arm copies the words in
        -- place.
        | .sendLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                tcb.registerContext 4 tid executingCore (routedExtraCapCount .send tcb.registerContext) st)
              (fun _ =>
                    dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (routedExtraCapCount .send tcb.registerContext) st)
        -- A call of more than four words: read as the long send's,
        -- the call's arm copying the words in place.
        | .callLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchCallCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                tcb.registerContext 4 tid executingCore (routedExtraCapCount .call tcb.registerContext) st)
              (fun _ =>
                    dispatchCallLongCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (routedExtraCapCount .call tcb.registerContext) st)
        -- A reply of more than four words: read as the long send's,
        -- the reply's arm copying the words in place.
        | .replyLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchReplyCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                tcb.registerContext 4 msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .reply tcb.registerContext) st)
              (fun _ =>
                    dispatchReplyLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .reply tcb.registerContext) st)
        -- A reply-receive of more than four words: read as the
        -- long reply's, the arm copying the words in place.
        | .replyRecvLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchReplyRecvCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                tcb.registerContext 4 msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext) st)
              (fun _ =>
                    dispatchReplyRecvLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext) st)
        -- A send or call carrying capabilities: the capability operand checked
        -- before the first write; one that blocks writes in place, one that
        -- meets a receiver takes the specification's transfer
        -- (`dispatchTransferringCheckedR_eq`).  Past the inline words, its
        -- overflow slots read as the long send's.
        | .transferring sid capAddr msgInfo =>
          if msgInfo.length ≤ 4 then
            dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext msgInfo.length tid
              executingCore (routedExtraCapCount sid tcb.registerContext) st
          else
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext 4 tid
                executingCore (routedExtraCapCount sid tcb.registerContext) st)
              (fun _ =>
                    dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext
                      msgInfo.length tid executingCore (routedExtraCapCount sid tcb.registerContext) st)
        -- WS-ZA ZA5.13: a declassification or an audit call, its arguments
        -- read from the caller's registers; an admitted one writes the audit
        -- ring, the taint words and the return registers in place.
        | .audited sid capAddr =>
          dispatchAuditedCheckedR ctx sid capAddr tcb.registerContext tid executingCore (routedExtraCapCount sid tcb.registerContext) st
        -- A call past the inline words whose dispatch reads no word past slot
        -- 0: its overflow slots read as the long send's are, then
        -- the short route's dispatch (`dispatchOverflowedCheckedR_eq`).
        | .overflowed sid capAddr len =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchShortArgsCheckedR sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) st)
              (fun w =>
                    dispatchOverflowedCheckedR ctx sid capAddr tcb.registerContext w
                      (overflowWordAt st tid 1) (overflowWordAt st tid 2) len tid executingCore
                      (routedExtraCapCount sid tcb.registerContext) st)
        -- A five-word invocation of the inline words alone, short of its
        -- fifth argument: refused once its capability is found and checked.
        | .shortArgs sid capAddr => dispatchShortArgsCheckedR sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) st
        -- A message-info word or a syscall number the decode refuses: refused
        -- before any write.
        | .refused e => .error (e, st)
        | .viaDecode =>
          RefusalCarrying.ofKernel (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st
      | some _ => .error (.illegalState, st)
      | none => .error (.objectNotFound, st)

/-- The saved registers the entry routes on are the executing thread's own,
which is what the send and call arms read their message from. -/
theorem frameOf {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb)) :
    ∀ t, st.getTcb? tid = some t → t.registerContext = tcb.registerContext := by
  intro t ht
  have hT : st.getTcb? tid = some tcb := by
    rw [SystemState.getObject?_eq_getElem] at hObj
    simp only [SystemState.getTcb?, hObj]
  rw [hT] at ht
  cases ht
  rfl

/-- **The state a routed reply-receive's refusal reports**: the reply-receive's
operand report (`replyRecvOperandReport` under `operandReport`) on the decode of
its frame, which the short route and every path of the long route dispatch on
(`syscallEntryCheckedR_eq_of_replyRecv`, `syscallEntryCheckedR_eq_of_replyRecvLong`):
the skipped reply's receive cancels its busy reply's holder before a refusal
that follows it.  The state as it was when the frame decodes to no reply-receive. -/
def replyRecvEntryReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (executingCore : Concurrency.CoreId) (st : SystemState) :
    SystemState :=
  match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout rf 32 with
  | .ok decoded =>
    if decoded.syscallId = .replyRecv then
      operandReport decoded.capAddr tid executingCore
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)
        (replyRecvOperandReport ctx tid decoded.msgInfo.length decoded.msgInfo.extraCaps
          decoded.msgRegs executingCore (syscallRequiredRight .replyRecv)) st
    else st
  | .error _ => st

/-- **The state a refusal of the checked entry reports** (WS-SX SX4, SX6): a
receive routed on the register file whose endpoint and flow gate pass has
cancelled its busy reply's holder in place (seL4-MCS `receiveIPC`'s
`cancelIPC(replyTCB)`) before the refusals that can follow, and those report the
cancelled state (`receiveOperandReport`); so has a reply-receive whose extra
capabilities fail, since it skips its reply and receives
(`replyRecvEntryReport`); every other refusal writes nothing before it and
reports the state the entry was handed. -/
def cancelReceiveBusyReply (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  if isInsecureDefaultContext ctx then st
  else
  match st.scheduler.currentOnCore executingCore with
  | none => st
  | some tid =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
              SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
      | .receive capAddr len replyAddr =>
        operandReport capAddr tid executingCore (routedExtraCapCount .receive tcb.registerContext)
          (receiveOperandReport ctx tid len replyAddr executingCore (syscallRequiredRight .receive)) st
      | .replyRecv _ _ | .replyRecvLong _ _ =>
        replyRecvEntryReport ctx tid tcb.registerContext executingCore st
      | _ => st
    | _ => st

/-- The routed receive's report is the state handed to it or its busy reply's
cancel, the holder its decode's busy-reply code names through any gate on the
caller's CSpace root. -/
private theorem receiveEntryReport_cases (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (capAddr : SeLe4n.CPtr) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRecvRegs : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .receive capAddr len replyAddr) :
    operandReport capAddr tid executingCore (routedExtraCapCount .receive tcb.registerContext)
        (receiveOperandReport ctx tid len replyAddr executingCore (syscallRequiredRight .receive))
        st = st ∨
      ∃ (decoded : SyscallDecodeResult) (k : Nat),
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
          SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
        decoded.syscallId = .receive ∧
        (∀ gate : SyscallGate, gate.cspaceRootCap = callerCspaceRoot st tid →
          recvBusyReplyHolderCode ctx tid gate decoded st = k + 1) ∧
        operandReport capAddr tid executingCore (routedExtraCapCount .receive tcb.registerContext)
          (receiveOperandReport ctx tid len replyAddr executingCore (syscallRequiredRight .receive))
          st = cancelReplyHolder st ⟨k⟩ executingCore := by
  obtain ⟨decoded, hDec, hRecv, -, -, hLen, hReplyAddr⟩ :=
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
      st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr len replyAddr hRecvRegs
  have hArgs : len ≠ 0 → SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeRecvArgs decoded
      = .ok { replyCPtr := replyAddr } := by
    intro hN
    have h := hReplyAddr hN
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨h0, hv⟩ := h
    simp only [SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeRecvArgs,
      SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg, h0, ↓reduceDIte, hv, bind,
      Except.bind, pure, Except.pure, SeLe4n.RegValue.val_mk, SeLe4n.CPtr.ofNat_word_toNat]
  have hCode : ∀ k, receiveArmHolderCode ctx tid len replyAddr (callerCspaceRoot st tid) st = k + 1 →
      ∀ gate : SyscallGate, gate.cspaceRootCap = callerCspaceRoot st tid →
        recvBusyReplyHolderCode ctx tid gate decoded st = k + 1 := by
    intro k hK gate hRoot
    rw [← receiveArmHolderCode_eq ctx tid _ gate decoded len replyAddr st hRoot hLen hArgs]
    exact hK
  -- the arm's report, through the operand and the receive's checks
  have hArm : ∀ cap? : Option Capability,
      receiveOperandReport ctx tid len replyAddr executingCore (syscallRequiredRight .receive)
          cap? st = st ∨
        ∃ k, receiveArmHolderCode ctx tid len replyAddr (callerCspaceRoot st tid) st = k + 1 ∧
          receiveOperandReport ctx tid len replyAddr executingCore
            (syscallRequiredRight .receive) cap? st = cancelReplyHolder st ⟨k⟩ executingCore := by
    intro cap?
    unfold receiveOperandReport
    split
    · exact Or.inl rfl
    rename_i cap
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · unfold receiveArmReport
      split
      · split
        · exact Or.inl rfl
        · unfold cancelReceiveArmBusyReply
          split
          · exact Or.inl rfl
          · rename_i k hK
            exact Or.inr ⟨k, hK, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  unfold operandReport
  split
  · exact Or.inl rfl
  rw [hObj]
  simp only
  split
  · rename_i ref _
    simp only [routedExtraCapCount_receive, extraCapsLookupFault?_zero]
    split
    · exact Or.inl rfl
    rcases hArm (SystemState.lookupSlotCap st ref) with h | ⟨k, hK, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨decoded, k, hDec, hRecv, hCode k hK, h⟩
  · exact Or.inl rfl

/-- A reply-receive's report on its decode is the state handed to it or its
busy reply's cancel: the latter only when its extra capabilities fail, so it
skipped its reply and received, the holder named by the receive's busy-reply
code through any gate on the caller's CSpace root. -/
theorem replyRecvDecodedReport_cases (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (decoded : SyscallDecodeResult) (xc : Nat)
    (st : SystemState) :
    operandReport decoded.capAddr tid executingCore xc
        (replyRecvOperandReport ctx tid decoded.msgInfo.length decoded.msgInfo.extraCaps
          decoded.msgRegs executingCore (syscallRequiredRight .replyRecv)) st = st ∨
      ∃ k : Nat, (callerExtraCapsFault? st tid decoded.msgInfo.extraCaps).isSome ∧
        (∀ gate : SyscallGate, gate.cspaceRootCap = callerCspaceRoot st tid →
          recvBusyReplyHolderCode ctx tid gate decoded st = k + 1) ∧
        operandReport decoded.capAddr tid executingCore xc
          (replyRecvOperandReport ctx tid decoded.msgInfo.length decoded.msgInfo.extraCaps
            decoded.msgRegs executingCore (syscallRequiredRight .replyRecv)) st =
          cancelReplyHolder st ⟨k⟩ executingCore := by
  have hArm : ∀ cap? : Option Capability,
      replyRecvOperandReport ctx tid decoded.msgInfo.length decoded.msgInfo.extraCaps
          decoded.msgRegs executingCore (syscallRequiredRight .replyRecv) cap? st = st ∨
        ∃ k : Nat, (callerExtraCapsFault? st tid decoded.msgInfo.extraCaps).isSome ∧
          (∀ gate : SyscallGate, gate.cspaceRootCap = callerCspaceRoot st tid →
            recvBusyReplyHolderCode ctx tid gate decoded st = k + 1) ∧
          replyRecvOperandReport ctx tid decoded.msgInfo.length decoded.msgInfo.extraCaps
            decoded.msgRegs executingCore (syscallRequiredRight .replyRecv) cap? st =
            cancelReplyHolder st ⟨k⟩ executingCore := by
    intro cap?
    unfold replyRecvOperandReport replyRecvArmReport replyRecvSkipReport
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · split
      · rename_i hXc
        split
        · rename_i r0 hM
          unfold receiveArmReport
          split
          · split
            · exact Or.inl rfl
            · unfold cancelReceiveArmBusyReply
              split
              · exact Or.inl rfl
              · rename_i k hK
                refine Or.inr ⟨k, by rw [hXc]; rfl, fun gate hRoot => ?_, rfl⟩
                rw [← receiveArmHolderCode_eq ctx tid _ gate decoded _ _ st hRoot rfl
                  (fun _ => decodeRecvArgs_of_requireMsgReg hM)]
                exact hK
          · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  unfold operandReport
  split
  · exact Or.inl rfl
  split
  · split
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact hArm _
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **What a refusal of the checked entry reports is the state handed to it or
its busy reply's cancel**: `cancelReceiveBusyReply` is the identity, or the
routed receive's arm, or a routed reply-receive that skipped its reply, cancelled
the holder its decode's busy-reply code names through any gate on the caller's
CSpace root (`recvBusyReplyHolderCode`). -/
theorem cancelReceiveBusyReply_cases_decoded (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) :
    cancelReceiveBusyReply ctx executingCore st = st ∨
      ∃ (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (k : Nat),
        st.scheduler.currentOnCore executingCore = some tid ∧
        st.getObject? tid.toObjId = some (.tcb tcb) ∧
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
          SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
        receivesWithoutReply decoded tid st ∧
        (∀ gate : SyscallGate, gate.cspaceRootCap = callerCspaceRoot st tid →
          recvBusyReplyHolderCode ctx tid gate decoded st = k + 1) ∧
        cancelReceiveBusyReply ctx executingCore st = cancelReplyHolder st ⟨k⟩ executingCore := by
  unfold cancelReceiveBusyReply
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  rename_i tid hCur
  split
  · rename_i tcb hObj
    split
    · rename_i capAddr len replyAddr hRecvRegs
      rcases receiveEntryReport_cases ctx executingCore st tid tcb capAddr len replyAddr hObj
        hRecvRegs with h | ⟨decoded, k, hDec, hRecv, hK, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨tid, tcb, decoded, k, hCur, hObj, hDec, .inl hRecv, hK, h⟩
    all_goals first
      | exact Or.inl rfl
      | (unfold replyRecvEntryReport
         split
         · rename_i decoded hDec
           split
           · rename_i hRR
             rcases replyRecvDecodedReport_cases ctx tid executingCore decoded _ st with
               h | ⟨k, hXc, hK, h⟩
             · exact Or.inl h
             · exact Or.inr ⟨tid, tcb, decoded, k, hCur, hObj, hDec, .inr ⟨hRR, hXc⟩, hK, h⟩
           · exact Or.inl rfl
         · exact Or.inl rfl)
  · exact Or.inl rfl

/-- `cancelReceiveBusyReply_cases_decoded` at the holder: the identity, or the
cancel of a holder that is not the receiving thread, which the executing core
runs. -/
theorem cancelReceiveBusyReply_cases_holder (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) :
    cancelReceiveBusyReply ctx executingCore st = st ∨
      ∃ (tid holder : SeLe4n.ThreadId), st.scheduler.currentOnCore executingCore = some tid ∧
        holder ≠ tid ∧
        cancelReceiveBusyReply ctx executingCore st = cancelReplyHolder st holder executingCore := by
  rcases cancelReceiveBusyReply_cases_decoded ctx executingCore st with
    h | ⟨tid, _, decoded, k, hCur, -, -, -, hK, h⟩
  · exact Or.inl h
  let gate : SyscallGate :=
    { callerId := tid, cspaceRootCap := callerCspaceRoot st tid, capAddr := decoded.capAddr,
      requiredRight := syscallRequiredRight .receive }
  have hC := hK gate rfl
  exact Or.inr ⟨tid, ⟨k⟩, hCur, busyReplyHolder?_ne (recvBusyReplyHolderCode_succ hC), h⟩

/-- The entry routed to a receive: `syscallEntryCheckedR_eq`'s receive case. -/
theorem syscallEntryCheckedR_eq_of_receive (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (capAddr : SeLe4n.CPtr) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hCtx : ¬ isInsecureDefaultContext ctx = true)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRecvRegs : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .receive capAddr len replyAddr) :
    syscallEntryCheckedR ctx executingCore st =
      RefusalCarrying.ofKernelReporting (cancelReceiveBusyReply ctx executingCore)
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st := by
  have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  obtain ⟨decoded, hDec, hRecv, hCap, hZero, hLen, hReplyAddr⟩ :=
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
      st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr len replyAddr hRecvRegs
  subst hCap
  simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRecvRegs, Bool.false_eq_true, ↓reduceIte]
  rw [routedExtraCapCount_eq hDec hRecv]
  rw [dispatchReceiveCheckedR_eq ctx decoded tid executingCore len replyAddr hRecv hLen
    hReplyAddr]
  simp only [RefusalCarrying.ofKernelReporting, cancelReceiveBusyReply, syscallEntryChecked, hCtx,
    hCur, hRegs, hDec, hObj, hRecvRegs, hZero, Bool.false_eq_true, ↓reduceIte, routedExtraCapCount_eq hDec hRecv]

/-- The entry routed to a short reply-receive: `syscallEntryCheckedR_eq`'s
reply-receive case, reporting the skipped reply's receive's cancel
(`replyRecvEntryReport`). -/
theorem syscallEntryCheckedR_eq_of_replyRecv (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (capAddr : SeLe4n.CPtr) (msgInfo : MessageInfo)
    (hCtx : ¬ isInsecureDefaultContext ctx = true)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRRRegs : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .replyRecv capAddr msgInfo) :
    syscallEntryCheckedR ctx executingCore st =
      RefusalCarrying.ofKernelReporting (cancelReceiveBusyReply ctx executingCore)
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st := by
  have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  obtain ⟨decoded, hDec, hRR, hCap, hZero, hInfo, hRegs'⟩ :=
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
      st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRRRegs
  subst hCap hInfo
  simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRRRegs, Bool.false_eq_true, ↓reduceIte]
  rw [routedExtraCapCount_eq hDec hRR]
  rw [dispatchReplyRecvCheckedR_eq ctx decoded tid executingCore SeLe4n.arm64DefaultLayout
    tcb.registerContext hRR hRegs'.symm]
  simp only [RefusalCarrying.ofKernelReporting, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
    hZero, hObj, hRRRegs, hRR, cancelReceiveBusyReply, replyRecvEntryReport, Bool.false_eq_true,
    ↓reduceIte]

/-- The entry routed to a long reply-receive: `syscallEntryCheckedR_eq`'s long
reply-receive case, reporting the skipped reply's receive's cancel
(`replyRecvEntryReport`). -/
theorem syscallEntryCheckedR_eq_of_replyRecvLong (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (capAddr : SeLe4n.CPtr) (msgInfo : MessageInfo)
    (hCtx : ¬ isInsecureDefaultContext ctx = true)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRRLRegs : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .replyRecvLong capAddr msgInfo) :
    syscallEntryCheckedR ctx executingCore st =
      RefusalCarrying.ofKernelReporting (cancelReceiveBusyReply ctx executingCore)
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st := by
  have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRRLRegs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hGt, hMax, -⟩ :=
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong
      st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRRLRegs
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hT : st.getTcb? tid = some tcb := by
    rw [SystemState.getObject?_eq_getElem] at hObj
    simp only [SystemState.getTcb?, hObj]
  have hn0 : 0 < msgInfo.length - 4 := by omega
  have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
    have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
    have h120 : maxMessageRegisters = 120 := rfl
    rw [h116]; rw [h120] at hMax; omega
  rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
  cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
  | error e =>
    have hD := decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo
      .replyRecv (.inr (.inl ⟨hRRLRegs, rfl⟩)) 0 hn0 e hR0
    rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
    have hE := dispatchReplyRecvCheckedR_eq ctx (clampedFrameDecode .replyRecv tcb.registerContext capAddr msgInfo)
      tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext rfl rfl
    simp only [clampedFrameDecode] at hE
    rw [congrFun hE st]
    simp only [RefusalCarrying.ofKernelReporting, syscallEntryChecked, hCtx, hCur, hRegs, hD,
      cancelReceiveBusyReply, hObj, hRRLRegs, replyRecvEntryReport,
      Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
  | ok w0 =>
    dsimp only
    have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
      hn ⟨w0, hR0⟩
    have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
      .replyRecv (.inr (.inl ⟨hRRLRegs, rfl⟩)) hRead
    rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
    simp only [RefusalCarrying.ofKernelReporting, syscallEntryChecked, hCtx, hCur, hRegs, hD,
    cancelReceiveBusyReply, hObj, hRRLRegs, replyRecvEntryReport,
      Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount]
    exact dispatchReplyRecvLongCheckedR_eq ctx
      (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo)
      tcb.registerContext capAddr tid executingCore st rfl hRRLRegs rfl hRead
      (frameOf hObj)
theorem syscallEntryCheckedR_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId) :
    syscallEntryCheckedR ctx executingCore =
      RefusalCarrying.ofKernelReporting (cancelReceiveBusyReply ctx executingCore)
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) := by
  funext st
  by_cases hR : ∃ tid tcb, ¬ isInsecureDefaultContext ctx = true ∧
      st.scheduler.currentOnCore executingCore = some tid ∧
      st.getObject? tid.toObjId = some (.tcb tcb) ∧
      ((∃ capAddr len replyAddr, SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
          SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .receive capAddr len replyAddr) ∨
        (∃ capAddr msgInfo, SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
          SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .replyRecv capAddr msgInfo) ∨
        (∃ capAddr msgInfo, SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
          SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .replyRecvLong capAddr msgInfo))
  · obtain ⟨tid, tcb, hCtx, hCur, hObj, hRoute⟩ := hR
    rcases hRoute with ⟨capAddr, len, replyAddr, hRecvRegs⟩ | ⟨capAddr, msgInfo, hRRRegs⟩ |
      ⟨capAddr, msgInfo, hRRLRegs⟩
    · exact syscallEntryCheckedR_eq_of_receive ctx executingCore st tid tcb capAddr len replyAddr
        hCtx hCur hObj hRecvRegs
    · exact syscallEntryCheckedR_eq_of_replyRecv ctx executingCore st tid tcb capAddr msgInfo
        hCtx hCur hObj hRRRegs
    · exact syscallEntryCheckedR_eq_of_replyRecvLong ctx executingCore st tid tcb capAddr msgInfo
        hCtx hCur hObj hRRLRegs
  have hFix : cancelReceiveBusyReply ctx executingCore st = st := by
    unfold cancelReceiveBusyReply
    split
    · rfl
    · next hCtx =>
      split
      · rfl
      · next tid hCur =>
        split
        · next tcb hObj =>
          split
          · next capAddr len replyAddr hRecvRegs =>
            exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inl ⟨capAddr, len, replyAddr, hRecvRegs⟩⟩ hR
          · next capAddr msgInfo hRRRegs =>
            exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inr (.inl ⟨capAddr, msgInfo, hRRRegs⟩)⟩ hR
          · next capAddr msgInfo hRRLRegs =>
            exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inr (.inr ⟨capAddr, msgInfo, hRRLRegs⟩)⟩ hR
          · rfl
        · rfl
  rw [RefusalCarrying.ofKernelReporting_of_fixed _ hFix]
  simp only [syscallEntryCheckedR]
  split
  · next hCtx => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, ↓reduceIte]
  · next hCtx =>
    split
    · next hCur => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur,
        Bool.false_eq_true, ↓reduceIte]
    · next tid hCur =>
      split
      · next tcb hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
          simp only [lookupThreadRegisterContext, hObj]
        split
        · next capAddr hSigRegs =>
          obtain ⟨decoded, hDec, hSig, hCap, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSignal
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr hSigRegs
          subst hCap
          rw [routedExtraCapCount_eq hDec hSig]
          rw [dispatchSignalCheckedR_eq ctx decoded tid executingCore hSig]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next capAddr hWaitRegs =>
          obtain ⟨decoded, hDec, hWait, hCap, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedWait
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr hWaitRegs
          subst hCap
          rw [routedExtraCapCount_eq hDec hWait]
          rw [dispatchWaitCheckedR_eq ctx decoded tid executingCore hWait]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next hYieldRegs =>
          obtain ⟨decoded, hDec, hYield, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedYield
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 hYieldRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            dispatchSyscallChecked, hYield, ne_eq, not_true_eq_false, dispatchYield,
            yieldOnCoreR_eq]
          cases yieldOnCore st executingCore <;> rfl
        · next capAddr msgInfo hSendRegs =>
          obtain ⟨decoded, hDec, hSend, hCap, hZero, -, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hSendRegs
          subst hCap
          rw [routedExtraCapCount_eq hDec hSend]
          rw [dispatchSendCheckedR_eq ctx decoded _ _ _ tid executingCore st hSend
            (frameOf hObj) (.inl hSendRegs)]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next capAddr msgInfo hCallRegs =>
          obtain ⟨decoded, hDec, hCall, hCap, hZero, -, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hCallRegs
          subst hCap
          rw [routedExtraCapCount_eq hDec hCall]
          rw [dispatchCallCheckedR_eq ctx decoded _ _ _ tid executingCore st hCall
            (frameOf hObj) (.inl hCallRegs)]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next capAddr msgInfo hReplyRegs =>
          obtain ⟨decoded, hDec, hReply, hCap, hZero, hInfo, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReply
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hReplyRegs
          subst hCap hInfo
          rw [routedExtraCapCount_eq hDec hReply]
          rw [dispatchReplyCheckedR_eq ctx decoded tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext
            hReply hRegs'.symm]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next capAddr len replyAddr hRecvRegs =>
          exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inl ⟨capAddr, len, replyAddr, hRecvRegs⟩⟩ hR
        · next capAddr msgInfo hRRRegs =>
          exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inr (.inl ⟨capAddr, msgInfo, hRRRegs⟩)⟩ hR
        · next sid capAddr hInvRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs', hLenT⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedInvoke
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hInvRegs
          subst hCap hSid
          rw [routedExtraCapCount_eq hDec rfl]
          rw [dispatchInvocationCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted (.of_eq hRegs' 4) hLenT]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next sid capAddr hCfgRegs =>
          obtain ⟨hRouted, msgInfo, hMl, hDec⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowOne
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hCfgRegs
          rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps)
            (by rw [hDec]; split <;> exact ⟨_, rfl, rfl⟩)]
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hE := dispatchShortArgsCheckedR_eq ctx
              (clampedFrameDecode sid tcb.registerContext capAddr msgInfo)
              tid executingCore (by simp [clampedFrameDecode, hRouted])
              (by simp [clampedFrameDecode, truncationMinimum_of_routedOverflowOne
                hRouted])
            simp only [clampedFrameDecode] at hE
            rw [congrFun hE st]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
              SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR,
              SeLe4n.Kernel.Architecture.RegisterDecode.clampToInline, Array.size_map,
              show SeLe4n.arm64DefaultLayout.msgRegs.size = 4 from rfl,
              Bool.false_eq_true, ↓reduceIte]
          | ok w =>
            have hD := dispatchOverflowOneCheckedR_eq ctx
              { capAddr, msgInfo, syscallId := sid,
                msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext) ++
                  #[(⟨w⟩ : RegValue)],
                inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 1 }
              tcb.registerContext w tid executingCore hRouted (.of_eq rfl 5)
              (show msgInfo.length = 5 by rw [hMl]; rfl)
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
              SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR,
              Bool.false_eq_true, ↓reduceIte]
            exact congrFun hD st
        · next capAddr msgInfo hLongRegs =>
          obtain ⟨hGt, hMax, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSendLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedSendLong_clamped st tid _ capAddr msgInfo
              hLongRegs 0 hn0 e hR0
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            have hE := dispatchSendCheckedR_eq ctx (clampedFrameDecode .send tcb.registerContext capAddr msgInfo)
              tcb.registerContext capAddr { msgInfo with length := 4 } tid executingCore st rfl
              (frameOf hObj) (.inr (.inr ⟨msgInfo, hLongRegs, rfl, 0, e, hn0, hR0⟩))
            simp only [clampedFrameDecode] at hE
            rw [hE]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
          | ok w0 =>
            dsimp only
            have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
              hn ⟨w0, hR0⟩
            have hD := decodeSyscallArgsFromState_of_routedSendLong_ok st tid _ capAddr msgInfo
              hLongRegs hRead
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, longSendDecode_overflowCount]
            exact dispatchSendCheckedR_eq ctx
              (longSendDecode st tid tcb.registerContext capAddr msgInfo)
              tcb.registerContext capAddr msgInfo tid executingCore st rfl (frameOf hObj)
              (.inr (.inl ⟨hLongRegs, hRead⟩))
        · next capAddr msgInfo hCallLongRegs =>
          obtain ⟨hGt, hMax, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCallLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hCallLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedCallLong_clamped st tid _ capAddr msgInfo
              hCallLongRegs 0 hn0 e hR0
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            have hE := dispatchCallCheckedR_eq ctx (clampedFrameDecode .call tcb.registerContext capAddr msgInfo)
              tcb.registerContext capAddr { msgInfo with length := 4 } tid executingCore st rfl
              (frameOf hObj) (.inr ⟨msgInfo, hCallLongRegs, rfl, 0, e, hn0, hR0⟩)
            simp only [clampedFrameDecode] at hE
            rw [hE]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
          | ok w0 =>
            dsimp only
            have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
              hn ⟨w0, hR0⟩
            have hD := decodeSyscallArgsFromState_of_routedCallLong_ok st tid _ capAddr msgInfo
              hCallLongRegs hRead
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, longCallDecode_overflowCount]
            exact dispatchCallLongCheckedR_eq ctx
              (longCallDecode st tid tcb.registerContext capAddr msgInfo)
              tcb.registerContext capAddr msgInfo tid executingCore st rfl (frameOf hObj)
              hCallLongRegs hRead
        · next capAddr msgInfo hReplyLongRegs =>
          obtain ⟨hGt, hMax, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hReplyLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo
              .reply (.inl ⟨hReplyLongRegs, rfl⟩) 0 hn0 e hR0
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            have hE := dispatchReplyCheckedR_eq ctx (clampedFrameDecode .reply tcb.registerContext capAddr msgInfo)
              tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext rfl rfl
            simp only [clampedFrameDecode] at hE
            rw [congrFun hE st]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
          | ok w0 =>
            dsimp only
            have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
              hn ⟨w0, hR0⟩
            have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
              .reply (.inl ⟨hReplyLongRegs, rfl⟩) hRead
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount]
            exact dispatchReplyLongCheckedR_eq ctx
              (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo)
              tcb.registerContext capAddr tid executingCore st rfl hReplyLongRegs rfl hRead
              (frameOf hObj)
        · next capAddr msgInfo hReplyRecvLongRegs =>
          exact absurd ⟨tid, tcb, hCtx, hCur, hObj, .inr (.inr ⟨capAddr, msgInfo, hReplyRecvLongRegs⟩)⟩ hR
        · next sid capAddr msgInfo hTrRegs =>
          obtain ⟨hSC, -, hMax, hShortDec, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr msgInfo hTrRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          split
          · next hShort =>
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps)
              ⟨_, hShortDec (by rw [hSz]; exact hShort), rfl⟩]
            rw [show dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext msgInfo.length
                tid executingCore (syscallExtraCapCount sid msgInfo.extraCaps) st = _ from
              dispatchTransferringCheckedR_eq ctx
                { capAddr, msgInfo, syscallId := sid,
                  msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext),
                  inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 0 }
                sid tid executingCore st rfl hSC tcb.registerContext capAddr msgInfo
                (frameOf hObj) (.inl ⟨hTrRegs, fun h => absurd hShort (by omega)⟩)]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
              hShortDec (by rw [hSz]; exact hShort), Bool.false_eq_true, ↓reduceIte]
          · next hLong =>
            have hGt : 4 < msgInfo.length := by omega
            have hRR : (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .replyLong capAddr msgInfo ∧ sid = .reply) ∨
                (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .replyRecvLong capAddr msgInfo ∧ sid = .replyRecv) ∨
                (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .transferring sid capAddr msgInfo ∧ 4 < msgInfo.length) :=
              .inr (.inr ⟨hTrRegs, hGt⟩)
            have hT : st.getTcb? tid = some tcb := by
              rw [SystemState.getObject?_eq_getElem] at hObj
              simp only [SystemState.getTcb?, hObj]
            have hn0 : 0 < msgInfo.length - 4 := by omega
            have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
              have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
              have h120 : maxMessageRegisters = 120 := rfl
              rw [h116]; rw [h120] at hMax; omega
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo
                sid hRR 0 hn0 e hR0
              rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
              have hE := dispatchTransferringCheckedR_eq ctx
                (clampedFrameDecode sid tcb.registerContext capAddr msgInfo)
                sid tid executingCore st rfl hSC tcb.registerContext capAddr
                { msgInfo with length := 4 } (frameOf hObj)
                (.inr ⟨msgInfo, hTrRegs, rfl, 0, e, hn0, hR0⟩)
              simp only [clampedFrameDecode] at hE
              rw [hE]
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
            | ok w0 =>
              dsimp only
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hn ⟨w0, hR0⟩
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
                sid hRR hRead
              rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount]
              exact dispatchTransferringCheckedR_eq ctx
                (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo)
                sid tid executingCore st rfl hSC tcb.registerContext capAddr msgInfo
                (frameOf hObj) (.inl ⟨hTrRegs, fun _ => hRead⟩)
        · next sid capAddr hAudRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs', hMIa⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedAudited
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hAudRegs
          subst hCap hSid
          rw [routedExtraCapCount_eq hDec rfl]
          rw [dispatchAuditedCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted (.of_eq hRegs' 4) (routedLength_of_decode hMIa).symm]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next sid capAddr len hOvRegs =>
          obtain ⟨msgInfo, hMI, hLenEq, hGt, hMax, hRt, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowed
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr len hOvRegs
          subst hLenEq
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedOverflowed_clamped st tid _ sid capAddr
              msgInfo hMI hOvRegs 0 hn0 e hR0
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            have hE := dispatchShortArgsCheckedR_eq ctx (clampedFrameDecode sid tcb.registerContext capAddr msgInfo)
              tid executingCore (by simp [clampedFrameDecode, hRt])
              (by simp [clampedFrameDecode, truncationMinimum_of_routedOverflowOne hRt])
            simp only [clampedFrameDecode] at hE
            rw [congrFun hE st]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, clampedFrameDecode]
          | ok w0 =>
            dsimp only
            have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
              hn ⟨w0, hR0⟩
            have hD := decodeSyscallArgsFromState_of_routedOverflowed_ok st tid _ sid capAddr
              msgInfo hMI hOvRegs hRead
            rw [routedExtraCapCount_of_msgInfo (n := msgInfo.extraCaps) ⟨_, hD, rfl⟩]
            have hW : overflowWordAt st tid 0 = w0 := by rw [overflowWordAt_eq, hR0]
            have hDisp := dispatchOverflowedCheckedR_eq ctx st tid tcb.registerContext sid
              capAddr msgInfo executingCore hRt (by omega)
            simp only [hW] at hDisp
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte, overflowedDecode_overflowCount]
            exact hDisp st
        · next sid capAddr hShortRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, -, hT⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedShortArgs
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hShortRegs
          subst hCap hSid
          rw [routedExtraCapCount_eq hDec rfl]
          rw [dispatchShortArgsCheckedR_eq ctx decoded tid executingCore hRouted hT]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte]
        · next e hRefRegs =>
          have hD := SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedRefused
            st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 e hRefRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
            Bool.false_eq_true, ↓reduceIte]
        · rfl
      · next o hNot hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .illegalState := by
          unfold lookupThreadRegisterContext; rw [hObj]
          cases o <;> first | rfl | exact absurd rfl (hNot _)
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]
      · next hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .objectNotFound := by
          simp only [lookupThreadRegisterContext, hObj]
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]


-- ============================================================================
-- The entry with its operand's failed resolution told apart
-- ============================================================================

/-- Whether a resolved slot holds no capability user space may hold
(`capHeldNone`).  Out of line, with the slot borrowed, so the entry tests the
slot without projecting its capability: the arm alone takes the capability out
of the slot, once.  An inlined test would give the compiled entry two
projections of one field ahead of the arm's reuse of the cell, a shape Lean
4.28's reset-reuse expansion releases twice. -/
@[noinline] def slotHeldNone (c : @& Option Capability) : Bool := capHeldNone c

/-- Whether a receive refuses the capability in a resolved slot at its type or
its right (`receiveGateRefuses`).  Out of line, with the slot and the state
borrowed, so the entry asks it before the arm takes the state. -/
@[noinline] def receiveSlotRefused (sid : SyscallId) (tid : SeLe4n.ThreadId) (st : @& SystemState)
    (c : @& Option Capability) : Bool :=
  match c with
  | some cap => receiveGateRefuses sid tid st cap
  | none => false

/-- Whether a resolved slot's capability is refused as seL4's `handleRecv`
refuses it, its lookup's failure rather than the arm's: `false`, with nothing
read, on every syscall that does not receive on its capability. -/
@[inline] def receiveRefusedAt (sid : SyscallId) (tid : SeLe4n.ThreadId) (st : SystemState)
    (c : Option Capability) : Bool :=
  syscallReceivesOnCap sid && receiveSlotRefused sid tid st c

theorem receiveRefusedAt_some (sid : SyscallId) (tid : SeLe4n.ThreadId) (st : SystemState)
    (cap : Capability) :
    receiveRefusedAt sid tid st (some cap) = receiveGateRefuses sid tid st cap := by
  unfold receiveRefusedAt receiveSlotRefused receiveGateRefuses
  cases syscallReceivesOnCap sid <;> rfl

/-- The arm's result on a resolved slot.  Where the slot holds no capability
user space may hold (`noCap`: an empty slot, or a capability naming a reserved
idle object, `capHeldNone`), the resolution `syscallResolveCap` fails with
`.invalidCapability`, so a refusal with that error is the resolution's, handed
to `onLookup`; any other result is the arm's, handed to `kArm`.  The arm runs
once, on the slot's contents, as `dispatchOperandCheckedR` runs it. -/
@[inline] def noCapRefusal {β : Type} (noCap : Bool)
    (kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .error (e, s) =>
    if noCap = true ∧ e = (.invalidCapability 0) then onLookup e s else kArm (.error (e, s))
  | .ok v => kArm (.ok v)

/-- The gate a receive's reply capability is looked up through: the caller's
CSpace root, the reply capability's address and the reply authority. -/
@[inline] def replyCapGate (tid : SeLe4n.ThreadId) (root : Option Capability)
    (replyAddr : SeLe4n.CPtr) : SyscallGate :=
  { callerId := tid, cspaceRootCap := root, capAddr := replyAddr, requiredRight := .write }

/-- **A receive's arm result, its reply capability's failed lookup told
apart** (seL4-MCS's `lookupReply`, `syscall.c`): on a receive that names a reply
capability (`names`), a `failedLookup` refusal that the reply capability's own
lookup through `gate` raises, re-read on the state the refusal hands back
(`lookupReplyCap`), is handed to `onReply` with its lookup fault, which the
entry raises as the receive's capability fault at the reply capability's
address (`receiveReplyFaults`); every other result is the arm's, handed to
`kArm`. -/
@[inline] def replyLookupRefusal {β : Type} (names : Bool) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr)
    (kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onReply : LookupFault → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .error (.failedLookup w lf, s) =>
    if names && !w then
      match lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s with
      | .error lf' => if lf' = lf then onReply lf s else kArm (.error (.failedLookup w lf, s))
      | .ok _ => kArm (.error (.failedLookup w lf, s))
    else kArm (.error (.failedLookup w lf, s))
  | r => kArm r

/-- A function of `replyLookupRefusal`'s result is the refusal told apart with
the function taken into each continuation. -/
theorem replyLookupRefusal_map {β γ : Type} (g : β → γ) (names : Bool) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr)
    (kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onReply : LookupFault → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    g (replyLookupRefusal names tid replyAddr kArm onReply r) =
      replyLookupRefusal names tid replyAddr (fun r => g (kArm r)) (fun lf s => g (onReply lf s)) r := by
  unfold replyLookupRefusal
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

/-- The reply capability's address a reply-receive names: its first message
register, as the arm reads it (`endpointReplyRecvCheckedArmR`). -/
@[inline] def replyRecvReplyAddr (rf : SeLe4n.RegisterFile) : SeLe4n.CPtr :=
  SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf
    (SeLe4n.arm64DefaultLayout.msgRegs[0]'(Nat.lt_of_lt_of_eq (by decide : 0 < 4) rfl)))

/-- **`dispatchOperandCheckedR`, continued**: a refusal before the operand's
resolution is handed to `kPre`; a resolution that fails as `syscallResolveCap`
fails -- the address not resolving, or the slot holding no capability user
space may hold -- is handed to `onLookup` with the operand's address, its
error and the state the refusal carries; an extra capability whose lookup
fails (`extraCapsLookupK`, seL4's `lookupExtraCaps`) is handed to `onLookup`
with its own address and `.failedLookup false`; a receive's capability of the
wrong type or without its right likewise, at the operand's address; and the
arm's result on a capability the operand resolved to is handed to `kArm`
(`dispatchOperandCheckedK_spec`).  The entry delivers a lookup failure as a
capability fault from the words it already has, the address and the error, so
each lookup runs once. -/
@[inline] def dispatchOperandCheckedK {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (xc : Nat)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : SeLe4n.CPtr → KernelError → SystemState → β) : β :=
  if !(st.scheduler.currentOnCore executingCore).isEqSome tid then
    kPre (.error (.illegalState, st))
  else
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    lookupSlotK tcb capAddr st
      (fun t a b c => onLookup capAddr (.failedLookup false (LookupFault.ofWords t a b c)) st)
      (fun cnode slot =>
        let c := SystemState.lookupSlotCap st { cnode := cnode, slot := slot }
        -- seL4's `lookupExtraCaps`, after `lookupCapAndSlot` and before the
        -- invocation's decode; a receive-phase syscall looks none up
        extraCapsLookupK st tcb xc
          (fun cptr t a b c' =>
            onLookup cptr (.failedLookup false (LookupFault.ofWords t a b c')) st)
          (fun _ =>
            -- a slot holding no capability user space may hold is refused
            -- without running the arm: the receive's capability fault
            -- (seL4 `handleRecv`), any other syscall's `InvalidCapability`
            -- error (seL4 `decodeInvocation` on the null capability)
            if slotHeldNone c then
              if syscallReceivesOnCap sid then onLookup capAddr (.invalidCapability 0) st
              else kArm (.error (.invalidCapability 0, st))
            else
              -- a receive's capability of the wrong type or without its right
              -- is the lookup's failure (seL4 `handleRecv`), asked before the
              -- arm takes the state; the arm runs once on either branch
              let k := fun noCap => noCapRefusal noCap kArm (onLookup capAddr) (arm c st)
              if receiveRefusedAt sid tid st c then k true else k false))
  | some _ => kPre (.error (.illegalState, st))
  | none => kPre (.error (.objectNotFound, st))

/-- **What `dispatchOperandCheckedK` hands on.**  Either the refusal before the
resolution, as `dispatchOperandCheckedR` returns it; or, the caller's TCB and
CSpace root found, the arm's result, every refusal of which differs from any
error the lookup raises; or the lookup's failure (`syscallOperandLookup`), at
the address that failed, its error the one `dispatchOperandCheckedR` refuses
with. -/
theorem dispatchOperandCheckedK_spec {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (xc : Nat)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : SeLe4n.CPtr → KernelError → SystemState → β) (rr : AccessRight) :
    (dispatchOperandCheckedK sid capAddr tid executingCore xc arm st kPre kArm onLookup =
        kPre (dispatchOperandCheckedR capAddr tid executingCore xc arm st) ∧
      ∀ tcb, st.scheduler.currentOnCore executingCore = some tid →
        st.getObject? tid.toObjId ≠ some (.tcb tcb)) ∨
      ∃ tcb, st.getObject? tid.toObjId = some (.tcb tcb) ∧
        ((dispatchOperandCheckedK sid capAddr tid executingCore xc arm st kPre kArm onLookup =
            kArm (dispatchOperandCheckedR capAddr tid executingCore xc arm st) ∧
          ∀ ke s, dispatchOperandCheckedR capAddr tid executingCore xc arm st = .error (ke, s) →
            ∀ a e, syscallOperandLookup sid ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ xc st =
              .error (a, e) → e ≠ ke) ∨
         ∃ a e s, dispatchOperandCheckedK sid capAddr tid executingCore xc arm st kPre kArm
            onLookup = onLookup a e s ∧
          dispatchOperandCheckedR capAddr tid executingCore xc arm st = .error (e, s) ∧
          syscallOperandLookup sid ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ xc st =
            .error (a, e)) := by
  unfold dispatchOperandCheckedK dispatchOperandCheckedR
  by_cases hc : (!(st.scheduler.currentOnCore executingCore).isEqSome tid) = true
  · rw [if_pos hc, if_pos hc]
    refine .inl ⟨rfl, fun _ hCur => absurd hc ?_⟩
    simp only [(threadId_isEqSome_iff _ _).2 hCur, Bool.not_true, Bool.false_eq_true,
      not_false_eq_true]
  rw [if_neg hc, if_neg hc]
  cases hObj : st.getObject? tid.toObjId with
  | none => exact .inl ⟨rfl, fun _ _ h => by cases h⟩
  | some o =>
  cases o <;> (try dsimp only) <;> try exact .inl ⟨rfl, fun _ _ h => by cases h⟩
  rename_i tcb
  refine .inr ⟨tcb, rfl, ?_⟩
  have hXf : callerExtraCapsFault? st tid xc = extraCapsLookupFault? st tcb xc :=
    callerExtraCapsFault?_of_tcb hObj xc
  simp only [lookupSlotK_eq]
  cases hRes : lookupSlot tcb capAddr st with
  | error f =>
    simp only [LookupFault.ofWords_word]
    exact .inr ⟨_, _, st, rfl, rfl, by
      simp only [syscallOperandLookup, syscallResolveCap, SyscallGate.lookupSlot_mk, hRes]⟩
  | ok ref =>
    obtain ⟨cn, sl⟩ := ref
    dsimp only
    rw [extraCapsLookupK_eq]
    cases hX : lookupExtraCaps st tcb xc with
    | error p =>
      obtain ⟨cptr, f⟩ := p
      have hF : extraCapsLookupFault? st tcb xc = some (cptr, f) := by
        simp only [extraCapsLookupFault?, hX]
      simp only [hF, LookupFault.ofWords_word]
      refine .inr ⟨cptr, _, st, rfl, rfl, ?_⟩
      cases hC : SystemState.lookupSlotCap st { cnode := cn, slot := sl } with
      | none =>
        simp only [syscallOperandLookup, syscallResolveCap, SyscallGate.lookupSlot_mk, hRes, hC,
          hXf, hF]
      | some cap =>
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true <;>
          simp only [syscallOperandLookup, syscallResolveCap, SyscallGate.lookupSlot_mk, hRes, hC,
            hXf, hF, hIdle, ↓reduceIte, Bool.false_eq_true]
    | ok refs =>
      have hF : extraCapsLookupFault? st tcb xc = none := by
        simp only [extraCapsLookupFault?, hX]
      simp only [hF]
      by_cases hN : capHeldNone (SystemState.lookupSlotCap st { cnode := cn, slot := sl }) = true
      · rw [if_pos (by simpa only [slotHeldNone] using hN), if_pos hN]
        have hLk : syscallOperandLookup sid ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ xc st =
            if syscallReceivesOnCap sid then .error (capAddr, .invalidCapability 0) else .ok () := by
          revert hN
          cases hC : SystemState.lookupSlotCap st { cnode := cn, slot := sl } with
          | none =>
            intro _
            simp only [syscallOperandLookup, syscallResolveCap, SyscallGate.lookupSlot_mk, hRes,
              hC, hXf, hF]
          | some cap =>
            intro hN
            simp only [capHeldNone] at hN
            simp only [syscallOperandLookup, syscallResolveCap, SyscallGate.lookupSlot_mk, hRes,
              hC, hN, ↓reduceIte, hXf, hF]
        by_cases hRecv : syscallReceivesOnCap sid = true
        · rw [if_pos hRecv]
          exact .inr ⟨capAddr, .invalidCapability 0, st, rfl, rfl, by rw [hLk, if_pos hRecv]⟩
        · rw [if_neg hRecv]
          refine .inl ⟨rfl, fun ke s _ a e h => ?_⟩
          rw [hLk, if_neg hRecv] at h
          cases h
      rw [if_neg (by simpa only [slotHeldNone] using hN), if_neg hN]
      obtain ⟨cap, hC, hIdle⟩ : ∃ cap, SystemState.lookupSlotCap st { cnode := cn, slot := sl } =
          some cap ∧ SeLe4n.Kernel.capTargetsReservedKernelObject cap = false := by
        revert hN
        cases SystemState.lookupSlotCap st { cnode := cn, slot := sl } with
        | none => intro hN; exact absurd rfl hN
        | some cap => intro hN; exact ⟨cap, rfl, by simpa only [capHeldNone, Bool.not_eq_true] using hN⟩
      have hResolve : syscallResolveCap ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ st = .ok (cap, st) := by
        simp only [syscallResolveCap, SyscallGate.lookupSlot_mk, hRes, hC, hIdle, Bool.false_eq_true,
          ↓reduceIte]
      simp only [hC]
      -- the receive's refusal flag
      obtain ⟨noCap, hK, hLk⟩ : ∃ noCap : Bool,
          (if receiveRefusedAt sid tid st (some cap) = true then
              noCapRefusal true kArm (onLookup capAddr) (arm (some cap) st)
            else noCapRefusal false kArm (onLookup capAddr) (arm (some cap) st)) =
            noCapRefusal noCap kArm (onLookup capAddr) (arm (some cap) st) ∧
          (noCap = true → syscallOperandLookup sid
            ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ xc st = .error (capAddr, .invalidCapability 0)) ∧
          (∀ a e, syscallOperandLookup sid ⟨tid, tcb.spaceCells[0], capAddr, rr⟩ xc st =
            .error (a, e) → noCap = true ∧ a = capAddr ∧ e = (.invalidCapability 0)) := by
        rw [receiveRefusedAt_some]
        by_cases hG : receiveGateRefuses sid tid st cap = true
        · refine ⟨true, by simp [hG], fun _ => ?_, fun a e h => ?_⟩
          · simp only [syscallOperandLookup, hResolve, hXf, hF, hG, ↓reduceIte]
          · simp only [syscallOperandLookup, hResolve, hXf, hF, hG, ↓reduceIte,
              Except.error.injEq, Prod.mk.injEq] at h
            exact ⟨rfl, h.1.symm, h.2.symm⟩
        · refine ⟨false, by simp [hG], (fun h => nomatch h), fun a e h => ?_⟩
          simp [syscallOperandLookup, hResolve, hXf, hF, hG] at h
      rw [hK]
      unfold noCapRefusal
      rcases hA : arm (some cap) st with ⟨e, s⟩ | v <;> (try dsimp only)
      · by_cases hX2 : noCap = true ∧ e = (.invalidCapability 0)
        · rw [if_pos hX2]
          refine .inr ⟨capAddr, e, s, rfl, rfl, ?_⟩
          rw [hX2.2]; exact hLk.1 hX2.1
        · rw [if_neg hX2]
          refine .inl ⟨rfl, fun ke s' h a e' h' => ?_⟩
          cases h
          obtain ⟨hN', -, hE⟩ := hLk.2 a e' h'
          subst hE
          exact fun h => hX2 ⟨hN', h.symm⟩
      · exact .inl ⟨rfl, fun ke s' h => by cases h⟩

/-- **The one-overflow-word route's operand arm**: the configure's, the
service register's or the CNode copy's, with its fifth word `w`, and the CNode
mint's refusal short of its sixth; no other syscall is routed here
(`routedOverflowOne`, `dispatchOverflowOneCheckedR_eq_operand`). -/
@[inline] def overflowOneOperandArmR (ctx : LabelingContext) (sid : SyscallId)
    (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) (xc : Nat) :
    Option Capability → RefusalCarrying Unit :=
  match sid with
  | .serviceRegister => serviceRegisterOperandArmR ctx tid xc regs w
  | .cspaceCopy => copyOperandArmR ctx tid xc regs w
  | .cspaceMint => shortArgsOperandArmR .cspaceMint
  | .untypedRetype => shortArgsOperandArmR .untypedRetype
  | _ => configureOperandArmR regs w tid xc

theorem dispatchOverflowOneCheckedR_eq_operand (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat)
    (h : Architecture.RegisterDecode.routedOverflowOne sid = true) :
    dispatchOverflowOneCheckedR ctx sid capAddr regs w tid executingCore xc =
      dispatchOperandCheckedR capAddr tid executingCore xc
        (overflowOneOperandArmR ctx sid regs w tid xc) := by
  cases sid <;> first | (cases h; done) | rfl

/-- A function of `ipcBufferReadMrK`'s result is the read with the function
taken into each continuation. -/
theorem ipcBufferReadMrK_comp {α β : Type} (f : α → β) (st : SystemState) (tid : SeLe4n.ThreadId)
    (idx : Nat) (err : SeLe4n.Kernel.Architecture.IpcBufferRead.IpcBufferReadError → α)
    (ok : UInt64 → α) :
    f (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid idx err ok) =
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid idx (fun e => f (err e))
        (fun w => f (ok w)) := by
  rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq,
    SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
  cases SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid idx <;> rfl

/-- **`syscallEntryCheckedR`, continued, its operand's failed resolution told
apart** (`syscallEntryCheckedK_spec`): each call routed to an operand dispatch
runs `dispatchOperandCheckedK`, which hands a failed resolution to `kLook`
with the syscall, the operand's address and the error, and the arm's result
on a resolved operand to `kRes`; every other result -- a refusal before the
resolution, and every call not routed to an operand dispatch -- is handed to
`kGen` as `syscallEntryCheckedR` returns it.  The routing, the arms and the
resolution are `syscallEntryCheckedR`'s own.

A specification too: compiled, it is the dispatch over the out-of-line arms
(`syscallEntryRoutedK`, through `syscallEntryCheckedK_eq_routed`), so an entry
that inlines it holds one dispatch rather than every arm, and no code is
generated for this form. -/
noncomputable def syscallEntryCheckedK {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) : β :=
  if isInsecureDefaultContext ctx then kGen (.error (.policyDenied, st))
  else
  match st.scheduler.currentOnCore executingCore with
  | none => kGen (.error (.illegalState, st))
  | some tid =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
              SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
      | .signal capAddr =>
        dispatchOperandCheckedK .notificationSignal capAddr tid executingCore (routedExtraCapCount .notificationSignal tcb.registerContext)
          (signalOperandArmThenTaintR ctx tid executingCore
            (syscallRequiredRight .notificationSignal)) st kGen kRes
          (kLook .notificationSignal)
      | .wait capAddr =>
        dispatchOperandCheckedK .notificationWait capAddr tid executingCore (routedExtraCapCount .notificationWait tcb.registerContext)
          (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
          st kGen kRes (kLook .notificationWait)
      | .yield =>
        kGen (match yieldOnCoreR st executingCore with
          | .error r => .error r
          | .ok st' => .ok ((), st'))
      | .send capAddr msgInfo =>
        dispatchOperandCheckedK .send capAddr tid executingCore (routedExtraCapCount .send tcb.registerContext)
          (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .send)) st kGen kRes
          (kLook .send)
      | .call capAddr msgInfo =>
        dispatchOperandCheckedK .call capAddr tid executingCore (routedExtraCapCount .call tcb.registerContext)
          (callOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .call)) st kGen kRes
          (kLook .call)
      | .reply capAddr msgInfo =>
        dispatchOperandCheckedK .reply capAddr tid executingCore (routedExtraCapCount .reply tcb.registerContext)
          (replyOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length msgInfo.extraCaps msgInfo.label tid executingCore
            (syscallRequiredRight .reply)) st kGen kRes (kLook .reply)
      | .receive capAddr len replyAddr =>
        dispatchOperandCheckedK .receive capAddr tid executingCore (routedExtraCapCount .receive tcb.registerContext)
          (receiveOperandArmThenTaintR ctx tid len replyAddr executingCore
            (syscallRequiredRight .receive)) st kGen
          (replyLookupRefusal (len != 0) tid replyAddr kRes
            (fun lf s => kLook .receive replyAddr (.failedLookup false lf) s))
          (kLook .receive)
      | .replyRecv capAddr msgInfo =>
        dispatchOperandCheckedK .replyRecv capAddr tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext)
          (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length msgInfo.extraCaps msgInfo.label tid executingCore
            (syscallRequiredRight .replyRecv)) st kGen
          (replyLookupRefusal (msgInfo.length != 0) tid (replyRecvReplyAddr tcb.registerContext) kRes
            (fun lf s => kLook .replyRecv (replyRecvReplyAddr tcb.registerContext)
              (.failedLookup false lf) s))
          (kLook .replyRecv)
      | .invoke sid capAddr =>
        dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
          (invocationOperandArmR ctx sid capAddr (routedExtraCapCount sid tcb.registerContext) tcb.registerContext tid executingCore) st kGen
          kRes (kLook sid)
      | .overflowOne sid capAddr =>
        -- the continuations taken into both of the read's, so each is a tail
        -- call the compiled read jumps to (`ipcBufferReadMrK_comp`); the
        -- dispatch's refusals reach `kRes` and `kLook` as the entry found them
        -- (`dispatchOperandCheckedK_spec`).
        SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
            (fun _ => dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) (shortArgsOperandArmR sid)
              st kGen kRes (kLook sid))
            (fun w => dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
              (overflowOneOperandArmR ctx sid tcb.registerContext w tid (routedExtraCapCount sid tcb.registerContext)) st kGen kRes
              (kLook sid))
      | .sendLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK .send capAddr tid executingCore (routedExtraCapCount .send tcb.registerContext)
                (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext 4 tid
                  executingCore (syscallRequiredRight .send)) st kGen kRes (kLook .send))
              (fun _ => dispatchOperandCheckedK .send capAddr tid executingCore (routedExtraCapCount .send tcb.registerContext)
                    (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight .send))
                    st kGen kRes (kLook .send))
      | .callLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK .call capAddr tid executingCore (routedExtraCapCount .call tcb.registerContext)
                (callOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext 4 tid
                  executingCore (syscallRequiredRight .call)) st kGen kRes (kLook .call))
              (fun _ => dispatchOperandCheckedK .call capAddr tid executingCore (routedExtraCapCount .call tcb.registerContext)
                    (callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight .call))
                    st kGen kRes (kLook .call))
      | .replyLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK .reply capAddr tid executingCore (routedExtraCapCount .reply tcb.registerContext)
                (replyOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext 4
                  msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .reply))
                st kGen kRes (kLook .reply))
              (fun _ => dispatchOperandCheckedK .reply capAddr tid executingCore (routedExtraCapCount .reply tcb.registerContext)
                    (replyLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .reply))
                    st kGen kRes (kLook .reply))
      | .replyRecvLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK .replyRecv capAddr tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext)
                (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext 4
                  msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .replyRecv))
                st kGen
                (replyLookupRefusal true tid (replyRecvReplyAddr tcb.registerContext) kRes
                  (fun lf s => kLook .replyRecv (replyRecvReplyAddr tcb.registerContext)
                    (.failedLookup false lf) s))
                (kLook .replyRecv))
              (fun _ => dispatchOperandCheckedK .replyRecv capAddr tid executingCore (routedExtraCapCount .replyRecv tcb.registerContext)
                    (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore
                      (syscallRequiredRight .replyRecv))
                    st kGen
                    (replyLookupRefusal true tid (replyRecvReplyAddr tcb.registerContext) kRes
                      (fun lf s => kLook .replyRecv (replyRecvReplyAddr tcb.registerContext)
                        (.failedLookup false lf) s))
                    (kLook .replyRecv))
      | .transferring sid capAddr msgInfo =>
        if msgInfo.length ≤ 4 then
          dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
            (transferringOperandArmThenTaintR ctx sid tcb.registerContext msgInfo.length tid
              executingCore (syscallRequiredRight sid))
            st kGen kRes (kLook sid)
        else
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
                (transferringOperandArmThenTaintR ctx sid tcb.registerContext 4 tid
                  executingCore (syscallRequiredRight sid)) st kGen kRes (kLook sid))
              (fun _ => dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
                    (transferringOperandArmThenTaintR ctx sid tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight sid))
                    st kGen kRes (kLook sid))
      | .audited sid capAddr =>
        dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
          (auditedOperandArmR ctx sid tcb.registerContext capAddr tid executingCore
            (routedExtraCapCount sid tcb.registerContext)) st kGen kRes
          (kLook sid)
      | .overflowed sid capAddr len =>
          -- a five-word invocation behind the long route's operand dispatch,
          -- its refusals handed to `kRes` and `kLook` as the dispatch told them
          -- apart (`dispatchOperandCheckedK_spec`), so none is resolved again; one whose
          -- overflow slot does not read is clamped to its inline words and
          -- refused short of its arguments, as seL4's `handleInvocation`
          -- clamps a message with no IPC buffer.
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) (shortArgsOperandArmR sid)
                st kGen kRes (kLook sid))
              (fun w =>
                    dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext)
                      (overflowedArmOf ctx sid tcb.registerContext w (overflowWordAt st tid 1)
                        (overflowWordAt st tid 2) len tid executingCore capAddr
                        (routedExtraCapCount sid tcb.registerContext))
                      st kGen kRes (kLook sid))
      | .shortArgs sid capAddr =>
        dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) (shortArgsOperandArmR sid) st kGen kRes
          (kLook sid)
      | .refused e => kGen (.error (e, st))
      | .viaDecode =>
        kGen (RefusalCarrying.ofKernel
          (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
    | some _ => kGen (.error (.illegalState, st))
    | none => kGen (.error (.objectNotFound, st))

/-- The decode facts a capability fault reads: the caller current, its TCB, its
saved frame's decode and its CSpace root, and what the continued entry handed
on -- the arm's result, every refusal of which differs from any error the
operand's resolution raises and names no reply capability's fault; or the
resolution's failure, refused alike; or a receive's reply capability's failed
lookup (`receiveReplyFaults`), raised at the reply capability's address. -/
def EntryOperandOutcome {β : Type} (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) (result : β) : Prop :=
  ∃ tid tcb decoded,
    st.scheduler.currentOnCore executingCore = some tid ∧
    st.getObject? tid.toObjId = some (.tcb tcb) ∧
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
    ((result = kRes (syscallEntryCheckedR ctx executingCore st) ∧
      ∀ ke s, syscallEntryCheckedR ctx executingCore st = .error (ke, s) → (∀ a e,
        syscallOperandLookup decoded.syscallId ⟨tid, tcb.spaceCells[0], decoded.capAddr,
          syscallRequiredRight decoded.syscallId⟩
          (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st =
            .error (a, e) → e ≠ ke) ∧
        receiveReplyFaults ⟨tid, callerCspaceRoot s tid, decoded.capAddr,
          syscallRequiredRight decoded.syscallId⟩ decoded s ke = none) ∨
     (∃ a e s, result = kLook decoded.syscallId a e s ∧
      syscallEntryCheckedR ctx executingCore st = .error (e, s) ∧
      syscallOperandLookup decoded.syscallId ⟨tid, tcb.spaceCells[0], decoded.capAddr,
        syscallRequiredRight decoded.syscallId⟩
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st = .error (a, e)) ∨
     ∃ ke s replyAddr lf, result = kLook decoded.syscallId replyAddr (.failedLookup false lf) s ∧
      syscallEntryCheckedR ctx executingCore st = .error (ke, s) ∧
      (∀ a e, syscallOperandLookup decoded.syscallId ⟨tid, tcb.spaceCells[0], decoded.capAddr,
          syscallRequiredRight decoded.syscallId⟩
          (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st =
            .error (a, e) → e ≠ ke) ∧
      receiveReplyFaults ⟨tid, callerCspaceRoot s tid, decoded.capAddr,
        syscallRequiredRight decoded.syscallId⟩ decoded s ke = some (replyAddr, lf))

/-- One routed operand dispatch's share of `syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_dispatch {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (hNR : syscallNamesReply sid = false)
    (arm : Option Capability → RefusalCarrying Unit)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid)
    (hR : syscallEntryCheckedR ctx executingCore st =
      dispatchOperandCheckedR decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st) :
    dispatchOperandCheckedK sid decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen kRes
        (kLook sid) = kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (dispatchOperandCheckedK sid decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen kRes
          (kLook sid)) := by
  rw [routedExtraCapCount_eq hDec hSid] at hR ⊢
  rw [hR]
  subst hSid
  rcases dispatchOperandCheckedK_spec decoded.syscallId decoded.capAddr tid executingCore _ arm st kGen kRes
      (kLook decoded.syscallId) (syscallRequiredRight decoded.syscallId) with
    h | ⟨tcb', hObj', h⟩
  · exact .inl h.1
  · rw [hObj] at hObj'
    cases hObj'
    have hNone' : ∀ g s ke, receiveReplyFaults g decoded s ke = none := fun g s ke => by
      exact receiveReplyFaults_none_of_namesReply g decoded s ke hNR
    rcases h with ⟨hK, hNe⟩ | hL
    · exact .inr ⟨tid, tcb, decoded, hCur, hObj, hDec, .inl ⟨by rw [hR]; exact hK,
        fun ke s hE => ⟨hNe ke s (by rw [← hR]; exact hE), hNone' _ s ke⟩⟩⟩
    · exact .inr ⟨tid, tcb, decoded, hCur, hObj, hDec, .inr (.inl (by rw [hR]; exact hL))⟩

/-- `replyLookupRefusal` either hands a receive's `failedLookup` refusal to its
reply continuation, or hands its result on unchanged, no refusal of which is a
`failedLookup` it was asked to tell apart. -/
theorem replyLookupRefusal_cases {β : Type} (names : Bool) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr)
    (kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onReply : LookupFault → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    (∃ lf s, names = true ∧ r = .error (.failedLookup false lf, s) ∧
        lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s = .error lf ∧
        replyLookupRefusal names tid replyAddr kArm onReply r = onReply lf s) ∨
      (replyLookupRefusal names tid replyAddr kArm onReply r = kArm r ∧
        ∀ ke s, r = .error (ke, s) → names = true → ∀ lf,
          lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s = .error lf → ke ≠ .failedLookup false lf) := by
  unfold replyLookupRefusal
  split
  · next w lf s =>
    cases names
    · exact .inr ⟨rfl, fun _ _ _ h => nomatch h⟩
    · cases w
      · simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
        cases hL : lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s with
        | error lf' =>
          by_cases hEq : lf' = lf
          · subst hEq; exact .inl ⟨lf', s, by simp, by simp, hL, by simp⟩
          · refine .inr ⟨by simp [hEq], fun ke s' hr _ lf'' hL' hke => ?_⟩
            cases hr
            simp only [KernelError.failedLookup.injEq, true_and] at hke
            subst hke
            rw [hL] at hL'; cases hL'; exact hEq rfl
        | ok _ =>
          refine .inr ⟨rfl, fun ke s' hr _ lf'' hL' _ => ?_⟩
          cases hr; rw [hL] at hL'; cases hL'
      · refine .inr ⟨rfl, fun ke s' hr _ lf' _ hke => ?_⟩
        cases hr; cases hke
  · next r hNot =>
    refine .inr ⟨rfl, fun ke s hr _ lf _ hke => ?_⟩
    subst hr hke
    exact hNot false lf s rfl

/-- A receive route's arm result, its reply capability's failed lookup told
apart (`replyLookupRefusal`), is the outcome `EntryOperandOutcome` names: the
address the route hands the fault is the one `receiveReplyAddr?` reads, and the
lookup it re-reads is the one `receiveReplyFaults` reads. -/
theorem entryOperandOutcome_of_replyArm {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (names : Bool)
    (replyAddr : SeLe4n.CPtr) (result : β)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hRA : names = true → receiveReplyAddr? decoded = some replyAddr)
    (hRN : names = false → receiveReplyAddr? decoded = none)
    (h : (result = replyLookupRefusal names tid replyAddr kRes
            (fun lf s => kLook decoded.syscallId replyAddr (.failedLookup false lf) s)
            (syscallEntryCheckedR ctx executingCore st) ∧
          ∀ ke s, syscallEntryCheckedR ctx executingCore st = .error (ke, s) → ∀ a e,
            syscallOperandLookup decoded.syscallId ⟨tid, tcb.spaceCells[0], decoded.capAddr,
              syscallRequiredRight decoded.syscallId⟩ (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st =
                .error (a, e) → e ≠ ke) ∨
        ∃ a e s, result = kLook decoded.syscallId a e s ∧
          syscallEntryCheckedR ctx executingCore st = .error (e, s) ∧
          syscallOperandLookup decoded.syscallId ⟨tid, tcb.spaceCells[0], decoded.capAddr,
            syscallRequiredRight decoded.syscallId⟩ (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st = .error (a, e)) :
    EntryOperandOutcome ctx executingCore st kRes kLook result := by
  -- The reply capability's lookup is re-read on the state the refusal hands
  -- back, from that state's own CSpace root, as `replyLookupRefusal` reads it.
  have hRF : ∀ s ke, names = true →
      receiveReplyFaults ⟨tid, callerCspaceRoot s tid, decoded.capAddr,
          syscallRequiredRight decoded.syscallId⟩ decoded s ke =
        match lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s with
        | .error lf => if ke = .failedLookup false lf then some (replyAddr, lf) else none
        | .ok _ => none := by
    intro s ke hn
    unfold receiveReplyFaults receiveReplyFault?
    rw [hRA hn]
    dsimp only
    have hC := lookupReplyCap_congr (st := s)
      { callerId := tid, cspaceRootCap := callerCspaceRoot s tid, capAddr := replyAddr,
        requiredRight := syscallRequiredRight decoded.syscallId }
      (replyCapGate tid (callerCspaceRoot s tid) replyAddr) rfl rfl rfl
    rw [hC]
    cases lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s <;> rfl
  rcases h with ⟨hK, hNe⟩ | hL
  · rcases replyLookupRefusal_cases names tid replyAddr kRes
        (fun lf s => kLook decoded.syscallId replyAddr (.failedLookup false lf) s)
        (syscallEntryCheckedR ctx executingCore st) with
      ⟨lf, s, hn, hE, hLk, hEq⟩ | ⟨hEq, hNot⟩
    · refine ⟨tid, tcb, decoded, hCur, hObj, hDec, .inr (.inr ⟨_, s, replyAddr, lf,
        by rw [hK, hEq], hE, hNe _ s hE, ?_⟩)⟩
      rw [hRF s _ hn, hLk]; simp
    · refine ⟨tid, tcb, decoded, hCur, hObj, hDec, .inl ⟨by rw [hK, hEq],
        fun ke s hE => ⟨hNe ke s hE, ?_⟩⟩⟩
      cases names with
      | false =>
        unfold receiveReplyFaults receiveReplyFault?
        rw [hRN rfl]
      | true =>
        rw [hRF s ke rfl]
        cases hLk : lookupReplyCap (replyCapGate tid (callerCspaceRoot s tid) replyAddr) s with
        | ok _ => rfl
        | error lf => simp [hNot ke s hE rfl lf hLk]
  · exact ⟨tid, tcb, decoded, hCur, hObj, hDec, .inr (.inl hL)⟩

/-- A receive or reply-receive whose message declares its first register names
the reply capability that register holds. -/
theorem receiveReplyAddr?_of_msgReg0 (decoded : SyscallDecodeResult) (r : SeLe4n.CPtr)
    (hLen : decoded.msgInfo.length ≠ 0)
    (hSid : decoded.syscallId = .receive ∨ decoded.syscallId = .replyRecv)
    (h0 : decoded.msgRegs[0]? = some ⟨r.word⟩) :
    receiveReplyAddr? decoded = some r := by
  have hR : SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg decoded.msgRegs 0 =
      .ok ⟨r.word⟩ := by
    rw [Array.getElem?_eq_some_iff] at h0
    obtain ⟨hs, hv⟩ := h0
    simp only [SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg, hs, ↓reduceDIte, hv]
  have hL : (decoded.msgInfo.length == 0) = false := by simp [hLen]
  unfold receiveReplyAddr?
  rcases hSid with hS | hS <;>
    simp only [hL, hS, Bool.false_eq_true, ↓reduceIte,
      SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeRecvArgs,
      SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeReplyRecvArgs, hR, bind, Except.bind,
      pure, Except.pure, SeLe4n.RegValue.val_mk, SeLe4n.CPtr.ofNat_word_toNat]

/-- The reply-receive's first message register holds the reply capability's
address `replyRecvReplyAddr` reads. -/
theorem replyRecvReplyAddr_msgReg0 (rf : SeLe4n.RegisterFile) :
    (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf))[0]? =
      some ⟨(replyRecvReplyAddr rf).word⟩ := by
  simp only [Array.getElem?_map, replyRecvReplyAddr, readReg_eq_word]
  rfl

/-- …and so does the long frame's merge, whose inline registers come first. -/
theorem replyRecvReplyAddr_longMsgReg0 (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (longMessageDecode .replyRecv st tid rf capAddr mi).msgRegs[0]? =
      some ⟨(replyRecvReplyAddr rf).word⟩ := by
  simp only [longMessageDecode]
  rw [Array.getElem?_append_left (by simp [Architecture.regMessageRegs]; decide)]
  exact replyRecvReplyAddr_msgReg0 rf

/-- A receive route's operand dispatch, its reply capability's failed lookup
told apart, and its share of `syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_replyDispatch {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (arm : Option Capability → RefusalCarrying Unit) (names : Bool) (replyAddr : SeLe4n.CPtr)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid)
    (hR : syscallEntryCheckedR ctx executingCore st =
      dispatchOperandCheckedR decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st)
    (hRA : names = true → receiveReplyAddr? decoded = some replyAddr)
    (hRN : names = false → receiveReplyAddr? decoded = none) :
    (dispatchOperandCheckedK sid decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen
        (replyLookupRefusal names tid replyAddr kRes
          (fun lf s => kLook sid replyAddr (.failedLookup false lf) s))
        (kLook sid) = kGen (syscallEntryCheckedR ctx executingCore st) ∧
      ∀ tcb, st.scheduler.currentOnCore executingCore = some tid →
        st.getObject? tid.toObjId ≠ some (.tcb tcb)) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (dispatchOperandCheckedK sid decoded.capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen
          (replyLookupRefusal names tid replyAddr kRes
            (fun lf s => kLook sid replyAddr (.failedLookup false lf) s))
          (kLook sid)) := by
  rw [routedExtraCapCount_eq hDec hSid] at hR ⊢
  rw [hR]
  subst hSid
  rcases dispatchOperandCheckedK_spec decoded.syscallId decoded.capAddr tid executingCore _ arm st
      kGen (replyLookupRefusal names tid replyAddr kRes
        (fun lf s => kLook decoded.syscallId replyAddr (.failedLookup false lf) s))
      (kLook decoded.syscallId) (syscallRequiredRight decoded.syscallId) with
    h | ⟨tcb', hObj', h⟩
  · exact .inl h
  · rw [hObj] at hObj'
    cases hObj'
    exact .inr (entryOperandOutcome_of_replyArm ctx executingCore st kRes kLook tid tcb decoded
      names replyAddr _ hCur hObj hDec hRA hRN (by rw [hR]; exact h))

/-- The reply-receive's long route, its reply capability's failed lookup told
apart, and its share of `syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_replyLong {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (arm : Option Capability → RefusalCarrying Unit)
    (replyAddr : SeLe4n.CPtr)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid) (hCap : decoded.capAddr = capAddr)
    (hR : syscallEntryCheckedR ctx executingCore st =
      dispatchOperandCheckedR capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st)
    (hRA : receiveReplyAddr? decoded = some replyAddr) :
    (dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen
        (replyLookupRefusal true tid replyAddr kRes
          (fun lf s => kLook sid replyAddr (.failedLookup false lf) s))
        (kLook sid) = kGen (syscallEntryCheckedR ctx executingCore st) ∧
      ∀ tcb, st.scheduler.currentOnCore executingCore = some tid →
        st.getObject? tid.toObjId ≠ some (.tcb tcb)) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (dispatchOperandCheckedK sid capAddr tid executingCore (routedExtraCapCount sid tcb.registerContext) arm st kGen
          (replyLookupRefusal true tid replyAddr kRes
            (fun lf s => kLook sid replyAddr (.failedLookup false lf) s))
          (kLook sid)) := by
  rw [routedExtraCapCount_eq hDec hSid] at hR ⊢
  rw [hR]
  subst hSid hCap
  rcases dispatchOperandCheckedK_spec decoded.syscallId decoded.capAddr tid executingCore _ arm st kGen
      (replyLookupRefusal true tid replyAddr kRes
        (fun lf s => kLook decoded.syscallId replyAddr (.failedLookup false lf) s))
      (kLook decoded.syscallId) (syscallRequiredRight decoded.syscallId) with h | ⟨tcb', hObj', h⟩
  · exact .inl h
  · rw [hObj] at hObj'
    cases hObj'
    exact .inr (entryOperandOutcome_of_replyArm ctx executingCore st kRes kLook tid tcb decoded
      true replyAddr _ hCur hObj hDec (fun _ => hRA) (fun h => nomatch h) (by rw [hR]; exact h))

/-- **What `syscallEntryCheckedK` hands on**: `syscallEntryCheckedR`'s result to
`kGen`, or, on a call routed to an operand dispatch whose caller's TCB, decode
and CSpace root were found, the outcome `EntryOperandOutcome` names. -/
theorem syscallEntryCheckedK_spec {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) :
    syscallEntryCheckedK ctx executingCore st kGen kRes kLook =
        kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (syscallEntryCheckedK ctx executingCore st kGen kRes kLook) := by
  by_cases hCtx : isInsecureDefaultContext ctx = true
  · exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, ↓reduceIte])
  cases hCur : st.scheduler.currentOnCore executingCore with
  | none =>
    exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur,
      Bool.false_eq_true, ↓reduceIte])
  | some tid =>
  cases hObj : st.getObject? tid.toObjId with
  | none =>
    exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur, hObj,
      Bool.false_eq_true, ↓reduceIte])
  | some o =>
  cases o <;> try (refine .inl ?_; simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx,
    hCur, hObj, Bool.false_eq_true, ↓reduceIte]; done)
  rename_i tcb
  · have hD := entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
    cases hRt : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
        SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
    | signal capAddr =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSignal
          st tid _ _ 32 capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by decide) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | wait capAddr =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedWait
          st tid _ _ 32 capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by decide) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | send capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by decide) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | call capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by decide) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | reply capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReply
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by decide) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | receive capAddr len replyAddr =>
      obtain ⟨decoded, hDec, hSid, hCap, -, hLen, hR0⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
          st tid _ _ 32 capAddr len replyAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      refine (entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
        decoded _ _ (len != 0) replyAddr hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
        (fun h => receiveReplyAddr?_of_msgReg0 decoded replyAddr
          (by rw [hLen]; simpa using h) (.inl hSid) (hR0 (by simpa using h)))
        (fun h => by
          have h0 : len = 0 := by simpa using h
          simp [receiveReplyAddr?, hLen, h0])).imp_left And.left
    | replyRecv capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -, hMi, hRegs⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      refine (entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
        decoded _ _ (msgInfo.length != 0) (replyRecvReplyAddr tcb.registerContext) hCur hObj hDec
        hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
        (fun h => receiveReplyAddr?_of_msgReg0 decoded _
          (by rw [hMi]; simpa using h) (.inr hSid)
          (by rw [hRegs]; exact replyRecvReplyAddr_msgReg0 tcb.registerContext))
        (fun h => by
          have h0 : msgInfo.length = 0 := by simpa using h
          simp [receiveReplyAddr?, hMi, h0])).imp_left And.left
    | invoke sid capAddr =>
      obtain ⟨decoded, hDec, hSid, hRI, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedInvoke
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (syscallNamesReply_of_routedInvocation hRI) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | audited sid capAddr =>
      obtain ⟨decoded, hDec, hSid, hRA, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedAudited
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (syscallNamesReply_of_routedAudited hRA) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | overflowOne sid capAddr =>
      obtain ⟨hRouted, msgInfo, -, hDecM⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowOne
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hRt
      have hNRs := syscallNamesReply_of_routedOverflowOne hRouted
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact hD (SeLe4n.Kernel.Architecture.RegisterDecode.clampToInline
            { capAddr, msgInfo, syscallId := sid,
              msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext),
              inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 0 })
          sid hNRs _ hCur hObj (by rw [hDecM]; simp only [SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR0])
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
      | ok w =>
        dsimp only
        have hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
            tcb.registerContext 32 = .ok
              { capAddr, msgInfo, syscallId := sid,
                msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext) ++
                  #[(⟨w⟩ : RegValue)],
                inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 1 } := by
          rw [hDecM]
          simp only [SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR0]
        exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb _ sid hNRs
          (overflowOneOperandArmR ctx sid tcb.registerContext w tid (routedExtraCapCount sid tcb.registerContext)) hCur hObj hDec rfl
          (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0,
              dispatchOverflowOneCheckedR_eq_operand ctx sid capAddr _ w tid _ _ hRouted])
    | sendLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSendLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact hD (clampedFrameDecode .send tcb.registerContext capAddr msgInfo) .send (by decide) _ hCur hObj
          (decodeSyscallArgsFromState_of_routedSendLong_clamped st tid _ capAddr msgInfo hRt 0 hn0 e hR0)
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
      | ok w0 =>
        dsimp only
        have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
        have hDec := decodeSyscallArgsFromState_of_routedSendLong_ok st tid _ capAddr msgInfo hRt hRead
        exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
          (longSendDecode st tid tcb.registerContext capAddr msgInfo) .send (by decide)
          (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .send)) hCur hObj hDec rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
    | callLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCallLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact hD (clampedFrameDecode .call tcb.registerContext capAddr msgInfo) .call (by decide) _ hCur hObj
          (decodeSyscallArgsFromState_of_routedCallLong_clamped st tid _ capAddr msgInfo hRt 0 hn0 e hR0)
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
      | ok w0 =>
        dsimp only
        have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
        have hDec := decodeSyscallArgsFromState_of_routedCallLong_ok st tid _ capAddr msgInfo hRt hRead
        exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
          (longCallDecode st tid tcb.registerContext capAddr msgInfo) .call (by decide)
          (callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .call)) hCur hObj hDec rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
    | replyLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact hD (clampedFrameDecode .reply tcb.registerContext capAddr msgInfo) .reply (by decide) _ hCur hObj
          (decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo .reply (.inl ⟨hRt, rfl⟩) 0 hn0 e hR0)
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
      | ok w0 =>
        dsimp only
        have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
        have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
          .reply (.inl ⟨hRt, rfl⟩) hRead
        exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
          (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo) .reply (by decide)
          (replyLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .reply)) hCur hObj hDec rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
    | replyRecvLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        refine (entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
          (clampedFrameDecode .replyRecv tcb.registerContext capAddr msgInfo) .replyRecv _ true
          (replyRecvReplyAddr tcb.registerContext) hCur hObj
          (decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo .replyRecv (.inr (.inl ⟨hRt, rfl⟩)) 0 hn0 e hR0)
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
          (fun _ => receiveReplyAddr?_of_msgReg0 _ _ (by simp [clampedFrameDecode]) (.inr rfl)
            (replyRecvReplyAddr_msgReg0 tcb.registerContext)) (fun h => nomatch h)).imp_left And.left
      | ok w0 =>
        dsimp only
        have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
        have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
          .replyRecv (.inr (.inl ⟨hRt, rfl⟩)) hRead
        refine (entryOperandOutcome_of_replyLong ctx executingCore st kGen kRes kLook tid tcb
          (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo) .replyRecv capAddr
          (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore
            (syscallRequiredRight .replyRecv))
          (replyRecvReplyAddr tcb.registerContext) hCur hObj hDec rfl rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
          (receiveReplyAddr?_of_msgReg0 _ _ (by simp [longMessageDecode]; omega) (.inr rfl)
            (replyRecvReplyAddr_longMsgReg0 st tid tcb.registerContext capAddr msgInfo))).imp_left
          And.left
    | transferring sid capAddr msgInfo =>
      have hNRs : syscallNamesReply sid = false := by
        rcases (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
          st tid _ _ 32 sid capAddr msgInfo hRt).1 with h | h <;> subst h <;> rfl
      by_cases hShort : msgInfo.length ≤ 4
      · obtain ⟨-, -, -, hShortDec, -⟩ :=
          SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
            st tid _ _ 32 sid capAddr msgInfo hRt
        have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
        have hDec := hShortDec (by rw [hSz]; exact hShort)
        simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
          ↓reduceIte]
        exact hD
          ({ capAddr := capAddr, msgInfo := msgInfo, syscallId := sid,
             msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext),
             inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size,
             overflowCount := 0 } : SyscallDecodeResult)
          sid hNRs _ hCur hObj hDec rfl (by
          simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
            ↓reduceIte]
          rfl)
      · obtain ⟨-, -, hMax, -, -⟩ :=
          SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
            st tid _ _ 32 sid capAddr msgInfo hRt
        have hGt : 4 < msgInfo.length := by omega
        have hRR : (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .replyLong capAddr msgInfo ∧ sid = .reply) ∨
            (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .replyRecvLong capAddr msgInfo ∧ sid = .replyRecv) ∨
            (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .transferring sid capAddr msgInfo ∧ 4 < msgInfo.length) :=
          .inr (.inr ⟨hRt, hGt⟩)
        have hT : st.getTcb? tid = some tcb := by
          rw [SystemState.getObject?_eq_getElem] at hObj
          simp only [SystemState.getTcb?, hObj]
        have hn0 : 0 < msgInfo.length - 4 := by omega
        have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
          have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
          have h120 : maxMessageRegisters = 120 := rfl
          rw [h116]; rw [h120] at hMax; omega
        simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
          ↓reduceIte]
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
        | error e =>
          exact hD (clampedFrameDecode sid tcb.registerContext capAddr msgInfo) sid hNRs _ hCur hObj
            (decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo sid hRR 0 hn0 e hR0)
            rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
              rfl)
        | ok w0 =>
          dsimp only
          have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
          have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
            sid hRR hRead
          exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
            (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo) sid hNRs
            (transferringOperandArmThenTaintR ctx sid tcb.registerContext
              msgInfo.length tid executingCore (syscallRequiredRight sid)) hCur hObj hDec rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort,
                Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
              rfl)
    | overflowed sid capAddr len =>
      obtain ⟨msgInfo, hMI, hLenEq, hGt, hMax, hOv, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowed
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr len hRt
      have hNRs := syscallNamesReply_of_routedOverflowOne hOv
      subst hLenEq
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact hD (clampedFrameDecode sid tcb.registerContext capAddr msgInfo) sid hNRs _ hCur hObj
          (decodeSyscallArgsFromState_of_routedOverflowed_clamped st tid _ sid capAddr msgInfo hMI hRt 0 hn0 e hR0)
          rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
            rfl)
      | ok w0 =>
        dsimp only
        have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
        have hDec := decodeSyscallArgsFromState_of_routedOverflowed_ok st tid _ sid capAddr
          msgInfo hMI hRt hRead
        exact entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
          (overflowedDecode st tid tcb.registerContext sid capAddr msgInfo) sid hNRs
          (overflowedArmOf ctx sid tcb.registerContext w0 (overflowWordAt st tid 1)
            (overflowWordAt st tid 2) msgInfo.length tid executingCore capAddr
            (routedExtraCapCount sid tcb.registerContext)) hCur hObj hDec rfl (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0,
              dispatchOverflowedCheckedR_eq_operand ctx sid capAddr tcb.registerContext
                w0 _ _ _ tid executingCore _ hOv]
            rfl)
    | shortArgs sid capAddr =>
      obtain ⟨decoded, hDec, hSid, hRS, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedShortArgs
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ (by
          rcases Bool.or_eq_true _ _ ▸ hRS with h | h
          · exact syscallNamesReply_of_routedInvocation h
          · exact syscallNamesReply_of_routedOverflowOne h) _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
    | yield | viaDecode | refused _ =>
      exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur, hObj,
        hRt, Bool.false_eq_true, ↓reduceIte])


/-- The long reply-receive route's operand dispatch, once its caller's TCB is
found, ends in the outcome `EntryOperandOutcome` names: `syscallEntryCheckedK`
hands nothing to `kGen` on it. -/
theorem replyRecvLong_entryOperandOutcome {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (capAddr : SeLe4n.CPtr) (msgInfo : MessageInfo)
    (hCtx : ¬ isInsecureDefaultContext ctx = true)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRt : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .replyRecvLong capAddr msgInfo) :
    EntryOperandOutcome ctx executingCore st kRes kLook
      (syscallEntryCheckedK ctx executingCore st kGen kRes kLook) := by
  obtain ⟨hGt, hMax, -⟩ :=
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong
      st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hT : st.getTcb? tid = some tcb := by
    rw [SystemState.getObject?_eq_getElem] at hObj
    simp only [SystemState.getTcb?, hObj]
  have hn0 : 0 < msgInfo.length - 4 := by omega
  have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
    have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
    have h120 : maxMessageRegisters = 120 := rfl
    rw [h116]; rw [h120] at hMax; omega
  simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
  rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
  cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
  | error e =>
    rcases entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
      (clampedFrameDecode .replyRecv tcb.registerContext capAddr msgInfo) .replyRecv _ true
      (replyRecvReplyAddr tcb.registerContext) hCur hObj
      (decodeSyscallArgsFromState_of_routedReplyLong_clamped st tid _ capAddr msgInfo .replyRecv (.inr (.inl ⟨hRt, rfl⟩)) 0 hn0 e hR0)
      rfl (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
      Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
        rfl)
      (fun _ => receiveReplyAddr?_of_msgReg0 _ _ (by simp [clampedFrameDecode]) (.inr rfl)
        (replyRecvReplyAddr_msgReg0 tcb.registerContext)) (fun h => nomatch h) with h | h
    · exact absurd hObj (h.2 tcb hCur)
    · exact h
  | ok w0 =>
    dsimp only
    have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, hR0⟩
    have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
      .replyRecv (.inr (.inl ⟨hRt, rfl⟩)) hRead
    rcases entryOperandOutcome_of_replyLong ctx executingCore st kGen kRes kLook tid tcb
      (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo) .replyRecv capAddr
      (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
        msgInfo.extraCaps msgInfo.label tid executingCore
        (syscallRequiredRight .replyRecv))
      (replyRecvReplyAddr tcb.registerContext) hCur hObj hDec rfl rfl (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
          ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0]
        rfl)
      (receiveReplyAddr?_of_msgReg0 _ _ (by simp [longMessageDecode]; omega) (.inr rfl)
        (replyRecvReplyAddr_longMsgReg0 st tid tcb.registerContext capAddr msgInfo)) with h | h
    · exact absurd hObj (h.2 tcb hCur)
    · exact h

/-- `syscallEntryCheckedK_spec` with the report told apart: a result handed to
`kGen` is one whose refusals report the state the entry was handed
(`cancelReceiveBusyReply` leaves it as it is), and a receive whose busy reply's
cancel the report names is an operand dispatch whose arm ran. -/
theorem syscallEntryCheckedK_spec_fixedReport {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) :
    (syscallEntryCheckedK ctx executingCore st kGen kRes kLook =
        kGen (syscallEntryCheckedR ctx executingCore st) ∧
      cancelReceiveBusyReply ctx executingCore st = st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (syscallEntryCheckedK ctx executingCore st kGen kRes kLook) := by
  by_cases hFix : cancelReceiveBusyReply ctx executingCore st = st
  · exact (syscallEntryCheckedK_spec ctx executingCore st kGen kRes kLook).imp_left
      (fun h => ⟨h, hFix⟩)
  right
  unfold cancelReceiveBusyReply at hFix
  split at hFix
  · exact absurd rfl hFix
  next hCtx =>
  split at hFix
  · exact absurd rfl hFix
  next tid hCur =>
  split at hFix
  · next tcb hObj =>
    split at hFix
    · next capAddr len replyAddr hRt =>
      obtain ⟨decoded, hDec, hSid, hCap, -, hLen, hR0⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
          st tid _ _ 32 capAddr len replyAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rcases entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
        decoded _ _ (len != 0) replyAddr hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
        (fun h => receiveReplyAddr?_of_msgReg0 decoded replyAddr
          (by rw [hLen]; simpa using h) (.inl hSid) (hR0 (by simpa using h)))
        (fun h => by
          have h0 : len = 0 := by simpa using h
          simp [receiveReplyAddr?, hLen, h0]) with h | h
      · exact absurd hObj (h.2 tcb hCur)
      · exact h
    · next capAddr msgInfo hRt =>
      obtain ⟨decoded, hDec, hSid, hCap, -, hMi, hRegs⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rcases entryOperandOutcome_of_replyDispatch ctx executingCore st kGen kRes kLook tid tcb
        decoded _ _ (msgInfo.length != 0) (replyRecvReplyAddr tcb.registerContext) hCur hObj hDec
        hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl)
        (fun h => receiveReplyAddr?_of_msgReg0 decoded _
          (by rw [hMi]; simpa using h) (.inr hSid)
          (by rw [hRegs]; exact replyRecvReplyAddr_msgReg0 tcb.registerContext))
        (fun h => by
          have h0 : msgInfo.length = 0 := by simpa using h
          simp [receiveReplyAddr?, hMi, h0]) with h | h
      · exact absurd hObj (h.2 tcb hCur)
      · exact h
    · next capAddr msgInfo hRt =>
      exact replyRecvLong_entryOperandOutcome ctx executingCore st kGen kRes kLook tid tcb capAddr
        msgInfo hCtx hCur hObj hRt
    · exact absurd rfl hFix
  · exact absurd rfl hFix

end SeLe4n.Kernel
