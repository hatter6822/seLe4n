-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace

/-!
# The endpoint syscalls, refusing in the state they were refused in

WS-ZA ZA4.7.  `RefusalCarryingDispatch` gives the signal, the wait and the yield
dispatches that refuse in the state they were handed; this module gives the
endpoint syscalls theirs, each proven equal to `RefusalCarrying.ofKernel` of
the specification's dispatch.  A send with no capabilities to transfer checks
everything before its first write (`endpointSendCrossCoreDispatchChecked_error_state`),
so the state goes to the send and nothing keeps it for a refusal.  A receive
that names no reply object and blocks makes its writes in place, after every
check (`receiveBlock_inPlace_eq`), so it too holds no pre-state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- The checked send arm (`dispatchWithCapChecked`'s `.send` case) for a
message with no capabilities to transfer, refusing in the state it was handed
(`endpointSendCheckedArmR_eq`).  It takes the message words rather than the
decode, so a caller that reads them from the register file builds no decode
record. -/
@[inline] def endpointSendCheckedArmR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendCrossCoreDispatchChecked ctx epId tid
            { registers := body, caps := #[], badge := cap.badge,
              capsGranted := cap.rights.mem .grant } cap.rights (SeLe4n.Slot.ofNat 0)
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery (clearWokenReceiverStashPure woken? st')
              woken? summary.installedCount)
        | (st', .error e) => .error (e, st')
    | _ => .error (.invalidCapability, st)

theorem endpointSendCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (body : Array SeLe4n.RegValue)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    endpointSendCheckedArmR ctx body tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  subst hBody
  funext st
  simp only [endpointSendCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSend, hCaps, hSlot, resolveExtraCaps_empty]
  cases cap.target with
  | object epId =>
    simp only []
    rcases hRun : endpointSendCrossCoreDispatchChecked ctx epId tid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := #[],
          badge := cap.badge, capsGranted := cap.rights.mem .grant } cap.rights
        (SeLe4n.Slot.ofNat 0) executingCore st with ⟨st', _ | ⟨summary, sgi⟩⟩
    · have hst := endpointSendCrossCoreDispatchChecked_error_state ctx epId tid _ cap.rights
        (SeLe4n.Slot.ofNat 0) executingCore st _ rfl (by rw [hRun])
      rw [hRun] at hst
      simp only at hst
      rw [hst]
    · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- The receiver a send's content reaches, read from the pre-state before the
arm: the head of the receive queue of the endpoint its capability names
(`senderTaintEdges`). -/
@[inline] def sendTaintHead? (st : SystemState) (cap : Capability) : Option SeLe4n.ThreadId :=
  match cap.target with
  | .object epId => (st.getEndpoint? epId).bind (·.receiveQ.head)
  | _ => none

/-- The send's taint step, without the plan: the sender's pre-state taint joins
the receiver's (`sendTaintStep_eq`).  It builds no edge list and no plan
record. -/
@[inline] def sendTaintStep (head? : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match head? with
  | some r =>
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt r.toObjId (preTaint tid.toObjId) }
  | none => post

theorem sendTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult)
    (hSend : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLog preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (sendTaintHead? st cap) tid preTaint post
        | none => post) := by
  rcases hSend with hSend | hSend <;>
  simp only [syscallTaintPlan, contentFlowClass, hSend, contentFlowEdges, contentFlowClears,
    contentFlowBypassed] <;>
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩ <;>
  first
  | simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]; done
  | cases target with
    | object epId =>
      simp only [sendTaintHead?, senderTaintEdges]
      cases (st.getEndpoint? epId).bind (·.receiveQ.head) <;>
        simp [sendTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [sendTaintHead?, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The send's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`sendOperandArmThenTaintR_eq`). -/
@[inline] def sendOperandArmThenTaintR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let head? := sendTaintHead? st cap
          match endpointSendCheckedArmR ctx body tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep head? tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem sendOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (body : Array SeLe4n.RegValue)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    sendOperandArmThenTaintR ctx body tid executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLog preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSend, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inl hSend), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [sendOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointSendCheckedArmR_eq ctx decoded tid executingCore gate cap body hSend hCaps
          hSlot hBody]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The send's dispatch for a message with no capabilities to transfer:
`dispatchOperandCheckedR` with the send's arm (`dispatchSendCheckedR_eq`). -/
@[inline] def dispatchSendCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (sendOperandArmThenTaintR ctx body tid executingCore (syscallRequiredRight .send))

theorem dispatchSendCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    dispatchSendCheckedR ctx decoded.capAddr body tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hSend]; rfl)
    (by rw [hSend]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := sendOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref body hSend hCaps hSlot hBody hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hSend] at hArm ⊢
  exact hArm

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) for a
message with no capabilities to transfer, through the specification's dispatch,
refusing in the state it was handed. -/
def endpointCallCheckedArmGeneralR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid
            { registers := body, caps := #[], badge := cap.badge,
              capsGranted := cap.rights.mem .grant } cap.rights (SeLe4n.Slot.ofNat 0)
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' woken? summary.installedCount)
        | (_, .error e) => .error (e, st)
    | _ => .error (.invalidCapability, st)

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) for a
message with no capabilities to transfer, refusing in the state it was handed
(`endpointCallCheckedArmR_eq`).  WS-ZA ZA4.7: a rendezvous whose checks all
pass before any write (`callWakesInPlace`, the seL4 decode/perform split) writes
in place on a state nothing else holds (`performCallRendezvous`,
`callDispatchChecked_inPlace`); any other call takes the general arm. -/
@[inline] def endpointCallCheckedArmR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.objects[epId]? with
        | some (.endpoint ep) =>
            match ep.receiveQ.head with
            | some r =>
                match st.objects[r.toObjId]? with
                | some (.tcb rt) =>
                    match rt.pendingReceiveReply with
                    | some rid =>
                        if !decide (body.size > maxMessageRegisters) &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callWakesInPlace st epId tid r rt rid then
                          .ok ((), Architecture.stageWokenDelivery
                            (performCallRendezvous st epId tid r rt.queueNext rid
                              { registers := body, caps := #[], badge := cap.badge,
                                capsGranted := cap.rights.mem .grant } executingCore)
                            (some r) 0)
                        else endpointCallCheckedArmGeneralR ctx body tid executingCore cap st
                    | none => endpointCallCheckedArmGeneralR ctx body tid executingCore cap st
                | _ => endpointCallCheckedArmGeneralR ctx body tid executingCore cap st
            | none => endpointCallCheckedArmGeneralR ctx body tid executingCore cap st
        | _ => endpointCallCheckedArmGeneralR ctx body tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointCallCheckedArmR_eq_general (ctx : LabelingContext)
    (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) :
    endpointCallCheckedArmR ctx body tid executingCore cap =
      endpointCallCheckedArmGeneralR ctx body tid executingCore cap := by
  funext st
  unfold endpointCallCheckedArmR
  split
  · next epId hTgt =>
    split
    · next ep hE =>
      split
      · next r hH =>
        split
        · next rt hT =>
          split
          · next rid hRid =>
            split
            · next hG =>
              simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hG
              obtain ⟨⟨hSz, hFlow⟩, hW⟩ := hG
              obtain ⟨sgi, hD⟩ := callDispatchChecked_inPlace ctx st epId ep tid r rt rid
                { registers := body, caps := #[], badge := cap.badge,
                  capsGranted := cap.rights.mem .grant } cap.rights (SeLe4n.Slot.ofNat 0)
                executingCore rfl rfl hSz hE hH hT hRid hW hFlow
              have hEp : st.getEndpoint? epId = some ep :=
                (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
              simp only [endpointCallCheckedArmGeneralR, hTgt, hEp, Option.bind_some, hH, hD]
              rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · next hTgt =>
    unfold endpointCallCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

theorem endpointCallCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (body : Array SeLe4n.RegValue)
    (hCall : decoded.syscallId = .call)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    endpointCallCheckedArmR ctx body tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  subst hBody
  rw [endpointCallCheckedArmR_eq_general]
  funext st
  simp only [endpointCallCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hCall, hCaps, hSlot, resolveExtraCaps_empty]
  cases cap.target with
  | object epId =>
    simp only []
    rcases endpointCallCrossCoreDispatchChecked ctx epId tid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := #[],
          badge := cap.badge, capsGranted := cap.rights.mem .grant } cap.rights
        (SeLe4n.Slot.ofNat 0) executingCore st with ⟨st', _ | ⟨summary, sgi⟩⟩ <;> rfl
  | _ => rfl

/-- The call's slot check, gate, arm and taint step on the capability its
operand resolved to; a call moves content as a send does (`sendTaintStep`).
Every refusal carries the state it was handed (`callOperandArmThenTaintR_eq`). -/
@[inline] def callOperandArmThenTaintR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let head? := sendTaintHead? st cap
          match endpointCallCheckedArmR ctx body tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep head? tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem callOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (body : Array SeLe4n.RegValue)
    (hCall : decoded.syscallId = .call)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    callOperandArmThenTaintR ctx body tid executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLog preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hCall, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inr hCall), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [callOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointCallCheckedArmR_eq ctx decoded tid executingCore gate cap body hCall hCaps
          hSlot hBody]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The call's dispatch for a message with no capabilities to transfer:
`dispatchOperandCheckedR` with the call's arm (`dispatchCallCheckedR_eq`). -/
@[inline] def dispatchCallCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (callOperandArmThenTaintR ctx body tid executingCore (syscallRequiredRight .call))

theorem dispatchCallCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hCall : decoded.syscallId = .call)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    dispatchCallCheckedR ctx decoded.capAddr body tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hCall]; rfl)
    (by rw [hCall]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := callOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref body hCall hCaps hSlot hBody hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hCall] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.7: the tail of an endpoint's receive queue. -/
@[inline] def receiveQueueTail? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getEndpoint? endpointId with
  | some ep => ep.receiveQ.tail
  | none => none

/-- WS-ZA ZA4.7: a receive blocks, and writes only its slots: no sender is
waiting, the receiver may block (`receiveBlockAdmits`) and every write stays
in place (`receiveBlocksInPlace`). -/
@[inline] def receiveBlocksFast (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) : Bool :=
  match st.getEndpoint? endpointId with
  | some ep =>
      ep.sendQ.head.isNone &&
      (match st.objects[receiver.toObjId]? with
       | some (.tcb rt) => receiveBlockAdmits rt &&
           receiveBlocksInPlace st endpointId receiver ep.receiveQ.tail replyId
       | _ => false)
  | none => false

/-- The CSpace root of the calling thread, as the syscall gate reads it. -/
@[inline] def callerCspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId) : SeLe4n.ObjId :=
  match st.getObject? tid.toObjId with
  | some (.tcb t) => t.cspaceRoot
  | _ => tid.toObjId

/-- The depth of the calling thread's CSpace root, as the syscall gate reads it. -/
@[inline] def callerCspaceDepth (st : SystemState) (tid : SeLe4n.ThreadId) : Nat :=
  match st.getObject? tid.toObjId with
  | some (.tcb t) =>
      match st.getObject? t.cspaceRoot with
      | some (.cnode cn) => cn.depth
      | _ => 0
  | _ => 0

/-- `resolveRecvReplyId` on the message length and first message register
alone, with the gate the caller's own CSpace gives
(`resolveRecvReplyIdR_eq`), so the entry builds no decode record for it. -/
@[inline] def resolveRecvReplyIdR (st : SystemState) (tid : SeLe4n.ThreadId)
    (len mr0 : Nat) : Except KernelError (Option SeLe4n.ReplyId) :=
  if len = 0 then .ok none else
  let gate : SyscallGate :=
    { callerId := tid
      cspaceRoot := callerCspaceRoot st tid
      capAddr := SeLe4n.CPtr.ofNat mr0
      capDepth := callerCspaceDepth st tid
      requiredRight := .write }
  match syscallLookupCap gate st with
  | .error e => .error e
  | .ok (rcap, _) =>
      match extractReplyId rcap with
      | .error e => .error e
      | .ok rid =>
          match st.getReply? rid with
          | some r =>
              if r.caller.isNone && !st.replyIsStashed rid then .ok (some rid)
              else .error .replyCapInvalid
          | none => .error .replyCapInvalid

theorem resolveRecvReplyIdR_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (len mr0 : Nat)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hLen : decoded.msgInfo.length = len)
    (hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := mr0 }) :
    resolveRecvReplyIdR st tid len mr0 = resolveRecvReplyId gate decoded st := by
  unfold resolveRecvReplyIdR resolveRecvReplyId
  by_cases h0 : len = 0
  · simp [h0, hLen]
  · rw [if_neg h0, hArgs h0]
    have hL : (decoded.msgInfo.length == 0) = false := by simp [hLen, h0]
    simp only [hL, Bool.false_eq_true, ↓reduceIte]
    rcases gate with ⟨c, r, a, d, rr⟩
    simp only at hCaller hRoot hDepth
    subst hCaller hRoot hDepth
    rfl

/-- The checked receive arm (`dispatchWithCapChecked`'s `.receive` case), on
the message length and first message register, refusing in the state it was
handed (`endpointReceiveCheckedArmR_eq`).  Every check, the reply object's
included, precedes the first write; a receive that blocks in place
(`receiveBlocksFast`) holds no pre-state (`receiveBlock_inPlace_eq`). -/
@[inline] def endpointReceiveCheckedArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len mr0 : Nat) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
      match resolveRecvReplyIdR st tid len mr0 with
      | .error e => .error (e, st)
      | .ok rid =>
        if receiveBlocksFast st epId tid rid then
          .ok ((), removeRunnableOnCore
            (storeReceiveBlock st epId tid (receiveQueueTail? st epId) rid) tid executingCore)
        else
          let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
          match endpointReceiveDualWithCapsOnCore epId tid rid (callerCspaceRoot st tid)
              (SeLe4n.Slot.ofNat 0) executingCore st with
          | (st', .ok (dequeued, summary, _sgi)) =>
              match applyReceiveRendezvousHandoff st' tid dequeued executingCore with
              | .error e => .error (e, st)
              | .ok stDon =>
                  .ok ((), Architecture.stageDeliveredMessage
                    (Architecture.stageWokenSendCompletion stDon wokenSender?) tid
                    summary.installedCount)
          | (_, .error e) => .error (e, st)
    | _ => .error (.invalidCapability, st)

theorem endpointReceiveCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRecv : decoded.syscallId = .receive)
    (len mr0 : Nat)
    (hRid : resolveRecvReplyIdR st tid len mr0 = resolveRecvReplyId gate decoded st)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot) :
    endpointReceiveCheckedArmR ctx tid len mr0 executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointReceiveCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hRecv]
  cases cap.target with
  | object epId =>
    simp only []
    split
    · rfl
    · rw [hRid]
      cases resolveRecvReplyId gate decoded st with
      | error e => rfl
      | ok rid =>
      simp only []
      by_cases hF : receiveBlocksFast st epId tid rid = true
      · rw [if_pos hF]
        unfold receiveBlocksFast at hF
        cases hEp : st.getEndpoint? epId with
        | none => rw [hEp] at hF; cases hF
        | some ep =>
          rw [hEp] at hF
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hF
          obtain ⟨hS, hO⟩ := hF
          cases hR : st.objects[tid.toObjId]? with
          | none => rw [hR] at hO; cases hO
          | some o =>
            cases o with
            | tcb rt =>
              rw [hR] at hO
              simp only [Bool.and_eq_true] at hO
              obtain ⟨hA, hG⟩ := hO
              have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
              have hTail : receiveQueueTail? st epId = ep.receiveQ.tail := by
                simp only [receiveQueueTail?, hEp]
              obtain ⟨t, hT, hB⟩ := receiveBlock_receiver_blocked st epId ep tid rt rid
                executingCore hE hR hA hG
              unfold endpointReceiveDualWithCapsOnCore
              rw [receiveBlock_inPlace_eq st epId ep tid rt rid executingCore hE hS hR hA hG]
              have hSnd : (receiveRendezvousSender? st epId).isNone = true := by
                simp [receiveRendezvousSender?, hEp, hS]
              simp only [hSnd, ↓reduceIte, hTail]
              have hNoCall : rendezvousDequeuedCall (removeRunnableOnCore
                  (storeReceiveBlock st epId tid ep.receiveQ.tail rid) tid executingCore) tid =
                  false := by
                unfold rendezvousDequeuedCall
                rw [show lookupTcb _ tid = some t from by
                  simp only [lookupTcb]
                  split
                  · next hRes =>
                    simp only [receiveBlocksInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
                    rw [hG.1.1.1.1.1.1] at hRes; cases hRes
                  · exact hT]
                simp only [hB]
              rw [applyReceiveRendezvousHandoff_of_no_call _ _ _ _ hNoCall]
              simp only [hS, Option.bind_some, Architecture.stageWokenSendCompletion_none]
              unfold Architecture.stageDeliveredMessage
              simp only [hT, hB, reduceCtorEq, ↓reduceIte]
            | _ => rw [hR] at hO; cases hO
      · rw [if_neg hF]
        simp only [hRoot, hSlot]
        rcases endpointReceiveDualWithCapsOnCore epId tid rid gate.cspaceRoot
          (SeLe4n.Slot.ofNat 0) executingCore st with ⟨st', _ | ⟨dq, summary, sgi⟩⟩
        · rfl
        · simp only []
          cases applyReceiveRendezvousHandoff st' tid dq executingCore <;> rfl
  | _ => rfl

/-- The sender whose content a receive takes, read from the pre-state before
the arm: the head of the send queue of the endpoint its capability names
(`receiverTaintEdges`). -/
@[inline] def receiveTaintSource? (st : SystemState) (cap : Capability) :
    Option SeLe4n.ThreadId :=
  match cap.target with
  | .object epId => (st.getEndpoint? epId).bind (·.sendQ.head)
  | _ => none

/-- The receive's taint step, without the plan: the sender's pre-state taint
joins the receiver's (`receiveTaintStep_eq`). -/
@[inline] def receiveTaintStep (source? : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match source? with
  | some s =>
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt tid.toObjId (preTaint s.toObjId) }
  | none => post

theorem receiveTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hRecv : decoded.syscallId = .receive)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLog preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => receiveTaintStep (receiveTaintSource? st cap) tid preTaint post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hRecv, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target with
    | object epId =>
      simp only [receiveTaintSource?, receiverTaintEdges]
      cases (st.getEndpoint? epId).bind (·.sendQ.head) <;>
        simp [receiveTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [receiveTaintSource?, receiveTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The receive's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`receiveOperandArmThenTaintR_eq`). -/
@[inline] def receiveOperandArmThenTaintR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len mr0 : Nat) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let source? := receiveTaintSource? st cap
          match endpointReceiveCheckedArmR ctx tid len mr0 executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), receiveTaintStep source? tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem receiveOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (hRecv : decoded.syscallId = .receive) (len mr0 : Nat)
    (hRid : resolveRecvReplyIdR st tid len mr0 = resolveRecvReplyId gate decoded st)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    receiveOperandArmThenTaintR ctx tid len mr0 executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLog preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hRecv, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [receiveTaintStep_eq st tid decoded hRecv, hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [receiveOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointReceiveCheckedArmR_eq ctx decoded tid executingCore gate cap st hRecv len mr0
          hRid hSlot hRoot]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The receive's dispatch, on the message length and first message register
the entry read: `dispatchOperandCheckedR` with the receive's arm
(`dispatchReceiveCheckedR_eq`). -/
@[inline] def dispatchReceiveCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (len mr0 : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (receiveOperandArmThenTaintR ctx tid len mr0 executingCore (syscallRequiredRight .receive))

theorem dispatchReceiveCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (len mr0 : Nat)
    (hRecv : decoded.syscallId = .receive)
    (hLen : decoded.msgInfo.length = len)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hMr0 : len ≠ 0 → decoded.msgRegs[0]? = some ⟨mr0⟩) :
    dispatchReceiveCheckedR ctx decoded.capAddr len mr0 tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hRecv]; rfl)
    (by rw [hRecv]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := mr0 } := by
    intro hN
    have h := hMr0 hN
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨h0, hv⟩ := h
    simp only [decodeRecvArgs, requireMsgReg, h0, ↓reduceDIte, hv]
    rfl
  have hRid := resolveRecvReplyIdR_eq st tid
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    decoded len mr0 rfl (by simp only [callerCspaceRoot, hTcb])
    (by simp only [callerCspaceDepth, hTcb, hRoot]) hLen hArgs
  have hArm := receiveOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref hRecv len mr0 hRid hSlot (by simp only [callerCspaceRoot, hTcb]) hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hRecv] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
