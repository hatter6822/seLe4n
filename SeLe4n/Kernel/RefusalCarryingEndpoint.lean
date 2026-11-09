-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInPlace
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDonatingInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyUnheldInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReceiveInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultReceiveInPlace
import SeLe4n.Kernel.IPC.CrossCore.InertCapTransferInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongSendInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.CapTransferDelivered
import SeLe4n.Kernel.IPC.CrossCore.CallCapsDelivered

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

/-- WS-ZA ZA4.7: **a frame that routes as a capability-free send or call**, read
for the sender `tid` whose saved registers `rf` are: whatever endpoint it
names, it asks to transfer no capability, and a present sender's message is the
inline words of `rf` (`sendFrame_of_routed`). -/
theorem routedSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi ∨
      registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    (∀ endpointId badge grant, sendCapRequest st endpointId tid (.frame badge grant) = none) ∧
      ∀ badge grant, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant) =
          { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf mi.length,
            badge := badge } := by
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ => ?_, fun _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    exact ⟨fun endpointId badge grant =>
        (sendFrame_of_routed st tid tcb hT capAddr mi hR endpointId badge grant).2,
      fun badge grant _ => (sendFrame_of_routed st tid tcb hT capAddr mi hR tid.toObjId badge
        grant).1⟩

/-- **The message a routed capability-carrying frame of at most four words
sends**: its inline words, as a capability-free send's
(`decodeSyscallArgsFromState_of_routedTransferring`). -/
theorem routedTransferringMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi)
    (hLen : mi.length ≤ 4) :
    ∀ badge grant, (st.getTcb? tid).isSome = true →
      sendPayloadMessage st tid (.frame badge grant) =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf mi.length,
          badge := badge } := by
  intro badge grant hS
  obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp hS
  have hRf := hFrame tcb hT
  subst hRf
  obtain ⟨-, -, -, hShort, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring st tid _ _ 32
      sid capAddr mi hR
  have hDec : blockedSenderDecode st tid tcb = _ := hShort hLen
  simp only [sendPayloadMessage, senderFrameDecode, hT, hDec, senderFrameMessage]
  rfl

/-- The checked send arm (`dispatchWithCapChecked`'s `.send` case) through the
specification's send, refusing in the state it was handed
(`endpointSendCheckedArmGeneralR_eq`).  As the specification's, it is handed
only the capability's badge and grant right: the words are read from the
sender's frame. -/
def endpointSendCheckedArmGeneralR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendCrossCoreDispatchChecked ctx epId tid
            (.frame cap.badge (cap.rights.mem .grant))
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery (clearWokenReceiverStashPure woken? st')
              woken? summary.capInfo)
        | (st', .error e) => .error (e, st')
    | _ => .error (.invalidCapability, st)

/-- The general send arm is the specification's for a sender whose frame asks
to transfer no capability: a refusal then precedes every write
(`endpointSendCrossCoreDispatchChecked_error_state`). -/
theorem endpointSendCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hReq : ∀ endpointId badge grant,
      sendCapRequest st endpointId tid (.frame badge grant) = none) :
    endpointSendCheckedArmGeneralR ctx tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointSendCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSend]
  cases cap.target with
  | object epId =>
    simp only []
    rcases hRun : endpointSendCrossCoreDispatchChecked ctx epId tid
        (.frame cap.badge (cap.rights.mem .grant)) executingCore st with
      ⟨st', _ | ⟨summary, sgi⟩⟩
    · have hst := endpointSendCrossCoreDispatchChecked_error_state ctx epId tid _
        executingCore st _ (hReq _ _ _) (by rw [hRun])
      rw [hRun] at hst
      simp only at hst
      rw [hst]
    · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- WS-ZA ZA4.7: **a checked send to a waiting receiver, in place**: for a
send whose message is `msg` and which transfers no capability, with the sender
present and the rendezvous's writes in their slots (`sendWakesInPlace`), the
checked send is the in-place rendezvous and the receiver's wake. -/
theorem sendDispatchChecked_inPlace (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender r : SeLe4n.ThreadId) (rt : TCB)
    (payload : SendPayload) (msg : IpcMessage) (executingCore : Concurrency.CoreId)
    (hM : sendPayloadMessage st sender payload = msg)
    (hReq : sendCapRequest st endpointId sender payload = none)
    (hE : st.getEndpoint? endpointId = some ep) (hH : ep.receiveQ.head = some r)
    (hT : st.getTcb? r = some rt) (hS : (st.getTcb? sender).isSome = true)
    (hW : sendWakesInPlace st endpointId r rt.queueNext = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
    executingCore st =
      ((wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r executingCore).1,
        .ok ({ results := #[] },
          (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
            executingCore).2)) := by
  obtain ⟨sTcb, hSTcb⟩ := Option.isSome_iff_exists.mp hS
  unfold endpointSendCrossCoreDispatchChecked
  rw [if_pos hFlow, endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ hReq,
    endpointSendDualOnCore_eq_impl]
  unfold endpointSendDualOnCoreImpl
  simp only [sendWakesInPlaceCode_eq, storeSendRendezvousCode_eq, TCB.ofOptCode_queueNextCode,
    hE, hH, hSTcb, hT, hW, hM, ↓reduceIte]
  rfl

/-- **A checked send to a waiting receiver whose transfer transfers nothing, in
place**: the receiver takes no capability, or its buffer names no receive slot
and the first capability does not unwrap (`capTransferInert`), so the transfer,
run after the rendezvous, which writes no CNode, transfers none and writes
nothing (`receiveTransferCaps_of_inert`); the send is the in-place rendezvous and
the receiver's wake, as one that transfers nothing. -/
theorem sendDispatchChecked_inPlace_inert (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender r : SeLe4n.ThreadId) (rt : TCB)
    (payload : SendPayload) (msg : IpcMessage) (executingCore : Concurrency.CoreId)
    (hM : sendPayloadMessage st sender payload = msg)
    (hE : st.getEndpoint? endpointId = some ep) (hH : ep.receiveQ.head = some r)
    (hT : st.getTcb? r = some rt) (hS : (st.getTcb? sender).isSome = true)
    (hW : sendWakesInPlace st endpointId r rt.queueNext = true)
    (hInert : capTransferInert st endpointId (receiverCapTarget? st r)
      (sendCapRequest st endpointId sender payload) = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    ∃ s : CapTransferSummary, s.capInfo = 0 ∧
    endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
    executingCore st =
      ((wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r executingCore).1,
        .ok (s, (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
            executingCore).2)) := by
  obtain ⟨sTcb, hSTcb⟩ := Option.isSome_iff_exists.mp hS
  have hNo : st.objects.noResizeDue := by
    have hW' := hW
    simp only [sendWakesInPlace, Bool.and_eq_true] at hW'
    exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW'.1.1.1.2
  have hTr := receiveTransferCaps_of_inert hInert
    (getCNode?_sendRendezvousWoken st endpointId r rt.queueNext msg executingCore hNo)
  unfold endpointSendCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointSendDualWithCapsOnCore
  rw [endpointSendDualOnCore_eq_impl]
  unfold endpointSendDualOnCoreImpl
  simp only [sendWakesInPlaceCode_eq, storeSendRendezvousCode_eq, TCB.ofOptCode_queueNextCode,
    hE, hH, hSTcb, hT, hW, hM, ↓reduceIte, Option.bind_some, hTr]
  split <;> exact ⟨_, rfl, rfl⟩

/-- **A checked send to a waiting receiver, in place up to its transfer**: the
in-place rendezvous and the receiver's wake, then the specification's transfer
of the sender's request to the receiver's side, both read before the
rendezvous. -/
theorem sendDispatchChecked_inPlace_transfer (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender r : SeLe4n.ThreadId) (rt : TCB)
    (payload : SendPayload) (msg : IpcMessage) (executingCore : Concurrency.CoreId)
    (hM : sendPayloadMessage st sender payload = msg)
    (hE : st.getEndpoint? endpointId = some ep) (hH : ep.receiveQ.head = some r)
    (hT : st.getTcb? r = some rt) (hS : (st.getTcb? sender).isSome = true)
    (hW : sendWakesInPlace st endpointId r rt.queueNext = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender payload executingCore st =
      match receiveTransferCaps (sendCapRequest st endpointId sender payload) (some endpointId)
          (receiverCapTarget? st r)
          (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r executingCore).1 with
      | .ok (s, st'') =>
        (st'', .ok (s, (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
          executingCore).2))
      | .error e =>
        ((wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r executingCore).1,
          .error e) := by
  obtain ⟨sTcb, hSTcb⟩ := Option.isSome_iff_exists.mp hS
  unfold endpointSendCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointSendDualWithCapsOnCore
  rw [endpointSendDualOnCore_eq_impl]
  unfold endpointSendDualOnCoreImpl
  simp only [sendWakesInPlaceCode_eq, storeSendRendezvousCode_eq, TCB.ofOptCode_queueNextCode,
    hE, hH, hSTcb, hT, hW, hM, ↓reduceIte, Option.bind_some]
  cases sendCapRequest st endpointId sender payload with
  | none => rfl
  | some _ =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    split <;> next h => rw [h]

/-- **A call's transfer that transfers nothing is the identity**: the WithCaps
call returns the call rendezvous's state, transferring nothing, when the
rendezvous reads every CNode as the call found it. -/
theorem endpointCallWithCapsOnCore_inert (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (payload : SendPayload) (core : Concurrency.CoreId)
    (st st' : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hCall : endpointCallOnCore endpointId caller payload core st = (st', .ok sgi))
    (hRecv : (st.getEndpoint? endpointId).bind (·.receiveQ.head) = some r)
    (hInert : capTransferInert st endpointId (receiverCapTarget? st r)
      (sendCapRequest st endpointId caller payload) = true)
    (hCNode : ∀ id, st'.getCNode? id = st.getCNode? id) :
    ∃ s : CapTransferSummary, s.capInfo = 0 ∧
      endpointCallWithCapsOnCore endpointId caller payload core st =
        (st', .ok (s, sgi)) := by
  have hTr := receiveTransferCaps_of_inert hInert hCNode
  unfold endpointCallWithCapsOnCore
  simp only [hCall, hRecv, Option.bind_some, hTr]
  split <;> exact ⟨_, rfl, rfl⟩

/-- **The checked call dispatch whose transfer transfers nothing, in place**:
as `callDispatchChecked_inPlace`, the receiver taking none of the capabilities
the caller asks to transfer (`capTransferInert`). -/
theorem callDispatchChecked_inPlace_inert (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (rid : SeLe4n.ReplyId) (payload : SendPayload) (msg : IpcMessage)
    (core : Concurrency.CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callWakesInPlace st endpointId caller r rt rid = true)
    (hInert : capTransferInert st endpointId (receiverCapTarget? st r)
      (sendCapRequest st endpointId caller payload) = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    ∃ s : CapTransferSummary, s.capInfo = 0 ∧ ∃ sgi,
      endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
        core st = (performCallRendezvous st endpointId caller r rt.queueNext rid msg core,
          .ok (s, sgi)) := by
  have hG' := hG
  simp only [callWakesInPlace, sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  have hCRes : caller.isReserved = false := hG'.1.1.1.1.1.1.1.1.2
  have hRRes : r.isReserved = false := hG'.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hNo : st.objects.noResizeDue :=
    RobinHood.RHTable.noResizeDue_of_findsInPlace hG'.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  obtain ⟨hEq, hDon⟩ := callRendezvous_inPlace st endpointId ep caller r rt rid payload msg core hM
    hE hH hT hRid hG
  obtain ⟨s, hC, hW⟩ := endpointCallWithCapsOnCore_inert endpointId caller r payload core st
    _ _ hEq (by simp only [hEp, Option.bind_some, hH]) hInert
    (getCNode?_storeCallRendezvous st endpointId caller r rt.queueNext rid msg core hNo
      (callWakesInPlace_ne hG))
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff caller).mpr hCRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff r).mpr hRRes)
  have hcv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  refine ⟨s, hC, (wakeThread ((storePopHead st endpointId true r rt.queueNext).updateTcb r
    (callReceiverTcb msg)) r core).2, ?_⟩
  unfold endpointCallCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointCallCrossCoreDispatch
  rw [hW]
  simp only [hEp, hH, hcv, hrv]
  unfold applyCallDonationOnCore
  rw [applyCallDonation_eq_ok_self_of_no_donation _ _ _ (by rw [hcv', hrv']; exact hDon)]
  simp only [hcv', hrv', hDon]
  rfl

/-- **What a sender blocked by a routed capability-carrying send of at most
four words sends**: the inline words of its saved registers, under its badge
(`decodeSyscallArgsFromState_of_routedTransferring`). -/
theorem blockedSender_of_routedTransferring (st : SystemState) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    {sid : SyscallId}
    (h : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .transferring sid capAddr mi)
    (hLen : mi.length ≤ 4) (hF : sTcb.ipcFaultSend = false) :
    blockedSenderMessage st s sTcb =
      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
          sTcb.registerContext mi.length,
        badge := sTcb.ipcBadgeView } := by
  obtain ⟨-, -, -, hShort, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring st s _ _ 32
      sid capAddr mi h
  unfold blockedSenderMessage blockedSenderMessageOf blockedSenderDecode
  rw [hShort hLen]
  simp only [hF, Bool.false_eq_true, ↓reduceIte, senderFrameMessage]
  rfl

/-- **The take of a blocked capability-carrying send whose transfer transfers
nothing, in place**: as `receiveTake_delivered`, the receiver taking none of the
capabilities the sender asks to transfer (`capTransferInert`), so the WithCaps
receive, run after the take, which writes no CNode, transfers none and writes
nothing (`receiveTransferCaps_of_inert`). -/
theorem receiveTakeCaps_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .transferring .send capAddr mi)
    (hLen : mi.length ≤ 4) (hF : sTcb.ipcFaultSend = false)
    (hInert : capTransferInert st endpointId (receiverCapTarget? st receiver)
      (receiveCapRequest st endpointId) = true) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    let f := Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length sTcb.ipcBadgeView
    (∃ summary : CapTransferSummary, summary.capInfo = 0 ∧
      endpointReceiveDualWithCapsOnCore endpointId receiver replyId
        core st = (S4, .ok (s, summary, W.2))) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion S4 (some s))
          receiver 0 =
        performReceiveDelivered st endpointId s sTcb.queueNextCode receiver core
          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 := by
  intro P W S4 f
  obtain ⟨hTake, h2, h3⟩ := receiveTake_delivered_of_message st endpointId ep receiver replyId
    core s sTcb mi hE hH hT hG
    (fun X => blockedSender_of_routedTransferring X s sTcb capAddr mi hR hLen hF)
  refine ⟨?_, h2, h3⟩
  have hSnd : receiveRendezvousSender? st endpointId = some s := by
    simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
      Option.bind_some, hH]
  have hSW : sendWakesInPlace st endpointId s sTcb.queueNext = true := by
    have hG' := hG
    unfold receiveTakesInPlace at hG'
    revert hG'
    cases sendWakesInPlace st endpointId s sTcb.queueNext <;> simp
  have hNo : st.objects.noResizeDue := by
    simp only [sendWakesInPlace, Bool.and_eq_true] at hSW
    exact RobinHood.RHTable.noResizeDue_of_findsInPlace hSW.1.1.1.2
  have hTr := receiveTransferCaps_of_inert hInert
    (getCNode?_receiveTake st endpointId receiver s sTcb.queueNext
      (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb) core hNo)
  refine ⟨{ results := #[] }, rfl, ?_⟩
  unfold endpointReceiveDualWithCapsOnCore
  rw [hTake]
  simp only [hSnd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hTr]
  rfl

/-- A thread kept up to its link words reads the same rendezvous guard: a
state that keeps a non-caller's thread dequeues no caller there. -/
theorem rendezvousDequeuedCall_of_keepsBindings {B S : SystemState} (h : KeepsBindings B S)
    (t : SeLe4n.ThreadId) (hB : rendezvousDequeuedCall B t = false) :
    rendezvousDequeuedCall S t = false := by
  unfold rendezvousDequeuedCall lookupTcb at *
  cases hRes : t.isReserved
  · simp only [hRes, Bool.false_eq_true, ↓reduceIte] at hB ⊢
    cases hS : S.getTcb? t with
    | none => rfl
    | some t' =>
      obtain ⟨t0, h0, e0⟩ := h.2 t t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hS)
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h0] at hB
      have hI : t'.ipcState = t0.ipcState := by
        have h' := congrArg TCB.ipcState (show t'.withoutLinks = t0.withoutLinks from e0)
        exact h'
      simp only [hI]
      exact hB
  · simp

/-- **The take of a blocked capability-carrying send that transfers, delivered**:
the WithCaps receive takes the sender in place and runs the specification's
transfer on the state the take left, the rendezvous hands off no donation, and
staging the woken sender's completion and the receiver's message with the
transfer's report writes `performTakeCapsDelivered`'s state. -/
theorem receiveTakeCapsTransfer_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (s : SeLe4n.ThreadId) (sTcb rt : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hRT : st.getTcb? receiver = some rt)
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .transferring .send capAddr mi)
    (hLen : mi.length ≤ 4) (hF : sTcb.ipcFaultSend = false) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    ∃ (summary : CapTransferSummary) (st'' : SystemState),
      endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (st'', .ok (s, summary, W.2)) ∧
      applyReceiveRendezvousHandoff st'' receiver s core = .ok st'' ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion st'' (some s))
          receiver summary.capInfo =
        performTakeCapsDelivered st endpointId s sTcb.queueNextCode receiver core
          SeLe4n.arm64DefaultLayout mi.length
          (Architecture.badgeWordIf (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 0)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 1)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 2)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 3)
          sTcb.vspaceRoot sTcb.ipcBuffer
          sTcb.cspaceRoot (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0)
          rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot := by
  intro P W S4
  obtain ⟨hTake, h2, -⟩ := receiveTake_delivered_of_message st endpointId ep receiver replyId
    core s sTcb mi hE hH hT hG
    (fun X => blockedSender_of_routedTransferring X s sTcb capAddr mi hR hLen hF)
  have hMsg := blockedSender_of_routedTransferring P s sTcb capAddr mi hR hLen hF
  have hSnd : receiveRendezvousSender? st endpointId = some s := by
    simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
      Option.bind_some, hH]
  have hSW : sendWakesInPlace st endpointId s sTcb.queueNext = true := by
    have hG' := hG
    unfold receiveTakesInPlace at hG'
    revert hG'
    cases sendWakesInPlace st endpointId s sTcb.queueNext <;> simp
  have hRS : s ≠ receiver := by
    have hG' := hG
    simp only [receiveTakesInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at hG'
    exact fun h => hG'.1.1.1.1.1.2 h.symm
  have hNo : st.objects.noResizeDue := by
    simp only [sendWakesInPlace, Bool.and_eq_true] at hSW
    exact RobinHood.RHTable.noResizeDue_of_findsInPlace hSW.1.1.1.2
  have hNoP : P.objects.noResizeDue := storePopHead_noResizeDue _ _ _ _ _ hNo
  have hNoW : W.1.objects.noResizeDue :=
    wakeThread_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ hNoP)
  have hNoY : (W.1.updateTcb receiver receiverReady).objects.noResizeDue :=
    updateTcb_noResizeDue _ _ _ hNoW
  have hS4 : S4 = (W.1.updateTcb receiver receiverReady).mapTcbInPlace receiver
      (holdMessage (blockedSenderMessage P s sTcb)) := by
    show W.1.updateTcb receiver _ = _
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
      SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.mapTcbInPlace_mapTcbInPlace,
      holdMessage_receiverReady]
  have hReq : receiveCapRequest st endpointId =
      frameCapRequestOf st sTcb
        (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0) := by
    simp only [receiveCapRequest, hSnd, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT,
      blockedSenderCapRequest, hF, Bool.false_eq_true, ↓reduceIte]
    exact senderFrameCapRequest_routed st s sTcb _ capAddr mi .send _ rfl hR hLen
  have hA := ipcBufferReadsAgree_takeReady st endpointId s sTcb.queueNext receiver core hNo
  obtain ⟨summary, Y1, hTY⟩ := receiveTransferCaps_ok
    (frameCapRequestOf st sTcb (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0))
    (some endpointId) (capTargetOf st rt) (W.1.updateTcb receiver receiverReady)
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ _ Y1 summary hNoY hTY
  have hTr : receiveTransferCaps (receiveCapRequest st endpointId) (some endpointId)
      (receiverCapTarget? st receiver) S4 =
        .ok (summary, Y1.mapTcbInPlace receiver (holdMessage (blockedSenderMessage P s sTcb))) := by
    rw [hReq, receiverCapTarget?_eq_capTargetOf hRT, hS4,
      receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) receiver _ _ _ _
        hNoY, hTY]
    rfl
  refine ⟨summary, Y1.mapTcbInPlace receiver (holdMessage (blockedSenderMessage P s sTcb)), ?_, ?_, ?_⟩
  · have hTr' := hTr
    simp only [S4, W, P] at hTr'
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hTr']
    rfl
  · have hK0 : KeepsBindings S4 S4 := KeepsBindings.refl S4
      (by rw [hS4]; exact (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY)
    have hK := receiveTransferCaps_keepsBindings _ _ _ hK0 hTr
    apply applyReceiveRendezvousHandoff_of_no_call
    exact rendezvousDequeuedCall_of_keepsBindings hK s
      (receiveTake_dequeuedNoCall st endpointId ep receiver core s sTcb _ hE hH hT hG)
  · have hNoZ : (Architecture.stageWokenSendCompletion Y1 (some s)).objects.noResizeDue := by
      unfold Architecture.stageWokenSendCompletion
      dsimp only
      split
      · split
        · exact updateTcb_noResizeDue _ _ _ hNo1
        · exact hNo1
      · exact hNo1
    rw [stageWokenSendCompletion_msg _ receiver s _ _ _ hRS hNo1,
      stageDeliveredMessage_holdMessage_caps _ _ _ _ hNoZ
        (by rw [hMsg, Architecture.regMessageBody_size]
            simp only [Architecture.regMessageLength]
            have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
            omega),
      hMsg, TCB.ipcBadgeView_eq_opt, returnFrameOfMessage_regMessageBody_caps]
    have hKY : KeepsBindings (W.1.updateTcb receiver receiverReady) Y1 :=
      receiveTransferCaps_keepsBindings _ _ _ (KeepsBindings.refl _ hNoY) hTY
    have hFrame : ∀ g, writeDeliveredFrameIfReady
        (Architecture.stageWokenSendCompletion Y1 (some s))
        receiver (regMessageFrameCapsW SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged summary.capInfo) g =
        finishTakeCaps summary.capInfo Y1 s receiver SeLe4n.arm64DefaultLayout mi.length
          (Architecture.badgeWordIf (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 0)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 1)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 2)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 3) := by
      intro g
      unfold writeDeliveredFrameIfReady finishTakeCaps
      rw [stageWokenSendCompletion_getTcb?_ne _ s receiver hRS hNo1]
      cases hZ : Y1.getTcb? receiver with
      | none =>
        exact (mapTcbInPlace_eq_self_of_getTcb?_none _ _ _
          (by rw [stageWokenSendCompletion_getTcb?_ne _ s receiver hRS hNo1, hZ])).symm
      | some t =>
        simp only [ready_of_keepsBindings_receiverReady hNoW hKY hZ, ↓reduceIte]
        rfl
    rw [hFrame]
    unfold performTakeCapsDelivered
    have hK := capTransferK_eq
      ((wakeThread ((storePopHead st endpointId false s
        (ThreadId.ofOptCode sTcb.queueNextCode)).updateTcb s receiverReady) s core).1.updateTcb
          receiver receiverReady)
      endpointId sTcb (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0) rt
      (fun i Y => finishTakeCaps i Y s receiver SeLe4n.arm64DefaultLayout mi.length
          (Architecture.badgeWordIf (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 0)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 1)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 2)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 3))
    simp only at hK
    rw [hK]
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode, hA.frameCapRequestOf,
      hA.capTargetOf]
    rw [hTY]

/-- **The take of a blocked capability-carrying call that transfers,
delivered**: the WithCaps receive takes the caller in place and runs the
specification's transfer on the state the take left; the transfer keeps every
thread's binding and carries every thread, so the rendezvous still dequeues a
caller and donates nothing, and runs the receiver's priority walk; the caller
stays blocked, so its completion stages nothing, and staging the receiver's
message with the transfer's report writes `performCallTakeCapsDelivered`'s
state. -/
theorem receiveCallTakeCapsTransfer_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (s : SeLe4n.ThreadId) (sTcb rt : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hRT : st.getTcb? receiver = some rt)
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .transferring .call capAddr mi)
    (hLen : mi.length ≤ 4) (hF : sTcb.ipcFaultSend = false) :
    ∃ (summary : CapTransferSummary) (st'' : SystemState),
      endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) core st =
        (st'', .ok (s, summary, none)) ∧
      applyReceiveRendezvousHandoff st'' receiver s core =
        .ok (applyReceiverPipHandoff st'' receiver core) ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion
          (applyReceiverPipHandoff st'' receiver core) (some s)) receiver summary.capInfo =
        performCallTakeCapsDelivered st endpointId s sTcb.queueNextCode receiver rid core
          SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.vspaceRoot sTcb.ipcBuffer
          sTcb.cspaceRoot (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0)
          rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot := by
  obtain ⟨hTake, hIpc, hBs, hBr⟩ :=
    receiveCallTake_inPlace st endpointId ep receiver rid core s sTcb hE hH hT hG
  have hG' := hG
  simp only [receiveCallTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hRTd⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, _⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RobinHood.RHTable.noResizeDue_of_findsInPlace hFE
  have hDN : callDonatesNothing sTcb rt = true := by simpa only [hRT] using hRTd
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hSnd : receiveRendezvousSender? st endpointId = some s := by
    simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
      Option.bind_some, hH]
  have hMsg := blockedSender_of_routedTransferring
    (storePopHead st endpointId false s sTcb.queueNext) s sTcb capAddr mi hR hLen hF
  have hReq : receiveCapRequest st endpointId =
      frameCapRequestOf st sTcb
        (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0) := by
    simp only [receiveCapRequest, hSnd, hTs, blockedSenderCapRequest, hF, Bool.false_eq_true,
      ↓reduceIte]
    exact senderFrameCapRequest_routed st s sTcb _ capAddr mi .call _ rfl hR hLen
  have hNoX := storeReceiveCallReady_noResizeDue st endpointId s sTcb.queueNextCode receiver
    rid hNo
  have hA := ipcBufferReadsAgree_storeReceiveCallReady st endpointId s sTcb.queueNextCode
    receiver rid hNo
  obtain ⟨summary, Y1, hTY⟩ := receiveTransferCaps_ok
    (frameCapRequestOf st sTcb (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0))
    (some endpointId) (capTargetOf st rt)
    (storeReceiveCallReady st endpointId s sTcb.queueNextCode receiver rid)
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ _ Y1 summary hNoX hTY
  have hS4 := receiveCallTakeState_eq_hold st endpointId s sTcb receiver rid hNo
  have hTr : receiveTransferCaps (receiveCapRequest st endpointId) (some endpointId)
      (receiverCapTarget? st receiver) (receiveCallTakeState st endpointId s sTcb receiver rid) =
        .ok (summary, Y1.mapTcbInPlace receiver (holdMessage (blockedSenderMessage
          (storePopHead st endpointId false s sTcb.queueNext) s sTcb))) := by
    rw [hReq, receiverCapTarget?_eq_capTargetOf hRT, hS4,
      receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) receiver _ _ _ _
        hNoX, hTY]
    rfl
  have hNoS4 : (receiveCallTakeState st endpointId s sTcb receiver rid).objects.noResizeDue := by
    rw [hS4]; exact (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoX
  have hNoZ : (Y1.mapTcbInPlace receiver (holdMessage (blockedSenderMessage
      (storePopHead st endpointId false s sTcb.queueNext) s sTcb))).objects.noResizeDue :=
    (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo1
  have hC := receiveTransferCaps_carriesThreads _ _ _ (CarriesThreads.refl _ hNoS4) hTr
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpc
  obtain ⟨x', hx', e'⟩ := hC.2 s x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  have hxI' : x'.ipcState = .blockedOnReply endpointId (some receiver) := by
    have h' := congrArg TCB.ipcState (show x'.withoutLinks = x.withoutLinks from e')
    rw [← hxI]; exact h'
  refine ⟨summary, Y1.mapTcbInPlace receiver (holdMessage (blockedSenderMessage
    (storePopHead st endpointId false s sTcb.queueNext) s sTcb)), ?_, ?_, ?_⟩
  · unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hTr]
  · have hK := receiveTransferCaps_keepsBindings _ _ _ (KeepsBindings.refl _ hNoS4) hTr
    have hCall : rendezvousDequeuedCall (Y1.mapTcbInPlace receiver (holdMessage
        (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb))) s =
          true := by
      unfold rendezvousDequeuedCall
      simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte,
        (SystemState.getTcb?_eq_some_iff _ _ _).mpr hx', hxI']
    obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff s).mpr hSRes)
    obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff receiver).mpr hRRes)
    have hNone0 : callDonationSchedContext? (receiveCallTakeState st endpointId s sTcb receiver rid)
        s receiver = none := by
      rw [callDonationSchedContext?_congr (s := st) hBs hBr, callDonationSchedContext?_eq_bindings]
      simp only [lookupTcb, hRRes, hSRes, Bool.false_eq_true, ↓reduceIte, hRT, hTs,
        Option.map_some]
      revert hDN
      unfold callDonatesNothing
      cases rt.schedContextBinding <;> cases sTcb.schedContextBinding <;>
        simp [donationOfBindings, SchedContextBinding.scId?]
    have hNone := callDonationSchedContext?_none_of_sameSchedContextBindings
      hK.sameSchedContextBindings s receiver hNone0
    unfold applyReceiveRendezvousHandoff
    rw [applyReceiveRendezvousDonation_of_no_donation _ receiver s sv rv hsv hrv hNone]
    simp only [hCall, ↓reduceIte]
  · obtain ⟨x'', hx'', hxI''⟩ := propagatePipChainCrossCore_ipcStateCarried _ receiver core hNoZ
      s x' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hx')
    unfold applyReceiverPipHandoff
    rw [Architecture.stageWokenSendCompletion_id_when_not_ready _ s x'' hx''
      (by rw [hxI'', hxI']; simp)]
    rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNo1,
      stageDeliveredMessage_holdMessage_caps _ _ _ _
        (propagatePipChainCrossCore_noResizeDue _ _ _ hNo1)
        (by rw [hMsg, Architecture.regMessageBody_size]
            simp only [Architecture.regMessageLength]
            have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
            omega),
      hMsg, TCB.ipcBadgeView_eq_opt, returnFrameOfMessage_regMessageBody_caps]
    unfold performCallTakeCapsDelivered
    have hK := capTransferK_eq (storeReceiveCallReady st endpointId s sTcb.queueNextCode receiver rid)
      endpointId sTcb (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0) rt
      (fun i Y => finishCallCaps i Y receiver core SeLe4n.arm64DefaultLayout sTcb.registerContext
        mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
    simp only at hK
    rw [hK, hA.frameCapRequestOf, hA.capTargetOf, hTY]
    rfl

/-- WS-ZA ZA4.7: **the staged send rendezvous is the delivered one** for a
message of at most four words read in the sender's registers. -/
theorem sendRendezvous_eq_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (hNo : st.objects.noResizeDue) (hSz : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.stageWokenDelivery
        (clearWokenReceiverStashPure (some r)
          (wakeThread (storeSendRendezvous st endpointId r next
            { registers := Architecture.regMessageBody layout rf len,
              badge := SeLe4n.Badge.opt badgeWord badged }) r core).1)
        (some r) 0 =
      performSendDelivered st endpointId r (ThreadId.optCode next) layout rf len badgeWord badged
        core := by
  have hNo0 := storeSendRendezvousWith_noResizeDue st endpointId r next ipcReadyTcb hNo
  unfold performSendDelivered storeSendRendezvousReady
  rw [Architecture.regMessageFrameW_eq, SeLe4n.ThreadId.ofOptCode_optCode]
  rw [storeSendRendezvous_eq_with, receiveCompleteTcb_eq_slots, receiveReadyTcb_eq_slots,
    storeSendRendezvousWith_comp _ _ _ _ _ _ hNo, storeSendRendezvousWith_comp _ _ _ _ _ _ hNo]
  simp only [receiveCompleteSlots, clearMessageSlots]
  rw [wakeThread_msg _ _ _ _ _ _ _ hNo0, wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace,
    Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _
      ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr (wakeThread_noResizeDue _ _ _ hNo0))
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

/-- WS-ZA ZA6.35: **the staged send rendezvous is the delivered one** for a
message of more than four words, its inline words read in the sender's
registers and the rest in its IPC buffer. -/
theorem sendRendezvous_eq_deliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (sender : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue)
    (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    Architecture.stageWokenDelivery
        (clearWokenReceiverStashPure (some r)
          (wakeThread (storeSendRendezvous st endpointId r next
            (longSendMessage layout rf st sender len (SeLe4n.Badge.opt badgeWord badged))) r
            core).1)
        (some r) 0 =
      performSendDeliveredLong st endpointId r (ThreadId.optCode next) layout rf len sender
        badgeWord badged core := by
  have hNo0 := storeSendRendezvousWith_noResizeDue st endpointId r next ipcReadyTcb hNo
  have hNoX : (wakeThread (storeSendRendezvousReady st endpointId r (ThreadId.optCode next)) r
      core).1.objects.noResizeDue :=
    wakeThread_noResizeDue _ r core
      (storeSendRendezvousWith_noResizeDue st endpointId r
        (ThreadId.ofOptCode (ThreadId.optCode next)) receiveReadyTcb hNo)
  unfold performSendDeliveredLong
  rw [deliverLongSendFrame_eq _ st r sender layout rf len badgeWord badged hNoX
    (ipcBufferReadsAgree_sendWoken st endpointId r _ core hNo) hSize hLen]
  unfold storeSendRendezvousReady
  rw [SeLe4n.ThreadId.ofOptCode_optCode]
  rw [storeSendRendezvous_eq_with, receiveCompleteTcb_eq_slots, receiveReadyTcb_eq_slots,
    storeSendRendezvousWith_comp _ _ _ _ _ _ hNo, storeSendRendezvousWith_comp _ _ _ _ _ _ hNo]
  simp only [receiveCompleteSlots, clearMessageSlots]
  rw [wakeThread_msg _ _ _ _ _ _ _ hNo0, wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace, Architecture.stageWokenDelivery_some]

/-- WS-ZA ZA4.7: a send blocks, and writes only its slots: the sender may be
enqueued (`enqueueAdmits`) and every write stays in place
(`enqueuesInPlace`), the send queue's tail read as its code. -/
@[inline] def sendBlocksFast (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (tailCode : Nat) : Bool :=
  match st.getTcb? sender with
  | some t => enqueueAdmits t && enqueuesInPlaceCode st endpointId sender tailCode
  | none => false

/-- WS-ZA ZA4.7: the checked send arm (`dispatchWithCapChecked`'s `.send` case)
for a sender whose saved registers `rf` hold a message of `len` words and no
capability addresses, refusing in the state it was handed
(`endpointSendCheckedArmR_eq`).  A send to a waiting receiver whose checks all
pass before any write (`sendWakesInPlace`) wakes the receiver in place and
writes the words into its saved registers (`performSendDelivered`,
`sendRendezvous_eq_delivered`); WS-ZA ZA6.35: a send of more than four words
also copies the words past the fourth from the sender's IPC buffer into the
receiver's, word by word (`performSendDeliveredLong`,
`sendRendezvous_eq_deliveredLong`), as seL4's `copyMRs` does; a send with no
receiver waiting whose checks all pass (`sendBlocksFast`) blocks in place,
its words left in its registers (`sendBlock_inPlace_eq`); any other send takes
the general arm. -/
@[inline] def endpointSendCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    if (st.getTcb? tid).isSome &&
                        endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                          (ctx.endpointLabelOf epId) &&
                        sendWakesInPlaceCode st epId r rt.queueNextCode then
                      if len ≤ 4 then
                        .ok ((), performSendDelivered st epId r rt.queueNextCode layout rf len
                          cap.badgeWord cap.badged executingCore)
                      else
                        .ok ((), performSendDeliveredLong st epId r rt.queueNextCode layout rf len
                          tid cap.badgeWord cap.badged executingCore)
                    else endpointSendCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointSendCheckedArmGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeSendBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointSendCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointSendCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

/-- WS-ZA ZA6.35: **what a send's frame routes as**, read for the sender `tid`
whose saved registers `rf` are: a capability-free send of at most four words,
or a capability-free long send whose overflow slots all read in `st`. -/
def SendFrameRouted (st : SystemState) (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) : Prop :=
  registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi ∨
    (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi ∧
      ∀ j, j < mi.length - 4 →
        ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)

/-- A routed frame asks to transfer no capability. -/
theorem SendFrameRouted.capRequest {st : SystemState} {tid : SeLe4n.ThreadId}
    {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr} {mi : MessageInfo}
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : SendFrameRouted st tid rf capAddr mi) :
    ∀ endpointId badge grant, sendCapRequest st endpointId tid (.frame badge grant) = none := by
  rcases hR with hR | ⟨hR, hRead⟩
  · exact (routedSenderFrame st tid rf capAddr mi hFrame (.inl hR)).1
  · exact (routedLongSenderFrame st tid rf capAddr mi hFrame hR hRead).1

/-- The fast send arm is the general one for a sender whose saved registers
`rf` route as a capability-free send (`SendFrameRouted`): the words it writes
in place are the words the specification's send reads from that frame
(`routedSenderFrame`, `routedLongSenderFrame`). -/
theorem endpointSendCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : SendFrameRouted st tid rf capAddr mi) :
    endpointSendCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      endpointSendCheckedArmGeneralR ctx tid executingCore cap st := by
  have hReq := SendFrameRouted.capRequest hFrame hR
  unfold endpointSendCheckedArmR
  split
  · next epId hTgt =>
    split
    · next ep hE =>
      split
      · next r hH =>
        split
        · next rt hT =>
          split
          · next hG =>
            simp only [Bool.and_eq_true] at hG
            obtain ⟨⟨hS, hFlow⟩, hW⟩ := hG
            rw [sendWakesInPlaceCode_eq, TCB.ofOptCode_queueNextCode] at hW
            have hNo : st.objects.noResizeDue := by
              simp only [sendWakesInPlace, Bool.and_eq_true] at hW
              exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW.1.1.1.2
            unfold endpointSendCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            split
            · next hShort =>
              rcases hR with hR | ⟨hR, _⟩
              · have hMsg := (routedSenderFrame st tid rf capAddr mi hFrame (.inl hR)).2
                have hSz : Architecture.regMessageLength SeLe4n.arm64DefaultLayout mi.length ≤ 4 := by
                  unfold Architecture.regMessageLength; omega
                rw [sendDispatchChecked_inPlace ctx st epId ep tid r rt _ _ executingCore
                  (hMsg _ _ hS) (hReq _ _ _) hE hH hT hS hW hFlow]
                simp only []
                rw [← TCB.optCode_queueNext,
                  ← sendRendezvous_eq_delivered _ _ _ _ _ _ _ _ _ _ hNo hSz]
                rfl
              · have hGt := (decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr
                  mi hR).1
                have hSz4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
                rw [hSz4] at hGt
                exact absurd hShort (by omega)
            · next hLong =>
              rcases hR with hR | ⟨hR, hRead⟩
              · exact absurd (Nat.le_trans
                  (registerRoutedSyscall_send_length _ rf 32 capAddr mi hR) (by decide)) hLong
              · have hMsg := (routedLongSenderFrame st tid rf capAddr mi hFrame hR hRead).2
                rw [sendDispatchChecked_inPlace ctx st epId ep tid r rt _ _ executingCore
                  (hMsg _ _ hS) (hReq _ _ _) hE hH hT hS hW hFlow]
                simp only []
                rw [← TCB.optCode_queueNext,
                  ← sendRendezvous_eq_deliveredLong _ _ _ _ _ _ _ _ _ _ _ hNo rfl (by omega)]
                rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            unfold endpointSendCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointSendCrossCoreDispatchChecked
            rw [if_pos hFlow,
              endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ (hReq _ _ _),
              sendBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointSendCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

/-- The fast send arm is the specification's for a sender whose saved
registers `rf` route as a capability-free send of `mi.length` words. -/
theorem endpointSendCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : SendFrameRouted st tid rf capAddr mi) :
    endpointSendCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointSendCheckedArmR_eq_general ctx rf capAddr mi tid executingCore cap st hFrame hR]
  exact endpointSendCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hSend
    (SendFrameRouted.capRequest hFrame hR)

/-- The receiver a send's content reaches, read from the pre-state before the
arm: the head of the receive queue of the endpoint its capability names
(`senderTaintEdges`), as its code (`SeLe4n.ThreadId.optCode`), so the value
held across the arm is a word, not an `Option` cell. -/
@[inline] def sendTaintHeadCode (st : SystemState) (cap : Capability) : Nat :=
  match cap.target with
  | .object epId =>
      match st.getEndpoint? epId with
      | some ep => ep.recvHeadCode
      | none => 0
  | _ => 0

/-- The send's taint step, without the plan: the sender's words `wT`, captured
before the arm, join the receiver's taint words (`sendTaintStep_eq`).  It builds
no edge list and no plan record. -/
@[inline] def sendTaintStep (headCode : Nat) (tid : SeLe4n.ThreadId)
    (wT : TaintWords) (post : SystemState) : SystemState :=
  match headCode with
  | r + 1 =>
      let receiver : SeLe4n.ThreadId := ⟨r⟩
      joinTaintAt post receiver.toObjId wT
  | 0 => post

theorem sendTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult)
    (hSend : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (preEpoch : Nat) (preLength : Nat) (wT : TaintWords)
    (hT : wT.decode = st.declassificationTaint tid.toObjId) (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength
        st.declassificationTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (sendTaintHeadCode st cap) tid wT post
        | none => post) := by
  rcases hSend with hSend | hSend <;>
  simp only [syscallTaintPlan, contentFlowClass, hSend, contentFlowEdges, contentFlowClears,
    contentFlowBypassed] <;>
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩ <;>
  first
  | simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]; done
  | cases target with
    | object epId =>
      simp only [sendTaintHeadCode, senderTaintEdges]
      cases st.getEndpoint? epId with
      | none =>
        simp [sendTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_recvHeadCode]
        cases ep.recvHeadCode <;>
          simp [sendTaintStep, SeLe4n.ThreadId.ofOptCode, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep,
            joinTaintAt_toWords_of_decode _ _ hT]
    | _ =>
      simp [sendTaintHeadCode, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]

/-- The send's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`sendOperandArmThenTaintR_eq`). -/
@[inline] def sendOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointSendCheckedArmR ctx layout rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep headCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem sendOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSend : decoded.syscallId = .send)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : SendFrameRouted st tid rf capAddr mi)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore
        gate.requiredRight
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSend, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inl hSend) (wT := st.taintWordsAt tid.toObjId)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [sendOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointSendCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr mi st
          hSend hFrame hR]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The send's dispatch for a sender whose saved registers hold its message and
no capability addresses: `dispatchOperandCheckedR` with the send's arm
(`dispatchSendCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchSendCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (sendOperandArmThenTaintR ctx layout rf len tid executingCore (syscallRequiredRight .send))

theorem dispatchSendCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : SendFrameRouted st tid rf capAddr mi) :
    dispatchSendCheckedR ctx decoded.capAddr SeLe4n.arm64DefaultLayout rf mi.length tid
        executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hSend]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := sendOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref rf capAddr mi hSend hFrame hR hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hSend] at hArm ⊢
  exact hArm

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) through the
specification's dispatch, refusing in the state it was handed
(`endpointCallCheckedArmGeneralR_eq`).  As the specification's, it is handed
only the capability's badge and grant right: the words are read from the
caller's frame. -/
def endpointCallCheckedArmGeneralR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid
            (.frame cap.badge (cap.rights.mem .grant))
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' woken? summary.capInfo)
        | (_, .error e) => .error (e, st)
    | _ => .error (.invalidCapability, st)

theorem endpointCallCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hCall : decoded.syscallId = .call) :
    endpointCallCheckedArmGeneralR ctx tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [endpointCallCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hCall]
  cases cap.target with
  | object epId =>
    simp only []
    rcases endpointCallCrossCoreDispatchChecked ctx epId tid
        (.frame cap.badge (cap.rights.mem .grant)) executingCore st with
      ⟨st', _ | ⟨summary, sgi⟩⟩ <;> rfl
  | _ => rfl

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) for a
caller whose saved registers `rf` hold a message of `len` words and no
capability addresses, refusing in the state it was handed
(`endpointCallCheckedArmR_eq`).  WS-ZA ZA4.7: a rendezvous whose checks all
pass before any write (`callWakesInPlace`, the seL4 decode/perform split) writes
in place on a state nothing else holds (`performCallRendezvous`,
`callDispatchChecked_inPlace`); a call that lends the caller's context to a
passive server, every check of the rendezvous and of the donation passing first
(`callDonatesInPlace`), writes its donation and the replenishment migration
between the two home cores in place too (`performCallDonating`,
`callDispatchChecked_donating_inPlace`; the homes are read here, before the
first write); a call with no receiver waiting whose checks all pass blocks in
place, its words left in its registers (`callBlock_inPlace_eq`), as the send's
does; any other call takes the general arm. -/
@[inline] def endpointCallCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    match rt.pendingReceiveReply with
                    | some rid =>
                        if (st.getTcb? tid).isSome &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callWakesInPlace st epId tid r rt rid then
                          .ok ((), callRendezvousDelivered st epId tid r rt.queueNextCode rid
                            layout rf len
                            cap.badgeWord cap.badged executingCore)
                        else if (st.getTcb? tid).isSome &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callDonatesInPlace st epId tid r rt rid then
                          .ok ((), callRendezvousDonatingDelivered st epId tid r rt.queueNextCode
                            rid (callerScId st tid) (determineTargetCore st tid)
                            (determineTargetCore st r) layout rf len cap.badgeWord cap.badged
                            executingCore)
                        else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                    | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeCallBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

/-- The fast call arm is the general one for a caller whose saved registers
`rf` route as a capability-free call: the words it writes in place are the
words the specification's call reads from that frame (`routedSenderFrame`). -/
theorem endpointCallCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    endpointCallCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      endpointCallCheckedArmGeneralR ctx tid executingCore cap st := by
  obtain ⟨hReq, hMsg⟩ := routedSenderFrame st tid rf capAddr mi hFrame (.inr hR)
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
              simp only [Bool.and_eq_true] at hG
              obtain ⟨⟨hS, hFlow⟩, hW⟩ := hG
              obtain ⟨sgi, hD⟩ := callDispatchChecked_inPlace ctx st epId ep tid r rt rid
                (.frame cap.badge (cap.rights.mem .grant)) _ executingCore
                (hMsg cap.badge (cap.rights.mem .grant) hS) (hReq epId _ _)
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hFlow
              rw [callRendezvousDelivered_eq _ _ _ _ _ _ _ _ _ _ _ _ hW]
              simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH, hD]
              rfl
            · split
              · next hG =>
                simp only [Bool.and_eq_true] at hG
                obtain ⟨⟨hS, hFlow⟩, hW⟩ := hG
                obtain ⟨sgi, hD⟩ := callDispatchChecked_donating_inPlace ctx st epId ep tid r rt rid
                  (.frame cap.badge (cap.rights.mem .grant)) _ executingCore
                  (hMsg cap.badge (cap.rights.mem .grant) hS) (hReq epId _ _)
                  ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hFlow
                rw [callRendezvousDonatingDelivered_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW]
                simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH, hD]
                rfl
              · rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            have hNoRecv : (match st.getEndpoint? epId with
                | some ep => ep.receiveQ.head | none => none) = none := by
              rw [hE]; exact hH
            unfold endpointCallCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointCallCrossCoreDispatchChecked
            rw [if_pos hFlow, endpointCallCrossCoreDispatch_no_receiver _ _ _ _ _ hNoRecv,
              endpointCallWithCapsOnCore_no_caps _ _ _ _ _ (hReq epId _ _),
              callBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointCallCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

/-- The fast call arm is the specification's for a caller whose saved
registers `rf` route as a capability-free call of `mi.length` words. -/
theorem endpointCallCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    endpointCallCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointCallCheckedArmR_eq_general ctx rf capAddr mi tid executingCore cap st hFrame hR,
    endpointCallCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hCall]

/-- The call's slot check, gate, arm and taint step on the capability its
operand resolved to; a call moves content as a send does (`sendTaintStep`).
Every refusal carries the state it was handed (`callOperandArmThenTaintR_eq`). -/
@[inline] def callOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointCallCheckedArmR ctx layout rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep headCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem callOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    callOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore
        gate.requiredRight
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hCall, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inr hCall) (wT := st.taintWordsAt tid.toObjId)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [callOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointCallCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr mi st
          hCall hFrame hR]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The call's dispatch for a caller whose saved registers hold its message
and no capability addresses: `dispatchOperandCheckedR` with the call's arm
(`dispatchCallCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchCallCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (callOperandArmThenTaintR ctx layout rf len tid executingCore (syscallRequiredRight .call))

theorem dispatchCallCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    dispatchCallCheckedR ctx decoded.capAddr SeLe4n.arm64DefaultLayout rf mi.length tid
        executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hCall]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := callOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref rf capAddr mi hCall hFrame hR hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hCall] at hArm ⊢
  exact hArm

/-! ### The long call -/

/-- The checked call arm for a caller whose saved registers `rf` hold a message
of `len` words, more than four, and no capability addresses, refusing in the
state it was handed (`endpointCallLongCheckedArmR_eq`).  A rendezvous whose
checks all pass before any write (`callWakesInPlace`) wakes the receiver
without the message, then writes the inline words into its saved registers and
copies the rest from the caller's IPC buffer into the receiver's, word by word
(`performCallDeliveredLong`, `stageWokenDelivery_performCallRendezvous_long`),
as seL4's `copyMRs` does; any other call takes the general arm. -/
@[inline] def endpointCallLongCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    match rt.pendingReceiveReply with
                    | some rid =>
                        if (st.getTcb? tid).isSome &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callWakesInPlace st epId tid r rt rid then
                          .ok ((), performCallDeliveredLong st epId tid r rt.queueNextCode rid
                            layout rf len cap.badgeWord cap.badged executingCore)
                        else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                    | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeCallBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

/-- The long call arm is the general one for a caller whose saved registers
`rf` route as a capability-free long call whose overflow slots all read: the
words it writes in place are the words the specification's call reads from
that frame (`routedLongCallerFrame`). -/
theorem endpointCallLongCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    endpointCallLongCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap
        st =
      endpointCallCheckedArmGeneralR ctx tid executingCore cap st := by
  obtain ⟨hGt, -, -, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32
      capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hL : ¬ mi.length ≤ 4 := by omega
  obtain ⟨hReq, hMsg⟩ := routedLongCallerFrame st tid rf capAddr mi hFrame hR hRead
  unfold endpointCallLongCheckedArmR
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
              simp only [Bool.and_eq_true] at hG
              obtain ⟨⟨hS, hFlow⟩, hW⟩ := hG
              obtain ⟨sgi, hD⟩ := callDispatchChecked_inPlace ctx st epId ep tid r rt rid
                (.frame cap.badge (cap.rights.mem .grant)) _ executingCore
                (hMsg cap.badge (cap.rights.mem .grant) hS) (hReq epId _ _)
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hFlow
              simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH, hD]
              rw [← TCB.optCode_queueNext]
              rw [← stageWokenDelivery_performCallRendezvous_long st epId tid r rt.queueNext rid
                SeLe4n.arm64DefaultLayout rf mi.length cap.badgeWord cap.badged executingCore
                (callWakesInPlace_noResizeDue hW) (callWakesInPlace_ne hW) hSz (by omega)]
              rfl
            · rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            have hNoRecv : (match st.getEndpoint? epId with
                | some ep => ep.receiveQ.head | none => none) = none := by
              rw [hE]; exact hH
            unfold endpointCallCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointCallCrossCoreDispatchChecked
            rw [if_pos hFlow, endpointCallCrossCoreDispatch_no_receiver _ _ _ _ _ hNoRecv,
              endpointCallWithCapsOnCore_no_caps _ _ _ _ _ (hReq epId _ _),
              callBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointCallCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

/-- The long call arm is the specification's. -/
theorem endpointCallLongCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    endpointCallLongCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap
        st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointCallLongCheckedArmR_eq_general ctx rf capAddr mi tid executingCore cap st hFrame hR
      hRead,
    endpointCallCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hCall]

/-- The long call's slot check, gate, arm and taint step on the capability its
operand resolved to (`endpointCallLongCheckedArmR`); a call moves content as a send does (`sendTaintStep`).
Every refusal carries the state it was handed (`callLongOperandArmThenTaintR_eq`). -/
@[inline] def callLongOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointCallLongCheckedArmR ctx layout rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep headCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem callLongOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore
        gate.requiredRight
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hCall, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inr hCall) (wT := st.taintWordsAt tid.toObjId)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [callLongOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointCallLongCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr mi st
          hCall hFrame hR hRead]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The long call's dispatch for a caller whose saved registers and IPC buffer
hold its message and no capability addresses: `dispatchOperandCheckedR` with the call's arm
(`dispatchCallLongCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchCallLongCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (callLongOperandArmThenTaintR ctx layout rf len tid executingCore (syscallRequiredRight .call))

theorem dispatchCallLongCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    dispatchCallLongCheckedR ctx decoded.capAddr SeLe4n.arm64DefaultLayout rf mi.length tid
        executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hCall]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := callLongOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref rf capAddr mi hCall hFrame hR hRead hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hCall] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.7: the caller a reply's content reaches, read from the pre-state
before the arm: the caller the reply object its capability names records
(`replyTaintEdges`). -/
@[inline] def replyTaintCaller? (st : SystemState) (cap : Capability) :
    Option SeLe4n.ThreadId :=
  match cap.target with
  | .replyCap rid => (st.getReply? rid).bind (·.caller)
  | _ => none

/-- The reply's taint step is the send's, toward the answered caller. -/
theorem replyTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hReply : decoded.syscallId = .reply)
    (preEpoch : Nat) (preLength : Nat) (wT : TaintWords)
    (hT : wT.decode = st.declassificationTaint tid.toObjId) (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength
        st.declassificationTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (ThreadId.optCode (replyTaintCaller? st cap)) tid wT post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hReply, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
  · cases target with
    | replyCap rid =>
      simp only [replyTaintCaller?, replyTaintEdges]
      cases (st.getReply? rid).bind (·.caller) <;>
        simp [sendTaintStep, ThreadId.optCode, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep,
          joinTaintAt_toWords_of_decode _ _ hT]
    | _ =>
      simp [replyTaintCaller?, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]

/-- WS-ZA ZA4.7: the checked reply arm (`dispatchWithCapChecked`'s `.reply`
case), through the specification's transfer, refusing in the state it was
handed (`endpointReplyCheckedArmGeneralR_eq`). -/
def endpointReplyCheckedArmGeneralR (ctx : LabelingContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .replyCap rid =>
        match replyAnsweredCaller? st rid with
        | none => .error (.replyCapInvalid, st)
        | some callerTid =>
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) then
              match replyTransferOnCoreChecked ctx tid callerTid mi regs
                  { registers := extractMessageRegisters regs mi,
                    badge := cap.badge } (cap.rights.mem .grant) executingCore st with
              | .ok ((), st') => .ok ((), st')
              | .error e => .error (e, st)
            else .error (.replyCapInvalid, st)
    | _ => .error (.invalidCapability, st)

theorem endpointReplyCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hReply : decoded.syscallId = .reply) :
    endpointReplyCheckedArmGeneralR ctx decoded.msgInfo decoded.msgRegs tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [endpointReplyCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hReply]
  cases cap.target with
  | replyCap rid =>
    simp only []
    cases replyAnsweredCaller? st rid with
    | none => rfl
    | some callerTid =>
      simp only []
      split
      · rcases replyTransferOnCoreChecked ctx tid callerTid decoded.msgInfo decoded.msgRegs
          { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
            badge := cap.badge } (cap.rights.mem .grant) executingCore st with
          _ | ⟨⟨⟩, st'⟩ <;> rfl
      · rfl
  | _ => rfl

/-- The general reply arm on a message read in registers: the registers are read
where this is called, so only the general arm reads them. -/
@[inline] def endpointReplyCheckedArmRegsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  endpointReplyCheckedArmGeneralR ctx
      { length := len, extraCaps := extraCaps, label := label }
      (Architecture.regMessageRegs layout rf) tid
    executingCore cap

/-- WS-ZA ZA6.33: the checked reply arm on a reply whose reply object heads the
stack of the context its server holds on loan (seL4-MCS's `reply_pop`): a reply
of at most four words whose checks all pass before any write
(`replyPopsInPlace`) writes in place (`performReplyDonatedDelivered`,
`replyTransferChecked_donated_inPlace`); any other takes the general arm.  Out
of line, taking the caller's binding code and fault flag rather than its TCB,
so nothing the writes rewrite is held across them. -/
@[noinline] def replyDonatedAdmits (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (tid : SeLe4n.ThreadId)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (cBinding : Nat) (cFault : Bool)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len ≤ 4) &&
    securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
    !server.isReserved && !cFault && replyPopsInPlace st c cBinding server rid

/-- The donated reply's arm: the checks of `replyDonatedAdmits`, then the
in-place writes or the general arm. -/
@[inline] def endpointReplyDonatedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (cBinding : Nat) (cFault : Bool) :
    RefusalCarrying Unit :=
  fun st =>
    if replyDonatedAdmits ctx layout len tid c server rid cBinding cFault st then
      .ok ((), performReplyDonatedDelivered st c server rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)
        layout rf len cap.badgeWord cap.badged executingCore)
    else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap st

/-- WS-ZA ZA6.34: the checked reply arm on a caller recording no server, its
server finalised (seL4-MCS's `doReplyTransfer` on a caller `finaliseCap` left
blocked): a reply of at most four words whose checks all pass before any write
(`replyUnheldPopsInPlace`), the reply object heading a context no thread holds,
writes in place (`performReplyUnheldDelivered`,
`replyTransferChecked_unheld_inPlace`); any other takes the general arm.  Out of
line, taking the caller's fault flag rather than its TCB, so nothing the writes
rewrite is held across them. -/
@[noinline] def replyUnheldAdmits (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (cFault : Bool) (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len ≤ 4) &&
    securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
    !cFault && replyUnheldPopsInPlace st c rid

/-- The no-server reply's arm: the checks of `replyUnheldAdmits`, then the
in-place writes or the general arm. -/
@[inline] def endpointReplyUnheldArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (cFault : Bool) : RefusalCarrying Unit :=
  fun st =>
    if replyUnheldAdmits ctx layout len tid c rid cFault st then
      .ok ((), performReplyUnheldDelivered st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) layout rf len cap.badgeWord cap.badged)
    else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap st

/-- Whether a reply to a faulted caller may answer it in place on a donated
reply (`replyPopsInPlace`), behind the flow gate.  Out of line, taking the
caller's binding code rather than its TCB, as `replyDonatedAdmits` does. -/
@[noinline] def replyDonatedFaultAdmits (ctx : LabelingContext) (tid c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (cBinding : Nat) (st : SystemState) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
    !server.isReserved && replyPopsInPlace st c cBinding server rid

/-- The donated reply to a faulted caller: the checks of
`replyDonatedFaultAdmits`, then the fault answered in place
(`performFaultReplyDonatedAnswer`, `faultReplyTransferChecked_donated_inPlace`)
from the caller's fault words, read off the pre-state, or the general arm. -/
@[inline] def endpointReplyDonatedFaultArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (cBinding kind : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : RefusalCarrying Unit :=
  fun st =>
    if replyDonatedFaultAdmits ctx tid c server rid cBinding st then
      .ok ((), performFaultReplyDonatedAnswer st c server rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) executingCore kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
        layout rf (min len layout.msgRegs.size))
    else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap st

/-- Whether a reply to a faulted caller recording no server may answer it in
place (`replyUnheldPopsInPlace`), behind the flow gate. -/
@[noinline] def replyUnheldFaultAdmits (ctx : LabelingContext) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (st : SystemState) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) && replyUnheldPopsInPlace st c rid

/-- The reply to a faulted caller recording no server: the checks of
`replyUnheldFaultAdmits`, then the fault answered in place
(`performFaultReplyUnheldAnswer`, `faultReplyTransferChecked_unheld_inPlace`),
or the general arm. -/
@[inline] def endpointReplyUnheldFaultArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (kind : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : RefusalCarrying Unit :=
  fun st =>
    if replyUnheldFaultAdmits ctx tid c rid st then
      .ok ((), performFaultReplyUnheldAnswer st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf
        (min len layout.msgRegs.size))
    else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap st

/-- WS-ZA ZA4.7: the checked reply arm (`dispatchWithCapChecked`'s `.reply`
case), refusing in the state it was handed (`endpointReplyCheckedArmR_eq`).  A
reply to an unfaulted caller blocked on it whose checks all pass before any
write (`replyWakesInPlace`) writes in place on a state nothing else holds
(`performReplyRendezvous`, `replyTransferChecked_inPlace`), and one to a
faulted caller under the same checks answers its fault in place
(`performFaultReplyAnswer`, `faultReplyTransferChecked_inPlace`), as one on a
donated reply or to a caller recording no server does
(`endpointReplyDonatedFaultArmR`, `endpointReplyUnheldFaultArmR`), the answer the
`.replyRecv` arm shares (`performFaultAnswer`).  An unfaulted caller is
answered in place only when the reply transfers no capability
(`replyTransferInertW`: the reply capability lacks the grant right, or the
caller has no IPC buffer or names no receive slot); any other reply takes the
general arm, which runs seL4's `doReplyTransfer` capability transfer. -/
@[inline] def endpointReplyCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .replyCap rid0 =>
        match st.getReply? rid0 with
        | some rp0 =>
            match rp0.caller with
            | some c =>
                match st.getTcb? c with
                | some ct =>
                    match ct.ipcState with
                    | .blockedOnReply _ (some server) =>
                        match ct.replyObject with
                        | some rid =>
                            if !decide (Architecture.regMessageLength layout len >
                                  maxMessageRegisters) &&
                                securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
                                !server.isReserved && replyWakesInPlace st c ct rid then
                              if !ct.faultWords.isFault then
                                if replyTransferInertW st ct (cap.rights.mem .grant) then
                                  .ok ((), replyRendezvousDelivered st c server rid
                                    layout rf len cap.badgeWord cap.badged executingCore)
                                else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps
                                  label tid executingCore cap st
                              else
                                .ok ((), performFaultReplyAnswer st c server rid executingCore
                                  ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
                                  ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
                                  ct.faultX6 ct.faultX7 layout rf (min len layout.msgRegs.size))
                            else if ct.faultWords.isFault then
                              endpointReplyDonatedFaultArmR ctx layout rf len extraCaps label tid
                                executingCore cap c server rid ct.scBindingScCode ct.faultKind
                                ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
                                ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 st
                            else if replyTransferInertW st ct (cap.rights.mem .grant) then
                              endpointReplyDonatedArmR ctx layout rf len extraCaps label tid
                                executingCore cap c server rid ct.scBindingScCode
                                ct.faultWords.isFault st
                            else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                              tid executingCore cap st
                        | none => endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                            tid executingCore cap st
                    | .blockedOnReply _ none =>
                        match ct.replyObject with
                        | some rid =>
                            if ct.faultWords.isFault then
                              endpointReplyUnheldFaultArmR ctx layout rf len extraCaps label tid
                                executingCore cap c rid ct.faultKind ct.faultIp ct.faultSp
                                ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
                                ct.faultX5 ct.faultX6 ct.faultX7 st
                            else if replyTransferInertW st ct (cap.rights.mem .grant) then
                              endpointReplyUnheldArmR ctx layout rf len extraCaps label tid
                                executingCore cap c rid ct.faultWords.isFault st
                            else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                              tid executingCore cap st
                        | none => endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                            tid executingCore cap st
                    | _ =>
                        endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                          tid executingCore cap st
                | none =>
                    endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                      tid executingCore cap st
            | none =>
                endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                  tid executingCore cap st
        | none =>
            endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
              tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointReplyCheckedArmR_eq_general (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore cap =
      endpointReplyCheckedArmGeneralR ctx
      { length := len, extraCaps := extraCaps, label := label }
      (Architecture.regMessageRegs layout rf) tid
        executingCore cap := by
  funext st
  unfold endpointReplyCheckedArmR
  split
  · next rid0 hTgt =>
    split
    · next rp0 hR0 =>
      split
      · next c hC =>
        split
        · next ct hT =>
          split
          · next ep server hIpc =>
            split
            · next rid hRO =>
              split
              · next hG =>
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hG
                obtain ⟨⟨⟨hSz, hFlow⟩, hSRes⟩, hW⟩ := hG
                have hAns : replyAnsweredCaller? st rid0 = some c := by
                  rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                split
                · next hNoF =>
                  simp only [Bool.not_eq_true'] at hNoF
                  split
                  · next hI =>
                    rw [replyRendezvousDelivered_eq _ _ _ _ _ _ _ _ _ _ _ hW]
                    rw [replyTransferChecked_inPlace ctx st tid c server ct ep rid
                      { length := len, extraCaps := extraCaps, label := label }
                      (Architecture.regMessageRegs layout rf) _ _ executingCore
                      (by rw [← Architecture.regMessageBody_size layout rf len] at hSz; exact hSz)
                      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes hW hNoF
                      (replyTransferInert_of_W hI) hFlow]
                    rfl
                  · simp only [endpointReplyCheckedArmRegsR, endpointReplyCheckedArmGeneralR, hTgt,
                      hAns, hFlow, ↓reduceIte]
                · next hF =>
                  simp only [Bool.not_eq_true', Bool.not_eq_false] at hF
                  rw [faultReplyTransferChecked_inPlace ctx st tid c server ct ep rid
                    { length := len, extraCaps := extraCaps, label := label } layout rf _ _
                    executingCore ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes
                    hW hF]
              · split
                · next hF =>
                  unfold endpointReplyDonatedFaultArmR
                  split
                  · next hG =>
                    unfold replyDonatedFaultAdmits at hG
                    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
                    obtain ⟨⟨hFlow, hSRes⟩, hP⟩ := hG
                    have hAns : replyAnsweredCaller? st rid0 = some c := by
                      rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                    simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                    rw [faultReplyTransferChecked_donated_inPlace ctx st tid c server ct ep rid
                      { length := len, extraCaps := extraCaps, label := label } layout rf _ _
                      executingCore ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes
                      hP hF]
                  · rfl
                split
                rotate_left
                · rfl
                rename_i hI
                unfold endpointReplyDonatedArmR
                split
                · next hG =>
                  unfold replyDonatedAdmits at hG
                  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hG
                  obtain ⟨⟨⟨⟨hSz4, hFlow⟩, hSRes⟩, hNoF⟩, hP⟩ := hG
                  have hAns : replyAnsweredCaller? st rid0 = some c := by
                    rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                  simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                  rw [replyTransferChecked_donated_inPlace ctx st tid c server ct ep rid
                    { length := len, extraCaps := extraCaps, label := label }
                    (Architecture.regMessageRegs layout rf) layout rf len cap.badgeWord cap.badged
                    executingCore
                    { registers := extractMessageRegisters (Architecture.regMessageRegs layout rf) { length := len, extraCaps := extraCaps, label := label }, badge := cap.badge }
                    _ rfl (by simp only [maxMessageRegisters]; omega) hSz4
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes hP hNoF
                    (replyTransferInert_of_W hI) hFlow]
                · rfl
            · rfl
          · next ep hIpc =>
            split
            · next rid hRO =>
              split
              · next hF =>
                unfold endpointReplyUnheldFaultArmR
                split
                · next hG =>
                  unfold replyUnheldFaultAdmits at hG
                  simp only [Bool.and_eq_true] at hG
                  obtain ⟨hFlow, hP⟩ := hG
                  have hAns : replyAnsweredCaller? st rid0 = some c := by
                    rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                  simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                  rw [faultReplyTransferChecked_unheld_inPlace ctx st tid c ct ep rid
                    { length := len, extraCaps := extraCaps, label := label } layout rf _ _
                    executingCore ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hP hF]
                · rfl
              split
              rotate_left
              · rfl
              rename_i hI
              unfold endpointReplyUnheldArmR
              split
              · next hG =>
                unfold replyUnheldAdmits at hG
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hG
                obtain ⟨⟨⟨hSz4, hFlow⟩, hNoF⟩, hP⟩ := hG
                have hAns : replyAnsweredCaller? st rid0 = some c := by
                  rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                rw [replyTransferChecked_unheld_inPlace ctx st tid c ct ep rid
                  { length := len, extraCaps := extraCaps, label := label }
                  (Architecture.regMessageRegs layout rf) layout rf len cap.badgeWord cap.badged
                  executingCore
                  { registers := extractMessageRegisters (Architecture.regMessageRegs layout rf) { length := len, extraCaps := extraCaps, label := label }, badge := cap.badge }
                  _ rfl (by simp only [maxMessageRegisters]; omega) hSz4
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hP hNoF
                  (replyTransferInert_of_W hI) hFlow]
              · rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · next hTgt =>
    unfold endpointReplyCheckedArmGeneralR
    split
    · next rid h => exact absurd h (hTgt rid)
    · rfl

theorem endpointReplyCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
    endpointReplyCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  rw [endpointReplyCheckedArmR_eq_general, hRegs]
  exact endpointReplyCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hReply

/-- WS-ZA ZA4.7: the reply's slot check, gate, arm and taint step on the
capability its operand resolved to; a reply moves content to the answered
caller (`replyTaintCaller?`).  Every refusal carries the state it was handed
(`replyOperandArmThenTaintR_eq`). -/
@[inline] def replyOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let callerCode := ThreadId.optCode (replyTaintCaller? st cap)
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore cap
              st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep callerCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem replyOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    replyOperandArmThenTaintR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        gate.requiredRight (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hReply, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [replyTaintStep_eq st tid decoded hReply (wT := st.taintWordsAt tid.toObjId)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyCheckedArmR_eq ctx decoded tid executingCore gate cap layout rf hReply
          hRegs]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- WS-ZA ZA4.7: the reply's dispatch: `dispatchOperandCheckedR` with the
reply's arm (`dispatchReplyCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchReplyCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (replyOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .reply))

theorem dispatchReplyCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
    dispatchReplyCheckedR ctx decoded.capAddr layout rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hReply]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := replyOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref layout rf hReply hRegs hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hReply] at hArm ⊢
  exact hArm

/-! ### The capability-carrying send and call -/

/-- The checked send arm for a sender whose frame asks to transfer
capabilities, through the specification's send.  Every refusal carries the
state the arm was handed, as the specification's refusal does: a send whose
receiver holds no CSpace root is refused after the rendezvous's writes
(`endpointSendDualWithCapsOnCore`'s fail-closed `.invalidCapability`), and the
whole send is rolled back (`endpointSendCapsGeneralR_eq`). -/
def endpointSendCapsGeneralR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendCrossCoreDispatchChecked ctx epId tid
            (.frame cap.badge (cap.rights.mem .grant))
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery (clearWokenReceiverStashPure woken? st')
              woken? summary.capInfo)
        | (_, .error e) => .error (e, st)
    | _ => .error (.invalidCapability, st)

theorem endpointSendCapsGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hSend : decoded.syscallId = .send) :
    endpointSendCapsGeneralR ctx tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [endpointSendCapsGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSend]
  cases cap.target with
  | object epId =>
    simp only []
    rcases endpointSendCrossCoreDispatchChecked ctx epId tid
        (.frame cap.badge (cap.rights.mem .grant)) executingCore st with
      ⟨st', _ | ⟨summary, sgi⟩⟩
    · rfl
    · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- The checked send arm for a sender whose frame asks to transfer
capabilities, refusing in the state it was handed
(`endpointSendCapsCheckedArmR_eq`).  With no receiver waiting a send resolves
no capability (seL4's `sendIPC` blocks the sender with its message and
capability addresses where they are; the receive that takes it resolves
them), so one whose checks all pass blocks in place
(`sendBlock_inPlace_eq`).  One of at most four words whose transfer transfers
nothing (`senderTransferInertW`, the specification's `capTransferInert`: the
receiver takes no capability, or its buffer names no receive slot and the first
capability does not unwrap, so seL4's `transferCaps` stops at it) writes the
rendezvous in place (`sendDispatchChecked_inPlace_inert`); any other of at most
four words writes the rendezvous in place, resolves the capabilities in its
CSpace and installs or unwraps them in the receiver's in place, and writes the
frame with the transfer's report (`performSendCapsDelivered`, the
specification's transfer by `sendRendezvousCaps_eq_delivered`).  A longer one
runs the specification's transfer (`endpointSendCapsGeneralR`). -/
@[inline] def endpointSendCapsCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    if decide (len ≤ 4) &&
                        endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                          (ctx.endpointLabelOf epId) &&
                        sendWakesInPlaceCode st epId r rt.queueNextCode then
                      if senderTransferInertW st epId rt tid then
                        .ok ((), performSendDelivered st epId r rt.queueNextCode
                          SeLe4n.arm64DefaultLayout rf len cap.badgeWord cap.badged executingCore)
                      else
                      match st.getTcb? tid with
                      | some stcb =>
                        .ok ((), performSendCapsDelivered st epId r rt.queueNextCode
                          SeLe4n.arm64DefaultLayout rf len cap.badgeWord cap.badged executingCore
                          stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
                          (if cap.rights.mem .grant then routedExtraCaps rf else 0)
                          rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot)
                      | none => endpointSendCapsGeneralR ctx tid executingCore cap st
                    else endpointSendCapsGeneralR ctx tid executingCore cap st
                | none => endpointSendCapsGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeSendBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointSendCapsGeneralR ctx tid executingCore cap st
        | none => endpointSendCapsGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointSendCapsCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    endpointSendCapsCheckedArmR ctx rf mi.length tid executingCore cap st =
      endpointSendCapsGeneralR ctx tid executingCore cap st := by
  unfold endpointSendCapsCheckedArmR
  split
  · next epId hTgt =>
    split
    · next ep hE =>
      split
      · next r hH =>
        split
        · next rt hT =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
            obtain ⟨⟨hShort, hFlow⟩, hW⟩ := hG
            rw [sendWakesInPlaceCode_eq, TCB.ofOptCode_queueNextCode] at hW
            have hNo : st.objects.noResizeDue := by
              simp only [sendWakesInPlace, Bool.and_eq_true] at hW
              exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW.1.1.1.2
            have hSz : Architecture.regMessageLength SeLe4n.arm64DefaultLayout mi.length ≤ 4 := by
              unfold Architecture.regMessageLength; omega
            split
            · next hSI =>
              have hS := senderTransferInertW_isSome hSI
              have hMsg := routedTransferringMessage st tid rf capAddr mi sid hFrame hR hShort
              unfold endpointSendCapsGeneralR
              simp only [hTgt, hE, Option.bind_some, hH]
              have hInert := capTransferInert_sendCapRequest_of_W st epId r rt tid cap.badge
                (cap.rights.mem .grant) hT hSI
              obtain ⟨s, hC, hD⟩ := sendDispatchChecked_inPlace_inert ctx st epId ep tid r rt
                _ _ executingCore (hMsg _ _ hS) hE hH hT hS hW hInert hFlow
              rw [hD]
              simp only [hC]
              rw [← TCB.optCode_queueNext,
                ← sendRendezvous_eq_delivered _ _ _ _ _ _ _ _ _ _ hNo hSz]
              rfl
            · split
              · next stcb hS =>
                have hMsg := routedTransferringMessage st tid rf capAddr mi sid hFrame hR hShort
                have hSome : (st.getTcb? tid).isSome = true := by rw [hS]; rfl
                have hb : cap.badge = SeLe4n.Badge.opt cap.badgeWord cap.badged := rfl
                unfold endpointSendCapsGeneralR
                simp only [hTgt, hE, Option.bind_some, hH]
                rw [sendDispatchChecked_inPlace_transfer ctx st epId ep tid r rt _ _ executingCore
                  (hMsg _ _ hSome) hE hH hT hSome hW hFlow,
                  sendCapRequest_routed st epId tid r stcb rf capAddr mi sid _ _
                    (by simp only [hE, Option.bind_some, hH]) hS (hFrame stcb hS) hR hShort,
                  receiverCapTarget?_eq_capTargetOf hT, hb]
                have hEq := sendRendezvousCaps_eq_delivered st epId r rt.queueNext
                  SeLe4n.arm64DefaultLayout rf mi.length cap.badgeWord cap.badged executingCore
                  stcb rt (if cap.rights.mem .grant then routedExtraCaps rf else 0) hNo hSz
                rw [TCB.optCode_queueNext] at hEq
                obtain ⟨s, st'', hOk⟩ := receiveTransferCaps_ok
                  (frameCapRequestOf st stcb (if cap.rights.mem .grant then routedExtraCaps rf else 0))
                  (some epId) (capTargetOf st rt)
                  (wakeThread (storeSendRendezvous st epId r rt.queueNext
                    { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf mi.length,
                      badge := SeLe4n.Badge.opt cap.badgeWord cap.badged }) r executingCore).1
                rw [hOk] at hEq ⊢
                dsimp only at hEq ⊢
                rw [hEq]
              · rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            have hReq := sendCapRequest_of_no_receiver st epId tid
              (.frame cap.badge (cap.rights.mem .grant)) (by simp only [hE, Option.bind_some, hH])
            unfold endpointSendCapsGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointSendCrossCoreDispatchChecked
            rw [if_pos hFlow,
              endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ hReq,
              sendBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointSendCapsGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

theorem endpointSendCapsCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) (hSend : decoded.syscallId = .send)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    endpointSendCapsCheckedArmR ctx rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointSendCapsCheckedArmR_eq_general ctx rf capAddr mi sid tid executingCore cap st
      hFrame hR,
    endpointSendCapsGeneralR_eq ctx decoded tid executingCore gate cap hSend]

/-- The checked call arm for a caller whose frame asks to transfer
capabilities, refusing in the state it was handed
(`endpointCallCapsCheckedArmR_eq`): one with no receiver waiting whose checks
all pass blocks in place, resolving nothing (`callBlock_inPlace_eq`); one of
at most four words whose transfer transfers nothing (`senderTransferInertW`)
writes the call rendezvous in place, the transfer installing nothing
(`callDispatchChecked_inPlace_inert`); any other takes the general
arm, which resolves and installs the capabilities at the rendezvous through
the specification's transfer and refuses in the state it was handed
(`endpointCallCheckedArmGeneralR`). -/
@[inline] def endpointCallCapsCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    match rt.pendingReceiveReply with
                    | some rid =>
                        if decide (len ≤ 4) &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callWakesInPlace st epId tid r rt rid then
                          if senderTransferInertW st epId rt tid then
                            .ok ((), callRendezvousDelivered st epId tid r rt.queueNextCode rid
                              SeLe4n.arm64DefaultLayout rf len cap.badgeWord cap.badged
                              executingCore)
                          else
                            match st.getTcb? tid with
                            | some ctcb =>
                              .ok ((), performCallCapsDelivered st epId tid r rt.queueNextCode
                                rid SeLe4n.arm64DefaultLayout rf len cap.badgeWord cap.badged
                                executingCore ctcb.vspaceRoot ctcb.ipcBuffer ctcb.cspaceRoot
                                (if cap.rights.mem .grant then routedExtraCaps rf else 0)
                                rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot)
                            | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                        else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                    | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeCallBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointCallCapsCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    endpointCallCapsCheckedArmR ctx rf mi.length tid executingCore cap st =
      endpointCallCheckedArmGeneralR ctx tid executingCore cap st := by
  unfold endpointCallCapsCheckedArmR
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
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
              obtain ⟨⟨hShort, hFlow⟩, hW⟩ := hG
              have hSz : Architecture.regMessageLength SeLe4n.arm64DefaultLayout mi.length ≤ 4 := by
                unfold Architecture.regMessageLength; omega
              split
              · next hSI =>
                have hS := senderTransferInertW_isSome hSI
                have hMsg := routedTransferringMessage st tid rf capAddr mi sid hFrame hR hShort
                have hInert := capTransferInert_sendCapRequest_of_W st epId r rt tid cap.badge
                  (cap.rights.mem .grant) hT hSI
                obtain ⟨s, hC, sgi, hD⟩ := callDispatchChecked_inPlace_inert ctx st epId ep
                  tid r rt rid (.frame cap.badge (cap.rights.mem .grant)) _ executingCore
                  (hMsg cap.badge (cap.rights.mem .grant) hS)
                  ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hInert hFlow
                rw [callRendezvousDelivered_eq _ _ _ _ _ _ _ _ _ _ _ _ hW]
                simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH, hD, hC]
                rfl
              · split
                · next ctcb hS =>
                  have hMsg := routedTransferringMessage st tid rf capAddr mi sid hFrame hR hShort
                  have hSome : (st.getTcb? tid).isSome = true := by rw [hS]; rfl
                  have hb : cap.badge = SeLe4n.Badge.opt cap.badgeWord cap.badged := rfl
                  obtain ⟨sgi, hD⟩ := callDispatchChecked_inPlace_transfer ctx st epId ep tid r rt
                    rid (.frame cap.badge (cap.rights.mem .grant)) _ executingCore
                    (hMsg cap.badge (cap.rights.mem .grant) hSome)
                    ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hFlow
                  simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH]
                  rw [hD, sendCapRequest_routed st epId tid r ctcb rf capAddr mi sid _ _
                      (by simp only [hE, Option.bind_some, hH]) hS (hFrame ctcb hS) hR hShort,
                    receiverCapTarget?_eq_capTargetOf hT, hb]
                  have hEq := callRendezvousCaps_eq_delivered st epId tid r rt.queueNext rid
                    SeLe4n.arm64DefaultLayout rf mi.length cap.badgeWord cap.badged executingCore
                    ctcb rt (if cap.rights.mem .grant then routedExtraCaps rf else 0)
                    (callWakesInPlace_noResizeDue hW) (callWakesInPlace_ne hW) hSz
                  rw [TCB.optCode_queueNext] at hEq
                  obtain ⟨s, st'', hOk⟩ := receiveTransferCaps_ok
                    (frameCapRequestOf st ctcb
                      (if cap.rights.mem .grant then routedExtraCaps rf else 0))
                    (some epId) (capTargetOf st rt)
                    (storeCallRendezvous st epId tid r rt.queueNext rid
                      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf
                          mi.length,
                        badge := SeLe4n.Badge.opt cap.badgeWord cap.badged } executingCore)
                  rw [hOk] at hEq ⊢
                  dsimp only at hEq ⊢
                  rw [hEq]
                · rfl
            · rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            have hNoRecv : (match st.getEndpoint? epId with
                | some ep => ep.receiveQ.head | none => none) = none := by
              rw [hE]; exact hH
            have hReq := sendCapRequest_of_no_receiver st epId tid
              (.frame cap.badge (cap.rights.mem .grant)) (by simp only [hE, Option.bind_some, hH])
            unfold endpointCallCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointCallCrossCoreDispatchChecked
            rw [if_pos hFlow, endpointCallCrossCoreDispatch_no_receiver _ _ _ _ _ hNoRecv,
              endpointCallWithCapsOnCore_no_caps _ _ _ _ _ hReq,
              callBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointCallCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

theorem endpointCallCapsCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) (hCall : decoded.syscallId = .call)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    endpointCallCapsCheckedArmR ctx rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointCallCapsCheckedArmR_eq_general ctx rf capAddr mi sid tid executingCore cap st
      hFrame hR,
    endpointCallCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hCall]

/-- The arm of a send or a call that transfers capabilities. -/
@[inline] def transferringCheckedArmR (ctx : LabelingContext) (sid : SyscallId)
    (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  match sid with
  | .call => endpointCallCapsCheckedArmR ctx rf len tid executingCore cap
  | _ => endpointSendCapsCheckedArmR ctx rf len tid executingCore cap

theorem transferringCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) (hSid : decoded.syscallId = sid) (hSC : sid = .send ∨ sid = .call)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    transferringCheckedArmR ctx sid rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rcases hSC with rfl | rfl
  · exact endpointSendCapsCheckedArmR_eq ctx decoded tid executingCore gate cap st hSid
      rf capAddr mi _ hFrame hR
  · exact endpointCallCapsCheckedArmR_eq ctx decoded tid executingCore gate cap st hSid
      rf capAddr mi _ hFrame hR

/-- The capability-carrying send's or call's slot check, gate, arm and taint
step on the capability its operand resolved to; it moves content as a send
does (`sendTaintStep`).  Every refusal carries the state it was handed
(`transferringOperandArmThenTaintR_eq`). -/
@[inline] def transferringOperandArmThenTaintR (ctx : LabelingContext) (sid : SyscallId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match transferringCheckedArmR ctx sid rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), sendTaintStep headCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem transferringOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (hSid : decoded.syscallId = sid) (hSC : sid = .send ∨ sid = .call)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    transferringOperandArmThenTaintR ctx sid rf mi.length tid executingCore gate.requiredRight
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hTk : syscallChecksTargetFirst decoded.syscallId = false := by
    rcases hSC with rfl | rfl <;> rw [hSid] <;> rfl
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hTk, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (by rcases hSC with rfl | rfl <;> simp [hSid])
    (wT := st.taintWordsAt tid.toObjId) (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [transferringOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [transferringCheckedArmR_eq ctx decoded sid tid executingCore gate cap st hSid hSC
          rf capAddr mi hFrame hR]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The capability-carrying send's or call's operand dispatch
(`dispatchTransferringCheckedR_eq`).  A specification: the compiled entry runs
the arm out of line. -/
noncomputable def dispatchTransferringCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (transferringOperandArmThenTaintR ctx sid rf len tid executingCore (syscallRequiredRight sid))

theorem dispatchTransferringCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hSid : decoded.syscallId = sid) (hSC : sid = .send ∨ sid = .call)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi) :
    dispatchTransferringCheckedR ctx sid decoded.capAddr rf mi.length tid executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  subst hSid
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _
    (by rcases hSC with h | h <;> rw [h] <;> decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  exact transferringOperandArmThenTaintR_eq ctx decoded _ tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref rfl hSC hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef) rf capAddr mi
    hFrame hR

/-! ### The long reply -/

/-- The words a long reply's general arm reads: the inline words in `rf`, then
the replier's overflow slots in `st` (`longMessageDecode`'s). -/
@[inline] def longReplyRegs (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) : Array SeLe4n.RegValue :=
  Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
    (overflowRegsFrom st tid 0 (len - 4)).toArray

/-- The long reply's general arm, its words read where it runs. -/
@[inline] def endpointReplyLongGeneralR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st => endpointReplyCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label } (longReplyRegs st tid rf len) tid
    executingCore cap st

/-- The checked reply arm for a reply of `len` words, more than four, refusing
in the state it was handed (`endpointReplyLongCheckedArmR_eq`).  A reply to an
unfaulted caller blocked on it whose checks all pass before any write
(`replyWakesInPlace`) wakes the caller without the message, runs the server's
priority walk, then writes the inline words into the caller's saved registers
and copies the rest from the replier's IPC buffer into the caller's, word by
word (`performReplyDeliveredLong`, `performReplyRendezvous_eq_deliveredLong`),
as seL4's `doReplyTransfer` does, when the reply transfers no capability
(`replyTransferInertW`); any other reply takes the general arm. -/
@[inline] def endpointReplyLongCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .replyCap rid0 =>
        match st.getReply? rid0 with
        | some rp0 =>
            match rp0.caller with
            | some c =>
                match st.getTcb? c with
                | some ct =>
                    match ct.ipcState with
                    | .blockedOnReply _ (some server) =>
                        match ct.replyObject with
                        | some rid =>
                            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
                                !server.isReserved && !ct.faultWords.isFault &&
                                replyWakesInPlace st c ct rid &&
                                replyTransferInertW st ct (cap.rights.mem .grant) then
                              .ok ((), performReplyDeliveredLong st c server rid rf len tid
                                cap.badgeWord cap.badged executingCore)
                            else endpointReplyLongGeneralR ctx rf len extraCaps label tid
                              executingCore cap st
                        | none => endpointReplyLongGeneralR ctx rf len extraCaps label tid
                            executingCore cap st
                    | _ => endpointReplyLongGeneralR ctx rf len extraCaps label tid
                        executingCore cap st
                | none => endpointReplyLongGeneralR ctx rf len extraCaps label tid
                    executingCore cap st
            | none => endpointReplyLongGeneralR ctx rf len extraCaps label tid executingCore cap st
        | none => endpointReplyLongGeneralR ctx rf len extraCaps label tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointReplyLongCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi) :
    endpointReplyLongCheckedArmR ctx rf mi.length mi.extraCaps mi.label tid executingCore cap st =
      endpointReplyLongGeneralR ctx rf mi.length mi.extraCaps mi.label tid executingCore cap st := by
  obtain ⟨hGt, hMax, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyLong st tid _ rf 32
      capAddr mi hR
  have hSz4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz4] at hGt
  unfold endpointReplyLongCheckedArmR
  split
  · next rid0 hTgt =>
    split
    · next rp0 hR0 =>
      split
      · next c hC =>
        split
        · next ct hT =>
          split
          · next ep server hIpc =>
            split
            · next rid hRO =>
              split
              · next hG =>
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
                obtain ⟨⟨⟨⟨hFlow, hSRes⟩, hNoF⟩, hW⟩, hI⟩ := hG
                have hAns : replyAnsweredCaller? st rid0 = some c := by
                  rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                simp only [endpointReplyLongGeneralR, endpointReplyCheckedArmGeneralR, hTgt, hAns,
                  hFlow, ↓reduceIte]
                rw [replyTransferChecked_inPlace ctx st tid c server ct ep rid
                  { length := mi.length, extraCaps := mi.extraCaps, label := mi.label }
                  (longReplyRegs st tid rf mi.length) _ _ executingCore
                  (by simp only [extractMessageRegisters, Array.size_extract]; omega)
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes hW hNoF
                  (replyTransferInert_of_W hI) hFlow]
                have hMsg := longMessageDecode_message .reply st tid rf capAddr mi cap.badge
                  (by omega) hMax
                simp only [longMessageDecode] at hMsg
                simp only [longReplyRegs]
                have hX : ∀ regs, Architecture.RegisterDecode.extractMessageRegisters regs
                    { length := mi.length, extraCaps := mi.extraCaps, label := mi.label } =
                    Architecture.RegisterDecode.extractMessageRegisters regs mi := fun _ => rfl
                rw [hX, hMsg]
                exact congrArg (fun x => Except.ok ((), x))
                  (performReplyRendezvous_eq_deliveredLong st c server rid rf mi.length tid
                    cap.badgeWord cap.badged executingCore (replyWakesInPlace_noResizeDue hW)
                    (by omega)).symm
              · rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · next hTgt =>
    unfold endpointReplyLongGeneralR endpointReplyCheckedArmGeneralR
    split
    · next rid h => exact absurd h (hTgt rid)
    · rfl

/-- The long reply arm is the specification's. -/
theorem endpointReplyLongCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (st : SystemState)
    (hReply : decoded.syscallId = .reply)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs) :
    endpointReplyLongCheckedArmR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointReplyLongCheckedArmR_eq_general ctx rf capAddr decoded.msgInfo tid executingCore cap
    st hR]
  unfold endpointReplyLongGeneralR
  rw [hRegs]
  exact congrFun (endpointReplyCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hReply) st

/-- The long reply's slot check, gate, arm and taint step on the capability its
operand resolved to (`endpointReplyLongCheckedArmR`); its content reaches the
answered caller (`replyTaintCaller?`) as the short reply's does.  Every refusal
carries the state it was handed (`replyLongOperandArmThenTaintR_eq`). -/
@[inline] def replyLongOperandArmThenTaintR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let callerCode := ThreadId.optCode (replyTaintCaller? st cap)
          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointReplyLongCheckedArmR ctx rf len extraCaps label tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep callerCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem replyLongOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (hReply : decoded.syscallId = .reply)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    replyLongOperandArmThenTaintR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        gate.requiredRight (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hReply, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [replyTaintStep_eq st tid decoded hReply (wT := st.taintWordsAt tid.toObjId)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyLongOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyLongCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr st
          hReply hR hRegs]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The long reply's operand dispatch. -/
noncomputable def dispatchReplyLongCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (replyLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
      (syscallRequiredRight .reply))

theorem dispatchReplyLongCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hReply : decoded.syscallId = .reply)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs) :
    dispatchReplyLongCheckedR ctx decoded.capAddr rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hReply]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := replyLongOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref rf capAddr hReply hR hRegs hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hReply] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.7: the tail of an endpoint's receive queue, as its code
(`SeLe4n.ThreadId.optCode`): read without building an `Option`. -/
@[inline] def receiveQueueTailCode (st : SystemState) (endpointId : SeLe4n.ObjId) : Nat :=
  match st.getEndpoint? endpointId with
  | some ep => ep.recvTailCode
  | none => 0

/-- WS-ZA ZA4.7: a receive blocks, and writes only its slots: no sender is
waiting, the receiver may block (`receiveBlockAdmits`) and every write stays
in place (`receiveBlocksInPlace`). -/
@[inline] def receiveBlocksFast (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyCode : Nat) : Bool :=
  match st.getEndpoint? endpointId with
  | some ep =>
      ep.sendQ.head.isNone &&
      (match st.getTcb? receiver with
       | some rt => receiveBlockAdmits rt &&
           receiveBlocksInPlaceCode st endpointId receiver ep.recvTailCode replyCode
       | none => false)
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
    (len : Nat) (replyAddr : SeLe4n.CPtr) : Except KernelError (Option SeLe4n.ReplyId) :=
  if len = 0 then .ok none else
  let gate : SyscallGate :=
    { callerId := tid
      cspaceRoot := callerCspaceRoot st tid
      capAddr := replyAddr
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
              if r.caller.isNone && !st.replyStashedAt rid r then .ok (some rid)
              else .error .replyCapInvalid
          | none => .error .replyCapInvalid

theorem resolveRecvReplyIdR_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hLen : decoded.msgInfo.length = len)
    (hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := replyAddr }) :
    resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st := by
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

/-- The reply capability a receive names, checked as `resolveRecvReplyIdR`
checks it once its slot is found: present, not the idle thread's, carrying the
write right, naming a reply object that is free of callers and not already
stashed.  The reply object goes to `onOk` as its code (`SeLe4n.ReplyId.optCode`),
a refusal to `onErr`, so no `Except` or `some` cell is built. -/
@[inline] def recvReplyCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (onErr : KernelError → α) (onOk : Nat → α) : α :=
  match cap? with
  | none => onErr .invalidCapability
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then onErr .invalidCapability
      else if !cap.hasRight .write then onErr .illegalAuthority
      else
        match cap.target with
        | .replyCap rid =>
            match st.getReply? rid with
            | some r =>
                if r.caller.isNone && !st.replyStashedAt rid r then onOk (rid.val + 1)
                else onErr .replyCapInvalid
            | none => onErr .replyCapInvalid
        | _ => onErr .invalidCapability

/-- `resolveRecvReplyIdR` in continuation form, the reply object as its code
(`resolveRecvReplyK_eq`): the slot is resolved through
`resolveCapAddressKUnrolled`, as the operand is, so the entry builds no gate,
slot reference or result cell for the receive's reply capability.  WS-ZA ZA4.7. -/
@[inline] def resolveRecvReplyK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onOk : Nat → α) : α :=
  if len = 0 then onOk 0 else
  resolveCapAddressKUnrolled (callerCspaceRoot st tid) (replyAddr)
    (callerCspaceDepth st tid) st onErr
    (fun cnode slot =>
      recvReplyCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
        onErr onOk)

theorem resolveRecvReplyK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onOk : Nat → α) :
    resolveRecvReplyK st tid len replyAddr onErr onOk =
      match resolveRecvReplyIdR st tid len replyAddr with
      | .error e => onErr e
      | .ok r => onOk (SeLe4n.ReplyId.optCode r) := by
  unfold resolveRecvReplyK resolveRecvReplyIdR
  by_cases h0 : len = 0
  · simp only [h0, ↓reduceIte, SeLe4n.ReplyId.optCode_none]
  · simp only [h0, ↓reduceIte, syscallLookupCap, syscallResolveCap]
    rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
    cases resolveCapAddress (callerCspaceRoot st tid) (replyAddr)
        (callerCspaceDepth st tid) st with
    | error e => rfl
    | ok ref =>
      simp only [recvReplyCapK]
      cases SystemState.lookupSlotCap st ref with
      | none => rfl
      | some cap =>
        simp only []
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
        · simp only [hIdle, ↓reduceIte]
        · by_cases hRight : cap.hasRight .write = true
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_true]
            unfold extractReplyId
            cases cap.target <;> try rfl
            rename_i rid
            simp only []
            cases st.getReply? rid with
            | none => rfl
            | some r =>
              simp only []
              split <;> rfl
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_false]

/-- The checked receive arm's rendezvous through the specification: the
WithCaps receive, the rendezvous hand-off, then the woken sender's completion
and the receiver's message staged. -/
@[inline] def endpointReceiveRendezvousR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
      let rid := SeLe4n.ReplyId.ofOptCode replyCode
      let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
      match endpointReceiveDualWithCapsOnCore epId tid rid
      executingCore st with
      | (st', .ok (dequeued, summary, _sgi)) =>
          match applyReceiveRendezvousHandoff st' tid dequeued executingCore with
          | .error e => .error (e, st)
          | .ok stDon =>
              .ok ((), Architecture.stageDeliveredMessage
                (Architecture.stageWokenSendCompletion stDon wokenSender?) tid
                summary.capInfo)
      | (_, .error e) => .error (e, st)

/-- WS-ZA ZA4.7: the checked receive arm's rendezvous.  A receive that takes a
sender blocked by a capability-free send (`registerRoutedSyscall` of its saved
frame), not delivering a fault, whose writes all stay in their slots
(`receiveTakesInPlace`), takes it in place: the six words of the delivered
frame are read from the sender's saved registers before any write and written
into the receiver's (`performReceiveDelivered`, `receiveTake_delivered`).  Any
other rendezvous goes through the specification
(`endpointReceiveTakeR_eq`). -/
@[inline] def endpointReceiveTakeR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          if sTcb.ipcFaultSend && sTcb.faultWords.isFault then
            match SeLe4n.ReplyId.ofOptCode replyCode with
            | some rid =>
              if receiveCallTakesInPlace st epId tid s sTcb rid then
                .ok ((), performFaultReceiveDelivered st epId s sTcb.queueNextCode tid rid
                  executingCore (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.faultKind
                  sTcb.faultFlag sTcb.faultWord0 sTcb.faultWord1 sTcb.faultLookup sTcb.faultIp
                  sTcb.faultSp sTcb.faultLr sTcb.faultSpsr sTcb.faultX0 sTcb.faultX1 sTcb.faultX2
                  sTcb.faultX3 sTcb.faultX4 sTcb.faultX5 sTcb.faultX6 sTcb.faultX7)
              else endpointReceiveRendezvousR epId tid replyCode executingCore st
            | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
          else
          match Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
              sTcb.registerContext 32 with
          | .send _ mi =>
            if !sTcb.ipcFaultSend && receiveTakesInPlace st epId tid s sTcb then
              let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout sTcb.registerContext
                mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
              .ok ((), performReceiveDelivered st epId s sTcb.queueNextCode tid executingCore
                f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
            else endpointReceiveRendezvousR epId tid replyCode executingCore st
          | .sendLong _ mi =>
            if !sTcb.ipcFaultSend && receiveTakesInPlace st epId tid s sTcb &&
                overflowWordsRead st s sTcb (mi.length - 4) then
              let rf := sTcb.registerContext
              .ok ((), performReceiveDeliveredLong st epId s sTcb.queueNextCode tid executingCore
                mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 0)
                (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 1)
                (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 2)
                (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 3))
            else endpointReceiveRendezvousR epId tid replyCode executingCore st
          | .callLong _ mi =>
            match SeLe4n.ReplyId.ofOptCode replyCode with
            | some rid =>
              if !sTcb.ipcFaultSend && receiveCallTakesInPlace st epId tid s sTcb rid &&
                  overflowWordsRead st s sTcb (mi.length - 4) then
                .ok ((), performReceiveCallDeliveredLong st epId s sTcb.queueNextCode tid rid
                  executingCore sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                  sTcb.ipcBadged)
              else endpointReceiveRendezvousR epId tid replyCode executingCore st
            | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
          | .call _ mi =>
            match SeLe4n.ReplyId.ofOptCode replyCode with
            | some rid =>
              if !sTcb.ipcFaultSend && receiveCallTakesInPlace st epId tid s sTcb rid then
                .ok ((), performReceiveCallDelivered st epId s sTcb.queueNextCode tid rid
                  executingCore sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                  sTcb.ipcBadged)
              else endpointReceiveRendezvousR epId tid replyCode executingCore st
            | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
          | .transferring .send _ mi =>
            if decide (mi.length ≤ 4) && !sTcb.ipcFaultSend &&
                receiveTakesInPlace st epId tid s sTcb then
              if receiverTransferInertW st epId tid sTcb then
                let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                  sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                  sTcb.ipcBadged
                .ok ((), performReceiveDelivered st epId s sTcb.queueNextCode tid executingCore
                  f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else
                match st.getTcb? tid with
                | some rt =>
                  let rf := sTcb.registerContext
                  .ok ((), performTakeCapsDelivered st epId s sTcb.queueNextCode tid executingCore
                    SeLe4n.arm64DefaultLayout mi.length
                    (Architecture.badgeWordIf (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
                    (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 0)
                    (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 1)
                    (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 2)
                    (Architecture.regMessageWord SeLe4n.arm64DefaultLayout rf mi.length 3)
                    sTcb.vspaceRoot sTcb.ipcBuffer sTcb.cspaceRoot
                    (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0)
                    rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot)
                | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
            else endpointReceiveRendezvousR epId tid replyCode executingCore st
          | .transferring .call _ mi =>
            match SeLe4n.ReplyId.ofOptCode replyCode with
            | some rid =>
              if decide (mi.length ≤ 4) && !sTcb.ipcFaultSend &&
                  receiveCallTakesInPlace st epId tid s sTcb rid then
                match st.getTcb? tid with
                | some rt =>
                  .ok ((), performCallTakeCapsDelivered st epId s sTcb.queueNextCode tid rid
                    executingCore SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
                    (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.vspaceRoot
                    sTcb.ipcBuffer sTcb.cspaceRoot
                    (if sTcb.ipcCanGrant then routedExtraCaps sTcb.registerContext else 0)
                    rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot)
                | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
              else endpointReceiveRendezvousR epId tid replyCode executingCore st
            | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
          | _ => endpointReceiveRendezvousR epId tid replyCode executingCore st
        | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
      | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
    | none => endpointReceiveRendezvousR epId tid replyCode executingCore st

theorem endpointReceiveTakeR_eq (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) :
    endpointReceiveTakeR epId tid replyCode executingCore =
      endpointReceiveRendezvousR epId tid replyCode executingCore := by
  funext st
  unfold endpointReceiveTakeR
  split
  · next ep hEp =>
    split
    · next s hH =>
      split
      · next sTcb hT =>
        split
        · next hFa =>
          simp only [Bool.and_eq_true] at hFa
          obtain ⟨hF, hIF⟩ := hFa
          obtain ⟨f, hf⟩ : ∃ f, sTcb.faultWords.fault? = some f := by
            cases h : sTcb.faultWords.fault? with
            | some f => exact ⟨f, rfl⟩
            | none =>
              have h0 := (ThreadFaultWords.decode_eq_none_iff _).mpr h
              have h1 := ThreadFaultWords.decode_isSome sTcb.faultWords
              rw [h0, hIF] at h1
              cases h1
          split
          · next rid hRid =>
            split
            · next hG =>
              obtain ⟨h1, h2, h3⟩ := receiveFaultTake_delivered st epId ep tid rid
                executingCore s sTcb f
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hF hf
              unfold endpointReceiveRendezvousR
              simp only [hEp, Option.bind_some, hH, hRid, h1, h2,
                CapTransferSummary.capInfo_empty]
              rw [h3]
            · rfl
          · rfl
        split
        · next capAddr mi hR =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
            obtain ⟨hF, hG⟩ := hG
            obtain ⟨h1, h2, h3⟩ := receiveTake_delivered st epId ep tid
              (SeLe4n.ReplyId.ofOptCode replyCode)
              executingCore s sTcb capAddr mi ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
              hH ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hR hF
            rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
            unfold endpointReceiveRendezvousR
            simp only [hEp, Option.bind_some, hH, h1, h2, CapTransferSummary.capInfo_empty]
            rw [h3]
          · rfl
        · next capAddr mi hR =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
            obtain ⟨⟨hF, hG⟩, hOk⟩ := hG
            have hTs : st.getTcb? s = some sTcb := hT
            obtain ⟨-, hMax, -, -⟩ :=
              decodeSyscallArgsFromState_of_routedSendLong st s _ _ 32 capAddr mi hR
            have hn : mi.length - 4 ≤ Architecture.IpcBufferRead.maxOverflowSlots := by
              have h116 : Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
              have h120 : maxMessageRegisters = 120 := rfl
              rw [h116]; rw [h120] at hMax; omega
            obtain ⟨h1, h2, h3⟩ := receiveTakeLong_delivered st epId ep tid
              (SeLe4n.ReplyId.ofOptCode replyCode)
              executingCore s sTcb capAddr mi ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
              hH ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hR
              (overflowWordsRead_spec hTs hn hOk) hF
            unfold endpointReceiveRendezvousR
            simp only [hEp, Option.bind_some, hH, h1, h2, CapTransferSummary.capInfo_empty]
            rw [h3]
          · rfl
        · next capAddr mi hR =>
          split
          · next rid hRid =>
            split
            · next hG =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
              obtain ⟨⟨hF, hG⟩, hOk⟩ := hG
              have hTs : st.getTcb? s = some sTcb := hT
              obtain ⟨-, hMax, -, -⟩ :=
                decodeSyscallArgsFromState_of_routedCallLong st s _ _ 32 capAddr mi hR
              have hn : mi.length - 4 ≤ Architecture.IpcBufferRead.maxOverflowSlots := by
                have h116 : Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
                have h120 : maxMessageRegisters = 120 := rfl
                rw [h116]; rw [h120] at hMax; omega
              obtain ⟨h1, h2, h3⟩ := receiveCallLongTake_delivered st epId ep tid rid
                executingCore s sTcb capAddr mi
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hF hR
                (overflowWordsRead_spec hTs hn hOk)
              unfold endpointReceiveRendezvousR
              simp only [hEp, Option.bind_some, hH, hRid, h1, h2,
                CapTransferSummary.capInfo_empty]
              rw [h3]
            · rfl
          · rfl
        · next capAddr mi hR =>
          split
          · next rid hRid =>
            split
            · next hG =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
              obtain ⟨hF, hG⟩ := hG
              obtain ⟨h1, h2, h3⟩ := receiveCallTake_delivered st epId ep tid rid
                executingCore s sTcb capAddr mi
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hF hR
              unfold endpointReceiveRendezvousR
              simp only [hEp, Option.bind_some, hH, hRid, h1, h2,
                CapTransferSummary.capInfo_empty]
              rw [h3]
            · rfl
          · rfl
        · next capAddr mi hR =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hG
            obtain ⟨⟨hLen, hF⟩, hG⟩ := hG
            split
            · next hRI =>
              have hInert := capTransferInert_receiveCapRequest_of_W st epId ep tid s sTcb
                hEp hH hT hRI
              obtain ⟨⟨summary, hC, h1⟩, h2, h3⟩ := receiveTakeCaps_delivered st epId ep tid
                (SeLe4n.ReplyId.ofOptCode replyCode) executingCore s sTcb
                capAddr mi ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
                hH ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hR hLen hF hInert
              rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
              unfold endpointReceiveRendezvousR
              simp only [hEp, Option.bind_some, hH, h1, h2, hC]
              rw [h3]
            · split
              · next rt hRT =>
                obtain ⟨summary, st'', h1, h2, h3⟩ := receiveTakeCapsTransfer_delivered st epId ep
                  tid (SeLe4n.ReplyId.ofOptCode replyCode) executingCore s sTcb rt capAddr mi
                  ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRT hG hR hLen hF
                unfold endpointReceiveRendezvousR
                simp only [hEp, Option.bind_some, hH, h1, h2]
                rw [h3]
              · rfl
          · rfl
        · next capAddr mi hR =>
          split
          · next rid hRid =>
            split
            · next hG =>
              simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hG
              obtain ⟨⟨hLen, hF⟩, hG⟩ := hG
              split
              · next rt hRT =>
                obtain ⟨summary, st'', h1, h2, h3⟩ := receiveCallTakeCapsTransfer_delivered st epId
                  ep tid rid executingCore s sTcb rt capAddr mi
                  ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRT hG hR hLen hF
                unfold endpointReceiveRendezvousR
                simp only [hEp, Option.bind_some, hH, hRid, h1, h2]
                rw [h3]
              · rfl
            · rfl
          · rfl
        all_goals rfl
      · rfl
    · rfl
  · rfl

/-- The checked receive arm once its reply object is resolved, given as its
code: the blocking receive written in place when it may be
(`receiveBlocksFast`), the rendezvous otherwise (`endpointReceiveTakeR`).
Inlined, so its result is matched by the caller rather than built. -/
@[inline] def endpointReceiveResolvedR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if receiveBlocksFast st epId tid replyCode then
      .ok ((), removeRunnableOnCore
        (storeReceiveBlock st epId tid (receiveQueueTailCode st epId) replyCode) tid executingCore)
    else endpointReceiveTakeR epId tid replyCode executingCore st

/-- The checked receive arm (`dispatchWithCapChecked`'s `.receive` case), on
the message length and first message register, refusing in the state it was
handed (`endpointReceiveCheckedArmR_eq`).  Every check, the reply object's
included, precedes the first write; a receive that blocks in place
(`receiveBlocksFast`) holds no pre-state (`receiveBlock_inPlace_eq`). -/
@[inline] def endpointReceiveCheckedArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
      let resolved := fun replyCode => endpointReceiveResolvedR epId tid replyCode executingCore st
      resolveRecvReplyK st tid len replyAddr (fun e => .error (e, st)) resolved
    | _ => .error (.invalidCapability, st)

theorem endpointReceiveCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRecv : decoded.syscallId = .receive)
    (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRid : resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot) :
    endpointReceiveCheckedArmR ctx tid len replyAddr executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointReceiveCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hRecv]
  cases cap.target with
  | object epId =>
    simp only []
    split
    · rfl
    · rw [resolveRecvReplyK_eq, hRid]
      cases resolveRecvReplyId gate decoded st with
      | error e => rfl
      | ok rid =>
      simp only [endpointReceiveResolvedR]
      by_cases hF : receiveBlocksFast st epId tid (SeLe4n.ReplyId.optCode rid) = true
      · rw [if_pos hF]
        unfold receiveBlocksFast at hF
        cases hEp : st.getEndpoint? epId with
        | none => rw [hEp] at hF; cases hF
        | some ep =>
          rw [hEp] at hF
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hF
          obtain ⟨hS, hO⟩ := hF
          cases hR : st.objects[tid.toObjId]? with
          | none => simp only [SystemState.getTcb?, hR] at hO; cases hO
          | some o =>
            cases o with
            | tcb rt =>
              simp only [SystemState.getTcb?, hR] at hO
              simp only [Bool.and_eq_true] at hO
              obtain ⟨hA, hG⟩ := hO
              rw [receiveBlocksInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode,
                SeLe4n.ReplyId.ofOptCode_optCode] at hG
              have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
              have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
                simp only [receiveQueueTailCode, hEp]
              obtain ⟨t, hT, hB⟩ := receiveBlock_receiver_blocked st epId ep tid rt rid
                executingCore hE hR hA hG
              unfold endpointReceiveDualWithCapsOnCore
              rw [receiveBlock_inPlace_eq st epId ep tid rt rid executingCore hE hS hR hA hG]
              have hSnd : (receiveRendezvousSender? st epId).isNone = true := by
                simp [receiveRendezvousSender?, hEp, hS]
              simp only [hSnd, ↓reduceIte, hTail]
              have hNoCall : rendezvousDequeuedCall (removeRunnableOnCore
                  (storeReceiveBlock st epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode rid))
                  tid executingCore) tid =
                  false := by
                unfold rendezvousDequeuedCall
                rw [show lookupTcb _ tid = some t from by
                  simp only [lookupTcb]
                  split
                  · next hRes =>
                    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
                    rw [hG.1.1.1.1.1.1.1] at hRes; cases hRes
                  · exact hT]
                simp only [hB]
              rw [applyReceiveRendezvousHandoff_of_no_call _ _ _ _ hNoCall]
              simp only [hS, Option.bind_some, Architecture.stageWokenSendCompletion_none]
              unfold Architecture.stageDeliveredMessage
              simp only [hT, hB, reduceCtorEq, ↓reduceIte]
            | _ => simp only [SystemState.getTcb?, hR] at hO; cases hO
      · rw [if_neg hF, endpointReceiveTakeR_eq]
        unfold endpointReceiveRendezvousR
        simp only [hRoot, SeLe4n.ReplyId.ofOptCode_optCode]
        rcases endpointReceiveDualWithCapsOnCore epId tid rid
            executingCore st with ⟨st', _ | ⟨dq, summary, sgi⟩⟩
        · rfl
        · simp only []
          cases applyReceiveRendezvousHandoff st' tid dq executingCore <;> rfl
  | _ => rfl

/-- The sender whose content a receive takes, read from the pre-state before
the arm: the head of the send queue of the endpoint its capability names
(`receiverTaintEdges`), as its code (`SeLe4n.ThreadId.optCode`). -/
@[inline] def receiveTaintSourceCode (st : SystemState) (cap : Capability) : Nat :=
  match cap.target with
  | .object epId =>
      match st.getEndpoint? epId with
      | some ep => ep.sendHeadCode
      | none => 0
  | _ => 0

/-- The object of the thread a taint code names (`SeLe4n.ThreadId.optCode`'s
`s + 1` for thread `s`); for the code `0`, naming none, the object of thread
`0`, which a step taking that code never reads. -/
@[inline] def threadObjOfCode (code : Nat) : SeLe4n.ObjId :=
  (⟨code - 1⟩ : SeLe4n.ThreadId).toObjId

/-- The receive's taint step, without the plan: the sender's words `wS`,
captured before the arm at `threadObjOfCode sourceCode`, join the receiver's
taint words (`receiveTaintStep_eq`). -/
@[inline] def receiveTaintStep (sourceCode : Nat) (tid : SeLe4n.ThreadId)
    (wS : TaintWords) (post : SystemState) : SystemState :=
  match sourceCode with
  | _ + 1 => joinTaintAt post tid.toObjId wS
  | 0 => post

theorem receiveTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hRecv : decoded.syscallId = .receive)
    (preEpoch : Nat) (preLength : Nat) (wS : Capability → TaintWords)
    (hS : ∀ cap, (wS cap).decode =
      st.declassificationTaint (threadObjOfCode (receiveTaintSourceCode st cap)))
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength
        st.declassificationTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => receiveTaintStep (receiveTaintSourceCode st cap) tid (wS cap) post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hRecv, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | cap
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
  · have h := hS cap
    rcases cap with ⟨target, _, _⟩
    cases target with
    | object epId =>
      simp only [receiveTaintSourceCode, receiverTaintEdges] at h ⊢
      revert h
      cases st.getEndpoint? epId with
      | none =>
        intro _
        simp [receiveTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_sendHeadCode]
        cases ep.sendHeadCode <;> intro h <;>
          simp only [threadObjOfCode, Nat.add_sub_cancel] at h <;>
          simp [receiveTaintStep, SeLe4n.ThreadId.ofOptCode, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow,
            applyTaintStep, joinTaintAt_toWords_of_decode _ _ h]
    | _ =>
      simp [receiveTaintSourceCode, receiveTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]

/-- The receive's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`receiveOperandArmThenTaintR_eq`). -/
@[inline] def receiveOperandArmThenTaintR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let sourceCode := receiveTaintSourceCode st cap
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          match endpointReceiveCheckedArmR ctx tid len replyAddr executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), receiveTaintStep sourceCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ stPost)
        else .error (.illegalAuthority, st)

theorem receiveOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (ref : CSpaceAddr)
    (hRecv : decoded.syscallId = .receive) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRid : resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    receiveOperandArmThenTaintR ctx tid len replyAddr executingCore gate.requiredRight
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hRecv, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [receiveTaintStep_eq st tid decoded hRecv
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (hS := fun _ => decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [receiveOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReceiveCheckedArmR_eq ctx decoded tid executingCore gate cap st hRecv len replyAddr
          hRid hRoot]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The receive's dispatch, on the message length and first message register
the entry read: `dispatchOperandCheckedR` with the receive's arm
(`dispatchReceiveCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchReceiveCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (receiveOperandArmThenTaintR ctx tid len replyAddr executingCore (syscallRequiredRight .receive))

theorem dispatchReceiveCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRecv : decoded.syscallId = .receive)
    (hLen : decoded.msgInfo.length = len)
    (hReplyAddr : len ≠ 0 → decoded.msgRegs[0]? = some ⟨replyAddr.toNat⟩) :
    dispatchReceiveCheckedR ctx decoded.capAddr len replyAddr tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hRecv]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := replyAddr } := by
    intro hN
    have h := hReplyAddr hN
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨h0, hv⟩ := h
    simp only [decodeRecvArgs, requireMsgReg, h0, ↓reduceDIte, hv, bind, Except.bind, pure, Except.pure,
      SeLe4n.CPtr.ofNat_toNat]
  have hRid := resolveRecvReplyIdR_eq st tid
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    decoded len replyAddr rfl (by simp only [callerCspaceRoot, hTcb])
    (by simp only [callerCspaceDepth, hTcb, hRoot]) hLen hArgs
  have hArm := receiveOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length
    st ref hRecv len replyAddr hRid (by simp only [callerCspaceRoot, hTcb]) hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hRecv] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
