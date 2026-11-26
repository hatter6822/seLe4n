-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReceiveInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyLegFrame

/-!
# A receive that takes a queued fault, written in place

WS-ZA ZA6.31.  A thread that faults while its handler is not waiting is queued
on the handler's endpoint as a caller holding its fault (`ipcFaultSend`), as
seL4's `sendFaultIPC` queues it.  The handler's receive pops it, blocks it on
the reply, links it to the handler's reply object, queues it on the handler's
reply waiters, and hands the handler the fault's message
(`endpointReceiveDualOnCore`'s call branch); the dispatch then runs the
handler's priority walk and stages the message.  When every write stays in its
slot (`receiveCallTakesInPlace`), those writes are the in-place pop and four
slot writes (`storeReceiveCallReady`), and the message is written straight
from the queued thread's fault words into the handler's saved registers and
IPC buffer (`deliverFaultFrame`), so neither the fault nor its message is
built (`receiveFaultTake_delivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **A receive taking a queued caller writes only its slots**: the pop's
(`sendWakesInPlace`, on the send queue), the receiver an unreserved thread
other than the caller and its successor, rewritten where it stands, the reply
object rewritten where it stands and free, the caller holding no reply object
and blocked on a call through a cap that grants (seL4 `receiveIPC` links a
caller to the reply only under `canGrant || canGrantReply`), and no
SchedContext donated. -/
@[inline] def receiveCallTakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  sendWakesInPlace st endpointId s sTcb.queueNext &&
  !receiver.isReserved && receiver != s &&
  (match sTcb.queueNext with
   | none => true
   | some n => receiver != n) &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  sTcb.replyObject.isNone &&
  (match st.getTcb? receiver with
   | some rt => callDonatesNothing sTcb rt
   | none => false) &&
  (match st.getReply? rid with
   | some rp => rp.isFree
   | none => false) &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

/-- `receiveCallTakesInPlace` as it is compiled: the caller's successor asked
of its link code, so no `some` cell is built for a caller with a successor
(`receiveCallTakesInPlace_eq_impl`). -/
@[inline] def receiveCallTakesInPlaceImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  sTcb.replyObject.isNone &&
  (match st.getTcb? receiver with
   | some rt => callDonatesNothing sTcb rt
   | none => false) &&
  (match st.getReply? rid with
   | some rp => rp.isFree
   | none => false) &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

@[csimp] theorem receiveCallTakesInPlace_eq_impl :
    @receiveCallTakesInPlace = @receiveCallTakesInPlaceImpl := by
  funext st endpointId receiver s sTcb rid
  unfold receiveCallTakesInPlace receiveCallTakesInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- A take that donates nothing is a take of the reply's slots. -/
theorem receiveCallTakesReplyInPlace_of_inPlace {st : SystemState} {endpointId : SeLe4n.ObjId}
    {receiver s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true) :
    receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid = true := by
  simp only [receiveCallTakesInPlace, receiveCallTakesReplyInPlace, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hW, hRes⟩, hNeS⟩, hNx⟩, hLR⟩, hFR⟩, hLQ⟩, hFQ⟩, hRO⟩, hRT⟩, hRp⟩,
    hCall⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hW, hRes⟩, hNeS⟩, hNx⟩, hLR⟩, hFR⟩, hLQ⟩, hFQ⟩, hRO⟩, ?_⟩, hRp⟩, hCall⟩
  split at hRT
  · next rt hR => rw [hR]; rfl
  · cases hRT

/-- **What an in-place take of a queued caller lends**: the caller and the
receiver donate nothing to each other. -/
theorem receiveCallTakesInPlace_lendsNothing {st : SystemState}
    {endpointId : SeLe4n.ObjId} {receiver s : SeLe4n.ThreadId} {sTcb rt : TCB}
    {rid : SeLe4n.ReplyId}
    (h : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hR : st.getTcb? receiver = some rt) :
    callDonatesNothing sTcb rt = true := by
  simp only [receiveCallTakesInPlace, Bool.and_eq_true] at h
  have hRT := h.1.1.2
  simp only [hR] at hRT
  exact hRT

/-- The receive's writes taking a queued caller, each in its slot: the caller
popped and blocked on the reply, the reply object linked to it, the caller
linked to the reply object, the receiver made ready holding no message, and
the caller queued on the receiver's reply waiters. -/
@[noinline] def storeReceiveCallReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  let s1 := (storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    (callCallerTcb endpointId receiver)
  let s2 := (s1.modifyObject rid.toObjId (replyWithCaller s)).updateTcb s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })
  (s2.updateTcb receiver receiverReady).linkReplyWaiter s receiver

theorem storeReceiveCallReady_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNo : st.objects.noResizeDue) :
    (storeReceiveCallReady st endpointId s nextCode receiver rid).objects.noResizeDue := by
  unfold storeReceiveCallReady
  dsimp only
  exact linkReplyWaiter_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
      (storePopHead_noResizeDue _ _ _ _ _ hNo)))))

/-- **The take holds its message in one write**: the receiver made ready with
the message is the receiver made ready without it, the message written in
afterwards. -/
theorem receiveCallTakeState_eq_hold (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNo : st.objects.noResizeDue) :
    receiveCallTakeState st endpointId s sTcb receiver rid =
      (storeReceiveCallReady st endpointId s sTcb.queueNextCode receiver rid).mapTcbInPlace
        receiver (holdMessage (blockedSenderMessage
          (storePopHead st endpointId false s sTcb.queueNext) s sTcb)) := by
  unfold receiveCallTakeState storeReceiveCallReady
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  dsimp only
  generalize blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb
    = msg
  have hNo1 := updateTcb_noResizeDue _ s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })
    (modifyObject_noResizeDue _ rid.toObjId
      (replyWithCaller s) (updateTcb_noResizeDue _ s (callCallerTcb endpointId receiver)
        (storePopHead_noResizeDue st endpointId false s sTcb.queueNext hNo)))
  generalize (((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
      (callCallerTcb endpointId receiver)).modifyObject rid.toObjId (replyWithCaller s)).updateTcb
      s (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = X at hNo1 ⊢
  have hHold : X.updateTcb receiver (callReceiverTcb msg) =
      (X.updateTcb receiver receiverReady).mapTcbInPlace receiver (holdMessage msg) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1,
      SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1, SystemState.mapTcbInPlace_mapTcbInPlace,
      holdMessage_receiverReady]
  rw [hHold, linkReplyWaiter_msg]

/-- **The receive's take leaves the receiver ready**: under
`receiveCallTakesInPlace` the receiver, untouched by the pop and the caller's
block and link, is made ready in its slot and stays ready on the reply waiter
queue. -/
theorem storeReceiveCallReady_ready (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (s : SeLe4n.ThreadId)
    (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid = true) :
    ipcStateHolds (storeReceiveCallReady st endpointId s sTcb.queueNextCode receiver rid) receiver
      (· = .ready) := by
  have hG' := hG
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, -⟩, hRS⟩, hRN⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hRT⟩, -⟩, -⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨-, -⟩, hFE⟩, -⟩, -⟩, -⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo⟩ : ∃ rt, st.objects[receiver.toObjId]? = some (.tcb rt) := by
    obtain ⟨rt, h⟩ := Option.isSome_iff_exists.mp hRT
    exact ⟨rt, (SystemState.getTcb?_eq_some_iff _ _ _).mp h⟩
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRTo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hSR : s ≠ receiver := fun h => hRS h.symm
  obtain ⟨-, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE hH hT hSG
  have hO1 := (hFr.other _ hNeER hNeSR hNxR).trans hRTo
  unfold storeReceiveCallReady
  dsimp only
  rw [TCB.ofOptCode_queueNextCode]
  have hNo1 := storePopHead_noResizeDue st endpointId false s sTcb.queueNext hNo
  generalize storePopHead st endpointId false s sTcb.queueNext = S1 at hO1 hNo1
  have h1 : ipcStateHolds S1 receiver (fun _ => True) :=
    ⟨rt, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO1, trivial⟩
  have h2 := ipcStateHolds.updateTcb_ne (callCallerTcb endpointId receiver) hNo1 hSR h1
  have hNo2 := updateTcb_noResizeDue S1 s (callCallerTcb endpointId receiver) hNo1
  have h3 := ipcStateHolds.of_carried (ipcStateCarried_modifyObject _ rid.toObjId
    (replyWithCaller s) hNo2 (fun _ => rfl)) h2
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId (replyWithCaller s) hNo2
  have h4 := ipcStateHolds.updateTcb_ne
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hNo3 hSR h3
  have hNo4 := updateTcb_noResizeDue _ s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hNo3
  obtain ⟨x, hx, -⟩ := h4
  have h5 := ipcStateHolds_updateTcb_self (P := (· = .ready)) receiverReady hNo4 hx
    (by simp only [receiverReady, TCB.ipcState_setIpcState])
  exact ipcStateHolds.of_carried
    (ipcStateCarried_of_agree (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks _ s receiver)) h5

/-- **The receive's take of a queued fault, delivered**: the caller popped,
blocked on the reply and linked, the receiver made ready holding no message,
the receiver's priority walk, then the fault delivered in place from the
caller's fault words (`deliverFaultFrame`), read before any write. -/
@[noinline] def performFaultReceiveDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : CoreId) (badgeWord : SeLe4n.Badge) (badged : Bool) (k : Nat) (flag : Bool)
    (w0 w1 : UInt64) (lk : UInt64) (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) :
    SystemState :=
  deliverFaultFrame (PriorityInheritance.propagatePipChainCrossCore
      (storeReceiveCallReady st endpointId s nextCode receiver rid) receiver core).1 receiver
    badgeWord badged k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7

/-- **The receive's take of a queued fault, delivered, is the
specification's**: under `receiveCallTakesInPlace`, for a queued caller holding
a fault, the WithCaps receive installs nothing and commits the take, the
rendezvous hands off no SchedContext and runs the receiver's priority walk, the
caller is left blocked on the reply, and staging the receiver's message writes `performFaultReceiveDelivered`'s state, the fault's
words read from the caller's TCB. -/
theorem receiveFaultTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB) (f : Fault)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hF : sTcb.ipcFaultSend = true) (hf : sTcb.faultWords.fault? = some f) :
    endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid,
          .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s core =
        .ok (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver core) ∧
      Architecture.stageDeliveredMessage (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
            receiver core) receiver 0 =
        performFaultReceiveDelivered st endpointId s sTcb.queueNextCode receiver rid core
          (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.faultKind sTcb.faultFlag
          sTcb.faultWord0 sTcb.faultWord1 sTcb.faultLookup sTcb.faultIp sTcb.faultSp sTcb.faultLr
          sTcb.faultSpsr sTcb.faultX0 sTcb.faultX1 sTcb.faultX2 sTcb.faultX3 sTcb.faultX4
          sTcb.faultX5 sTcb.faultX6 sTcb.faultX7 := by
  have hGR := receiveCallTakesReplyInPlace_of_inPlace hG
  obtain ⟨hTake, hIpc, hBs, hBr⟩ :=
    receiveCallTake_inPlace st endpointId ep receiver rid core s sTcb hE hH hT hGR
  have hG' := hGR
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hRT⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, _⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hDN := receiveCallTakesInPlace_lendsNothing hG hRTo
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpc
  refine ⟨?_, ?_, ?_⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [hTs, blockedSenderCapRequest, hF, ↓reduceIte]
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hCall : rendezvousDequeuedCall (receiveCallTakeState st endpointId s sTcb receiver rid)
        s = true := by
      unfold rendezvousDequeuedCall
      simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hx, hxI]
    obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff s).mpr hSRes)
    obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff receiver).mpr hRRes)
    have hNone : callDonationSchedContext? (receiveCallTakeState st endpointId s sTcb receiver rid)
        s receiver = none := by
      rw [callDonationSchedContext?_congr (s := st) hBs hBr, callDonationSchedContext?_eq_bindings]
      simp only [lookupTcb, hRRes, hSRes, Bool.false_eq_true, ↓reduceIte, hRTo, hTs,
        Option.map_some]
      revert hDN
      unfold callDonatesNothing
      cases rt.schedContextBinding <;> cases sTcb.schedContextBinding <;>
        simp [donationOfBindings, SchedContextBinding.scId?]
    unfold applyReceiveRendezvousHandoff
    rw [applyReceiveRendezvousDonation_of_no_donation _ receiver s sv rv hsv hrv hNone]
    simp only [hCall, ↓reduceIte]
  · have hNoS := storeReceiveCallReady_noResizeDue st endpointId s sTcb.queueNextCode receiver
      rid hNo
    have hNo4 : (receiveCallTakeState st endpointId s sTcb receiver rid).objects.noResizeDue := by
      unfold receiveCallTakeState
      exact linkReplyWaiter_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
        (updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
          (storePopHead_noResizeDue _ _ _ _ _ hNo)))))
    obtain ⟨x', hx', hxI'⟩ := propagatePipChainCrossCore_ipcStateCarried _ receiver core hNo4 s x hx
    unfold applyReceiverPipHandoff
    rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
    have hMsg : blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb =
        faultMessage f sTcb.faultWords.context
          (SeLe4n.Badge.opt (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
      unfold blockedSenderMessage blockedSenderMessageOf
      rw [if_pos hF, TCB.pendingFault]
      unfold ThreadFaultWords.decode
      rw [hf]
      rfl
    rw [hMsg]
    unfold performFaultReceiveDelivered
    exact (deliverFaultFrame_eq _ receiver sTcb.faultWords f hf _ _
      (propagatePipChainCrossCore_noResizeDue _ receiver core hNoS)
      (ipcStateHolds.of_carried (propagatePipChainCrossCore_ipcStateCarried _ receiver core hNoS)
        (storeReceiveCallReady_ready st endpointId ep receiver rid s sTcb hE hH hT hGR))).symm

end SeLe4n.Kernel
