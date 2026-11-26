/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.Architecture.RoutedRegisterDecode

/-!
# A receive that takes a blocked sender's message, written in place

WS-ZA ZA4.7.  A receive that finds a sender blocked on the endpoint pops it off
the send queue, makes it ready, wakes it on its home core, and hands the
receiver the message the sender kept in its registers
(`endpointReceiveDualOnCore`).  When every write stays in its slot
(`receiveTakesInPlace`), those writes are the in-place pop (`storePopHead`)
and two TCB writes (`receiveTake_inPlace`); the delivered frame is read
straight from the sender's saved registers (`performReceiveDelivered`).

The receive body and the capability-carrying receive over it are compiled
through their checks-first forms here (`endpointReceiveDualOnCoreChecked`,
`endpointReceiveDualWithCapsOnCoreChecked`): the first decides the take's
lookups on the entry state with `receiveTakesInPlace`,
`receiveCallNoLinkTakesInPlace` or `receiveCallTakesReplyInPlace` before the
pop, so it stands after the takes' in-place equalities it is proved by, the
two takes of a queued caller among them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **A receive taking a blocked sender writes only its slots**: the pop's
(`sendWakesInPlace`, here on the send queue), the receiver an unreserved
thread other than the sender and its successor, rewritten where it stands, and
the sender a plain sender, not a caller. -/
@[inline] def receiveTakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) : Bool :=
  sendWakesInPlace st endpointId s sTcb.queueNext &&
  !receiver.isReserved && receiver != s &&
  (match sTcb.queueNext with
   | none => true
   | some n => receiver != n) &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => false
   | _ => true)

/-- `receiveTakesInPlace` as it is compiled: the sender's successor asked of
its link code, so no `some` cell is built for a sender with a successor
(`receiveTakesInPlace_eq_impl`). -/
@[inline] def receiveTakesInPlaceImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => false
   | _ => true)

@[csimp] theorem receiveTakesInPlace_eq_impl :
    @receiveTakesInPlace = @receiveTakesInPlaceImpl := by
  funext st endpointId receiver s sTcb
  unfold receiveTakesInPlace receiveTakesInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- **The receive's take, in place**: under `receiveTakesInPlace` the
specification's receive pops the sender in place, makes it ready, wakes it and
hands the receiver the sender's message. -/
theorem receiveTake_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true) :
    endpointReceiveDualOnCore endpointId receiver replyId core st =
      ((wakeThread ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
          receiverReady) s core).1.updateTcb receiver
          (callReceiverTcb (blockedSenderMessage
            (storePopHead st endpointId false s sTcb.queueNext) s sTcb)),
        .ok (s, (wakeThread ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
          receiverReady) s core).2)) := by
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, hNC⟩ := hG
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, _⟩, hLH⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  unfold endpointReceiveDualOnCore
  simp only [(SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE, hH, hPop]
  rw [if_neg (by revert hNC; cases sTcb.ipcState <;> simp)]
  have hM2 : storeTcbIpcStateAndMessage (storePopHead st endpointId false s sTcb.queueNext) s
      .ready none = .ok ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
        receiverReady) :=
    modifyTcb_eq_updateTcb receiverReady hSRes hFr.head_tcb (hFr.leaves hLH)
  rw [hM2]
  simp only []
  generalize blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb
    = msg
  generalize hS1 : storePopHead st endpointId false s sTcb.queueNext = S1 at *
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hK2 : ∀ k, (S1.updateTcb s receiverReady).objects.findsInPlace k =
      st.objects.findsInPlace k := fun k =>
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 k).trans (hFr.keepsFinds k)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (S1.updateTcb s receiverReady) id ty = true :=
    fun h => updateTcb_storeLeaves _ hFr.head_tcb hFH1 (hFr.leaves h)
  generalize hS2 : S1.updateTcb s receiverReady = S2 at *
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace S2 (determineTargetCore S2 s) s _ hT2s
    rfl ((hK2 _).trans hFH)
  have hD3 := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer S2 (determineTargetCore S2 s) s
  have hL3 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (enqueueRunnableOnCore S2 (determineTargetCore S2 s) s) id ty
        = true := fun h => storeLeaves_of_agree hA3 (hL2 h)
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW : (wakeThread S2 s core).1 = enqueueRunnableOnCore S2 (determineTargetCore S2 s) s :=
    rfl
  rw [hW]
  have hM4 : storeTcbIpcStateAndMessage (enqueueRunnableOnCore S2 (determineTargetCore S2 s) s)
      receiver .ready (some msg) =
      .ok ((enqueueRunnableOnCore S2 (determineTargetCore S2 s) s).updateTcb receiver
        (callReceiverTcb msg)) :=
    modifyTcb_eq_updateTcb _ hRRes ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r)
      (hL3 hLR)
  rw [hM4]

/-- **What a sender blocked by a routed capability-free send holds**: it asks
to transfer no capability, and its message is the inline words of its saved
frame under the badge its capability carried. -/
theorem blockedSender_of_routedSend (st : SystemState) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (h : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    blockedSenderCapRequest st s sTcb = none ∧
      blockedSenderMessage st s sTcb =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
            sTcb.registerContext mi.length,
          badge := sTcb.ipcBadgeView } := by
  obtain ⟨d, hDec, _, _, _, hMi, hX, hRegs⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend st s _ _ 32 capAddr mi h
  refine ⟨?_, ?_⟩
  · have hE : ∀ s t, (senderExtraCapAddrs s t d.msgInfo.extraCaps).isEmpty = true := by
      intro s t; rw [hMi, hX, senderExtraCapAddrs_zero]; rfl
    unfold blockedSenderCapRequest senderFrameCapRequest blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, hE, ite_self]
  · unfold blockedSenderMessage blockedSenderMessageOf blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, senderFrameMessage, hRegs, hMi]
    rfl

/-- WS-ZA ZA4.7: **what a thread whose saved frame routes as a capability-free
send or call sends**: the message a send of its frame delivers is the inline
words of that frame under the capability's badge, and it asks
to transfer no capability -- so the send's register fast path, which writes
those words straight into the receiver's saved registers, delivers exactly what
the specification's send does. -/
theorem sendFrame_of_routed (st : SystemState) (s : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? s = some tcb) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (h : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout tcb.registerContext)
      SeLe4n.arm64DefaultLayout
        tcb.registerContext 32 = .send capAddr mi ∨
      Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout tcb.registerContext)
      SeLe4n.arm64DefaultLayout
        tcb.registerContext 32 = .call capAddr mi)
    (endpointId : SeLe4n.ObjId) (badge : Option SeLe4n.Badge) (grant grantReply : Bool) :
    sendPayloadMessage st s (.frame badge grant grantReply) =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
            tcb.registerContext mi.length,
          badge := badge } ∧
      sendCapRequest st endpointId s (.frame badge grant grantReply) = none := by
  obtain ⟨d, hDec, hMi, hX, hRegs⟩ : ∃ d, blockedSenderDecode st s tcb = .ok d ∧
      d.msgInfo = mi ∧ mi.extraCaps = 0 ∧
      d.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map
        (SeLe4n.readReg tcb.registerContext) := by
    rcases h with h | h
    · obtain ⟨d, hDec, _, _, _, hMi, hX, hRegs⟩ :=
        Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend st s _ _ 32
          capAddr mi h
      exact ⟨d, hDec, hMi, hX, hRegs⟩
    · obtain ⟨d, hDec, _, _, _, hMi, hX, hRegs⟩ :=
        Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall st s _ _ 32
          capAddr mi h
      exact ⟨d, hDec, hMi, hX, hRegs⟩
  refine ⟨?_, ?_⟩
  · simp only [sendPayloadMessage, senderFrameDecode, hT, hDec, senderFrameMessage, hRegs, hMi]
    rfl
  · unfold sendCapRequest
    split
    · rfl
    · rw [hT]
      simp only [sendPayloadCapRequest, senderFrameCapRequest, hDec]
      have hE : ∀ s t, (senderExtraCapAddrs s t d.msgInfo.extraCaps).isEmpty = true := by
        intro s t; rw [hMi, hX, senderExtraCapAddrs_zero]; rfl
      simp only [hE, ↓reduceIte]
      split <;> rfl

/-- **The taken sender was no caller**: under `receiveTakesInPlace` the
dequeued sender is made ready, so the rendezvous hands off no donation. -/
theorem receiveTake_dequeuedNoCall (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (core : CoreId) (s : SeLe4n.ThreadId)
    (sTcb : TCB) (msg : IpcMessage)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    rendezvousDequeuedCall (W.1.updateTcb receiver (callReceiverTcb msg)) s = false := by
  intro P W
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, hFH⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨_, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hNoP : P.objects.noResizeDue := storePopHead_noResizeDue _ _ _ _ _ hNo
  have hT2s : (P.updateTcb s receiverReady).getTcb? s = some (receiverReady (tcbOffQueue sTcb)) :=
    updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace (P.updateTcb s receiverReady)
    (determineTargetCore (P.updateTcb s receiverReady) s) s _ hT2s rfl
    (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hNo2 : (P.updateTcb s receiverReady).objects.noResizeDue := updateTcb_noResizeDue _ _ _ hNoP
  have hNoW : W.1.objects.noResizeDue := wakeThread_noResizeDue _ _ _ hNo2
  have hL : lookupTcb (W.1.updateTcb receiver (callReceiverTcb msg)) s = lookupTcb W.1 s := by
    unfold lookupTcb
    split
    · rfl
    · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.getTcb?_mapTcbInPlace,
        if_neg hRS]
  have h1 : rendezvousDequeuedCall (W.1.updateTcb receiver (callReceiverTcb msg)) s =
      rendezvousDequeuedCall W.1 s := by
    unfold rendezvousDequeuedCall; rw [hL]
  rw [h1, show W.1 = enqueueRunnableOnCore (P.updateTcb s receiverReady)
    (determineTargetCore (P.updateTcb s receiverReady) s) s from rfl,
    rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hA3 s]
  unfold rendezvousDequeuedCall
  simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT2s, receiverReady,
    TCB.ipcState_setIpcState]

/-- **The receive's take, delivered**: the sender popped, made ready and woken
(none of its registers written, as seL4's `receiveIPC`), the receiver made ready, and the six words of the
delivered frame -- read from the sender's saved registers before any write --
written into the receiver's saved registers.  No message is built. -/
@[noinline] def performReceiveDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (core : CoreId)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  let X := (wakeThread ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady) s core).1
  (X.updateTcb receiver receiverReady).mapTcbInPlace
    receiver (withFrameWords w0 w1 w2 w3 w4 w5)

/-- **The receive's take, delivered, is the specification's**: under
`receiveTakesInPlace`, a blocked sender whose message is the inline words of its
saved registers (`hMsgs`), the receive takes the in-place writes, the
rendezvous hands off no donation, and staging the receiver's message writes
`performReceiveDelivered`'s state, the frame's
words read from the sender's saved registers. -/
theorem receiveTake_delivered_of_message (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hMsgs : ∀ X : SystemState, blockedSenderMessage X s sTcb =
      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
          sTcb.registerContext mi.length,
        badge := sTcb.ipcBadgeView }) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    let f := Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length sTcb.ipcBadgeView
    endpointReceiveDualOnCore endpointId receiver replyId core st = (S4, .ok (s, W.2)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4
          receiver 0 =
        performReceiveDelivered st endpointId s sTcb.queueNextCode receiver core
          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 := by
  intro P W S4 f
  have hTake := receiveTake_inPlace st endpointId ep receiver replyId core s sTcb hE hH hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, hFH⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hNoP : P.objects.noResizeDue := storePopHead_noResizeDue _ _ _ _ _ hNo
  have hMsg := hMsgs P
  have hRS' : s ≠ receiver := fun h => hRS h.symm
  have hT2s : (P.updateTcb s receiverReady).getTcb? s = some (receiverReady (tcbOffQueue sTcb)) :=
    updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace (P.updateTcb s receiverReady)
    (determineTargetCore (P.updateTcb s receiverReady) s) s _ hT2s rfl
    (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hNo2 : (P.updateTcb s receiverReady).objects.noResizeDue := updateTcb_noResizeDue _ _ _ hNoP
  have hNoW : W.1.objects.noResizeDue := wakeThread_noResizeDue _ _ _ hNo2
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : W.1.getTcb? receiver = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  refine ⟨?_, ?_, ?_⟩
  · exact hTake
  · -- the dequeued sender was no caller: no donation
    apply applyReceiveRendezvousHandoff_of_no_call
    have hL : lookupTcb S4 s = lookupTcb W.1 s := by
      show lookupTcb (W.1.updateTcb receiver _) s = _
      unfold lookupTcb
      split
      · rfl
      · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.getTcb?_mapTcbInPlace,
          if_neg hRS]
    have h1 : rendezvousDequeuedCall S4 s = rendezvousDequeuedCall W.1 s := by
      unfold rendezvousDequeuedCall; rw [hL]
    rw [h1, show W.1 = enqueueRunnableOnCore (P.updateTcb s receiverReady)
      (determineTargetCore (P.updateTcb s receiverReady) s) s from rfl,
      rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hA3 s]
    unfold rendezvousDequeuedCall
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT2s, receiverReady,
      TCB.ipcState_setIpcState]
  · -- staging: the held message is the frame read from the sender's registers
    have hS4 : S4 = (W.1.updateTcb receiver receiverReady).mapTcbInPlace receiver
        (holdMessage (blockedSenderMessage P s sTcb)) := by
      show W.1.updateTcb receiver _ = _
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
        SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.mapTcbInPlace_mapTcbInPlace,
        holdMessage_receiverReady]
    have hNoY : (W.1.updateTcb receiver receiverReady).objects.noResizeDue :=
      updateTcb_noResizeDue _ _ _ hNoW
    have hYr : (W.1.updateTcb receiver receiverReady).getTcb? receiver =
        some (receiverReady rt3) := by
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
        SystemState.mapTcbInPlace_getTcb?_self, hW3r]
      rfl
    have hNoZ : (W.1.updateTcb receiver receiverReady).objects.noResizeDue := hNoY
    have hZr : (W.1.updateTcb receiver receiverReady).getTcb? receiver = some (receiverReady rt3) := hYr
    have hSz : (blockedSenderMessage P s sTcb).registers.size ≤ 4 := by
      rw [hMsg]
      simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
      have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      omega
    rw [hS4, stageDeliveredMessage_holdMessage _ _ _ hNoZ hSz, hMsg,
      Architecture.returnFrameOfMessage_regMessageBody]
    unfold writeDeliveredFrameIfReady performReceiveDelivered
    rw [hZr]
    simp only [receiverReady, TCB.ipcState_setIpcState, ↓reduceIte]
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]

/-- The take of a sender blocked by a routed capability-free send, not
delivering a fault: as `receiveTake_delivered_of_message`, the WithCaps receive
installing nothing. -/
theorem receiveTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    let f := Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length sTcb.ipcBadgeView
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (S4, .ok (s, { results := #[] }, W.2)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4
          receiver 0 =
        performReceiveDelivered st endpointId s sTcb.queueNextCode receiver core
          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 := by
  intro P W S4 f
  obtain ⟨hTake, h2, h3⟩ := receiveTake_delivered_of_message st endpointId ep receiver replyId
    core s sTcb mi hE hH hT hG
    (fun X => (blockedSender_of_routedSend X s sTcb capAddr mi hR hF).2)
  refine ⟨?_, h2, h3⟩
  have hSnd : receiveRendezvousSender? st endpointId = some s := by
    simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
      Option.bind_some, hH]
  have hReq : receiveCapRequest st endpointId = none := by
    unfold receiveCapRequest
    rw [hSnd]
    simp only [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT]
    exact (blockedSender_of_routedSend st s sTcb capAddr mi hR hF).1
  unfold endpointReceiveDualWithCapsOnCore
  rw [hTake]
  simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rfl
/-! ## A receive taking a queued caller

A caller blocked on the endpoint is taken by the receive with its reply
linked (`receiveCallTake_inPlace`) or, where the receive links it to no reply,
left `Inactive` (`receiveCallNoLinkTake_inPlace`).  Both equalities stand
here, below the ReplyRecv composite, so the receive body's checks-first form
(`endpointReceiveDualOnCoreChecked`) decides them too. -/

/-- **A receive taking a queued caller writes only its slots, whatever it
donates**: `receiveCallTakesInPlace` with the receiver asked only to be a
thread, so a take whose rendezvous then donates the caller's SchedContext is
asked the same of its slots (`receiveCallTake_inPlace_facts`). -/
@[inline] def receiveCallTakesReplyInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
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
  (st.getTcb? receiver).isSome &&
  (match st.getReply? rid with
   | some rp => rp.isFree
   | none => false) &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

/-- `receiveCallTakesReplyInPlace` as it is compiled: the caller's successor
asked of its link code (`receiveCallTakesReplyInPlace_eq_impl`). -/
@[inline] def receiveCallTakesReplyInPlaceImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  sTcb.replyObject.isNone &&
  (st.getTcb? receiver).isSome &&
  (match st.getReply? rid with
   | some rp => rp.isFree
   | none => false) &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

@[csimp] theorem receiveCallTakesReplyInPlace_eq_impl :
    @receiveCallTakesReplyInPlace = @receiveCallTakesReplyInPlaceImpl := by
  funext st endpointId receiver s sTcb rid
  unfold receiveCallTakesReplyInPlace receiveCallTakesReplyInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- The specification's state after a receive takes a queued caller: the
caller popped and blocked on the reply, the reply object and the caller linked,
the receiver made ready holding the caller's message, and the caller queued on
the receiver's reply waiters (`receiveCallTake_inPlace`). -/
def receiveCallTakeState (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    SystemState :=
  (((((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
      (callCallerTcb endpointId receiver)).modifyObject rid.toObjId
      (replyWithCaller s)).updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
      receiver (callReceiverTcb (blockedSenderMessage
        (storePopHead st endpointId false s sTcb.queueNext) s sTcb))).linkReplyWaiter
      s receiver

/-- **The receive's take of a queued caller, in place**: under
`receiveCallTakesInPlace` the specification's receive commits
`receiveCallTakeState`, the caller left blocked on the reply holding its
SchedContext binding and the receiver holding its own. -/
theorem receiveCallTake_inPlace_facts (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid = true) :
    endpointReceiveDualOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid, .ok (s, none)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map TCB.ipcState =
        some (.blockedOnReply endpointId (some receiver)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map
          TCB.schedContextBinding = (st.getTcb? s).map TCB.schedContextBinding ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? receiver).map
          TCB.schedContextBinding = (st.getTcb? receiver).map TCB.schedContextBinding ∧
      (∀ k, (receiveCallTakeState st endpointId s sTcb receiver rid).objects.findsInPlace k =
        st.objects.findsInPlace k) ∧
      (∀ {id ty}, storeLeavesIndexAndTypes st id ty = true → storeLeavesIndexAndTypes
        (receiveCallTakeState st endpointId s sTcb receiver rid) id ty = true) ∧
      (∀ k o, (∀ t, o ≠ .tcb t) → (∀ e, o ≠ .endpoint e) → k ≠ rid.toObjId →
        st.objects[k]? = some o →
        (receiveCallTakeState st endpointId s sTcb receiver rid).objects[k]? = some o) ∧
      (∀ rp, st.getReply? rid = some rp →
        (receiveCallTakeState st endpointId s sTcb receiver rid).getReply? rid =
          some { rp with callerCode := SeLe4n.ThreadId.optCode (some s) }) ∧
      (∃ ct', (receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s = some ct' ∧
        ct'.replyObject = some rid) ∧
      determineTargetCore (receiveCallTakeState st endpointId s sTcb receiver rid) s =
        determineTargetCore st s ∧
      determineTargetCore (receiveCallTakeState st endpointId s sTcb receiver rid) receiver =
        determineTargetCore st receiver := by
  unfold receiveCallTakeState
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hLQ⟩, hFQ⟩, hRO⟩, hRT⟩, hRp⟩,
    hCall⟩ := hG
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, _⟩, hLH⟩, hFH⟩, hNx⟩ := hSG'
  obtain ⟨rt, hRTo⟩ : ∃ rt, st.getTcb? receiver = some rt := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  obtain ⟨rp, hRpo, hFree⟩ : ∃ rp, st.objects[rid.toObjId]? = some (.reply rp) ∧
      rp.isFree = true := by
    split at hRp
    · next rp h => exact ⟨rp, (SystemState.getReply?_eq_some_iff _ _ _).mp h, hRp⟩
    · cases hRp
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNeEQ : endpointId ≠ rid.toObjId := fun h => by rw [h, hRpo] at hE; cases hE
  have hNeSQ : s.toObjId ≠ rid.toObjId := fun h => by rw [h, hRpo] at hT; cases hT
  have hNeRQ : receiver.toObjId ≠ rid.toObjId := fun h => by rw [h, hRpo] at hRo; cases hRo
  have hNeQS : rid.toObjId ≠ s.toObjId := fun h => hNeSQ h.symm
  have hNeQR : rid.toObjId ≠ receiver.toObjId := fun h => hNeRQ h.symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxQ : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ rid.toObjId := fun n hn h => by
    rw [hn] at hNx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hNx
    obtain ⟨_, hTnB⟩ := hNx
    obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
    have hTn' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn
    rw [h, hRpo] at hTn'; cases hTn'
  have hNk : ∀ n, sTcb.queueNext = some n → ∃ nt, st.objects[n.toObjId]? = some (.tcb nt) :=
    fun n hn => by
      rw [hn] at hNx
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hNx
      obtain ⟨_, hTnB⟩ := hNx
      obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
      exact ⟨nt, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn⟩
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  -- Every object but a thread, an endpoint or the reply object stays.
  have hOk1 : ∀ k o, (∀ t, o ≠ .tcb t) → (∀ e, o ≠ .endpoint e) → k ≠ rid.toObjId →
      st.objects[k]? = some o →
      (storePopHead st endpointId false s sTcb.queueNext).objects[k]? = some o :=
    fun k o hnt hne _ hk => (hFr.other k
      (fun e => by rw [e, hk] at hE; exact hne ep (Option.some.inj hE))
      (fun e => by rw [e, hk] at hT; exact hnt sTcb (Option.some.inj hT))
      (fun n hn e => by
        obtain ⟨nt, hTn⟩ := hNk n hn
        rw [e, hk] at hTn; exact hnt nt (Option.some.inj hTn))).trans hk
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hO1q := (hFr.other _ hNeEQ hNeSQ hNxQ).trans hRpo
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  have hM2 : storeTcbIpcStateAndMessage (storePopHead st endpointId false s sTcb.queueNext) s
      (.blockedOnReply endpointId (some receiver)) none =
      .ok ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
        (callCallerTcb endpointId receiver)) :=
    modifyTcb_eq_updateTcb (callCallerTcb endpointId receiver) hSRes hFr.head_tcb (hFr.leaves hLH)
  unfold endpointReceiveDualOnCore
  simp only [hEp, hH, hPop]
  rw [if_pos (by revert hCall; cases sTcb.ipcState <;> simp)]
  rw [if_pos (by revert hCall; cases sTcb.ipcState <;> simp)]
  rw [hM2]
  simp only []
  generalize blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb
    = msg
  generalize hS1 : storePopHead st endpointId false s sTcb.queueNext = S1 at *
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace (callCallerTcb endpointId receiver)
    hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace (callCallerTcb endpointId receiver)
    hFr.head_tcb hFH1 hNeSR).trans hO1r
  have hO2q := (updateTcb_get?_ne_of_findsInPlace (callCallerTcb endpointId receiver)
    hFr.head_tcb hFH1 hNeSQ).trans hO1q
  have hK2 : ∀ k, (S1.updateTcb s (callCallerTcb endpointId receiver)).objects.findsInPlace k =
      st.objects.findsInPlace k := fun k =>
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 k).trans (hFr.keepsFinds k)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (S1.updateTcb s (callCallerTcb endpointId receiver)) id ty =
        true :=
    fun h => updateTcb_storeLeaves _ hFr.head_tcb hFH1 (hFr.leaves h)
  have hOk2 : ∀ k o, (∀ t, o ≠ .tcb t) → (∀ e, o ≠ .endpoint e) → k ≠ rid.toObjId →
      st.objects[k]? = some o →
      (S1.updateTcb s (callCallerTcb endpointId receiver)).objects[k]? = some o :=
    fun k o hnt hne hq hk => (updateTcb_get?_ne_of_findsInPlace (callCallerTcb endpointId receiver)
      hFr.head_tcb hFH1 (fun e => by rw [e, hk] at hT; exact hnt sTcb (Option.some.inj hT))).trans
      (hOk1 k o hnt hne hq hk)
  generalize hS2 : S1.updateTcb s (callCallerTcb endpointId receiver) = S2 at *
  -- The reply object linked to the caller.
  have hFQ2 := (hK2 _).trans hFQ
  have hRp2 : S2.getReply? rid = some rp := (SystemState.getReply?_eq_some_iff _ _ _).mpr hO2q
  have hS3 : S2.modifyObject rid.toObjId (replyWithCaller s) =
      { S2 with objects := (S2.objects.insert rid.toObjId
          (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) })) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hO2q)]
    rfl
  have hStR : storeObject rid.toObjId
      (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) }) S2 =
      .ok ((), { S2 with objects := (S2.objects.insert rid.toObjId
          (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) })) }) :=
    storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL2 hLQ)
  rw [hS3]
  generalize hS3' : ({ S2 with objects := (S2.objects.insert rid.toObjId
      (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) })) } : SystemState)
      = S3 at *
  have hO3 : ∀ k, rid.toObjId ≠ k → S3.objects[k]? = S2.objects[k]? := fun k hk => by
    rw [← hS3']; exact RHTable.get?_insert_ne_of_findsInPlace k _ hFQ2 hk
  have hK3 : ∀ k, S3.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hS3']; exact (RHTable.findsInPlace_insert_of_findsInPlace k _ hFQ2).trans (hK2 k)
  have hL3 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S3 id ty = true := fun h => by
    rw [← hS3']
    exact storeLeavesIndexAndTypes_insert_inPlace hFQ2
      (fun o e => by rw [hO2q] at e; cases e; rfl) (hL2 h)
  have hOk3 : ∀ k o, (∀ t, o ≠ .tcb t) → (∀ e, o ≠ .endpoint e) → k ≠ rid.toObjId →
      st.objects[k]? = some o → S3.objects[k]? = some o :=
    fun k o hnt hne hq hk => (hO3 k (Ne.symm hq)).trans (hOk2 k o hnt hne hq hk)
  have hS3q : S3.objects[rid.toObjId]? =
      some (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) }) := by
    rw [← hS3']; exact RHTable.get?_insert_self_of_findsInPlace _ hFQ2
  have hT3s : S3.getTcb? s = some (callCallerTcb endpointId receiver (tcbOffQueue sTcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((hO3 _ hNeQS).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT2s))
  have hT3r : S3.getTcb? receiver = some rt :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hO3 _ hNeQR).trans hO2r)
  have hFS3 := (hK3 _).trans hFH
  -- The caller linked to the reply object.
  have hSt4 : storeObject s.toObjId
      (.tcb { callCallerTcb endpointId receiver (tcbOffQueue sTcb) with
        replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) S3 =
      .ok ((), S3.updateTcb s
        (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })) := by
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL3 hLH),
      SystemState.updateTcb_eq_of_some hT3s]
  have hRO3 : (callCallerTcb endpointId receiver (tcbOffQueue sTcb)).replyObject.isNone =
      true := hRO
  have hT4r : (S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).getTcb?
        receiver = some rt :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((updateTcb_get?_ne_of_findsInPlace _ hT3s hFS3 hNeSR).trans
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT3r))
  have hL4 : storeLeavesIndexAndTypes (S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }))
        receiver.toObjId .tcb = true :=
    updateTcb_storeLeaves _ hT3s hFS3 (hL3 hLR)
  -- The receiver made ready holding the message.
  have hM5 : storeTcbIpcStateAndMessage (S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })) receiver
        .ready (some msg) =
      .ok ((S3.updateTcb s
        (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
          receiver (callReceiverTcb msg)) :=
    modifyTcb_eq_updateTcb _ hRRes hT4r hL4
  have hFR4 := (updateTcb_findsInPlace
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hT3s hFS3
      receiver.toObjId).trans ((hK3 _).trans hFR)
  have hT4s := updateTcb_getTcb?_self_of_findsInPlace
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hT3s hFS3
  have hX_r := updateTcb_getTcb?_self_of_findsInPlace (callReceiverTcb msg) hT4r hFR4
  have hX_s : ((S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
        receiver (callReceiverTcb msg)).getTcb? s =
      some { callCallerTcb endpointId receiver (tcbOffQueue sTcb) with
        replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((updateTcb_get?_ne_of_findsInPlace _ hT4r hFR4 (fun h => hNeSR h.symm)).trans
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT4s))
  have hA := SystemState.linkReplyWaiter_objectsAgreeOffRunLinks ((S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
        receiver (callReceiverTcb msg)) s receiver
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  -- What the five writes and the waiter link leave.
  have hK5 : ∀ k, ((S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
        receiver (callReceiverTcb msg)).objects.findsInPlace k = st.objects.findsInPlace k :=
    fun k => (updateTcb_findsInPlace _ hT4r hFR4 k).trans
      ((updateTcb_findsInPlace _ hT3s hFS3 k).trans (hK3 k))
  have hL5 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes ((S3.updateTcb s
        (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
          receiver (callReceiverTcb msg)) id ty = true :=
    fun h => updateTcb_storeLeaves _ hT4r hFR4 (updateTcb_storeLeaves _ hT3s hFS3 (hL3 h))
  have hOk5 : ∀ k o, (∀ t, o ≠ .tcb t) → (∀ e, o ≠ .endpoint e) → k ≠ rid.toObjId →
      st.objects[k]? = some o → ((S3.updateTcb s
        (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
          receiver (callReceiverTcb msg)).objects[k]? = some o :=
    fun k o hnt hne hq hk => (updateTcb_get?_ne_of_findsInPlace _ hT4r hFR4
      (fun e => by rw [e, hk] at hRo; exact hnt rt (Option.some.inj hRo))).trans
      ((updateTcb_get?_ne_of_findsInPlace _ hT3s hFS3
        (fun e => by rw [e, hk] at hT; exact hnt sTcb (Option.some.inj hT))).trans
        (hOk3 k o hnt hne hq hk))
  have hRq5 : ((S3.updateTcb s
      (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
        receiver (callReceiverTcb msg)).objects[rid.toObjId]? =
      some (.reply { rp with callerCode := SeLe4n.ThreadId.optCode (some s) }) :=
    (updateTcb_get?_ne_of_findsInPlace _ hT4r hFR4 hNeRQ).trans
      ((updateTcb_get?_ne_of_findsInPlace _ hT3s hFS3 hNeSQ).trans hS3q)
  refine ⟨?_, ?_, ?_, ?_, fun k => (linkReplyWaiter_keepsFinds _ s receiver k).trans (hK5 k),
    fun h => storeLeaves_of_agree hA (hL5 h),
    fun k o hnt hne hq hk => hA.get_of_not_tcb hnt (hOk5 k o hnt hne hq hk),
    fun rp' hrp' => ?_, ?_, ?_, ?_⟩
  · unfold SystemState.linkCallerReply SystemState.linkReply
    simp only [hRp2, hFree, ↓reduceIte, hStR, hT3s, hRO3, hSt4, hM5]
  · rw [TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.ipcState (hA.getTcb? s), hX_s]
    exact congrArg some (TCB.ipcState_setIpcState { tcbOffQueue sTcb with pendingMessage := none }
      (.blockedOnReply endpointId (some receiver)))
  · rw [TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding (hA.getTcb? s), hX_s,
      hTs]
    rfl
  · rw [TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding
      (hA.getTcb? receiver), hX_r, hRTo]
    rfl
  · have hEq : rp' = rp := by
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRpo] at hrp'
      exact (Option.some.inj hrp').symm
    subst hEq
    exact (SystemState.getReply?_eq_some_iff _ _ _).mpr
      (hA.get_of_not_tcb (fun _ e => by cases e) hRq5)
  · obtain ⟨t', h', e'⟩ := hA.getTcb?_some hX_s
    refine ⟨t', h', ?_⟩
    have h1 : t'.replyObject = SeLe4n.ReplyId.ofOptCode (SeLe4n.ReplyId.optCode (some rid)) :=
      TCB.proj_eq_of_withoutRunLinks_eq TCB.replyObject e'
    rw [h1, SeLe4n.ReplyId.ofOptCode_optCode]
  · exact (determineTargetCore_of_objectsAgreeOffRunLinks hA s).trans
      (determineTargetCore_congr st _ s (by rw [hX_s, hTs]; rfl))
  · exact (determineTargetCore_of_objectsAgreeOffRunLinks hA receiver).trans
      (determineTargetCore_congr st _ receiver (by rw [hX_r, hRTo]; rfl))

/-- **The receive's take of a queued caller, in place**: under
`receiveCallTakesInPlace` the specification's receive commits
`receiveCallTakeState`, the caller left blocked on the reply holding its
SchedContext binding and the receiver holding its own. -/
theorem receiveCallTake_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid = true) :
    endpointReceiveDualOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid, .ok (s, none)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map TCB.ipcState =
        some (.blockedOnReply endpointId (some receiver)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map
          TCB.schedContextBinding = (st.getTcb? s).map TCB.schedContextBinding ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? receiver).map
          TCB.schedContextBinding = (st.getTcb? receiver).map TCB.schedContextBinding :=
  let ⟨h1, h2, h3, h4, _⟩ := receiveCallTake_inPlace_facts st endpointId ep receiver rid core s
    sTcb hE hH hT hG
  ⟨h1, h2, h3, h4⟩

/-- The caller a receive delivers without linking it to a reply: seL4
`receiveIPC`'s `setThreadState(sender, Inactive)` -- the Call is answered by
nothing, so the thread runs again only when something restarts it. -/
@[inline] def callerInactive (t : TCB) : TCB := { t with threadState := .Inactive }

/-- **A receive taking a caller it links to no reply writes only its slots**:
`receiveTakesInPlace`'s slots (the pop's, and the receiver an unreserved thread
other than the caller and its successor, rewritten where it stands), the sender
blocked on a call, and the link refused -- the cap grants neither `Grant` nor
`GrantReply`, or the receive supplies no reply object (`suppliesReply`).  seL4
then delivers the message and leaves the caller `Inactive`; no reply object, no
SchedContext and no reply-waiter queue is written, and nobody is woken. -/
@[inline] def receiveCallNoLinkTakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (suppliesReply : Bool) : Bool :=
  sendWakesInPlace st endpointId s sTcb.queueNext &&
  !receiver.isReserved && receiver != s &&
  (match sTcb.queueNext with
   | none => true
   | some n => receiver != n) &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => !((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && suppliesReply)
   | _ => false)

/-- `receiveCallNoLinkTakesInPlace` as it is compiled: the caller's successor
asked of its link code, so no `some` cell is built for a caller with a successor
(`receiveCallNoLinkTakesInPlace_eq_impl`). -/
@[inline] def receiveCallNoLinkTakesInPlaceImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (suppliesReply : Bool) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => !((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && suppliesReply)
   | _ => false)

@[csimp] theorem receiveCallNoLinkTakesInPlace_eq_impl :
    @receiveCallNoLinkTakesInPlace = @receiveCallNoLinkTakesInPlaceImpl := by
  funext st endpointId receiver s sTcb suppliesReply
  unfold receiveCallNoLinkTakesInPlace receiveCallNoLinkTakesInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- The state a no-link take commits: the caller popped, stored `.ready` and
made `Inactive`, the receiver made ready holding the caller's message. -/
def receiveCallNoLinkTakeState (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (receiver : SeLe4n.ThreadId) : SystemState :=
  (((storePopHead st endpointId false s sTcb.queueNext).updateTcb s receiverReady).updateTcb s
      callerInactive).updateTcb receiver
    (callReceiverTcb (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext)
      s sTcb))

/-- **The receive's no-link take, in place**: under
`receiveCallNoLinkTakesInPlace`, the specification's receive pops the caller in
place, stores it `.ready`, makes it `Inactive` and hands the receiver its
message -- the no-link arm of `endpointReceiveDualOnCore`, written in its
slots. -/
theorem receiveCallNoLinkTake_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome = true) :
    endpointReceiveDualOnCore endpointId receiver replyId core st =
      (receiveCallNoLinkTakeState st endpointId s sTcb receiver, .ok (s, none)) := by
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, hNC⟩ := hG
  obtain ⟨callEp, hCallSt, hNoLink⟩ : ∃ c, sTcb.ipcState = .blockedOnCall c ∧
      ((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && replyId.isSome) = false := by
    split at hNC
    · next c hc =>
      refine ⟨c, hc, ?_⟩
      revert hNC
      cases sTcb.ipcCanGrant <;> cases sTcb.ipcCanGrantReply <;> cases replyId <;> simp
    · cases hNC
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, _⟩, hLH⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  unfold endpointReceiveDualOnCore receiveCallNoLinkTakeState
  simp only [(SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE, hH, hPop]
  rw [if_pos (by rw [hCallSt]), if_neg (by rw [hNoLink]; simp)]
  have hM2 : storeTcbIpcStateAndMessage (storePopHead st endpointId false s sTcb.queueNext) s
      .ready none = .ok ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
        receiverReady) :=
    modifyTcb_eq_updateTcb receiverReady hSRes hFr.head_tcb (hFr.leaves hLH)
  rw [hM2]
  simp only []
  generalize blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb
    = msg
  generalize hS1 : storePopHead st endpointId false s sTcb.queueNext = S1 at *
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hFH2 : (S1.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hO3r := (updateTcb_get?_ne_of_findsInPlace callerInactive hT2s hFH2 hNeSR).trans hO2r
  have hL3 : storeLeavesIndexAndTypes ((S1.updateTcb s receiverReady).updateTcb s callerInactive)
      receiver.toObjId .tcb = true :=
    updateTcb_storeLeaves _ hT2s hFH2
      (updateTcb_storeLeaves _ hFr.head_tcb hFH1 (hFr.leaves hLR))
  have hM4 : storeTcbIpcStateAndMessage
      ((S1.updateTcb s receiverReady).updateTcb s callerInactive) receiver .ready (some msg) =
      .ok (((S1.updateTcb s receiverReady).updateTcb s callerInactive).updateTcb receiver
        (callReceiverTcb msg)) :=
    modifyTcb_eq_updateTcb _ hRRes ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r) hL3
  rw [show (fun t : TCB => { t with threadState := .Inactive }) = callerInactive from rfl, hM4]

/-- **A blocking receive refusing its reply object, decided first**: where the
receiver may block and its enqueue stays in its slots (`enqueuesInPlace`), the
specification's block path reaches its stash check with every earlier step
succeeding, and a reply object the receive may not stash (`replyStashValid`)
refuses it with the entry state, as if nothing had run. -/
theorem receiveBlock_stashRefused_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rt : TCB) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hS : ep.sendQ.head = none)
    (hR : st.objects[receiver.toObjId]? = some (.tcb rt))
    (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st endpointId receiver ep.receiveQ.tail = true)
    (hV : st.replyStashValid replyId = false) :
    endpointReceiveDualOnCore endpointId receiver replyId executingCore st =
      (st, .error .replyCapInvalid) := by
  have hA' := hA
  simp only [receiveBlockAdmits, Bool.and_eq_true] at hA'
  obtain ⟨hEnqOk, hT, hF, hL⟩ := endpointEnqueue_inPlace_eq st endpointId ep true receiver rt
    ep.receiveQ.tail hE rfl hR hA'.1 hEnq
  have hRes : receiver.isReserved = false := by
    simp only [enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hEnq
    exact hEnq.1.1.1.1.1
  have hNoDon : preReceiveDonation? st receiver = none := by
    have hLook : lookupTcb st receiver = some rt := by
      simp only [lookupTcb, hRes, Bool.false_eq_true, ↓reduceIte]
      exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hR
    unfold preReceiveDonation?
    rw [hLook]
    obtain ⟨_, hB⟩ := hA'
    revert hB
    cases h : rt.schedContextBinding <;> simp [h]
  unfold endpointReceiveDualOnCore
  simp only [(SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE, hS,
    cleanupPreReceiveDonationMigrated_of_no_donation st receiver hNoDon, hEnqOk]
  generalize storeEndpointEnqueue st endpointId true receiver ep.receiveQ.tail = S at hT hF hL ⊢
  let g2 := fun t : TCB => (TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive endpointId))
  have h1 : storeTcbIpcStateAndMessage S receiver (.blockedOnReceive endpointId) none =
      .ok (S.updateTcb receiver g2) := modifyTcb_eq_updateTcb _ hRes hT hL
  rw [h1]
  simp only []
  rw [updateTcb_getTcb?_self_of_findsInPlace g2 hT hF]
  simp only [hV, Bool.false_eq_true, ↓reduceIte]

/-- **The receive body, its checks first.**  The specification's rendezvous
pops the sender, then looks up the TCBs it writes, refusing with its entry
state where a lookup fails, so that state is alive across the pop.  Where
every write stays in its slot (`receiveTakesInPlace`) those lookups succeed,
so this form decides them on the entry state before the first write and runs
the take as its writes: the in-place pop, the sender made ready and woken on
its home core, and the receiver handed the message, read off the state the
pop left before anything writes the sender (`receiveTake_inPlace`).  A
queued caller is decided the same way: one the receive links to no reply
(`receiveCallNoLinkTakesInPlace`) is popped, made ready, left `Inactive` and
its message handed to the receiver (`receiveCallNoLinkTake_inPlace`); one it
links to the reply object it supplies (`receiveCallTakesReplyInPlace`) is
popped, blocked on the reply, linked to it and queued on the receiver's reply
waiters (`receiveCallTake_inPlace`).  The
block path's lookups and its stash check come after the cleanup, the enqueue
and the block; where the receiver may block and its enqueue stays in its slots
they are decided first too: a reply object the receive may not stash refuses
with the untouched entry state (`receiveBlock_stashRefused_eq`), and one whose
stasher record stays in its slot blocks the receiver in place
(`receiveBlock_inPlace_eq`).  Any other receive runs the specification.  It is the specification, with no assumption
(`endpointReceiveDualOnCore_eq_checked`), through which the compiler runs
it. -/
def endpointReceiveDualOnCoreChecked (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (SeLe4n.ThreadId × Option (CoreId × SgiKind)) :=
  match st.getEndpoint? endpointId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        if receiveTakesInPlace st endpointId receiver s sTcb then
          let popped := storePopHeadCode st endpointId false s sTcb.queueNextCode
          let msg := blockedSenderMessage popped s sTcb
          let woken := wakeThread (popped.updateTcb s receiverReady) s executingCore
          (woken.1.updateTcb receiver (callReceiverTcb msg), .ok (s, woken.2))
        else if receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome then
          let popped := storePopHeadCode st endpointId false s sTcb.queueNextCode
          let msg := blockedSenderMessage popped s sTcb
          (((popped.updateTcb s receiverReady).updateTcb s callerInactive).updateTcb receiver
            (callReceiverTcb msg), .ok (s, none))
        else
          match replyId with
          | some rid =>
            if receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid then
              let popped := storePopHeadCode st endpointId false s sTcb.queueNextCode
              let msg := blockedSenderMessage popped s sTcb
              ((((((popped.updateTcb s (callCallerTcb endpointId receiver)).modifyObject
                  rid.toObjId (replyWithCaller s)).updateTcb s
                  (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb
                  receiver (callReceiverTcb msg)).linkReplyWaiter s receiver), .ok (s, none))
            else endpointReceiveDualOnCore endpointId receiver replyId executingCore st
          | none => endpointReceiveDualOnCore endpointId receiver replyId executingCore st
      | none => endpointReceiveDualOnCore endpointId receiver replyId executingCore st
    | none =>
      match st.getTcb? receiver with
      | some rt =>
        if receiveBlockAdmits rt &&
            enqueuesInPlaceCode st endpointId receiver ep.recvTailCode then
          if replyStashValidCode st (SeLe4n.ReplyId.optCode replyId) then
            if replyRecordsInPlace st (SeLe4n.ReplyId.optCode replyId) then
              (removeRunnableOnCore (storeReceiveBlock st endpointId receiver ep.recvTailCode
                (SeLe4n.ReplyId.optCode replyId)) receiver executingCore, .ok (receiver, none))
            else endpointReceiveDualOnCore endpointId receiver replyId executingCore st
          else (st, .error .replyCapInvalid)
        else endpointReceiveDualOnCore endpointId receiver replyId executingCore st
      | none => endpointReceiveDualOnCore endpointId receiver replyId executingCore st
  | none => endpointReceiveDualOnCore endpointId receiver replyId executingCore st

/-- The receive body's checks-first form is the specification, with no
assumption; the compiler runs it in the specification's place. -/
@[csimp] theorem endpointReceiveDualOnCore_eq_checked :
    @endpointReceiveDualOnCore = @endpointReceiveDualOnCoreChecked := by
  funext endpointId receiver replyId executingCore st
  unfold endpointReceiveDualOnCoreChecked
  split
  · rename_i ep hE
    split
    · rename_i s hH
      split
      · rename_i sTcb hT
        split
        · rename_i hG
          rw [receiveTake_inPlace st endpointId ep receiver replyId executingCore s sTcb
            ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
            ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG,
            storePopHeadCode_eq, TCB.ofOptCode_queueNextCode]
        · split
          · rename_i hN
            rw [receiveCallNoLinkTake_inPlace st endpointId ep receiver replyId executingCore s
              sTcb ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
              ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hN,
              storePopHeadCode_eq, TCB.ofOptCode_queueNextCode]
            rfl
          · split
            · rename_i rid _
              split
              · rename_i hC
                rw [(receiveCallTake_inPlace st endpointId ep receiver rid executingCore s sTcb
                  ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hC).1,
                  storePopHeadCode_eq, TCB.ofOptCode_queueNextCode]
                rfl
              · rfl
            · rfl
      · rfl
    · rename_i hH
      have hE' := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE
      split
      · rename_i rt hRt
        have hR := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRt
        split
        · rename_i hAE
          rw [Bool.and_eq_true, enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hAE
          rw [replyStashValidCode_eq, SeLe4n.ReplyId.ofOptCode_optCode]
          split
          · rename_i hV
            split
            · rename_i hRec
              exact receiveBlock_inPlace_eq st endpointId ep receiver rt replyId executingCore
                hE' hH hR hAE.1 (by
                  simp only [receiveBlocksInPlace, hAE.2, hV, hRec, Bool.and_self])
            · rfl
          · rename_i hV
            exact receiveBlock_stashRefused_eq st endpointId ep receiver rt replyId executingCore
              hE' hH hR hAE.1 hAE.2 (by simpa using hV)
        · rfl
      · rfl
  · rfl


/-- **The capability-carrying receive, its reads first.**  Whether the receive
dequeued a sender, what that sender asks to transfer and the receiver's side
of it are read off the state the receive ran on; the specification reads the
first after the receive wrote.  This form branches on it before the receive,
and binds the transfer's two reads there too, so no entry state is alive
across the receive's writes.  It is the specification, with no assumption
(`endpointReceiveDualWithCapsOnCore_eq_checked`), through which the compiler
runs it. -/
def endpointReceiveDualWithCapsOnCoreChecked
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (st : SystemState) :
    SystemState ×
      Except KernelError
        (SeLe4n.ThreadId × CapTransferSummary × Option (CoreId × SgiKind)) :=
  if (receiveRendezvousSender? st endpointId).isNone then
    match endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
    | (st', .error e) => (st', .error e)
    | (st', .ok (senderId, sgi)) => (st', .ok (senderId, { results := #[] }, sgi))
  else
    let req := receiveCapRequest st endpointId
    let target? := receiverCapTarget? st receiver
    match endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
    | (st', .error e) => (st', .error e)
    | (st', .ok (senderId, sgi)) =>
        match receiveTransferCaps req endpointId target? st' with
        | .error e => (st', .error e)
        | .ok (summary, st'') => (st'', .ok (senderId, summary, sgi))

/-- The capability-carrying receive's reads-first form is the specification,
with no assumption; the compiler runs it in the specification's place. -/
@[csimp] theorem endpointReceiveDualWithCapsOnCore_eq_checked :
    @endpointReceiveDualWithCapsOnCore = @endpointReceiveDualWithCapsOnCoreChecked := by
  funext endpointId receiver replyId executingCore st
  unfold endpointReceiveDualWithCapsOnCore endpointReceiveDualWithCapsOnCoreChecked
  cases (receiveRendezvousSender? st endpointId).isNone <;>
    rcases endpointReceiveDualOnCore endpointId receiver replyId executingCore st
      with ⟨st', _ | ⟨senderId, sgi⟩⟩ <;> rfl

end SeLe4n.Kernel
