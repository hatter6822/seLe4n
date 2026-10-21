/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace

/-!
# A receive that takes a blocked sender's message, written in place

WS-ZA ZA4.7.  A receive that finds a sender blocked on the endpoint pops it off
the send queue, makes it ready, wakes it on its home core, and hands the
receiver the message the sender kept in its registers
(`endpointReceiveDualOnCore`).  When every write stays in its slot
(`receiveTakesInPlace`), those writes are the in-place pop (`storePopHead`)
and two TCB writes (`receiveTake_inPlace`); the delivered frame is read
straight from the sender's saved registers (`performReceiveDelivered`).
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
        = true := fun h => storeLeaves_of_onlyObjectsSchedulerDiffer hD3 hA3 (hL2 h)
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
frame under the badge and grant right its capability carried. -/
theorem blockedSender_of_routedSend (st : SystemState) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (h : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    blockedSenderCapRequest st s sTcb = none ∧
      blockedSenderMessage st s sTcb =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
            sTcb.registerContext mi.length,
          badge := sTcb.ipcBadgeView, capsGranted := sTcb.ipcCanGrant } := by
  obtain ⟨d, hDec, _, _, _, hMi, hX, _, hRegs⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend st s _ _ 32 capAddr mi h
  refine ⟨?_, ?_⟩
  · have hE : (Architecture.SyscallArgDecode.decodeExtraCapAddrs d).isEmpty = true := by
      unfold Architecture.SyscallArgDecode.decodeExtraCapAddrs
      rw [hMi, hX]
      rfl
    unfold blockedSenderCapRequest senderFrameCapRequest blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, hE, ite_self]
  · unfold blockedSenderMessage blockedSenderMessageOf blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, senderFrameMessage, hRegs, hMi]
    rfl

/-- WS-ZA ZA4.7: **what a thread whose saved frame routes as a capability-free
send or call sends**: the message a send of its frame delivers is the inline
words of that frame under the capability's badge and grant right, and it asks
to transfer no capability -- so the send's register fast path, which writes
those words straight into the receiver's saved registers, delivers exactly what
the specification's send does. -/
theorem sendFrame_of_routed (st : SystemState) (s : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? s = some tcb) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (h : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
        tcb.registerContext 32 = .send capAddr mi ∨
      Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
        tcb.registerContext 32 = .call capAddr mi)
    (endpointId : SeLe4n.ObjId) (badge : Option SeLe4n.Badge) (grant : Bool) :
    sendPayloadMessage st s (.frame badge grant) =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
            tcb.registerContext mi.length,
          badge := badge, capsGranted := grant } ∧
      sendCapRequest st endpointId s (.frame badge grant) = none := by
  obtain ⟨d, hDec, hMi, hX, hRegs⟩ : ∃ d, blockedSenderDecode st s tcb = .ok d ∧
      d.msgInfo = mi ∧ mi.extraCaps = 0 ∧
      d.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map
        (SeLe4n.readReg tcb.registerContext) := by
    rcases h with h | h
    · obtain ⟨d, hDec, _, _, _, hMi, hX, _, hRegs⟩ :=
        Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend st s _ _ 32
          capAddr mi h
      exact ⟨d, hDec, hMi, hX, hRegs⟩
    · obtain ⟨d, hDec, _, _, _, hMi, hX, _, hRegs⟩ :=
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
      have hE : (Architecture.SyscallArgDecode.decodeExtraCapAddrs d).isEmpty = true := by
        unfold Architecture.SyscallArgDecode.decodeExtraCapAddrs
        rw [hMi, hX]
        rfl
      simp only [hE, ↓reduceIte]
      split <;> rfl

/-- A woken sender's completion frame commutes with a message-slot write at
another thread. -/
theorem stageWokenSendCompletion_msg (Y : SystemState) (r s : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (hNe : s ≠ r) (hNo : Y.objects.noResizeDue) :
    Architecture.stageWokenSendCompletion (Y.mapTcbInPlace r (TCB.withMessageSlots ρ μ π))
        (some s) =
      (Architecture.stageWokenSendCompletion Y (some s)).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold Architecture.stageWokenSendCompletion
  dsimp only
  rw [SystemState.getTcb?_mapTcbInPlace, if_neg (fun h => hNe h.symm)]
  cases Y.getTcb? s with
  | none => rfl
  | some t =>
    dsimp only
    split
    · unfold Architecture.writeReturnFrameToTcb
      exact updateTcb_msg _ _ _ _ _ _ _ hNo (fun h => absurd h hNe)
    · rfl

/-- **The receive's take, delivered**: the sender popped, made ready and woken
with its completion frame, the receiver made ready, and the six words of the
delivered frame -- read from the sender's saved registers before any write --
written into the receiver's saved registers.  No message is built. -/
@[noinline] def performReceiveDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (core : CoreId)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  let X := (wakeThread ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady) s core).1
  (Architecture.stageWokenSendCompletion (X.updateTcb receiver receiverReady) (some s)).mapTcbInPlace
    receiver (withFrameWords w0 w1 w2 w3 w4 w5)

/-- **The receive's take, delivered, is the specification's**: under
`receiveTakesInPlace`, a sender blocked by a routed capability-free send and
not delivering a fault, the WithCaps receive installs nothing and takes the
in-place writes, the rendezvous hands off no donation, and staging the woken
sender's completion and the receiver's message writes
`performReceiveDelivered`'s state, the frame's words read from the sender's
saved registers. -/
theorem receiveTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    let f := Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length sTcb.ipcBadgeView
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId root slot core st =
        (S4, .ok (s, { results := #[] }, W.2)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion S4 (some s))
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
  obtain ⟨_, hMsg⟩ := blockedSender_of_routedSend P s sTcb capAddr mi hR hF
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
  · -- the WithCaps receive installs nothing
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
    have hNoZ : (Architecture.stageWokenSendCompletion (W.1.updateTcb receiver receiverReady)
        (some s)).objects.noResizeDue := by
      unfold Architecture.stageWokenSendCompletion
      dsimp only
      split
      · split
        · exact updateTcb_noResizeDue _ _ _ hNoY
        · exact hNoY
      · exact hNoY
    have hZr : (Architecture.stageWokenSendCompletion (W.1.updateTcb receiver receiverReady)
        (some s)).getTcb? receiver = some (receiverReady rt3) := by
      unfold Architecture.stageWokenSendCompletion
      dsimp only
      split
      · split
        · unfold Architecture.writeReturnFrameToTcb
          rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoY, SystemState.getTcb?_mapTcbInPlace,
            if_neg hRS', hYr]
        · exact hYr
      · exact hYr
    have hSz : (blockedSenderMessage P s sTcb).registers.size ≤ 4 := by
      rw [hMsg]
      simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
      have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      omega
    rw [hS4, stageWokenSendCompletion_msg _ receiver s _ _ _ hRS' hNoY,
      stageDeliveredMessage_holdMessage _ _ _ hNoZ hSz, hMsg,
      Architecture.returnFrameOfMessage_regMessageBody]
    unfold writeDeliveredFrameIfReady performReceiveDelivered
    rw [hZr]
    simp only [receiverReady, TCB.ipcState_setIpcState, ↓reduceIte]
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]

end SeLe4n.Kernel
