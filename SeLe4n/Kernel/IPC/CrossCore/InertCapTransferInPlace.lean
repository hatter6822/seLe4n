-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.InertCapTransfer
import SeLe4n.Kernel.IPC.CrossCore.LongCallInPlace
import SeLe4n.Kernel.Architecture.RoutedRegisterDecode

/-!
# A capability-carrying rendezvous that transfers nothing, decided in place

A short capability-carrying send, call or take whose transfer transfers nothing
(`capTransferInert`) writes the rendezvous in place.  The arm decides it from
the sender's and the receiver's buffers before any write
(`capTransferInertW`), and the decision is the specification's
(`capTransferInert_of_W`): the request the sender's frame makes reads its first
address from the same `caps_or_badges` word (`senderExtraCapAddrs`).  The transfer the specification then runs, after the rendezvous, reads
every CNode as the send found it (`ipcBufferReadsAgree.getCNode?`), so it is the
identity and reports zero (`receiveTransferCaps_of_inert`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A capability-carrying rendezvous that transfers nothing, decided in
place**, from the receiver `rt` and the sender `stcb`: the receiver has no
buffer, or its buffer names no receive slot and the sender's first address
(its `caps_or_badges` word 0) does not name a capability the transfer unwraps
at `endpointId`. -/
@[inline] def capTransferInertW (st : SystemState) (endpointId : SeLe4n.ObjId)
    (rt stcb : TCB) : Bool :=
  !receiverHasBuffer st rt ||
    (receiveSlotAbsentW st rt &&
      match senderExtraCapAddr? st stcb 0 with
      | none => true
      | some addr =>
        match stcb.spaceCells[0] with
        | none => true
        | some root => extraCapStaysW st endpointId root addr)

/-- **The in-place decision is the specification's**: for a sender whose saved
frame is a short capability-carrying one, the request it makes
(`senderFrameCapRequest`) transfers nothing to the receiver's side. -/
theorem capTransferInert_of_W (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (rt : TCB) (sender : SeLe4n.ThreadId) (stcb : TCB) (grant : Bool)
    (hT : st.getTcb? r = some rt)
    (hW : capTransferInertW st endpointId rt stcb = true) :
    capTransferInert st endpointId (receiverCapTarget? st r)
      (senderFrameCapRequest st sender stcb grant) = true := by
  unfold senderFrameCapRequest
  cases grant
  · rfl
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  split
  · rfl
  cases hCn : stcb.spaceCells[0] with
  | none => rfl
  | some root =>
    unfold receiverCapTarget?
    simp only [hT]
    unfold capTransferInertW at hW
    cases hB : receiverHasBuffer st rt
    · rfl
    simp only [hB, Bool.not_true, Bool.false_or, Bool.and_eq_true, receiveSlotAbsentW_eq,
      Option.isNone_iff_eq_none] at hW
    obtain ⟨hSlot, hFirst⟩ := hW
    simp only [↓reduceIte, hSlot, capTransferInert]
    split
    · rfl
    · next a ha =>
      rw [senderExtraCapAddrs_getElem?_zero ha] at hFirst
      simp only [hCn] at hFirst
      rw [extraCapStaysW_eq] at hFirst
      exact hFirst

/-- The decision for the sender `sender` by its id: its saved registers are
`rf`. -/
@[inline] def senderTransferInertW (st : SystemState) (endpointId : SeLe4n.ObjId) (rt : TCB)
    (sender : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? sender with
  | none => false
  | some stcb => capTransferInertW st endpointId rt stcb

theorem senderTransferInertW_isSome {st : SystemState} {endpointId : SeLe4n.ObjId} {rt : TCB}
    {sender : SeLe4n.ThreadId}
    (h : senderTransferInertW st endpointId rt sender = true) :
    (st.getTcb? sender).isSome = true := by
  unfold senderTransferInertW at h
  split at h
  · cases h
  · next hT => rw [hT]; rfl

/-- **A short capability-carrying send's decision is the specification's**: the
request the send makes (`sendCapRequest`) transfers nothing to the receiver's
side. -/
theorem capTransferInert_sendCapRequest_of_W (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (rt : TCB) (sender : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant : Bool)
    (hT : st.getTcb? r = some rt)
    (hW : senderTransferInertW st endpointId rt sender = true) :
    capTransferInert st endpointId (receiverCapTarget? st r)
      (sendCapRequest st endpointId sender (.frame badge grant)) = true := by
  unfold sendCapRequest
  split
  · rfl
  unfold senderTransferInertW at hW
  cases hS : st.getTcb? sender with
  | none => rfl
  | some stcb =>
    simp only [hS] at hW
    exact capTransferInert_of_W st endpointId r rt sender stcb grant hT hW

/-- **The send rendezvous reads every CNode where the send found it**: its pop,
the receiver's message and its wake write no CNode. -/
theorem getCNode?_sendRendezvousWoken (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (id : SeLe4n.ObjId) :
    (wakeThread (storeSendRendezvous st endpointId r next msg) r core).1.getCNode? id =
      st.getCNode? id := by
  rw [storeSendRendezvous_eq_with]
  have hg : ∀ t, (receiveCompleteTcb msg t).vspaceRoot = t.vspaceRoot ∧
      (receiveCompleteTcb msg t).ipcBuffer = t.ipcBuffer := fun t => by
    unfold receiveCompleteTcb TCB.setIpcState; exact ⟨rfl, rfl⟩
  have a1 := ipcBufferReadsAgree_storeSendRendezvousWith st endpointId r next
    (receiveCompleteTcb msg) hg hNo
  have a2 := ipcBufferReadsAgree_wakeThread
    (storeSendRendezvousWith st endpointId r next (receiveCompleteTcb msg)) r core
    (storeSendRendezvousWith_noResizeDue st endpointId r next (receiveCompleteTcb msg) hNo)
  exact (a2.trans a1).getCNode? id

/-- **The call rendezvous reads every CNode where the call found it**: its pop,
the receiver's message and wake, the caller's block on its reply and the reply
object write no CNode. -/
theorem getCNode?_storeCallRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue)
    (hNe : caller ≠ r) (id : SeLe4n.ObjId) :
    (storeCallRendezvous st endpointId caller r next rid msg core).getCNode? id =
      st.getCNode? id := by
  rw [storeCallRendezvous_eq_hold st endpointId caller r next rid msg core hNo hNe]
  have a1 := ipcBufferReadsAgree_storeCallRendezvousReady st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  generalize storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core
    = X at a1
  have a2 := ipcBufferReadsAgree_mapTcbInPlace X r (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)
  exact (a2.trans a1).getCNode? id

/-- **The take of a blocked sender reads every CNode where the receive found
it**: its pop, the sender's wake and the receiver's message write no CNode. -/
theorem getCNode?_receiveTake (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (id : SeLe4n.ObjId) :
    ((wakeThread ((storePopHead st endpointId false s next).updateTcb s receiverReady) s
      core).1.updateTcb receiver (callReceiverTcb msg)).getCNode? id = st.getCNode? id := by
  have h1 := storePopHead_noResizeDue st endpointId false s next hNo
  have a1 := ipcBufferReadsAgree_storePopHead st endpointId false s next hNo
  generalize storePopHead st endpointId false s next = P at h1 a1
  have a2 := ipcBufferReadsAgree_updateTcb P s receiverReady
    (fun t => by unfold receiverReady TCB.setIpcState; exact ⟨rfl, rfl⟩) h1
  have h2 := updateTcb_noResizeDue P s receiverReady h1
  generalize P.updateTcb s receiverReady = Q at h2 a2
  have a3 := ipcBufferReadsAgree_wakeThread Q s core h2
  have h3 := wakeThread_noResizeDue Q s core h2
  generalize (wakeThread Q s core).1 = W at h3 a3
  have a4 := ipcBufferReadsAgree_updateTcb W receiver (callReceiverTcb msg)
    (fun t => by unfold callReceiverTcb TCB.setIpcState; exact ⟨rfl, rfl⟩) h3
  exact (a4.trans (a3.trans (a2.trans a1))).getCNode? id

/-- The decision for a receive taking the blocked sender `stcb`, for the
receiver by its id. -/
@[inline] def receiverTransferInertW (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (stcb : TCB) : Bool :=
  match st.getTcb? receiver with
  | none => true
  | some rt => capTransferInertW st endpointId rt stcb

/-- **A take's decision is the specification's**: the request of the blocked
sender a receive dequeues (`receiveCapRequest`) transfers nothing to the
receiver's side. -/
theorem capTransferInert_receiveCapRequest_of_W (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.getEndpoint? endpointId = some ep) (hH : ep.sendQ.head = some s)
    (hS : st.getTcb? s = some sTcb)
    (hW : receiverTransferInertW st endpointId receiver sTcb = true) :
    capTransferInert st endpointId (receiverCapTarget? st receiver)
      (receiveCapRequest st endpointId) = true := by
  unfold receiveCapRequest
  have hSnd : receiveRendezvousSender? st endpointId = some s := by
    simp only [receiveRendezvousSender?, hE, Option.bind_some, hH]
  simp only [hSnd, hS, blockedSenderCapRequest]
  split
  · rfl
  · unfold receiverTransferInertW at hW
    cases hT : st.getTcb? receiver with
    | none =>
      have hTgt : receiverCapTarget? st receiver = none := by
        unfold receiverCapTarget?; rw [hT]
      rw [hTgt]
      rcases senderFrameCapRequest st s sTcb sTcb.ipcCanGrant with _ | ⟨_, _⟩ <;> rfl
    | some rt =>
      simp only [hT] at hW
      exact capTransferInert_of_W st endpointId receiver rt s sTcb sTcb.ipcCanGrant hT hW

end SeLe4n.Kernel
