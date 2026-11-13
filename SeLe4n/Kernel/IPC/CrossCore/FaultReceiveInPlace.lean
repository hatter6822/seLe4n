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
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace

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
and blocked on a call, and no SchedContext donated. -/
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
   | .blockedOnCall _ => true
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
   | .blockedOnCall _ => true
   | _ => false)

@[csimp] theorem receiveCallTakesInPlace_eq_impl :
    @receiveCallTakesInPlace = @receiveCallTakesInPlaceImpl := by
  funext st endpointId receiver s sTcb rid
  unfold receiveCallTakesInPlace receiveCallTakesInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

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
   | .blockedOnCall _ => true
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
   | .blockedOnCall _ => true
   | _ => false)

@[csimp] theorem receiveCallTakesReplyInPlace_eq_impl :
    @receiveCallTakesReplyInPlace = @receiveCallTakesReplyInPlaceImpl := by
  funext st endpointId receiver s sTcb rid
  unfold receiveCallTakesReplyInPlace receiveCallTakesReplyInPlaceImpl
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
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true) :
    endpointReceiveDualOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid, .ok (s, none)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map TCB.ipcState =
        some (.blockedOnReply endpointId (some receiver)) ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? s).map
          TCB.schedContextBinding = (st.getTcb? s).map TCB.schedContextBinding ∧
      ((receiveCallTakeState st endpointId s sTcb receiver rid).getTcb? receiver).map
          TCB.schedContextBinding = (st.getTcb? receiver).map TCB.schedContextBinding :=
  let ⟨h1, h2, h3, h4, _⟩ := receiveCallTake_inPlace_facts st endpointId ep receiver rid core s
    sTcb hE hH hT (receiveCallTakesReplyInPlace_of_inPlace hG)
  ⟨h1, h2, h3, h4⟩

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
caller left blocked on the reply is owed no completion frame, and staging the
receiver's message writes `performFaultReceiveDelivered`'s state, the fault's
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
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion
          (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
            receiver core) (some s)) receiver 0 =
        performFaultReceiveDelivered st endpointId s sTcb.queueNextCode receiver rid core
          (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.faultKind sTcb.faultFlag
          sTcb.faultWord0 sTcb.faultWord1 sTcb.faultLookup sTcb.faultIp sTcb.faultSp sTcb.faultLr
          sTcb.faultSpsr sTcb.faultX0 sTcb.faultX1 sTcb.faultX2 sTcb.faultX3 sTcb.faultX4
          sTcb.faultX5 sTcb.faultX6 sTcb.faultX7 := by
  obtain ⟨hTake, hIpc, hBs, hBr⟩ :=
    receiveCallTake_inPlace st endpointId ep receiver rid core s sTcb hE hH hT hG
  have hG' := hG
  simp only [receiveCallTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hRT⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, _⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo, hDN⟩ : ∃ rt, st.getTcb? receiver = some rt ∧
      callDonatesNothing sTcb rt = true := by
    split at hRT
    · next rt h => exact ⟨rt, h, hRT⟩
    · cases hRT
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
    rw [Architecture.stageWokenSendCompletion_id_when_not_ready _ s x' hx'
      (by rw [hxI', hxI]; simp)]
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
      (propagatePipChainCrossCore_noResizeDue _ receiver core hNoS)).symm

end SeLe4n.Kernel
