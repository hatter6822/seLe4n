-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core

/-!
# A thread appended to an endpoint queue, in place

WS-ZA ZA4.7.  A blocking receive appends the receiver to the endpoint's receive
queue, a blocking send appends the sender to its send queue; both are
`endpointQueueEnqueue`.  When every write it makes stays in its slot
(`enqueuesInPlace`), the enqueue is three in-place stores
(`storeEndpointEnqueue`): the endpoint's queue ends, the old tail's successor
link, the appended thread's own links (`endpointEnqueue_inPlace_eq`).  The
queue ends and links are written as codes, so no `some` cell is built.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The endpoint an enqueue leaves: `tid` appended to its receive queue
(`isReceiveQ`) or its send queue.  The old tail is passed as its code
(`SeLe4n.ThreadId.optCode`), so no `Option` is built to be read; the queue
ends are codes in the endpoint, rewritten in its cell
(`Endpoint.withReceiveQ_tail`, `Endpoint.withSendQ_tail`). -/
@[inline] def enqueueEndpoint (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (tailCode : Nat) : KernelObject → KernelObject
  | .endpoint e =>
      match isReceiveQ, tailCode with
      | true, 0 => .endpoint { e with recvHeadCode := tid.val + 1, recvTailCode := tid.val + 1 }
      | true, _ + 1 => .endpoint { e with recvTailCode := tid.val + 1 }
      | false, 0 => .endpoint { e with sendHeadCode := tid.val + 1, sendTailCode := tid.val + 1 }
      | false, _ + 1 => .endpoint { e with sendTailCode := tid.val + 1 }
  | o => o

/-- An appended thread's queue links behind `tail?`.  Written as link codes,
so no `some` cell is built to be encoded; the codes are `tcbWithQueueLinks`'s
by definition. -/
@[inline] def enqueueLinks (tail? : Option SeLe4n.ThreadId) (t : TCB) : TCB :=
  match tail? with
  | none => { t with queuePrevCode := 0, queuePPrevCode := 1, queueNextCode := 0 }
  | some p => { t with queuePrevCode := p.val + 1, queuePPrevCode := p.val + 2,
                       queueNextCode := 0 }

/-- A queue tail's successor link pointed at `next`, as a code
(`tcbWithQueueNext_eq`). -/
@[inline] def tcbWithQueueNext (next : SeLe4n.ThreadId) (t : TCB) : TCB :=
  { t with queueNextCode := next.val + 1 }

theorem tcbWithQueueNext_eq (next : SeLe4n.ThreadId) (t : TCB) :
    tcbWithQueueNext next t = tcbWithQueueLinks t t.queuePrev t.queuePPrev (some next) := by
  simp only [tcbWithQueueNext, tcbWithQueueLinks, TCB.optCode_queuePrev, TCB.optCode_queuePPrev]
  rfl

/-- The enqueue's writes, each in its slot: the endpoint's queue, the old
tail's successor link, the appended thread's own links. -/
@[inline] def storeEndpointEnqueue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (tail? : Option SeLe4n.ThreadId) :
    SystemState :=
  let s1 := st.modifyObject endpointId (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?))
  let s2 := match tail? with
    | none => s1
    | some p => s1.updateTcb p (tcbWithQueueNext tid)
  s2.updateTcb tid (enqueueLinks tail?)

/-- **An enqueue writes only its slots**: the endpoint, the appended thread and
the old tail each rewritten where it stands (`RHTable.findsInPlace`), each
store changing only `objects` (`storeLeavesIndexAndTypes`), the thread and the
tail distinct unreserved TCBs. -/
@[inline] def enqueuesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tail? : Option SeLe4n.ThreadId) : Bool :=
  !tid.isReserved &&
  storeLeavesIndexAndTypes st endpointId .endpoint &&
  st.objects.findsInPlace endpointId &&
  storeLeavesIndexAndTypes st tid.toObjId .tcb &&
  st.objects.findsInPlace tid.toObjId &&
  (match tail? with
   | none => true
   | some p => !p.isReserved && p != tid &&
       storeLeavesIndexAndTypes st p.toObjId .tcb &&
       st.objects.findsInPlace p.toObjId &&
       (st.getTcb? p).isSome)

/-- `enqueuesInPlace` asked of the queue's tail **code**, as a compiled guard
reads it: decoded by a match, so no `some` cell is built for it. -/
@[inline] def enqueuesInPlaceCode (st : SystemState) (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tailCode : Nat) : Bool :=
  !tid.isReserved &&
  storeLeavesIndexAndTypes st endpointId .endpoint &&
  st.objects.findsInPlace endpointId &&
  storeLeavesIndexAndTypes st tid.toObjId .tcb &&
  st.objects.findsInPlace tid.toObjId &&
  (match tailCode with
   | 0 => true
   | c + 1 =>
       let p : SeLe4n.ThreadId := ⟨c⟩
       !p.isReserved && p != tid &&
       storeLeavesIndexAndTypes st p.toObjId .tcb &&
       st.objects.findsInPlace p.toObjId &&
       (st.getTcb? p).isSome)

theorem enqueuesInPlaceCode_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tailCode : Nat) :
    enqueuesInPlaceCode st endpointId tid tailCode =
      enqueuesInPlace st endpointId tid (SeLe4n.ThreadId.ofOptCode tailCode) := by
  unfold enqueuesInPlaceCode
  rcases tailCode with _ | c <;> rfl

/-- The thread may be enqueued: it is ready and on no queue
(`endpointQueueEnqueue`'s own checks). -/
@[inline] def enqueueAdmits (t : TCB) : Bool :=
  decide (t.ipcState = .ready) &&
  t.queuePPrevCode == 0 && t.queuePrevCode == 0 && t.queueNextCode == 0

/-- **The guarded enqueue is the specification's**, and leaves the appended
thread resolving, in its slot, to its linked TCB. -/
theorem endpointEnqueue_inPlace_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (rt : TCB)
    (tail? : Option SeLe4n.ThreadId)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = tail?)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hA : enqueueAdmits rt = true)
    (hG : enqueuesInPlace st endpointId tid tail? = true) :
    endpointQueueEnqueue endpointId isReceiveQ tid st =
        .ok (storeEndpointEnqueue st endpointId isReceiveQ tid tail?) ∧
      (storeEndpointEnqueue st endpointId isReceiveQ tid tail?).getTcb? tid =
        some (enqueueLinks tail? rt) ∧
      (storeEndpointEnqueue st endpointId isReceiveQ tid tail?).objects.findsInPlace
        tid.toObjId = true ∧
      storeLeavesIndexAndTypes (storeEndpointEnqueue st endpointId isReceiveQ tid tail?)
        tid.toObjId .tcb = true := by
  simp only [enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hRes, hLE⟩, hFE⟩, hLR⟩, hFR⟩, hTl⟩ := hG
  simp only [enqueueAdmits, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hA
  obtain ⟨⟨⟨hReady, hPP⟩, hPv⟩, hNx⟩ := hA
  have hNeER : endpointId ≠ tid.toObjId := by
    intro h; rw [h, hR] at hE; cases hE
  have hRT : st.getTcb? tid = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hR
  have hLook : lookupTcb st tid = some rt := by
    simp only [lookupTcb, hRes, Bool.false_eq_true, ↓reduceIte]; exact hRT
  have hLinks : (rt.queuePPrev.isSome || rt.queuePrev.isSome || rt.queueNext.isSome) = false := by
    simp only [TCB.queuePPrev, TCB.queuePrev, TCB.queueNext] at *
    rw [hPP, hPv, hNx]; rfl
  have hLE' : ∀ e : Endpoint, storeLeavesIndexAndTypes st endpointId
      (KernelObject.endpoint e).objectType = true := fun _ => by
    simpa only [KernelObject.objectType] using hLE
  obtain ⟨S1, hS1⟩ : ∃ S1 : SystemState, S1 = { st with objects :=
      (st.objects.insert endpointId
        (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?) (.endpoint ep))) } :=
    ⟨_, rfl⟩
  have hMo : st.modifyObject endpointId
      (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?)) = S1 := by
    rw [hS1]; unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hNotV : ∀ r,
      enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?) (.endpoint ep) ≠
      .vspaceRoot r := by
    intro r h; simp only [enqueueEndpoint] at h; split at h <;> cases h
  have hF1 : ∀ k, S1.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [hS1]; exact SeLe4n.Kernel.RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k _ hFE
  have hG1 : ∀ k, endpointId ≠ k → S1.objects[k]? = st.objects[k]? := fun k hk => by
    rw [hS1]; exact SeLe4n.Kernel.RobinHood.RHTable.get?_insert_ne_of_findsInPlace k _ hFE hk
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [hS1]; exact storeLeavesIndexAndTypes_insert_inPlace hFE hNotV h
  have hRT1 : S1.getTcb? tid = some rt :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hG1 _ hNeER).trans hR)
  unfold endpointQueueEnqueue storeEndpointEnqueue
  simp only [SystemState.getObject?, hE, hLook, hReady, ne_eq, not_true_eq_false,
    ↓reduceIte, hLinks, Bool.false_eq_true, hTail]
  rw [hMo]
  cases tail? with
  | none =>
    have hSt : storeObject endpointId (.endpoint (if isReceiveQ then
        ep.withReceiveQ { head := some tid, tail := some tid }
        else ep.withSendQ { head := some tid, tail := some tid })) st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (hLE' _), hS1]
      cases isReceiveQ <;> rfl
    simp only [hSt]
    have hQ : storeTcbQueueLinks S1 tid none (some .endpointHead) none =
        .ok (S1.updateTcb tid (enqueueLinks none)) :=
      modifyTcb_eq_updateTcb _ hRes hRT1 (hL1 hLR)
    refine ⟨hQ, ?_, ?_, ?_⟩
    · exact updateTcb_getTcb?_self_of_findsInPlace _ hRT1 ((hF1 _).trans hFR)
    · rw [updateTcb_findsInPlace _ hRT1 ((hF1 _).trans hFR), hF1]; exact hFR
    · exact updateTcb_storeLeaves _ hRT1 ((hF1 _).trans hFR) (hL1 hLR)
  | some p =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hTl
    obtain ⟨⟨⟨⟨hRp, hNePR⟩, hLP⟩, hFP⟩, hTpB⟩ := hTl
    obtain ⟨pt, hTp⟩ := Option.isSome_iff_exists.mp hTpB
    have hNeEP : endpointId ≠ p.toObjId := by
      intro h; rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTp] at hE; cases hE
    have hNePRo : p.toObjId ≠ tid.toObjId :=
      fun h => hNePR (SeLe4n.ThreadId.toObjId_injective _ _ h)
    have hLookP : lookupTcb st p = some pt := by
      simp only [lookupTcb, hRp, Bool.false_eq_true, ↓reduceIte]; exact hTp
    simp only [hLookP]
    have hSt : storeObject endpointId (.endpoint (if isReceiveQ then
        ep.withReceiveQ ⟨(if isReceiveQ then ep.receiveQ else ep.sendQ).head, some tid⟩
        else ep.withSendQ ⟨(if isReceiveQ then ep.receiveQ else ep.sendQ).head, some tid⟩))
        st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (hLE' _), hS1]
      cases isReceiveQ
      · simp only [Bool.false_eq_true, ↓reduceIte, Endpoint.withSendQ_tail]; rfl
      · simp only [↓reduceIte, Endpoint.withReceiveQ_tail]; rfl
    simp only [hSt]
    have hTp1 : S1.getTcb? p = some pt :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr
        ((hG1 _ hNeEP).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTp))
    let g := tcbWithQueueNext tid
    have hQp : storeTcbQueueLinks S1 p pt.queuePrev pt.queuePPrev (some tid) =
        .ok (S1.updateTcb p g) := by
      have := modifyTcb_eq_updateTcb (fun t => tcbWithQueueLinks t pt.queuePrev pt.queuePPrev
        (some tid)) hRp hTp1 (hL1 hLP)
      rw [show storeTcbQueueLinks S1 p pt.queuePrev pt.queuePPrev (some tid) =
        modifyTcb S1 p (fun t => tcbWithQueueLinks t pt.queuePrev pt.queuePPrev (some tid))
        from rfl, this, SystemState.updateTcb_eq_of_some hTp1,
        SystemState.updateTcb_eq_of_some hTp1]
      simp only [g, tcbWithQueueNext_eq]
    rw [hQp]
    simp only []
    obtain ⟨S2, hS2⟩ : ∃ S2 : SystemState, S2 = S1.updateTcb p g := ⟨_, rfl⟩
    rw [← hS2]
    have hFp1 : S1.objects.findsInPlace p.toObjId = true := (hF1 _).trans hFP
    have hRT2 : S2.getTcb? tid = some rt := by
      rw [hS2, SystemState.getTcb?_eq_some_iff,
        updateTcb_get?_ne_of_findsInPlace g hTp1 hFp1 hNePRo]
      exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hRT1
    have hF2 : ∀ k, S2.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
      rw [hS2, updateTcb_findsInPlace g hTp1 hFp1, hF1]
    have hL2 : storeLeavesIndexAndTypes S2 tid.toObjId .tcb = true := by
      rw [hS2]; exact updateTcb_storeLeaves g hTp1 hFp1 (hL1 hLR)
    have hQ : storeTcbQueueLinks S2 tid (some p) (some (.tcbNext p)) none =
        .ok (S2.updateTcb tid (enqueueLinks (some p))) :=
      modifyTcb_eq_updateTcb _ hRes hRT2 hL2
    refine ⟨hQ, ?_, ?_, ?_⟩
    · exact updateTcb_getTcb?_self_of_findsInPlace _ hRT2 ((hF2 _).trans hFR)
    · rw [updateTcb_findsInPlace _ hRT2 ((hF2 _).trans hFR), hF2]; exact hFR
    · exact updateTcb_storeLeaves _ hRT2 ((hF2 _).trans hFR) hL2

/-- **A guarded enqueue leaves a Reply's slot**: it writes the endpoint, the
appended thread and the old tail, each in place, and none of those keys holds a
Reply. -/
theorem storeEndpointEnqueue_replySlotInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (tail? : Option SeLe4n.ThreadId)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hG : enqueuesInPlace st endpointId tid tail? = true)
    {rk : SeLe4n.ObjId} {r : Reply} (h : replySlotInPlace st rk r) :
    replySlotInPlace (storeEndpointEnqueue st endpointId isReceiveQ tid tail?) rk r := by
  simp only [enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨_, _⟩, hFE⟩, _⟩, hFR⟩, hTl⟩ := hG
  obtain ⟨h1, h2, h3⟩ := h
  have hNeE : endpointId ≠ rk := by intro he; rw [he, h3] at hE; cases hE
  have hNotV : ∀ r',
      enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?) (.endpoint ep) ≠
      .vspaceRoot r' := by
    intro r' h; simp only [enqueueEndpoint] at h; split at h <;> cases h
  have hMo : st.modifyObject endpointId
      (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?)) = { st with objects :=
        (st.objects.insert endpointId
          (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?) (.endpoint ep))) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hF1 : ∀ k, (st.modifyObject endpointId
      (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?))).objects.findsInPlace k =
        st.objects.findsInPlace k := fun k => by
    rw [hMo]; exact SeLe4n.Kernel.RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k _ hFE
  have hS1 : replySlotInPlace (st.modifyObject endpointId
      (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?))) rk r := by
    refine ⟨(hF1 rk).trans h1, ?_, ?_⟩
    · rw [hMo]; exact storeLeavesIndexAndTypes_insert_inPlace hFE hNotV h2
    · rw [hMo]
      exact (SeLe4n.Kernel.RobinHood.RHTable.get?_insert_ne_of_findsInPlace rk _ hFE hNeE).trans h3
  unfold storeEndpointEnqueue
  cases tail? with
  | none =>
    exact updateTcb_replySlotInPlace _ ((hF1 _).trans hFR) hS1
  | some p =>
    simp only [Bool.and_eq_true] at hTl
    obtain ⟨⟨_, hFP⟩, _⟩ := hTl
    simp only []
    exact updateTcb_replySlotInPlace _
      ((updateTcb_findsInPlace_of_key _ ((hF1 _).trans hFP) _).trans ((hF1 _).trans hFR))
      (updateTcb_replySlotInPlace _ ((hF1 _).trans hFP) hS1)

end SeLe4n.Kernel
