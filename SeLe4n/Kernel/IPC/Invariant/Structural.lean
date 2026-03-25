/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation

-- R3-E/L-08: Linter directives. The global `set_option linter.all false` has been
-- removed. Specific linters are disabled only where structurally necessary.
set_option linter.unusedVariables false

namespace SeLe4n.Kernel

open SeLe4n.Model


-- ============================================================================
-- WS-H5: Intrusive dual-queue structural invariant preservation proofs
-- C-04/A-22: Well-formedness predicates and preservation for all dual-queue ops.
-- A-23: Link dereference safety under well-formedness.
-- A-24: TCB existence after popHead.
-- ============================================================================

-- ---- Base cases ----

/-- WS-H5: Empty intrusive queue is trivially well-formed. -/
theorem intrusiveQueueWellFormed_empty (st : SystemState) :
    intrusiveQueueWellFormed {} st := by
  refine ⟨Iff.rfl, ?_, ?_⟩ <;> (intro _ h; cases h)

/-- WS-H5: tcbQueueLinkIntegrity for a state where no TCB has queue links. -/
theorem tcbQueueLinkIntegrity_initial (st : SystemState)
    (hNoLinks : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.queueNext = none ∧ tcb.queuePrev = none) :
    tcbQueueLinkIntegrity st := by
  constructor
  · intro a tA hA b hN; have := (hNoLinks a tA hA).1; rw [this] at hN; cases hN
  · intro b tB hB a hP; have := (hNoLinks b tB hB).2; rw [this] at hP; cases hP

/-- WS-H5: Empty endpoint has well-formed dual queues. -/
theorem dualQueueEndpointWellFormed_empty_endpoint
    (epId : SeLe4n.ObjId) (st : SystemState) (ep : Endpoint)
    (hObj : st.objects[epId]? = some (.endpoint ep))
    (hSendEmpty : ep.sendQ = {}) (hRecvEmpty : ep.receiveQ = {}) :
    dualQueueEndpointWellFormed epId st := by
  simp only [dualQueueEndpointWellFormed, hObj, hSendEmpty, hRecvEmpty]
  exact ⟨intrusiveQueueWellFormed_empty st, intrusiveQueueWellFormed_empty st⟩

/-- WS-H5: Non-endpoint objects trivially satisfy dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_non_endpoint
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hNoEp : ∀ ep, st.objects[epId]? ≠ some (.endpoint ep)) :
    dualQueueEndpointWellFormed epId st := by
  unfold dualQueueEndpointWellFormed
  cases hObj : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | endpoint ep => exact absurd hObj (hNoEp ep)
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial

-- ---- A-23 / A-24 closure ----

/-- WS-H5/A-23: Under tcbQueueLinkIntegrity, any TCB's queueNext link is safe
to dereference — it points to a valid TCB with consistent back-pointer. -/
theorem tcbQueueLink_forward_safe (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (a : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA))
    (b : SeLe4n.ThreadId) (hNext : tcbA.queueNext = some b) :
    ∃ tcbB, st.objects[b.toObjId]? = some (.tcb tcbB) ∧ tcbB.queuePrev = some a :=
  hInteg.1 a tcbA hA b hNext

/-- WS-H5/A-23: Under tcbQueueLinkIntegrity, any TCB's queuePrev link
is safe to dereference (symmetric direction). -/
theorem tcbQueueLink_reverse_safe (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (b : SeLe4n.ThreadId) (tcbB : TCB)
    (hB : st.objects[b.toObjId]? = some (.tcb tcbB))
    (a : SeLe4n.ThreadId) (hPrev : tcbB.queuePrev = some a) :
    ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b :=
  hInteg.2 b tcbB hB a hPrev

/-- WS-H5/A-24: Under intrusiveQueueWellFormed, the head of a non-empty queue
always has a valid TCB. Closes finding A-24. -/
theorem endpointQueuePopHead_sender_exists (q : IntrusiveQueue) (st : SystemState)
    (hWf : intrusiveQueueWellFormed q st)
    (hd : SeLe4n.ThreadId) (hHd : q.head = some hd) :
    ∃ tcb, st.objects[hd.toObjId]? = some (.tcb tcb) := by
  obtain ⟨_, hHead, _⟩ := hWf
  obtain ⟨tcb, hTcb, _⟩ := hHead hd hHd
  exact ⟨tcb, hTcb⟩

/-- WS-H5/A-24: Under dualQueueEndpointWellFormed, the sender popped from
sendQ is guaranteed to have a valid TCB. -/
theorem endpointReceiveDual_sender_exists
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hWf : dualQueueEndpointWellFormed epId st)
    (ep : Endpoint) (hObj : st.objects[epId]? = some (.endpoint ep))
    (hd : SeLe4n.ThreadId) (hHd : ep.sendQ.head = some hd) :
    ∃ tcb, st.objects[hd.toObjId]? = some (.tcb tcb) := by
  unfold dualQueueEndpointWellFormed at hWf; rw [hObj] at hWf
  exact endpointQueuePopHead_sender_exists ep.sendQ st hWf.1 hd hHd

/-- WS-H5/A-23: Under dualQueueSystemInvariant, popHead link dereference
is safe — the head TCB's queueNext either is none or points to a valid TCB. -/
theorem endpointQueuePopHead_link_safe (q : IntrusiveQueue) (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (_hWf : intrusiveQueueWellFormed q st)
    (hd : SeLe4n.ThreadId) (_hHd : q.head = some hd)
    (tcb : TCB) (hTcb : st.objects[hd.toObjId]? = some (.tcb tcb)) :
    match tcb.queueNext with
    | none => True
    | some next => ∃ nextTcb, st.objects[next.toObjId]? = some (.tcb nextTcb) := by
  cases hNext : tcb.queueNext with
  | none => trivial
  | some next => exact let ⟨t, h, _⟩ := hInteg.1 hd tcb hTcb next hNext; ⟨t, h⟩

-- ---- Helper: QueueNextPath transport across object equality ----

/-- If two states have the same objects, QueueNextPath transfers between them. -/
private theorem QueueNextPath_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath st' a b) : QueueNextPath st a b := by
  induction hp with
  | single x y tcbA hObj hNext =>
    exact .single x y tcbA (by rw [← hObjs]; exact hObj) hNext
  | cons x y z tcbA hObj hNext _ ih =>
    exact .cons x y z tcbA (by rw [← hObjs]; exact hObj) hNext ih

/-- If objects are unchanged, tcbQueueChainAcyclic transfers to the new state. -/
private theorem tcbQueueChainAcyclic_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (hAcyclic : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' :=
  fun tid hp => hAcyclic tid (QueueNextPath_of_objects_eq hObjs hp)

/-- Transport QueueNextPath from post-state to pre-state when storeObject replaces
a TCB at tid with a new TCB that has the same queueNext. -/
private theorem QueueNextPath_transport_storeObject_tcb
    {st st' : SystemState} {tid : SeLe4n.ObjId} {tcb tcb' : TCB}
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath st' a b) : QueueNextPath st a b := by
  induction hp with
  | single x y tcbX hObj hNext =>
    by_cases hx : x.toObjId = tid
    · rw [hx, storeObject_objects_eq st st' tid _ hObjInv hStore] at hObj
      cases hObj; rw [hNextEq] at hNext
      exact .single x y tcb (hx ▸ hTcbPre) hNext
    · exact .single x y tcbX (by rwa [storeObject_objects_ne st st' tid x.toObjId _ hx hObjInv hStore] at hObj) hNext
  | cons x y z tcbX hObj hNext _ ih =>
    by_cases hx : x.toObjId = tid
    · rw [hx, storeObject_objects_eq st st' tid _ hObjInv hStore] at hObj
      cases hObj; rw [hNextEq] at hNext
      exact .cons x y z tcb (hx ▸ hTcbPre) hNext ih
    · exact .cons x y z tcbX (by rwa [storeObject_objects_ne st st' tid x.toObjId _ hx hObjInv hStore] at hObj) hNext ih

/-- storeObject of a TCB with preserved queueNext preserves tcbQueueChainAcyclic. -/
private theorem storeObject_tcb_preserves_tcbQueueChainAcyclic
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (hAcyclic : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' :=
  fun tid' hp => hAcyclic tid' (QueueNextPath_transport_storeObject_tcb hNextEq hTcbPre hObjInv hStore hp)

/-- Transport QueueNextPath from post-state to pre-state when storeObject replaces
a non-TCB object. No TCB is modified, so all edges are preserved. -/
private theorem QueueNextPath_transport_storeObject_nonTcb
    {st st' : SystemState} {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hNotTcb : ∀ tcb : TCB, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath st' a b) : QueueNextPath st a b := by
  induction hp with
  | single x y tcbA hObj hNext =>
    have hx : x.toObjId ≠ oid := by
      intro h; rw [h, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj; exact hNotTcb tcbA rfl
    exact .single x y tcbA (by rwa [storeObject_objects_ne st st' oid x.toObjId _ hx hObjInv hStore] at hObj) hNext
  | cons x y z tcbA hObj hNext _ ih =>
    have hx : x.toObjId ≠ oid := by
      intro h; rw [h, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj; exact hNotTcb tcbA rfl
    exact .cons x y z tcbA (by rwa [storeObject_objects_ne st st' oid x.toObjId _ hx hObjInv hStore] at hObj) hNext ih

/-- storeObject of a non-TCB object preserves tcbQueueChainAcyclic. -/
private theorem storeObject_nonTcb_preserves_tcbQueueChainAcyclic
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNotTcb : ∀ tcb : TCB, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hAcyclic : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' :=
  fun tid hp => hAcyclic tid (QueueNextPath_transport_storeObject_nonTcb hNotTcb hObjInv hStore hp)

-- ---- Frame lemmas: ensureRunnable / removeRunnable ----

/-- WS-H5: ensureRunnable preserves intrusiveQueueWellFormed. -/
private theorem ensureRunnable_preserves_intrusiveQueueWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q (ensureRunnable st tid) := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  exact ⟨hHT,
    fun hd h => let ⟨t, ht, hp⟩ := hHead hd h; ⟨t, by rwa [ensureRunnable_preserves_objects], hp⟩,
    fun tl h => let ⟨t, ht, hn⟩ := hTail tl h; ⟨t, by rwa [ensureRunnable_preserves_objects], hn⟩⟩

/-- WS-H5: removeRunnable preserves intrusiveQueueWellFormed. -/
private theorem removeRunnable_preserves_intrusiveQueueWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q (removeRunnable st tid) := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  exact ⟨hHT,
    fun hd h => let ⟨t, ht, hp⟩ := hHead hd h; ⟨t, by rwa [removeRunnable_preserves_objects], hp⟩,
    fun tl h => let ⟨t, ht, hn⟩ := hTail tl h; ⟨t, by rwa [removeRunnable_preserves_objects], hn⟩⟩

/-- WS-H5: ensureRunnable preserves tcbQueueLinkIntegrity. -/
private theorem ensureRunnable_preserves_tcbQueueLinkIntegrity
    (st : SystemState) (tid : SeLe4n.ThreadId) (h : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity (ensureRunnable st tid) := by
  constructor
  · intro a tA hA b hN; rw [ensureRunnable_preserves_objects] at hA
    obtain ⟨tB, hB, hP⟩ := h.1 a tA hA b hN
    exact ⟨tB, by rw [ensureRunnable_preserves_objects]; exact hB, hP⟩
  · intro b tB hB a hP; rw [ensureRunnable_preserves_objects] at hB
    obtain ⟨tA, hA, hN⟩ := h.2 b tB hB a hP
    exact ⟨tA, by rw [ensureRunnable_preserves_objects]; exact hA, hN⟩

/-- WS-H5: removeRunnable preserves tcbQueueLinkIntegrity. -/
private theorem removeRunnable_preserves_tcbQueueLinkIntegrity
    (st : SystemState) (tid : SeLe4n.ThreadId) (h : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity (removeRunnable st tid) := by
  constructor
  · intro a tA hA b hN; rw [removeRunnable_preserves_objects] at hA
    obtain ⟨tB, hB, hP⟩ := h.1 a tA hA b hN
    exact ⟨tB, by rw [removeRunnable_preserves_objects]; exact hB, hP⟩
  · intro b tB hB a hP; rw [removeRunnable_preserves_objects] at hB
    obtain ⟨tA, hA, hN⟩ := h.2 b tB hB a hP
    exact ⟨tA, by rw [removeRunnable_preserves_objects]; exact hA, hN⟩

/-- WS-H5: ensureRunnable preserves dualQueueEndpointWellFormed. -/
private theorem ensureRunnable_preserves_dualQueueEndpointWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hWf : dualQueueEndpointWellFormed epId st) :
    dualQueueEndpointWellFormed epId (ensureRunnable st tid) := by
  unfold dualQueueEndpointWellFormed at hWf ⊢; rw [ensureRunnable_preserves_objects]
  cases hObjCase : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial
    | endpoint ep =>
        simp only [hObjCase] at hWf
        exact ⟨ensureRunnable_preserves_intrusiveQueueWellFormed st tid ep.sendQ hWf.1,
               ensureRunnable_preserves_intrusiveQueueWellFormed st tid ep.receiveQ hWf.2⟩

/-- WS-H5: removeRunnable preserves dualQueueEndpointWellFormed. -/
private theorem removeRunnable_preserves_dualQueueEndpointWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hWf : dualQueueEndpointWellFormed epId st) :
    dualQueueEndpointWellFormed epId (removeRunnable st tid) := by
  unfold dualQueueEndpointWellFormed at hWf ⊢; rw [removeRunnable_preserves_objects]
  cases hObjCase : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial
    | endpoint ep =>
        simp only [hObjCase] at hWf
        exact ⟨removeRunnable_preserves_intrusiveQueueWellFormed st tid ep.sendQ hWf.1,
               removeRunnable_preserves_intrusiveQueueWellFormed st tid ep.receiveQ hWf.2⟩

/-- WS-H5: ensureRunnable preserves dualQueueSystemInvariant. -/
private theorem ensureRunnable_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (ensureRunnable st tid) := by
  obtain ⟨hEp, hLink, hAcyclic⟩ := hInv
  refine ⟨?_, ensureRunnable_preserves_tcbQueueLinkIntegrity st tid hLink,
    tcbQueueChainAcyclic_of_objects_eq (ensureRunnable_preserves_objects st tid) hAcyclic⟩
  intro epId ep hObj; rw [ensureRunnable_preserves_objects] at hObj
  exact ensureRunnable_preserves_dualQueueEndpointWellFormed st tid epId (hEp epId ep hObj)

/-- WS-H5: removeRunnable preserves dualQueueSystemInvariant. -/
private theorem removeRunnable_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (removeRunnable st tid) := by
  obtain ⟨hEp, hLink, hAcyclic⟩ := hInv
  refine ⟨?_, removeRunnable_preserves_tcbQueueLinkIntegrity st tid hLink,
    tcbQueueChainAcyclic_of_objects_eq (removeRunnable_preserves_objects st tid) hAcyclic⟩
  intro epId ep hObj; rw [removeRunnable_preserves_objects] at hObj
  exact removeRunnable_preserves_dualQueueEndpointWellFormed st tid epId (hEp epId ep hObj)

-- ---- Frame lemma: storeObject for TCB preserves queue well-formedness ----
-- storeTcbIpcState / storeTcbIpcStateAndMessage / storeTcbPendingMessage all
-- call storeObject with { tcb with ipcState := ..., pendingMessage := ... },
-- preserving queueNext / queuePrev / queuePPrev.

/-- WS-H5: storeObject of a TCB-variant with preserved queue links maintains
intrusiveQueueWellFormed for queues whose boundary TCBs either:
(a) are at different ObjIds (unchanged), or
(b) are the modified TCB (queue links preserved by with-syntax). -/
private theorem storeObject_tcb_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hPrevEq : tcb'.queuePrev = tcb.queuePrev)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hObjInv hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid hd.toObjId _ hEq hObjInv hStore]; exact hT, hP⟩
  · intro tl hTl
    obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hObjInv hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hNextEq ▸ hN⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid tl.toObjId _ hEq hObjInv hStore]; exact hT, hN⟩

/-- WS-H5: storeObject of a TCB-variant with preserved queue links maintains
tcbQueueLinkIntegrity. -/
private theorem storeObject_tcb_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hPrevEq : tcb'.queuePrev = tcb.queuePrev)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid
    · rw [hEqA, storeObject_objects_eq st st' tid _ hObjInv hStore] at hA; cases hA
      -- tA = tcb', tA.queueNext = tcb'.queueNext = tcb.queueNext
      rw [hNextEq] at hN
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tcb (hEqA ▸ hTcbPre) b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hObjInv hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hObjInv hStore]; exact hB, hP⟩
    · rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hObjInv hStore] at hA
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hObjInv hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hObjInv hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid
    · rw [hEqB, storeObject_objects_eq st st' tid _ hObjInv hStore] at hB; cases hB
      rw [hPrevEq] at hP
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tcb (hEqB ▸ hTcbPre) a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hObjInv hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hObjInv hStore]; exact hA, hN⟩
    · rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hObjInv hStore] at hB
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hObjInv hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hObjInv hStore]; exact hA, hN⟩

-- ---- Helper: storeObject endpoint preserves queue invariant properties ----

/-- WS-H5: Storing an endpoint preserves tcbQueueLinkIntegrity (no TCB is modified). -/
private theorem storeObject_endpoint_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    have hA' := tcb_lookup_of_endpoint_store st st' epId a.toObjId tA epNew hObjInv hStore hA
    obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA' b hN
    have : b.toObjId ≠ epId := fun h => absurd (h ▸ hB) (hPreEp tB)
    exact ⟨tB, by rw [storeObject_objects_ne st st' epId b.toObjId _ this hObjInv hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    have hB' := tcb_lookup_of_endpoint_store st st' epId b.toObjId tB epNew hObjInv hStore hB
    obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB' a hP
    have : a.toObjId ≠ epId := fun h => absurd (h ▸ hA) (hPreEp tA)
    exact ⟨tA, by rw [storeObject_objects_ne st st' epId a.toObjId _ this hObjInv hStore]; exact hA, hN⟩

/-- WS-H5: Storing an endpoint preserves intrusiveQueueWellFormed.
Boundary TCBs can't be at the endpoint ObjId (they are TCBs, not endpoints). -/
private theorem storeObject_endpoint_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    have : hd.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId hd.toObjId _ this hObjInv hStore]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    have : tl.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId tl.toObjId _ this hObjInv hStore]; exact hT, hN⟩

-- ---- R3-B: storeObject notification preserves dualQueueSystemInvariant ----
-- Notification stores never modify TCBs or endpoints, so dual-queue structural
-- invariants are trivially preserved.

/-- R3-B: Storing a notification preserves tcbQueueLinkIntegrity (no TCB is modified). -/
private theorem storeObject_notification_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn' : Notification)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn') st = .ok ((), st'))
    (hPreNtfn : ∀ tcb : TCB, st.objects[nid]? ≠ some (.tcb tcb))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    by_cases hNeA : a.toObjId = nid
    · subst hNeA; rw [storeObject_objects_eq st st' a.toObjId _ hObjInv hStore] at hA; cases hA
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rw [storeObject_objects_ne st st' nid a.toObjId _ hNeA hObjInv hStore] at hA; exact hA
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA' b hN
      have : b.toObjId ≠ nid := fun h => absurd (h ▸ hB) (hPreNtfn tB)
      exact ⟨tB, by rw [storeObject_objects_ne st st' nid b.toObjId _ this hObjInv hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hNeB : b.toObjId = nid
    · subst hNeB; rw [storeObject_objects_eq st st' b.toObjId _ hObjInv hStore] at hB; cases hB
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rw [storeObject_objects_ne st st' nid b.toObjId _ hNeB hObjInv hStore] at hB; exact hB
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB' a hP
      have : a.toObjId ≠ nid := fun h => absurd (h ▸ hA) (hPreNtfn tA)
      exact ⟨tA, by rw [storeObject_objects_ne st st' nid a.toObjId _ this hObjInv hStore]; exact hA, hN⟩

/-- R3-B: Storing a notification preserves intrusiveQueueWellFormed. -/
private theorem storeObject_notification_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn' : Notification)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn') st = .ok ((), st'))
    (hPreNtfn : ∀ tcb : TCB, st.objects[nid]? ≠ some (.tcb tcb))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    have : hd.toObjId ≠ nid := fun h => absurd (h ▸ hT) (hPreNtfn t)
    exact ⟨t, by rw [storeObject_objects_ne st st' nid hd.toObjId _ this hObjInv hStore]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    have : tl.toObjId ≠ nid := fun h => absurd (h ▸ hT) (hPreNtfn t)
    exact ⟨t, by rw [storeObject_objects_ne st st' nid tl.toObjId _ this hObjInv hStore]; exact hT, hN⟩

/-- R3-B: Storing a notification preserves dualQueueSystemInvariant.
The notification store does not modify endpoint objects or TCB queue links. -/
theorem storeObject_notification_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn' : Notification)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn') st = .ok ((), st'))
    (hPreNtfn : (∃ n, st.objects[nid]? = some (.notification n)) ∨
                st.objects[nid]? = none)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  have hNotTcb : ∀ tcb : TCB, st.objects[nid]? ≠ some (.tcb tcb) := by
    intro tcb h; rcases hPreNtfn with ⟨n, hSome⟩ | hNone
    · rw [hSome] at h; cases h
    · rw [hNone] at h; cases h
  refine ⟨?_, storeObject_notification_preserves_tcbQueueLinkIntegrity
      st st' nid ntfn' hObjInv hStore hNotTcb hLink, ?_⟩
  · intro epId ep hEpPost
    by_cases hEq : epId = nid
    · subst hEq; rw [storeObject_objects_eq st st' epId _ hObjInv hStore] at hEpPost; cases hEpPost
    · have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
        rw [storeObject_objects_ne st st' nid epId _ hEq hObjInv hStore] at hEpPost; exact hEpPost
      have hWf := hEpInv epId ep hEpPre
      unfold dualQueueEndpointWellFormed at hWf ⊢
      rw [hEpPre] at hWf; rw [hEpPost]; simp at hWf ⊢
      exact ⟨storeObject_notification_preserves_intrusiveQueueWellFormed
               st st' nid ntfn' hObjInv hStore hNotTcb _ hWf.1,
             storeObject_notification_preserves_intrusiveQueueWellFormed
               st st' nid ntfn' hObjInv hStore hNotTcb _ hWf.2⟩
  · exact storeObject_nonTcb_preserves_tcbQueueChainAcyclic
      st st' nid (.notification ntfn') (fun _ h => by cases h) hObjInv hStore hAcyclic

-- ---- Derived frame lemmas for storeTcbIpcState, storeTcbIpcStateAndMessage, storeTcbPendingMessage ----

/-- WS-H5: storeTcbIpcState preserves dualQueueSystemInvariant.
storeTcbIpcState uses { tcb with ipcState := ipc }, preserving queue links. -/
private theorem storeTcbIpcState_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup
            split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with ipcState := ipc } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with ipcState := ipc } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb { tcb with ipcState := ipc } hPrev hNext hTcbPre hObjInv hStore hLink,
                 storeObject_tcb_preserves_tcbQueueChainAcyclic st pair.2
                       tid.toObjId tcb { tcb with ipcState := ipc } hNext hTcbPre hObjInv hStore hAcyclic⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hObjInv hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbIpcStateAndMessage preserves dualQueueSystemInvariant. -/
private theorem storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup; split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with ipcState := ipc, pendingMessage := msg } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with ipcState := ipc, pendingMessage := msg } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore hLink,
                 storeObject_tcb_preserves_tcbQueueChainAcyclic st pair.2
                       tid.toObjId tcb _ hNext hTcbPre hObjInv hStore hAcyclic⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hObjInv hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbPendingMessage preserves dualQueueSystemInvariant. -/
private theorem storeTcbPendingMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup; split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with pendingMessage := msg } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with pendingMessage := msg } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore hLink,
                 storeObject_tcb_preserves_tcbQueueChainAcyclic st pair.2
                       tid.toObjId tcb _ hNext hTcbPre hObjInv hStore hAcyclic⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hObjInv hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hObjInv hStore ep.receiveQ hWfPre.2⟩

-- ============================================================================
-- WS-H5 Part C: Preservation for the 7 dual-queue operations.
-- Strategy: endpointReply / endpointReplyRecv don't modify intrusive queues.
-- endpointSendDual / endpointReceiveDual / endpointCall compose
-- endpointQueueEnqueue/PopHead with state transition frame lemmas.
-- ============================================================================

/-- WS-H5: endpointReply preserves dualQueueSystemInvariant.
endpointReply performs storeTcbIpcStateAndMessage + ensureRunnable —
neither touches queue links or endpoint queue boundaries. -/
theorem endpointReply_preserves_dualQueueSystemInvariant
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointReply replier target msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId' rt =>
          simp only [hIpc] at hStep
          -- Resolve the let/if authorization + storeTcbIpcStateAndMessage
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e =>
              -- Regardless of authorization, store failed → error ≠ ok
              revert hStep; simp only [hStore]; intro hStep
              cases rt with
              | none => simp at hStep
              | some val => dsimp only [] at hStep; split at hStep <;> simp at hStep
          | ok st1 =>
              simp only [hStore] at hStep
              have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st st1 target .ready (some msg) hObjInv hStore hInv
              have hInvER := ensureRunnable_preserves_dualQueueSystemInvariant st1 target hInv1
              -- Case split on authorization to extract st' = ensureRunnable st1 target
              cases rt with
              | none => simp at hStep; subst hStep; exact hInvER
              | some val =>
                  dsimp only [] at hStep
                  split at hStep
                  · simp at hStep; subst hStep; exact hInvER
                  · simp at hStep

-- ---- WS-H5: storeTcbQueueLinks helper lemmas for queue invariant proofs ----

/-- Helper: storeTcbQueueLinks stores a specific TCB at tid.toObjId. -/
private theorem storeTcbQueueLinks_result_tcb
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ∃ origTcb, lookupTcb st tid = some origTcb ∧
    st'.objects[tid.toObjId]? = some (.tcb (tcbWithQueueLinks origTcb prev pprev next)) := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
      exact ⟨tcb, rfl, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore⟩

/-- Helper: storeTcbQueueLinks preserves intrusiveQueueWellFormed when
the new link values are compatible with the queue's head/tail boundaries.
Clearing (all none) is always compatible. -/
private theorem storeTcbQueueLinks_preserves_iqwf
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st)
    (hHeadOk : ∀ hd, q.head = some hd → hd.toObjId = tid.toObjId → prev = none)
    (hTailOk : ∀ tl, q.tail = some tl → tl.toObjId = tid.toObjId → next = none) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  obtain ⟨origTcb, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid prev pprev next hObjInv hStep
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hHeadOk hd hHd hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        hd.toObjId hEq hObjInv hStep]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hTailOk tl hTl hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        tl.toObjId hEq hObjInv hStep]; exact hT, hN⟩

/-- Helper: Clearing all queue links preserves tcbQueueLinkIntegrity when
no other TCB's forward/reverse links point to the cleared thread. -/
private theorem storeTcbQueueLinks_clearing_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid none none none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none none none hObjInv hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none a.toObjId hEqA hObjInv hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        b.toObjId hNeB hObjInv hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none b.toObjId hEqB hObjInv hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        a.toObjId hNeA hObjInv hStep]; exact hA, hN⟩

/-- Helper: storeTcbQueueLinks with prev=none and next=none (arbitrary pprev)
preserves tcbQueueLinkIntegrity when no external refs point to the modified thread.
This generalizes storeTcbQueueLinks_clearing_preserves_linkInteg to allow non-none pprev,
since tcbQueueLinkIntegrity only inspects queuePrev and queueNext. -/
private theorem storeTcbQueueLinks_noprevnext_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid none pprev none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none pprev none hObjInv hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none a.toObjId hEqA hObjInv hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        b.toObjId hNeB hObjInv hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none b.toObjId hEqB hObjInv hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        a.toObjId hNeA hObjInv hStep]; exact hA, hN⟩

/-- Helper: Two-step storeTcbQueueLinks append-to-tail preserves tcbQueueLinkIntegrity.
Step 1 sets old tail's next to newTid. Step 2 sets newTid's prev to tailTid.
The resulting forward link (tailTid→newTid) is matched by the reverse (newTid→tailTid). -/
private theorem storeTcbQueueLinks_append_tail_preserves_linkInteg
    (st1 st2 stF : SystemState) (tailTid newTid : SeLe4n.ThreadId)
    (prevT : Option SeLe4n.ThreadId) (pprevT pprevN : Option QueuePPrev)
    (hObjInv : st1.objects.invExt)
    (hStep1 : storeTcbQueueLinks st1 tailTid prevT pprevT (some newTid) = .ok st2)
    (hStep2 : storeTcbQueueLinks st2 newTid (some tailTid) pprevN none = .ok stF)
    (hNe : tailTid.toObjId ≠ newTid.toObjId)
    (hLink : tcbQueueLinkIntegrity st1)
    (hPrevMatch : ∀ t, st1.objects[tailTid.toObjId]? = some (.tcb t) → prevT = t.queuePrev)
    (hTailNext : ∀ t, st1.objects[tailTid.toObjId]? = some (.tcb t) → t.queueNext = none)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tA : TCB), st1.objects[a.toObjId]? = some (.tcb tA) →
      tA.queueNext ≠ some newTid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tB : TCB), st1.objects[b.toObjId]? = some (.tcb tB) →
      tB.queuePrev ≠ some newTid) :
    tcbQueueLinkIntegrity stF := by
  -- Extract TCB results from both steps
  obtain ⟨origTail, hLookupTail, hTailSt2⟩ := storeTcbQueueLinks_result_tcb
    st1 st2 tailTid prevT pprevT (some newTid) hObjInv hStep1
  have hObjInv2 : st2.objects.invExt :=
    storeTcbQueueLinks_preserves_objects_invExt st1 st2 tailTid prevT pprevT (some newTid) hObjInv hStep1
  obtain ⟨origNew, hLookupNew2, hNewStF⟩ := storeTcbQueueLinks_result_tcb
    st2 stF newTid (some tailTid) pprevN none hObjInv2 hStep2
  -- tailTid's TCB in stF is preserved from st2 (step 2 only modifies newTid)
  have hTailStF : stF.objects[tailTid.toObjId]? =
      some (.tcb (tcbWithQueueLinks origTail prevT pprevT (some newTid))) := by
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      tailTid.toObjId hNe hObjInv2 hStep2]
    exact hTailSt2
  -- Original tail TCB
  have hTailOrig := lookupTcb_some_objects st1 tailTid origTail hLookupTail
  -- prevT matches original prev
  have hPM := hPrevMatch origTail hTailOrig
  -- Original tail had next=none
  have hTN := hTailNext origTail hTailOrig
  -- Transport: for oid ≠ tailTid and oid ≠ newTid, objects unchanged
  have hOther : ∀ oid, oid ≠ tailTid.toObjId → oid ≠ newTid.toObjId →
      stF.objects[oid]? = st1.objects[oid]? := by
    intro oid hne1 hne2
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      oid hne2 hObjInv2 hStep2]
    rw [storeTcbQueueLinks_preserves_objects_ne st1 st2 tailTid prevT pprevT (some newTid)
      oid hne1 hObjInv hStep1]
  constructor
  -- Forward direction: a.next = some b → b.prev = some a
  · intro a tA hA b hN
    by_cases haT : a.toObjId = tailTid.toObjId
    · -- a is tailTid: tA has next = some newTid (from tcbWithQueueLinks)
      rw [haT] at hA; rw [hTailStF] at hA; cases hA
      simp only [tcbWithQueueLinks] at hN
      -- hN : some newTid = some b, so newTid = b
      simp only [Option.some.injEq] at hN
      rw [← hN, threadId_toObjId_injective haT]
      exact ⟨tcbWithQueueLinks origNew (some tailTid) pprevN none, hNewStF,
        by simp [tcbWithQueueLinks]⟩
    · by_cases haN : a.toObjId = newTid.toObjId
      · -- a is newTid: tA has next = none (from tcbWithQueueLinks)
        rw [haN] at hA; rw [hNewStF] at hA; cases hA
        simp [tcbWithQueueLinks] at hN
      · -- a is neither: tA unchanged from st1
        have hA1 : st1.objects[a.toObjId]? = some (.tcb tA) := by
          rwa [hOther a.toObjId haT haN] at hA
        obtain ⟨tB, hB1, hP⟩ := hLink.1 a tA hA1 b hN
        -- b ≠ newTid (since no TCB in st1 has next=newTid)
        have hbNeN : b.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA1)
        by_cases hbT : b.toObjId = tailTid.toObjId
        · -- b is tailTid: in stF, tailTid has prev = prevT = origTail.queuePrev
          rw [hbT] at hB1; rw [hTailOrig] at hB1; cases hB1
          -- hP : origTail.queuePrev = some a
          have hbEq := threadId_toObjId_injective hbT; rw [hbEq] at ⊢
          exact ⟨tcbWithQueueLinks origTail prevT pprevT (some newTid), hTailStF,
            by simp [tcbWithQueueLinks]; exact hPM ▸ hP⟩
        · exact ⟨tB, by rw [hOther b.toObjId hbT hbNeN]; exact hB1, hP⟩
  -- Reverse direction: b.prev = some a → a.next = some b
  · intro b tB hB a hP
    by_cases hbN : b.toObjId = newTid.toObjId
    · -- b is newTid: tB has prev = some tailTid
      rw [hbN] at hB; rw [hNewStF] at hB; cases hB
      simp only [tcbWithQueueLinks, Option.some.injEq] at hP
      -- hP : tailTid = a
      rw [← hP]
      refine ⟨tcbWithQueueLinks origTail prevT pprevT (some newTid), hTailStF, ?_⟩
      simp [tcbWithQueueLinks]
      exact (threadId_toObjId_injective hbN).symm
    · by_cases hbT : b.toObjId = tailTid.toObjId
      · -- b is tailTid: prev = prevT = origTail.queuePrev
        rw [hbT] at hB; rw [hTailStF] at hB; cases hB
        simp only [tcbWithQueueLinks] at hP
        rw [hPM] at hP
        obtain ⟨tA, hA1, hNxt⟩ := hLink.2 tailTid origTail hTailOrig a hP
        have haNeT : a.toObjId ≠ tailTid.toObjId := by
          intro hh; rw [hh] at hA1; rw [hTailOrig] at hA1; cases hA1
          rw [hTN] at hNxt; simp at hNxt
        have haNeN : a.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev tailTid origTail hTailOrig)
        refine ⟨tA, by rw [hOther a.toObjId haNeT haNeN]; exact hA1, ?_⟩
        rw [threadId_toObjId_injective hbT]; exact hNxt
      · -- b is neither: tB unchanged from st1
        have hB1 : st1.objects[b.toObjId]? = some (.tcb tB) := by
          rwa [hOther b.toObjId hbT hbN] at hB
        -- a ≠ newTid (no TCB in st1 has prev=newTid)
        have haNeN : a.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB1)
        obtain ⟨tA, hA1, hNxt⟩ := hLink.2 b tB hB1 a hP
        by_cases haT : a.toObjId = tailTid.toObjId
        · -- a = tailTid: but origTail.queueNext = none contradicts hNxt
          rw [haT] at hA1; rw [hTailOrig] at hA1; cases hA1
          exact absurd hNxt (by rw [hTN]; simp)
        · exact ⟨tA, by rw [hOther a.toObjId haT haNeN]; exact hA1, hNxt⟩

-- ---- WS-H5: storeTcbQueueLinks acyclicity helpers ----

/-- storeTcbQueueLinks with next=none (clearing or noprevnext) preserves acyclicity.
Removing/clearing the outgoing edge from tid cannot create new cycles. -/
private theorem storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev none = .ok st')
    (hAcyclic : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' := by
  obtain ⟨origTcb, hLookup, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid prev pprev none hObjInv hStep
  -- Any QueueNextPath in st' transfers to st: tid has next=none so can't be source,
  -- other ObjIds unchanged
  have hTransfer : ∀ a b, QueueNextPath st' a b → QueueNextPath st a b := by
    intro a b hp
    induction hp with
    | single x y tcbX hObj hNext =>
      by_cases hx : x.toObjId = tid.toObjId
      · rw [hx, hTcb'] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
      · exact .single x y tcbX (by rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev none x.toObjId hx hObjInv hStep] at hObj) hNext
    | cons x y z tcbX hObj hNext _ ih =>
      by_cases hx : x.toObjId = tid.toObjId
      · rw [hx, hTcb'] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
      · exact .cons x y z tcbX (by rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev none x.toObjId hx hObjInv hStep] at hObj) hNext ih
  intro t hp; exact hAcyclic t (hTransfer t t hp)

/-- storeTcbQueueLinks preserving queueNext preserves acyclicity.
The edge set is unchanged: tid's new TCB has the same queueNext. -/
private theorem storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hNextPreserved : ∀ tcb, lookupTcb st tid = some tcb → tcb.queueNext = next)
    (hAcyclic : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' := by
  obtain ⟨origTcb, hLookup, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid prev pprev next hObjInv hStep
  have hOrigObj := lookupTcb_some_objects st tid origTcb hLookup
  have hNextEq : (tcbWithQueueLinks origTcb prev pprev next).queueNext = origTcb.queueNext := by
    simp [tcbWithQueueLinks]; exact (hNextPreserved origTcb hLookup).symm
  -- storeTcbQueueLinks preserving queueNext: same edges, same acyclicity.
  -- Every QueueNextPath in st' transfers to st via the preserved queueNext at tid
  -- and unchanged objects at all other ObjIds.
  have hTransfer : ∀ a b, QueueNextPath st' a b → QueueNextPath st a b := by
    intro a b hp
    induction hp with
    | single x y tcbX hObj hNext =>
      by_cases hx : x.toObjId = tid.toObjId
      · rw [hx, hTcb'] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
        rw [← hNextPreserved origTcb hLookup] at hNext
        exact .single x y origTcb (hx ▸ hOrigObj) hNext
      · exact .single x y tcbX (by rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next x.toObjId hx hObjInv hStep] at hObj) hNext
    | cons x y z tcbX hObj hNext _ ih =>
      by_cases hx : x.toObjId = tid.toObjId
      · rw [hx, hTcb'] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
        rw [← hNextPreserved origTcb hLookup] at hNext
        exact .cons x y z origTcb (hx ▸ hOrigObj) hNext ih
      · exact .cons x y z tcbX (by rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next x.toObjId hx hObjInv hStep] at hObj) hNext ih
  intro t hp; exact hAcyclic t (hTransfer t t hp)

/-- Two-step storeTcbQueueLinks append (tailTid.next=newTid, newTid.next=none) preserves
acyclicity. The new edge tail→new cannot create a cycle because new.next=none. -/
private theorem storeTcbQueueLinks_append_preserves_tcbQueueChainAcyclic
    (st1 st2 stF : SystemState) (tailTid newTid : SeLe4n.ThreadId)
    (prevT : Option SeLe4n.ThreadId) (pprevT pprevN : Option QueuePPrev)
    (hObjInv : st1.objects.invExt)
    (hStep1 : storeTcbQueueLinks st1 tailTid prevT pprevT (some newTid) = .ok st2)
    (hStep2 : storeTcbQueueLinks st2 newTid (some tailTid) pprevN none = .ok stF)
    (hNe : tailTid.toObjId ≠ newTid.toObjId)
    (hTailNext : ∀ t, st1.objects[tailTid.toObjId]? = some (.tcb t) → t.queueNext = none)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tA : TCB), st1.objects[a.toObjId]? = some (.tcb tA) →
      tA.queueNext ≠ some newTid)
    (hAcyclic : tcbQueueChainAcyclic st1) :
    tcbQueueChainAcyclic stF := by
  -- Step 2 clears newTid.next. Acyclicity preserved from st2.
  -- Step 1 sets tailTid.next = some newTid. Prove st2 is acyclic.
  -- In pairB (=st1 for TCBs), tailTid.next = none.
  -- In st2, tailTid.next = some newTid, newTid unchanged from st1.
  -- A cycle in st2 through tail→new needs new→⁺tail, but new.next is original from st1
  -- and no cycle through tail→new can form because step 2 clears new.next.
  -- Simplest: compose step 2 (clearing) with step 1 proof.
  -- Step 2 clears newTid.next → use storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic.
  -- Need st2 is acyclic. Prove via storeObject_tcb: tailTid.next changed but
  -- no cycle can go through tail→new since in st1, no TCB has next=some newTid (hNoFwd).
  -- st2: tailTid has next=some newTid, everything else same as st1 for TCBs.
  -- Prove st2 acyclic: any cycle in st2 either goes through tailTid (as source) or not.
  -- If not, all edges from st1, cycle in st1 → contradiction.
  -- If yes, tailTid→newTid. Then newTid→⁺tailTid in st2.
  -- newTid in st2 has same TCB as st1 (step 1 only modified tailTid).
  -- For the sub-path newTid→⁺tailTid in st2:
  -- Each edge either uses tailTid (with next=newTid) or another thread (same as st1).
  -- If the path revisits tailTid→newTid, it loops through tail→new→...→tail→new,
  -- but each return to tail requires going through other st1 edges. Ultimately, removing
  -- the tail→new edge gives a path in st1 that forms a cycle. Contradiction.
  -- This is getting very complex. Let me use the two-step composition approach:
  -- stF is the result of clearing newTid.next in st2. Acyclicity of stF follows if st2 is acyclic.
  have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt st1 st2 tailTid prevT pprevT (some newTid) hObjInv hStep1
  -- Prove st2 is acyclic by showing it satisfies the conditions of storeObject_tcb with
  -- a changed queueNext. Actually, we can't use that lemma directly since queueNext changed.
  -- Instead, use the direct clearing approach on step 2 and provide acyclicity of st2.
  -- For st2 acyclicity, observe:
  -- st2.objects[tailTid.toObjId] = tcbWithQueueLinks origTail prevT pprevT (some newTid)
  -- st2.objects[oid] = st1.objects[oid] for oid ≠ tailTid.toObjId
  -- A QueueNextPath in st2: every edge from oid ≠ tailTid is from st1.
  -- Edge from tailTid goes to newTid (new). In st1, no edge goes TO newTid (hNoFwd).
  -- So newTid is "fresh" as a target. The only way to reach newTid in st2 is via tailTid.
  -- For a cycle, after reaching newTid, we'd need to get back to the cycle start.
  -- From newTid, edges are from st1 (newTid unchanged). From newTid we can reach
  -- some set of vertices via st1 edges. If we reach tailTid, in st2 tailTid→newTid,
  -- creating a loop. But in st1, tailTid.next = none, so tailTid is a dead end.
  -- The path newTid→...→tailTid in st1 (with st1 edges) can't continue from tailTid.
  -- So in st2, after going tailTid→newTid→...→tailTid (using st1 edges in between),
  -- we'd need the path from newTid to reach tailTid through st1 edges.
  -- If such a path exists, we can construct a path in st1: newTid→...→tailTid.
  -- Combined with tailTid.next=none, this path can't form a cycle in st1. Fine.
  -- But the cycle in st2 is: start→...→tailTid→newTid→...→start (through st1 edges and
  -- the one new edge). Removing the new edge, the rest uses st1 edges: start→...→tailTid
  -- (in st1) and newTid→...→start (in st1). These don't form a cycle in st1 unless
  -- connected, but tailTid.next=none in st1 disconnects them.
  -- Formal approach: transfer path from st2 to st1, handling the tail→new edge specially.
  obtain ⟨origTail, hLkT, hTailSt2⟩ := storeTcbQueueLinks_result_tcb st1 st2 tailTid prevT pprevT (some newTid) hObjInv hStep1
  obtain ⟨origNew, hLkN, hNewStF⟩ := storeTcbQueueLinks_result_tcb st2 stF newTid (some tailTid) pprevN none hObjInv2 hStep2
  have hTailOrig := lookupTcb_some_objects st1 tailTid origTail hLkT
  have hTailStF : stF.objects[tailTid.toObjId]? =
      some (.tcb (tcbWithQueueLinks origTail prevT pprevT (some newTid))) := by
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      tailTid.toObjId hNe hObjInv2 hStep2]; exact hTailSt2
  have hOther : ∀ oid, oid ≠ tailTid.toObjId → oid ≠ newTid.toObjId →
      stF.objects[oid]? = st1.objects[oid]? := by
    intro oid hne1 hne2
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none oid hne2 hObjInv2 hStep2,
        storeTcbQueueLinks_preserves_objects_ne st1 st2 tailTid prevT pprevT (some newTid) oid hne1 hObjInv hStep1]
  -- newTid.next = none in stF, so no QueueNextPath starts at newTid
  have hNoPathFromNew : ∀ a b, QueueNextPath stF a b → a.toObjId ≠ newTid.toObjId := by
    intro a b hp
    cases hp with
    | single x y tcbX hObj hNext =>
      intro hx; rw [hx, hNewStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
    | cons x y z tcbX hObj hNext _ =>
      intro hx; rw [hx, hNewStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
  -- Transfer: QueueNextPath stF a b where a ≠ newTid and (a = tailTid → b = newTid)
  -- translates to st1 edges (except the impossible tail single-step case which
  -- only arises when b = newTid, handled by caller)
  -- For the cycle proof, we handle each first step then use transfer for the tail.
  intro t hp
  -- Eliminate the first step of the cycle, then transfer the remaining path
  cases hp with
  | single _ _ tcbX hObj hNext =>
    by_cases hxN : t.toObjId = newTid.toObjId
    · rw [hxN, hNewStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
    · by_cases hxT : t.toObjId = tailTid.toObjId
      · rw [hxT, hTailStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
        exact absurd (hxT ▸ congrArg ThreadId.toObjId hNext : newTid.toObjId = tailTid.toObjId) (Ne.symm hNe)
      · exact hAcyclic t (.single t t tcbX (by rwa [hOther t.toObjId hxT hxN] at hObj) hNext)
  | cons _ y _ tcbX hObj hNext hTail =>
    by_cases hxN : t.toObjId = newTid.toObjId
    · rw [hxN, hNewStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext
    · by_cases hxT : t.toObjId = tailTid.toObjId
      · rw [hxT, hTailStF] at hObj; cases hObj; simp [tcbWithQueueLinks] at hNext; subst hNext
        exact absurd rfl (hNoPathFromNew newTid t hTail)
      · have hObjSt1 : st1.objects[t.toObjId]? = some (.tcb tcbX) := by
          rwa [hOther t.toObjId hxT hxN] at hObj
        -- hTail : QueueNextPath stF y z where z = t = x
        -- Need to transfer hTail to st1 to get QueueNextPath st1 y x.
        -- Transfer path y→⁺t from stF to st1. Since t.toObjId ≠ newTid.toObjId,
        -- the path can't end with tailTid→newTid, so all edges transfer to st1.
        have hPathTransfer : ∀ a b, QueueNextPath stF a b → b.toObjId ≠ newTid.toObjId → QueueNextPath st1 a b := by
          intro a b hpab hbN
          induction hpab with
          | single x' y' tcbX' hObj' hNext' =>
            by_cases hxN' : x'.toObjId = newTid.toObjId
            · rw [hxN', hNewStF] at hObj'; cases hObj'; simp [tcbWithQueueLinks] at hNext'
            · by_cases hxT' : x'.toObjId = tailTid.toObjId
              · rw [hxT', hTailStF] at hObj'; cases hObj'; simp [tcbWithQueueLinks] at hNext'
                subst hNext'; exact absurd rfl hbN
              · exact .single x' y' tcbX' (by rwa [hOther x'.toObjId hxT' hxN'] at hObj') hNext'
          | cons x' y' z' tcbX' hObj' hNext' _ ih =>
            by_cases hxN' : x'.toObjId = newTid.toObjId
            · rw [hxN', hNewStF] at hObj'; cases hObj'; simp [tcbWithQueueLinks] at hNext'
            · by_cases hxT' : x'.toObjId = tailTid.toObjId
              · rw [hxT', hTailStF] at hObj'; cases hObj'; simp [tcbWithQueueLinks] at hNext'
                subst hNext'
                exact absurd rfl (hNoPathFromNew newTid z' (by assumption))
              · exact .cons x' y' z' tcbX' (by rwa [hOther x'.toObjId hxT' hxN'] at hObj') hNext' (ih hbN)
        suffices hTailSt1 : QueueNextPath st1 y t from
          hAcyclic t (.cons t y t tcbX hObjSt1 hNext hTailSt1)
        exact hPathTransfer y t hTail hxN

-- ---- WS-H5: Dual-queue preservation for queue operations ----

/-- WS-H5: endpointQueuePopHead preserves dualQueueSystemInvariant. -/
theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some headTcb =>
          simp only [hLookup] at hStep
          have hHeadTcb := lookupTcb_some_objects st headTid headTcb hLookup
          have hNeEpHead : endpointId ≠ headTid.toObjId :=
            fun h => by rw [h] at hObj; rw [hHeadTcb] at hObj; cases hObj
          have hEpWf := hEpInv endpointId ep hObj
          unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
          have hWfQ : intrusiveQueueWellFormed (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
            cases isReceiveQ <;> simp_all
          obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
          obtain ⟨_, hTcbH, hPrevNone⟩ := hHdBnd headTid hHead
          rw [hHeadTcb] at hTcbH; cases hTcbH
          have hPreEp : ∀ tcb : TCB, st.objects[endpointId]? ≠ some (.tcb tcb) := by
            intro tcb h; rw [hObj] at h; cases h
          cases hNext : headTcb.queueNext with
          | none =>
            simp only [hNext] at hStep
            cases hStoreEp : storeObject endpointId
                (.endpoint (if isReceiveQ then { ep with receiveQ := {} }
                 else { ep with sendQ := {} })) st with
            | error e => simp [hStoreEp] at hStep
            | ok pair =>
              simp only [hStoreEp] at hStep
              -- Reduce the let/match on none to get storeTcbQueueLinks pair.2 headTid
              generalize hSt2 : storeTcbQueueLinks pair.2 headTid none none none = r at hStep
              cases r with
              | error e => simp at hStep
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨rfl, _, rfl⟩ := hStep
                have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                  st pair.2 endpointId _ hObjInv hStoreEp hPreEp hLink
                have hTransport : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                    pair.2.objects[x.toObjId]? = some (.tcb t) →
                    st.objects[x.toObjId]? = some (.tcb t) := by
                  intro x t h
                  by_cases hx : x.toObjId = endpointId
                  · rw [hx, storeObject_objects_eq st pair.2 endpointId _ hObjInv hStoreEp] at h; cases h
                  · rwa [storeObject_objects_ne st pair.2 endpointId x.toObjId _ hx hObjInv hStoreEp] at h
                have hNoFwd1 : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                    pair.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some headTid := by
                  intro a tA hA hN
                  obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTransport a tA hA) headTid hN
                  rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                have hNoRev1 : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                    pair.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some headTid := by
                  intro b tB hB hP
                  obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTransport b tB hB) headTid hP
                  rw [hHeadTcb] at hA; cases hA; rw [hNext] at hN; exact absurd hN (by simp)
                have hObjInvEp : pair.2.objects.invExt :=
                  storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStoreEp
                have hAcycEp := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                  st pair.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp hAcyclic
                refine ⟨?_, storeTcbQueueLinks_clearing_preserves_linkInteg
                  pair.2 st3 headTid hObjInvEp hSt2 hLink1 hNoFwd1 hNoRev1,
                  storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                  pair.2 st3 headTid none none hObjInvEp hSt2 hAcycEp⟩
                intro epId' ep' hObj'
                have hObj1 := storeTcbQueueLinks_endpoint_backward pair.2 st3 headTid none none none
                  epId' ep' hObjInvEp hSt2 hObj'
                unfold dualQueueEndpointWellFormed; rw [hObj']
                by_cases hNe : epId' = endpointId
                · rw [hNe] at hObj1
                  rw [storeObject_objects_eq st pair.2 endpointId _ hObjInv hStoreEp] at hObj1; cases hObj1
                  cases hRQ : isReceiveQ
                  · -- isReceiveQ = false: sendQ was emptied, receiveQ preserved
                    exact ⟨intrusiveQueueWellFormed_empty st3,
                      storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hObjInvEp hSt2
                        ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hObjInv hStoreEp hPreEp _ hEpWf.2)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                  · -- isReceiveQ = true: receiveQ was emptied, sendQ preserved
                    exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hObjInvEp hSt2
                        ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hObjInv hStoreEp hPreEp _ hEpWf.1)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                      intrusiveQueueWellFormed_empty st3⟩
                · have hObjSt : st.objects[epId']? = some (.endpoint ep') := by
                    rwa [storeObject_objects_ne st pair.2 endpointId epId' _ hNe hObjInv hStoreEp] at hObj1
                  have hWfPre := hEpInv epId' ep' hObjSt
                  unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt] at hWfPre
                  exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hObjInvEp hSt2
                      ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hObjInv hStoreEp hPreEp _ hWfPre.1)
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                    storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hObjInvEp hSt2
                      ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hObjInv hStoreEp hPreEp _ hWfPre.2)
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
          | some nextTid =>
            simp only [hNext] at hStep
            -- CASE B: multi-element queue (next = some nextTid)
            -- Steps: storeObject ep → lookupTcb nextTid → storeTcbQueueLinks nextTid → storeTcbQueueLinks headTid (clear)
            cases hStoreEpB : storeObject endpointId
                (.endpoint (if isReceiveQ then
                  { ep with receiveQ := ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ }
                 else
                  { ep with sendQ := ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ })) st with
            | error e => simp [hStoreEpB] at hStep
            | ok pairB =>
              cases hLkN : lookupTcb pairB.2 nextTid with
              | none => simp [hStoreEpB, hLkN] at hStep
              | some nextTcb =>
                cases hStN : storeTcbQueueLinks pairB.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hStoreEpB, hLkN, hStN] at hStep
                | ok st2 =>
                  cases hClH : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hStoreEpB, hLkN, hStN, hClH] at hStep
                  | ok st3 =>
                    simp [hStoreEpB, hLkN, hStN, hClH] at hStep
                    obtain ⟨rfl, _, rfl⟩ := hStep
                    -- Key facts
                    have hNeEpNextB : endpointId ≠ nextTid.toObjId := by
                      intro h; have := lookupTcb_some_objects pairB.2 nextTid nextTcb hLkN
                      rw [← h, storeObject_objects_eq st pairB.2 endpointId _ hObjInv hStoreEpB] at this; cases this
                    have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
                      have := lookupTcb_some_objects pairB.2 nextTid nextTcb hLkN
                      rwa [storeObject_objects_ne st pairB.2 endpointId nextTid.toObjId _
                        (Ne.symm hNeEpNextB) hObjInv hStoreEpB] at this
                    have hNextPrevB : nextTcb.queuePrev = some headTid := by
                      obtain ⟨_, hB, hP⟩ := hLink.1 headTid headTcb hHeadTcb nextTid hNext
                      rw [hNextTcbSt] at hB; cases hB; exact hP
                    have hNeHN : headTid.toObjId ≠ nextTid.toObjId := by
                      intro h
                      have hEq : st.objects[nextTid.toObjId]? = some (.tcb headTcb) := h ▸ hHeadTcb
                      rw [hNextTcbSt] at hEq; cases hEq
                      rw [hPrevNone] at hNextPrevB; exact absurd hNextPrevB (by simp)
                    have hLink1B := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                      st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp hLink
                    have hObjInvB : pairB.2.objects.invExt :=
                      storeObject_preserves_objects_invExt' st endpointId _ pairB hObjInv hStoreEpB
                    have hTransportB : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        pairB.2.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t h
                      by_cases hx : x.toObjId = endpointId
                      · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hObjInv hStoreEpB] at h; cases h
                      · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hObjInv hStoreEpB] at h
                    -- nextTid in st2 (after storeTcbQueueLinks nextTid)
                    have hNextResultB := storeTcbQueueLinks_result_tcb pairB.2 st2 nextTid none
                        (some QueuePPrev.endpointHead) nextTcb.queueNext hObjInvB hStN
                    obtain ⟨origNextB, hOrigLkB, hNextSt2B⟩ := hNextResultB
                    have hObjInvSt2B : st2.objects.invExt :=
                      storeTcbQueueLinks_preserves_objects_invExt pairB.2 st2 nextTid none
                        (some QueuePPrev.endpointHead) nextTcb.queueNext hObjInvB hStN
                    -- origNextB = nextTcb since both come from lookupTcb pairB.2 nextTid
                    rw [hLkN] at hOrigLkB; cases hOrigLkB
                    -- Now origNextB is replaced by nextTcb everywhere
                    -- nextTid in st3 (preserved by clearing headTid)
                    have hNextSt3 : st3.objects[nextTid.toObjId]? = some
                        (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _
                        nextTid.toObjId hNeHN.symm hObjInvSt2B hClH]; exact hNextSt2B
                    -- headTid in st3 (cleared)
                    have hHeadResultB := storeTcbQueueLinks_result_tcb st2 st3 headTid none none none hObjInvSt2B hClH
                    obtain ⟨_, _, hHeadSt3B⟩ := hHeadResultB
                    -- headTid in st2 (unchanged from st by storeObject + storeTcbQueueLinks nextTid)
                    have hHeadSt2 : st2.objects[headTid.toObjId]? = some (.tcb headTcb) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _
                        headTid.toObjId hNeHN hObjInvB hStN]
                      rwa [storeObject_objects_ne st pairB.2 endpointId headTid.toObjId _
                        hNeEpHead.symm hObjInv hStoreEpB]
                    -- Transport: other TCBs in st3 = TCBs in st
                    have hFwdOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st.objects[x.toObjId]? = some (.tcb t) →
                        st3.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hObjInvSt2B hClH,
                          storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hObjInvB hStN]
                      rw [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ ?_ hObjInv hStoreEpB]; exact ht
                      intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                    have hBackOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st3.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      have h1 : st2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hObjInvSt2B hClH] at ht
                      have h2 : pairB.2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hObjInvB hStN] at h1
                      exact hTransportB x t h2
                    -- Construct well-formedness of the new queue in st2
                    have hWfQNewSt2 : intrusiveQueueWellFormed
                        ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ st2 := by
                      refine ⟨⟨(fun h => absurd h (by simp)), (fun h => absurd (hHT.2 h) (by rw [hHead]; simp))⟩, ?_, ?_⟩
                      · intro hd hHdEq; cases hHdEq
                        exact ⟨_, hNextSt2B, by simp [tcbWithQueueLinks]⟩
                      · intro tl hTl
                        obtain ⟨tOrig, hTOrig, hTNextOrig⟩ := hTlBnd tl hTl
                        by_cases htN : tl.toObjId = nextTid.toObjId
                        · have := threadId_toObjId_injective htN; subst this
                          rw [hNextTcbSt] at hTOrig; cases hTOrig
                          exact ⟨_, hNextSt2B, by simp [tcbWithQueueLinks]; exact hTNextOrig⟩
                        · have hTSt2 : st2.objects[tl.toObjId]? = some (.tcb tOrig) := by
                            rw [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _
                              tl.toObjId htN hObjInvB hStN]
                            rw [storeObject_objects_ne st pairB.2 endpointId tl.toObjId _ ?_ hObjInv hStoreEpB]
                            exact hTOrig
                            intro h; rw [h] at hTOrig; rw [hObj] at hTOrig; cases hTOrig
                          exact ⟨tOrig, hTSt2, hTNextOrig⟩
                    -- Helper: if nextTid is the tail of any well-formed queue in st,
                    -- then nextTcb.queueNext = none.
                    have hNextTailProp : ∀ (q : IntrusiveQueue),
                        intrusiveQueueWellFormed q st →
                        ∀ tl, q.tail = some tl → tl.toObjId = nextTid.toObjId →
                        nextTcb.queueNext = none := by
                      intro q hWf tl hTl hEq
                      have hTlEq := threadId_toObjId_injective hEq
                      rw [hTlEq] at hTl
                      obtain ⟨_, hT, hN⟩ := hWf.2.2 nextTid hTl
                      rw [hNextTcbSt] at hT; cases hT; exact hN
                    -- SPLIT: endpoint well-formedness ∧ link integrity ∧ acyclicity
                    have hAcycEpB := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                      st pairB.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEpB hAcyclic
                    have hAcycSt2 := storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
                      pairB.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hObjInvB hStN
                      (fun tcb h => by rw [hLkN] at h; cases h; rfl) hAcycEpB
                    have hAcycSt3 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                      st2 st3 headTid none none hObjInvSt2B hClH hAcycSt2
                    refine ⟨?_, ?_, hAcycSt3⟩
                    -- PART 1: Endpoint well-formedness
                    · intro epId' ep' hObj'
                      have hObjSt2 := storeTcbQueueLinks_endpoint_backward st2 st3 headTid _ _ _
                        epId' ep' hObjInvSt2B hClH hObj'
                      have hObjPB := storeTcbQueueLinks_endpoint_backward pairB.2 st2 nextTid _ _ _
                        epId' ep' hObjInvB hStN hObjSt2
                      unfold dualQueueEndpointWellFormed; rw [hObj']
                      by_cases hNe : epId' = endpointId
                      · rw [hNe] at hObjPB
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hObjInv hStoreEpB] at hObjPB
                        cases hObjPB
                        cases hRQ : isReceiveQ
                        · -- false: sendQ = new queue, receiveQ unchanged
                          simp only [hRQ, Bool.false_eq_true, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ unchanged
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                              ep.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hObjInvB hStN
                                ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp _ hEpWf.2)
                                (fun _ _ _ => rfl) (hNextTailProp ep.receiveQ hEpWf.2))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                        · -- true: receiveQ = new queue, sendQ unchanged
                          simp only [hRQ, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ unchanged
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                              ep.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hObjInvB hStN
                                ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp _ hEpWf.1)
                                (fun _ _ _ => rfl) (hNextTailProp ep.sendQ hEpWf.1))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                      · have hObjSt' : st.objects[epId']? = some (.endpoint ep') := by
                          rw [storeObject_objects_ne st pairB.2 endpointId epId' _ hNe hObjInv hStoreEpB] at hObjPB
                          exact hObjPB
                        have hWfPre := hEpInv epId' ep' hObjSt'
                        unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt'] at hWfPre
                        exact ⟨storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                            ep'.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hObjInvB hStN
                              ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp _ hWfPre.1)
                              (fun _ _ _ => rfl) (hNextTailProp ep'.sendQ hWfPre.1))
                            (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                          storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hObjInvSt2B hClH
                            ep'.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hObjInvB hStN
                              ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp _ hWfPre.2)
                              (fun _ _ _ => rfl) (hNextTailProp ep'.receiveQ hWfPre.2))
                            (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                    -- PART 2: Link integrity
                    · constructor
                      -- Forward: a.queueNext = some b → b.queuePrev = some a
                      · intro a tcbA hA b hNxt
                        by_cases haH : a.toObjId = headTid.toObjId
                        · rw [haH] at hA; rw [hHeadSt3B] at hA; cases hA
                          simp [tcbWithQueueLinks] at hNxt
                        · by_cases haN : a.toObjId = nextTid.toObjId
                          · rw [haN] at hA; rw [hNextSt3] at hA; cases hA
                            simp [tcbWithQueueLinks] at hNxt
                            have ha := threadId_toObjId_injective haN
                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                            have hbH : b.toObjId ≠ headTid.toObjId := by
                              intro hh; have := threadId_toObjId_injective hh; subst this
                              rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP
                              exact absurd hP (by simp)
                            have hbN : b.toObjId ≠ nextTid.toObjId := by
                              intro hh; have hbEq := threadId_toObjId_injective hh
                              rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNeHN
                            exact ⟨tcbB, hFwdOther b tcbB hbH hbN hB, ha ▸ hP⟩
                          · have hA' := hBackOther a tcbA haH haN hA
                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                            have hbH : b.toObjId ≠ headTid.toObjId := by
                              intro hh; have := threadId_toObjId_injective hh; subst this
                              rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP
                              exact absurd hP (by simp)
                            have hbN : b.toObjId ≠ nextTid.toObjId := by
                              intro hh; have hbEq := threadId_toObjId_injective hh
                              rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haH
                            exact ⟨tcbB, hFwdOther b tcbB hbH hbN hB, hP⟩
                      -- Reverse: b.queuePrev = some a → a.queueNext = some b
                      · intro b tcbB hB a hPrv
                        by_cases hbH : b.toObjId = headTid.toObjId
                        · rw [hbH] at hB; rw [hHeadSt3B] at hB; cases hB
                          simp [tcbWithQueueLinks] at hPrv
                        · by_cases hbN : b.toObjId = nextTid.toObjId
                          · rw [hbN] at hB; rw [hNextSt3] at hB; cases hB
                            simp [tcbWithQueueLinks] at hPrv
                          · have hB' := hBackOther b tcbB hbH hbN hB
                            obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                            by_cases haH : a.toObjId = headTid.toObjId
                            · have haEq := threadId_toObjId_injective haH
                              rw [haEq, hHeadTcb] at hA; cases hA; rw [hNext] at hNxt
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                            · by_cases haN : a.toObjId = nextTid.toObjId
                              · have := threadId_toObjId_injective haN; subst this
                                rw [hNextTcbSt] at hA; cases hA
                                exact ⟨_, hNextSt3, by simp [tcbWithQueueLinks]; exact hNxt⟩
                              · exact ⟨tcbA, hFwdOther a tcbA haH haN hA, hNxt⟩

/-- WS-H5: endpointQueueEnqueue preserves dualQueueSystemInvariant.
Requires freshness preconditions: the enqueued thread must not currently appear
in any endpoint queue boundary, and the current tail (if any) must not be
shared across queue boundaries of different endpoints. -/
theorem endpointQueueEnqueue_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshTid : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some enqueueTid ∧ ep.sendQ.tail ≠ some enqueueTid ∧
      ep.receiveQ.head ≠ some enqueueTid ∧ ep.receiveQ.tail ≠ some enqueueTid)
    (hTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          (if isReceiveQ then ep'.sendQ else ep'.receiveQ).tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        have hTcbObj := lookupTcb_some_objects st enqueueTid tcb hLookup
        have hNeEpTid : endpointId ≠ enqueueTid.toObjId :=
          fun h => by rw [h] at hObj; rw [hTcbObj] at hObj; cases hObj
        -- Guard: ipcState and queue link checks
        split at hStep
        · simp at hStep
        · rename_i hNotIpc
          split at hStep
          · simp at hStep
          · rename_i hLinksClean
            -- Derive that enqueueTid has no existing queue links
            have hPrevNone : tcb.queuePrev = none := by
              cases hp : tcb.queuePrev <;> simp_all
            have hNextNone : tcb.queueNext = none := by
              cases hn : tcb.queueNext <;> simp_all
            have hEpWf := hEpInv endpointId ep hObj
            unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
            -- Select the queue
            cases hRQ : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              -- ====== Case A: Empty queue ======
              simp only [hRQ] at hStep
              -- Store endpoint with new head/tail
              generalize hStoreEp : storeObject endpointId (.endpoint
                (if isReceiveQ then { ep with receiveQ := { head := some enqueueTid, tail := some enqueueTid } }
                 else { ep with sendQ := { head := some enqueueTid, tail := some enqueueTid } })) st
                = rEp at hStep
              cases rEp with
              | error e => simp at hStep
              | ok pairA =>
                simp only [] at hStep
                generalize hSt2 : storeTcbQueueLinks pairA.2 enqueueTid none (some QueuePPrev.endpointHead) none
                  = rSt2 at hStep
                cases rSt2 with
                | error e => simp at hStep
                | ok stA =>
                  have hStEq : stA = st' := Except.ok.inj hStep
                  rw [← hStEq]
                  -- Goal: dualQueueSystemInvariant stA
                  -- hSt2 : storeTcbQueueLinks pairA.2 enqueueTid ... = .ok stA
                  have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
                    fun t h => by rw [hObj] at h; cases h
                  have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                    st pairA.2 endpointId _ hObjInv hStoreEp hPreEp hLink
                  have hObjInvA : pairA.2.objects.invExt :=
                    storeObject_preserves_objects_invExt' st endpointId _ pairA hObjInv hStoreEp
                  have hTA : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                      pairA.2.objects[x.toObjId]? = some (.tcb t) →
                      st.objects[x.toObjId]? = some (.tcb t) := by
                    intro x t h; by_cases hx : x.toObjId = endpointId
                    · rw [hx, storeObject_objects_eq st pairA.2 endpointId _ hObjInv hStoreEp] at h; cases h
                    · rwa [storeObject_objects_ne st pairA.2 endpointId x.toObjId _ hx hObjInv hStoreEp] at h
                  have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                      pairA.2.objects[a.toObjId]? = some (.tcb tcbA) →
                      tcbA.queueNext ≠ some enqueueTid := by
                    intro a tA hA hN
                    obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTA a tA hA) enqueueTid hN
                    rw [hTcbObj] at hB; cases hB; simp [hPrevNone] at hP
                  have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                      pairA.2.objects[b.toObjId]? = some (.tcb tcbB) →
                      tcbB.queuePrev ≠ some enqueueTid := by
                    intro b tB hB hP
                    obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTA b tB hB) enqueueTid hP
                    rw [hTcbObj] at hA; cases hA; simp [hNextNone] at hN
                  obtain ⟨origTcbA, _, hTcbFinal⟩ := storeTcbQueueLinks_result_tcb
                    pairA.2 stA enqueueTid none (some QueuePPrev.endpointHead) none hObjInvA hSt2
                  have hQT : ∀ q, intrusiveQueueWellFormed q pairA.2 →
                      intrusiveQueueWellFormed q stA :=
                    fun q hWf => storeTcbQueueLinks_preserves_iqwf pairA.2 stA enqueueTid
                      none (some QueuePPrev.endpointHead) none hObjInvA hSt2 q hWf
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                  have hAcycA := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                    pairA.2 stA enqueueTid none (some QueuePPrev.endpointHead) hObjInvA hSt2
                    (storeObject_nonTcb_preserves_tcbQueueChainAcyclic st pairA.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp hAcyclic)
                  refine ⟨?_, storeTcbQueueLinks_noprevnext_preserves_linkInteg
                    pairA.2 stA enqueueTid (some QueuePPrev.endpointHead) hObjInvA hSt2 hLink1 hNoFwd hNoRev,
                    hAcycA⟩
                  intro epId' ep'A hObj'A
                  have hObj1A := storeTcbQueueLinks_endpoint_backward pairA.2 stA enqueueTid
                    none (some QueuePPrev.endpointHead) none epId' ep'A hObjInvA hSt2 hObj'A
                  unfold dualQueueEndpointWellFormed; rw [hObj'A]
                  by_cases hNeA : epId' = endpointId
                  · rw [hNeA] at hObj1A
                    rw [storeObject_objects_eq st pairA.2 endpointId _ hObjInv hStoreEp] at hObj1A
                    simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hObj1A
                    subst hObj1A
                    have hSing : intrusiveQueueWellFormed
                        { head := some enqueueTid, tail := some enqueueTid } stA :=
                      ⟨Iff.rfl,
                       fun hd hhd => by simp at hhd; subst hhd; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩,
                       fun tl htl => by simp at htl; subst htl; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩⟩
                    cases isReceiveQ
                    · exact ⟨hSing, hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hObjInv hStoreEp hPreEp _ hEpWf.2)⟩
                    · exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hObjInv hStoreEp hPreEp _ hEpWf.1), hSing⟩
                  · rw [storeObject_objects_ne st pairA.2 endpointId epId' _ hNeA hObjInv hStoreEp] at hObj1A
                    have hWfOrig := hEpInv epId' ep'A hObj1A
                    unfold dualQueueEndpointWellFormed at hWfOrig; rw [hObj1A] at hWfOrig
                    exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hObjInv hStoreEp hPreEp _ hWfOrig.1),
                      hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hObjInv hStoreEp hPreEp _ hWfOrig.2)⟩
            | some tailTid =>
              -- ====== Case B: Non-empty queue ======
              simp only [hRQ] at hStep
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail] at hStep
              | some tailTcb =>
                simp only [hLookupTail] at hStep
                -- Store endpoint with new tail
                generalize hStoreEpB : storeObject endpointId (.endpoint
                  (if isReceiveQ
                   then { ep with receiveQ := { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } }
                   else { ep with sendQ := { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } })) st
                  = rEpB at hStep
                cases rEpB with
                | error e => simp at hStep
                | ok pairB =>
                  simp only [] at hStep
                  -- Update old tail's next pointer
                  generalize hSt2B : storeTcbQueueLinks pairB.2 tailTid tailTcb.queuePrev
                    tailTcb.queuePPrev (some enqueueTid) = rSt2B at hStep
                  cases rSt2B with
                  | error e => simp at hStep
                  | ok st2B =>
                    simp only [] at hStep
                    -- Set new node's prev pointer
                    generalize hSt3B : storeTcbQueueLinks st2B enqueueTid (some tailTid)
                      (some (QueuePPrev.tcbNext tailTid)) none = rSt3B at hStep
                    cases rSt3B with
                    | error e => simp at hStep
                    | ok st3B =>
                      have hEqStB : st3B = st' := Except.ok.inj hStep
                      rw [← hEqStB]
                      -- ====== Case B proof: Non-empty queue ======
                      have hTailTcbObj := lookupTcb_some_objects st tailTid tailTcb hLookupTail
                      have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
                        fun t h => by rw [hObj] at h; cases h
                      have hNeTailEp : tailTid.toObjId ≠ endpointId := fun h => by
                        rw [← h] at hObj; rw [hTailTcbObj] at hObj; cases hObj
                      have hNeTailEnq : tailTid.toObjId ≠ enqueueTid.toObjId := by
                        intro h; have hEq := threadId_toObjId_injective h; rw [hEq] at hRQ
                        exact absurd hRQ (by cases isReceiveQ <;> simp [hFreshTid endpointId ep hObj])
                      have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                        st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp hLink
                      have hObjInvB : pairB.2.objects.invExt :=
                        storeObject_preserves_objects_invExt' st endpointId _ pairB hObjInv hStoreEpB
                      have hTcbBack : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                          pairB.2.objects[x.toObjId]? = some (.tcb t) →
                          st.objects[x.toObjId]? = some (.tcb t) := by
                        intro x t h; by_cases hx : x.toObjId = endpointId
                        · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hObjInv hStoreEpB] at h; cases h
                        · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hObjInv hStoreEpB] at h
                      have hTailInPB : pairB.2.objects[tailTid.toObjId]? = some (.tcb tailTcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId tailTid.toObjId _
                          hNeTailEp hObjInv hStoreEpB]; exact hTailTcbObj
                      have hEnqInPB : pairB.2.objects[enqueueTid.toObjId]? = some (.tcb tcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId enqueueTid.toObjId _
                          (Ne.symm hNeEpTid) hObjInv hStoreEpB]; exact hTcbObj
                      have hTailNextNone : tailTcb.queueNext = none := by
                        have hQWf : intrusiveQueueWellFormed
                            (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
                          cases isReceiveQ
                          · exact hEpWf.1
                          · exact hEpWf.2
                        obtain ⟨_, hT, hN⟩ := hQWf.2.2 tailTid hRQ
                        rw [hTailTcbObj] at hT; cases hT; exact hN
                      have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tA : TCB),
                          pairB.2.objects[a.toObjId]? = some (.tcb tA) →
                          tA.queueNext ≠ some enqueueTid := by
                        intro a tA hA hN
                        obtain ⟨tB, hB, hP⟩ := hLink.1 a tA (hTcbBack a tA hA) enqueueTid hN
                        rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; cases hP
                      have hNoRev : ∀ (b : SeLe4n.ThreadId) (tB : TCB),
                          pairB.2.objects[b.toObjId]? = some (.tcb tB) →
                          tB.queuePrev ≠ some enqueueTid := by
                        intro b tB hB hP
                        obtain ⟨tA, hA, hN⟩ := hLink.2 b tB (hTcbBack b tB hB) enqueueTid hP
                        rw [hTcbObj] at hA; cases hA; rw [hNextNone] at hN; cases hN
                      have hObjInv2B : st2B.objects.invExt :=
                        storeTcbQueueLinks_preserves_objects_invExt pairB.2 st2B tailTid
                          tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) hObjInvB hSt2B
                      have hObjInv3B : st3B.objects.invExt :=
                        storeTcbQueueLinks_preserves_objects_invExt st2B st3B enqueueTid
                          (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hObjInv2B hSt3B
                      have hLinkFinal := storeTcbQueueLinks_append_tail_preserves_linkInteg
                        pairB.2 st2B st3B tailTid enqueueTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some (QueuePPrev.tcbNext tailTid))
                        hObjInvB hSt2B hSt3B hNeTailEnq hLink1
                        (fun t h => by rw [hTailInPB] at h; cases h; rfl)
                        (fun t h => by rw [hTailInPB] at h; cases h; exact hTailNextNone)
                        hNoFwd hNoRev
                      -- Endpoint well-formedness transport
                      obtain ⟨origEnq2, _, hEnqSt3⟩ := storeTcbQueueLinks_result_tcb
                        st2B st3B enqueueTid (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hObjInv2B hSt3B
                      -- Transport iqwf through both steps for unmodified queues
                      have hQT : ∀ q, intrusiveQueueWellFormed q pairB.2 →
                          (∀ hd, q.head = some hd → hd.toObjId = tailTid.toObjId → tailTcb.queuePrev = none) →
                          (∀ tl, q.tail = some tl → tl.toObjId ≠ tailTid.toObjId) →
                          (∀ hd, q.head = some hd → hd.toObjId ≠ enqueueTid.toObjId) →
                          intrusiveQueueWellFormed q st3B := by
                        intro q hWf hH1 hT1 hH2
                        exact storeTcbQueueLinks_preserves_iqwf st2B st3B enqueueTid
                          (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hObjInv2B hSt3B q
                          (storeTcbQueueLinks_preserves_iqwf pairB.2 st2B tailTid
                            tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) hObjInvB hSt2B q hWf
                            hH1 (fun tl hTl hOid => absurd hOid (hT1 tl hTl)))
                          (fun hd hHd hOid => absurd hOid (hH2 hd hHd))
                          (fun _ _ _ => rfl)
                      -- Common hH1 derivation: if any queue's head is at tailTid, then tailTcb.queuePrev = none
                      have hHeadTailPrev : ∀ q, intrusiveQueueWellFormed q st →
                          ∀ hd, q.head = some hd → hd.toObjId = tailTid.toObjId → tailTcb.queuePrev = none := by
                        intro q hWf hd hHd hOid
                        obtain ⟨t, hT, hP⟩ := hWf.2.1 hd hHd
                        rw [hOid, hTailTcbObj] at hT; cases hT; exact hP
                      -- Unmodified queue transport helper (used for both branches)
                      have hUnmodWfSt3B : ∀ q, intrusiveQueueWellFormed q st →
                          (∀ tl, q.tail = some tl → tl.toObjId ≠ tailTid.toObjId) →
                          (∀ hd, q.head = some hd → hd.toObjId ≠ enqueueTid.toObjId) →
                          intrusiveQueueWellFormed q st3B := by
                        intro q hWfSt hT1 hH2
                        exact hQT q (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pairB.2 endpointId _ hObjInv hStoreEpB hPreEp q hWfSt)
                          (hHeadTailPrev q hWfSt) hT1 hH2
                      have hAcycB := storeTcbQueueLinks_append_preserves_tcbQueueChainAcyclic
                        pairB.2 st2B st3B tailTid enqueueTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some (QueuePPrev.tcbNext tailTid))
                        hObjInvB hSt2B hSt3B hNeTailEnq
                        (fun t h => by rw [hTailInPB] at h; cases h; exact hTailNextNone)
                        hNoFwd
                        (storeObject_nonTcb_preserves_tcbQueueChainAcyclic st pairB.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEpB hAcyclic)
                      refine ⟨?_, hLinkFinal, hAcycB⟩
                      intro epId' ep'F hObj'F
                      have hObj'2 := storeTcbQueueLinks_endpoint_backward st2B st3B enqueueTid
                        (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none epId' ep'F hObjInv2B hSt3B hObj'F
                      have hObj'1 := storeTcbQueueLinks_endpoint_backward pairB.2 st2B tailTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) epId' ep'F hObjInvB hSt2B hObj'2
                      unfold dualQueueEndpointWellFormed; rw [hObj'F]
                      by_cases hNeEp : epId' = endpointId
                      · -- Same endpoint (modified)
                        rw [hNeEp] at hObj'1
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hObjInv hStoreEpB] at hObj'1
                        simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hObj'1
                        rw [← hObj'1]
                        -- Construct modified queue wf in pairB.2 then transport
                        have hSelQWf : intrusiveQueueWellFormed
                            (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
                          cases isReceiveQ
                          · exact hEpWf.1
                          · exact hEpWf.2
                        have hModWfPB : intrusiveQueueWellFormed
                            { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                              tail := some enqueueTid } pairB.2 := by
                          refine ⟨?_, ?_, ?_⟩
                          · constructor
                            · intro hh; exfalso
                              have hTN : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail ≠ none := by
                                rw [hRQ]; exact Option.some_ne_none _
                              exact hTN (hSelQWf.1.mp hh)
                            · intro h; simp at h
                          · intro hd hHd
                            obtain ⟨t, hT, hP⟩ := hSelQWf.2.1 hd hHd
                            have : hd.toObjId ≠ endpointId := fun hh =>
                              absurd (hh ▸ hT) (hPreEp t)
                            exact ⟨t, by rw [storeObject_objects_ne st pairB.2 endpointId hd.toObjId _
                              this hObjInv hStoreEpB]; exact hT, hP⟩
                          · intro tl hTl; simp only [Option.some.injEq] at hTl; rw [← hTl]
                            exact ⟨tcb, hEnqInPB, hNextNone⟩
                        have hModWf := hQT _ hModWfPB
                          (fun hd hHd hOid => hHeadTailPrev _ hSelQWf hd hHd hOid)
                          (fun tl hTl hOid => by simp only [Option.some.injEq] at hTl; rw [← hTl] at hOid
                                                 exact absurd hOid (Ne.symm hNeTailEnq))
                          (fun hd hHd hOid => by
                            have hEq := threadId_toObjId_injective hOid; rw [hEq] at hHd
                            exact absurd hHd (by cases isReceiveQ <;> simp [hFreshTid endpointId ep hObj]))
                        have hTFH := (hTailFresh ep tailTid hObj hRQ endpointId ep hObj).2 rfl
                        have hFH := hFreshTid endpointId ep hObj
                        cases isReceiveQ
                        · simp only [] at hModWf hTFH ⊢
                          exact ⟨hModWf, hUnmodWfSt3B ep.receiveQ hEpWf.2
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFH)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFH.2.2.1)⟩
                        · simp only [] at hModWf hTFH ⊢
                          exact ⟨hUnmodWfSt3B ep.sendQ hEpWf.1
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFH)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFH.1),
                            hModWf⟩
                      · -- Different endpoint
                        have hObjSt : st.objects[epId']? = some (.endpoint ep'F) := by
                          rwa [storeObject_objects_ne st pairB.2 endpointId epId' _ hNeEp hObjInv hStoreEpB] at hObj'1
                        have hWfOrig := hEpInv epId' ep'F hObjSt
                        unfold dualQueueEndpointWellFormed at hWfOrig; rw [hObjSt] at hWfOrig
                        have hFO := hFreshTid epId' ep'F hObjSt
                        have hTFO := (hTailFresh ep tailTid hObj hRQ epId' ep'F hObjSt).1 hNeEp
                        exact ⟨hUnmodWfSt3B ep'F.sendQ hWfOrig.1
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFO.1)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFO.1),
                          hUnmodWfSt3B ep'F.receiveQ hWfOrig.2
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFO.2)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFO.2.2.1)⟩

/-- WS-H5: endpointSendDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointSendDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointSendDual endpointId sender msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointSendDual at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            obtain ⟨rcvr, headTcb1, stPop⟩ := pair
            have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
              endpointId true st stPop rcvr hObjInv hPop hInv
            have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
              endpointId true st stPop rcvr headTcb1 hObjInv hPop
            exact ensureRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                stPop st2 rcvr .ready (some msg) hObjInv1 hStore hInv1)
      | none =>
        -- Path B: enqueue sender, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId false sender st st1 hEnq hInv hObjInv hFreshSender hSendTailFresh
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId false sender st st1 hObjInv hEnq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hStore hInv1)

/-- WS-H5: endpointReceiveDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointReceiveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointReceiveDual endpointId receiver) st = .ok (senderId, st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.sendQ.head with
      | some sndr =>
        -- Path A: dequeue sender, transfer message/unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          -- Case-split on returned TCB's ipcState to determine senderWasCall
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall epCall =>
            -- Call path: senderWasCall = true
            simp only [hSenderIpc, ite_true] at hStep
            cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1
                (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              cases hMsg : storeTcbPendingMessage st2 receiver pair.2.1.pendingMessage with
              | error e => simp [hMsg] at hStep
              | ok st3 =>
                simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
                  pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore
                exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant
                  st2 _ receiver pair.2.1.pendingMessage hObjInv2 hMsg
                  (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                    pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore hInv1)
          | ready | blockedOnSend _ | blockedOnReceive _
            | blockedOnReply _ _ | blockedOnNotification _ =>
            -- Send path: senderWasCall = false
            simp only [hSenderIpc] at hStep
            cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              cases hMsg : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver
                  pair.2.1.pendingMessage with
              | error e => simp [hMsg] at hStep
              | ok st3 =>
                simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
                  pair.2.2 st2 pair.1 .ready none hObjInv1 hStore
                have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt :=
                  ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
                exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant
                  (ensureRunnable st2 pair.1) _ receiver pair.2.1.pendingMessage hObjInvEns hMsg
                  (ensureRunnable_preserves_dualQueueSystemInvariant _ _
                    (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                      pair.2.2 st2 pair.1 .ready none hObjInv1 hStore hInv1))
      | none =>
        -- Path B: enqueue receiver, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep; rcases hStep with ⟨-, rfl⟩
            have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId true receiver st st1 hEnq hInv hObjInv hFreshReceiver hRecvTailFresh
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver st st1 hObjInv hEnq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcState_preserves_dualQueueSystemInvariant st1 st2 receiver _ hObjInv1 hStore hInv1)

/-- WS-H12a: endpointReplyRecv preserves dualQueueSystemInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation.
Freshness preconditions are transported through the reply phase since
storeTcbIpcStateAndMessage and ensureRunnable do not modify endpoint objects. -/
theorem endpointReplyRecv_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointReplyRecv endpointId receiver replyTarget msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReplyRecv at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            dualQueueSystemInvariant stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hInv
      have hInv2 := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hInv1
      -- Transport freshness: storeTcbIpcStateAndMessage + ensureRunnable don't modify endpoint objects
      -- Transport freshness through storeTcbIpcStateAndMessage + ensureRunnable
      -- Both operations preserve endpoint objects (only modify TCBs/scheduler)
      have hFreshReceiver' : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId]? = some (.endpoint ep) →
          ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
          ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver := by
        intro epId ep hEp
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp
        exact hFreshReceiver epId ep
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId ep hObjInv hMsg hEp)
      have hRecvTailFresh' : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
            (epId' ≠ endpointId →
              ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep'.sendQ.tail ≠ some tailTid) := by
        intro ep tailTid hEp hTail epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp hEp'
        exact hRecvTailFresh ep tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep hObjInv hMsg hEp)
          hTail epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hObjInv hMsg hEp')
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt
        st st1 replyTarget .ready (some msg) hObjInv hMsg
      have hObjInvEns1 : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      exact endpointReceiveDual_preserves_dualQueueSystemInvariant _ _ _ stR.2 stR.1
        hObjInvEns1
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)
        hInv2 hFreshReceiver' hRecvTailFresh'

/-- WS-H5: endpointCall preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointCall_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointCall endpointId caller msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, block caller for reply
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hObjInv hPop hInv
          have hObjInvPop1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hStore1 : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hStore1] at hStep
          | ok st2 =>
            simp only [hStore1] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              pair.2.2 st2 pair.1 .ready (some msg) hObjInvPop1 hStore1 hInv1
            have hObjInvSt2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              pair.2.2 st2 pair.1 .ready (some msg) hObjInvPop1 hStore1
            have hObjInvEns2 : (ensureRunnable st2 pair.1).objects.invExt :=
              ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInvSt2
            have hInv3 := ensureRunnable_preserves_dualQueueSystemInvariant st2 pair.1 hInv2
            cases hStore2 : storeTcbIpcState (ensureRunnable st2 pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hStore2] at hStep
            | ok st3 =>
              simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_dualQueueSystemInvariant _ _
                (storeTcbIpcState_preserves_dualQueueSystemInvariant
                  (ensureRunnable st2 pair.1) st3 caller _ hObjInvEns2 hStore2 hInv3)
      | none =>
        -- Path B: enqueue caller, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 caller
              (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInvEnq := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId false caller st st1 hEnq hInv hObjInv hFreshCaller hSendTailFresh
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt
              endpointId false caller st st1 hObjInv hEnq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInvEnq hStore hInvEnq)

-- ============================================================================
-- WS-H12c/H-03: contextMatchesCurrent preservation for IPC operations
-- ============================================================================

/-- WS-H12c: `storeObject` preserves `contextMatchesCurrent` when the stored
object at the current thread's ID preserves `registerContext`.

Requires `currentThreadValid` to exclude the impossible case where the current
thread has no TCB in the object store. -/
private theorem storeObject_preserves_contextMatchesCurrent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hRegCtx : ∀ tid tcb, st.scheduler.current = some tid → tid.toObjId = oid →
      st.objects[oid]? = some (.tcb tcb) →
      ∃ tcb', obj = .tcb tcb' ∧ tcb'.registerContext = tcb.registerContext) :
    contextMatchesCurrent st' := by
  have hSched : st'.scheduler = st.scheduler := storeObject_scheduler_eq st st' oid obj hStore
  have hMach : st'.machine = st.machine := storeObject_machine_eq st st' oid obj hStore
  unfold contextMatchesCurrent at hInv ⊢; rw [hSched, hMach]
  cases hCur : st.scheduler.current with
  | none => trivial
  | some tid =>
    simp only [hCur] at hInv ⊢
    simp only [currentThreadValid, hCur] at hValid
    obtain ⟨curTcb, hCurTcb⟩ := hValid
    by_cases hEq : tid.toObjId = oid
    · rw [hEq, storeObject_objects_eq st st' oid obj hObjInv hStore]
      obtain ⟨tcb', hNew, hReg⟩ := hRegCtx tid curTcb hCur hEq (hEq ▸ hCurTcb)
      rw [hNew]; simp only []
      simp only [hCurTcb] at hInv; rw [hReg]; exact hInv
    · rw [storeObject_objects_ne st st' oid tid.toObjId obj hEq hObjInv hStore]; exact hInv

/-- WS-H12c: IPC TCB stores preserve `contextMatchesCurrent`. -/
private theorem storeTcbIpcState_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc }, rfl, rfl⟩)

private theorem storeTcbIpcStateAndMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc, pendingMessage := msg }, rfl, rfl⟩)

private theorem storeTcbPendingMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with pendingMessage := msg }, rfl, rfl⟩)

private theorem storeTcbQueueLinks_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    simp only [tcbWithQueueLinks] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }, rfl, rfl⟩)

/-- WS-H12c: `ensureRunnable` preserves `contextMatchesCurrent`. -/
private theorem ensureRunnable_preserves_contextMatchesCurrent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st) :
    contextMatchesCurrent (ensureRunnable st tid) := by
  unfold ensureRunnable
  split
  · exact hInv
  · cases hObj : st.objects[tid.toObjId]? with
    | none => exact hInv
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [contextMatchesCurrent]
        cases hCur : st.scheduler.current with
        | none => trivial
        | some curTid =>
          simp only [contextMatchesCurrent, hCur] at hInv
          exact hInv
      | _ => exact hInv

/-- WS-H12c: `removeRunnable` preserves `contextMatchesCurrent`. -/
private theorem removeRunnable_preserves_contextMatchesCurrent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st) :
    contextMatchesCurrent (removeRunnable st tid) := by
  simp only [removeRunnable]
  show contextMatchesCurrent { st with scheduler := { st.scheduler with
    runQueue := st.scheduler.runQueue.remove tid,
    current := if st.scheduler.current = some tid then none else st.scheduler.current } }
  simp only [contextMatchesCurrent]
  by_cases hEq : st.scheduler.current = some tid
  · simp only [hEq, ite_true]
  · simp only [hEq, ite_false]; exact hInv

-- ============================================================================
-- WS-H12e: allPendingMessagesBounded preservation (frame lemmas)
-- Deferred from WS-H12d — see CHANGELOG v0.14.1 line 77.
-- ============================================================================

/-- WS-H12e: ensureRunnable preserves allPendingMessagesBounded.
ensureRunnable only modifies scheduler state; the object store is unchanged. -/
theorem ensureRunnable_preserves_allPendingMessagesBounded
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (ensureRunnable st tid) := by
  intro t tcb msg hObj hMsg
  rw [ensureRunnable_preserves_objects] at hObj
  exact hInv t tcb msg hObj hMsg

/-- WS-H12e: removeRunnable preserves allPendingMessagesBounded.
removeRunnable only modifies scheduler state; the object store is unchanged. -/
theorem removeRunnable_preserves_allPendingMessagesBounded
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (removeRunnable st tid) := by
  intro t tcb msg hObj hMsg
  rw [removeRunnable_preserves_objects] at hObj
  exact hInv t tcb msg hObj hMsg

/-- WS-H12e: storeTcbIpcState preserves allPendingMessagesBounded.
storeTcbIpcState only changes `ipcState`, not `pendingMessage`. -/
theorem storeTcbIpcState_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre := lookupTcb_some_objects st tid tcb hLookup
          intro t tcb' msg hObj hMsg
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hMsg
            -- pendingMessage is preserved: { tcb with ipcState := ipc }.pendingMessage = tcb.pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeTcbIpcStateAndMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          intro t tcb' m hObj hPend
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeTcbPendingMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbPendingMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          intro t tcb' m hObj hPend
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeObject for endpoint preserves allPendingMessagesBounded.
Endpoints don't carry pending messages, so the TCB predicate is unaffected. -/
theorem storeObject_endpoint_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hObjInv hStore] at hObj
    exact hInv t tcb msg hObjPre hMsg

/-- WS-H12e: storeTcbQueueLinks preserves allPendingMessagesBounded.
Queue link updates only change `queuePrev`/`queueNext`/`queuePPrev`,
not `pendingMessage`. -/
theorem storeTcbQueueLinks_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre := lookupTcb_some_objects st tid tcb hLookup
          intro t tcb' msg hObj hMsg
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp [tcbWithQueueLinks] at hMsg
            -- pendingMessage is preserved: queue link updates don't change pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeObject for notification preserves allPendingMessagesBounded.
Notifications are not TCBs, so no TCB's pendingMessage is affected. -/
theorem storeObject_notification_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.notification ntfn) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hObjInv hStore] at hObj
    exact hInv t tcb msg hObjPre hMsg

-- ============================================================================
-- WS-H12e: Compound operation allPendingMessagesBounded preservation
-- ============================================================================

/-- WS-H12e: notificationSignal preserves allPendingMessagesBounded.
notificationSignal stores a notification object and calls storeTcbIpcState +
ensureRunnable. None of these modify any TCB's pendingMessage. -/
theorem notificationSignal_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
          simp only [hWaiters] at hStep
          revert hStep
          cases hStore : storeObject notificationId
              (.notification { state := if rest.isEmpty then .idle else .waiting,
                               waitingThreads := rest, pendingBadge := none }) st with
          | error e => simp
          | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                st pair.2 notificationId _ hObjInv hStore hInv
              -- R3-A/M-16: storeTcbIpcStateAndMessage replaces storeTcbIpcState
              cases hIpc : storeTcbIpcStateAndMessage pair.2 waiter .ready
                  (some { IpcMessage.empty with badge := some badge }) with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  have hObjInvPair : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                  have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter .ready _
                    (fun m hm => by cases hm; exact IpcMessage.empty_bounded)
                    hObjInvPair hIpc hInv1
                  exact ensureRunnable_preserves_allPendingMessagesBounded st'' waiter hInv2
      | nil =>
          simp only [hWaiters] at hStep
          exact storeObject_notification_preserves_allPendingMessagesBounded
            st st' notificationId _ hObjInv hStep hInv

/-- WS-H12e: notificationWait preserves allPendingMessagesBounded.
notificationWait stores a notification object and calls storeTcbIpcState +
ensureRunnable/removeRunnable. None of these modify any TCB's pendingMessage. -/
theorem notificationWait_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    allPendingMessagesBounded st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
          simp only [hBadge] at hStep
          revert hStep
          cases hStore : storeObject notificationId
              (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
          | error e => simp
          | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                st pair.2 notificationId _ hObjInv hStore hInv
              cases hIpc : storeTcbIpcState pair.2 waiter .ready with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  have hObjInvPair : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                  exact storeTcbIpcState_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter _ hObjInvPair hIpc hInv1
      | none =>
          simp only [hBadge] at hStep
          cases hLk : lookupTcb st waiter with
          | none => simp [hLk] at hStep
          | some tcb =>
              simp only [hLk] at hStep
              split at hStep
              · simp at hStep
              · revert hStep
                cases hStore : storeObject notificationId
                    (.notification { state := .waiting,
                                     waitingThreads := waiter :: ntfn.waitingThreads,
                                     pendingBadge := none }) st with
                | error e => simp
                | ok pair =>
                    simp only []
                    have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
                    simp only [storeTcbIpcState_fromTcb_eq hLk']
                    have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                      st pair.2 notificationId _ hObjInv hStore hInv
                    have hObjInvPairN : pair.2.objects.invExt :=
                      storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                    cases hIpc : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
                    | error e => simp
                    | ok st'' =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have hInv2 := storeTcbIpcState_preserves_allPendingMessagesBounded
                          pair.2 st'' waiter _ hObjInvPairN hIpc hInv1
                        exact removeRunnable_preserves_allPendingMessagesBounded st'' waiter hInv2

/-- WS-H12e: endpointReply preserves allPendingMessagesBounded.
endpointReply bounds-checks the message at entry, then stores it in the target
TCB via storeTcbIpcStateAndMessage with (some msg) where msg.bounded follows
from the entry-point bounds check. -/
theorem endpointReply_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold endpointReply at hStep
  -- WS-H12d: Extract bounds facts, then eliminate branches
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId _ =>
          simp only [hIpc] at hStep
          -- Split on replyTarget: some expected vs none
          split at hStep
          · -- some expected: split on replier == expected
            split at hStep
            · -- authorized = true
              revert hStep
              cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  exact ensureRunnable_preserves_allPendingMessagesBounded st1 target
                    (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                      st st1 target _ _ (by intro m hm; cases hm; exact hMsgBounded)
                      hObjInv hStore hInv)
            · -- authorized = false
              simp_all
          · -- none: no replyTarget constraint → authorized = true
            dsimp only at hStep
            revert hStep
            cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
                simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hStEq⟩; subst hStEq
                exact ensureRunnable_preserves_allPendingMessagesBounded st1 target
                  (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                    st st1 target _ _ (by intro m hm; cases hm; exact hMsgBounded)
                    hObjInv hStore hInv)

-- ============================================================================
-- R3-B: Notification operation dualQueueSystemInvariant preservation
-- ============================================================================

/-- R3-B: notificationSignal preserves dualQueueSystemInvariant.
Wake path: storeObject(.notification) + storeTcbIpcStateAndMessage + ensureRunnable.
Merge path: storeObject(.notification) only. All preserve dual-queue invariant. -/
theorem notificationSignal_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    dualQueueSystemInvariant st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        simp only [hWaiters] at hStep; revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
            st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
          have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            exact ensureRunnable_preserves_dualQueueSystemInvariant st'' waiter
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                pair.2 st'' waiter .ready _ hObjInv1 hTcb hInv1)
      | nil =>
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_dualQueueSystemInvariant
          st st' notificationId _ hObjInv hStep (.inl ⟨ntfn, hObj⟩) hInv

/-- R3-B: notificationWait preserves dualQueueSystemInvariant.
Badge-consume path: storeObject(.notification) + storeTcbIpcState.
Block path: storeObject(.notification) + storeTcbIpcState + removeRunnable. -/
theorem notificationWait_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    dualQueueSystemInvariant st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hPending : ntfn.pendingBadge with
      | some pendBadge =>
        simp only [hPending] at hStep; revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
            st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
          have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            exact storeTcbIpcState_preserves_dualQueueSystemInvariant
              pair.2 st'' waiter .ready hObjInv1 hTcb hInv1
      | none =>
        simp only [hPending] at hStep; revert hStep
        cases hLk : lookupTcb st waiter with
        | none => simp
        | some tcb =>
          simp only []; split
          · simp
          · intro hStep; revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
                st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
              have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                exact removeRunnable_preserves_dualQueueSystemInvariant st'' waiter
                  (storeTcbIpcState_preserves_dualQueueSystemInvariant
                    pair.2 st'' waiter _ hObjInv1 hTcb hInv1)

-- ============================================================================
-- R3-B: Endpoint operation badgeWellFormed preservation
-- Endpoint operations only modify TCB and endpoint objects (never notifications
-- or CNodes), so badge well-formedness is preserved by construction.
-- ============================================================================

/-- R3-B: endpointReply preserves badgeWellFormed.
Calls storeTcbIpcStateAndMessage + ensureRunnable — neither stores a
notification or CNode. -/
theorem endpointReply_preserves_badgeWellFormed
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    badgeWellFormed st' := by
  -- Mirror the structure of endpointReply_preserves_dualQueueSystemInvariant
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId' rt =>
          simp only [hIpc] at hStep
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e =>
              revert hStep; simp only [hStore]; intro hStep
              cases rt with
              | none => simp at hStep
              | some val => dsimp only [] at hStep; split at hStep <;> simp at hStep
          | ok st1 =>
              simp only [hStore] at hStep
              have hInv1 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                st st1 target .ready (some msg) hInv hObjInv hStore
              have hInvER := ensureRunnable_preserves_badgeWellFormed st1 target hInv1
              cases rt with
              | none => simp at hStep; subst hStep; exact hInvER
              | some val =>
                  dsimp only [] at hStep
                  split at hStep
                  · simp at hStep; subst hStep; exact hInvER
                  · simp at hStep

-- ============================================================================
-- R3-C.2/M-19: Endpoint operation notificationWaiterConsistent preservation
-- ============================================================================

/-- R3-C.2/M-19: endpointReply preserves notificationWaiterConsistent.
The target thread has `ipcState = .blockedOnReply`, so by
`notificationWaiterConsistent` it is not in any notification wait list.
`storeTcbIpcStateAndMessage` + `ensureRunnable` therefore do not affect
any notification waiter's TCB. -/
theorem endpointReply_preserves_notificationWaiterConsistent
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    notificationWaiterConsistent st' := by
  -- Unfold endpointReply and extract the storeTcbIpcStateAndMessage + ensureRunnable steps
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
      | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId' rt =>
      simp only [hIpc] at hStep
      cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
      | error e =>
        revert hStep; simp only [hStore]; intro hStep
        cases rt with
        | none => simp at hStep
        | some val => dsimp only [] at hStep; split at hStep <;> simp at hStep
      | ok st1 =>
        simp only [hStore] at hStep
        -- target has .blockedOnReply, so it is not in any notification wait list
        have hTargetNotInWaitList : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
            st.objects[noid]? = some (.notification ntfn) → target ∉ ntfn.waitingThreads := by
          intro noid ntfn hNtfn hMem
          obtain ⟨tcb_w, hTcb_w, hIpc_w⟩ := hConsist noid ntfn target hNtfn hMem
          have hTcbTarget := lookupTcb_some_objects st target tcb hLookup
          rw [hTcb_w] at hTcbTarget; cases hTcbTarget; rw [hIpc_w] at hIpc; cases hIpc
        have hConsist1 := storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent
          st st1 target .ready (some msg) hConsist hObjInv hStore hTargetNotInWaitList
        -- Final state is ensureRunnable st1 target — objects unchanged
        have hSubst : st' = ensureRunnable st1 target := by
          cases rt with
          | none => simp at hStep; exact hStep.symm
          | some val =>
            dsimp only [] at hStep; split at hStep
            · simp at hStep; exact hStep.symm
            · simp at hStep
        subst hSubst
        intro noid ntfn tid hNtfnPost hMem
        have hNtfnSt1 : st1.objects[noid]? = some (.notification ntfn) := by
          rwa [ensureRunnable_preserves_objects] at hNtfnPost
        obtain ⟨tcb', hTcb', hIpc'⟩ := hConsist1 noid ntfn tid hNtfnSt1 hMem
        exact ⟨tcb', by rw [ensureRunnable_preserves_objects]; exact hTcb', hIpc'⟩

-- ============================================================================
-- WS-H12e/R3-B: Composed ipcInvariantFull preservation theorems
-- ============================================================================

/-- R3-B/M-18: notificationSignal preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants — no externalized hypotheses. -/
theorem notificationSignal_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨notificationSignal_preserves_ipcInvariant st st' notificationId badge hInv.1 hObjInv hStep,
   notificationSignal_preserves_dualQueueSystemInvariant st st' notificationId badge hInv.2.1 hObjInv hStep,
   notificationSignal_preserves_allPendingMessagesBounded st st' notificationId badge hInv.2.2.1 hObjInv hStep,
   notificationSignal_preserves_badgeWellFormed st st' notificationId badge hInv.2.2.2 hObjInv hStep⟩

/-- R3-B/M-18: notificationWait preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants — no externalized hypotheses. -/
theorem notificationWait_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariantFull st' :=
  ⟨notificationWait_preserves_ipcInvariant st st' notificationId waiter result hInv.1 hObjInv hStep,
   notificationWait_preserves_dualQueueSystemInvariant st st' notificationId waiter result hInv.2.1 hObjInv hStep,
   notificationWait_preserves_allPendingMessagesBounded st st' notificationId waiter result hInv.2.2.1 hObjInv hStep,
   notificationWait_preserves_badgeWellFormed st st' notificationId waiter result hInv.2.2.2 hObjInv hStep⟩

/-- R3-B/M-18: endpointReply preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants. -/
theorem endpointReply_preserves_ipcInvariantFull
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReply_preserves_ipcInvariant st st' replier target msg hInv.1 hObjInv hStep,
   endpointReply_preserves_dualQueueSystemInvariant replier target msg st st' hObjInv hStep hInv.2.1,
   endpointReply_preserves_allPendingMessagesBounded st st' replier target msg hInv.2.2.1 hObjInv hStep,
   endpointReply_preserves_badgeWellFormed st st' replier target msg hInv.2.2.2 hObjInv hStep⟩

/-- R3-B/M-18: endpointSendDual preserves the full IPC invariant.
`dualQueueSystemInvariant`, `allPendingMessagesBounded`, and `badgeWellFormed` remain
caller-supplied: the dual-queue theorem requires freshness preconditions (the sender
must not already be in any endpoint queue), and the bounds/badge come from the user-
provided message at the API entry point. -/
theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDual_preserves_ipcInvariant st st' endpointId sender msg hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- R3-B/M-18: endpointReceiveDual preserves the full IPC invariant. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDual_preserves_ipcInvariant st st' endpointId receiver senderId hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- R3-B/M-18: endpointCall preserves the full IPC invariant. -/
theorem endpointCall_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointCall_preserves_ipcInvariant st st' endpointId caller msg hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- WS-H12e: endpointReplyRecv preserves the full IPC invariant. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReplyRecv_preserves_ipcInvariant st st' endpointId receiver replyTarget msg hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- T4-K (L-P10): Convenience theorem for composing `ipcInvariantFull` from its
four individual components. Reduces boilerplate for callers that must manually
compose the invariant by providing all four proofs in one call. -/
theorem ipcInvariantFull_compositional
    (st : SystemState)
    (hIpc : ipcInvariant st)
    (hDual : dualQueueSystemInvariant st)
    (hBounded : allPendingMessagesBounded st)
    (hBadge : badgeWellFormed st) :
    ipcInvariantFull st :=
  ⟨hIpc, hDual, hBounded, hBadge⟩

-- ============================================================================
-- T4-E/F (M-IPC-3): WithCaps wrappers preserve ipcInvariantFull
-- ============================================================================

/-- T4-E (M-IPC-3): endpointSendDualWithCaps preserves the full IPC invariant.
Composes the proven ipcInvariant preservation with caller-supplied proofs for
the remaining three sub-invariants. -/
theorem endpointSendDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDualWithCaps_preserves_ipcInvariant endpointId sender msg
     endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- T4-F (M-IPC-3): endpointReceiveDualWithCaps preserves the full IPC invariant.
Same composition pattern as T4-E for the receive path. -/
theorem endpointReceiveDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReceiveDualWithCaps endpointId receiver endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDualWithCaps_preserves_ipcInvariant endpointId receiver endpointRights
     receiverCspaceRoot receiverSlotBase st st' senderId summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- T4-E (M-IPC-3): endpointCallWithCaps preserves the full IPC invariant. -/
theorem endpointCallWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointCallWithCaps_preserves_ipcInvariant endpointId caller msg
     endpointRights callerCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge'⟩

-- ============================================================================
-- WS-L3/L3-B: Standalone tcbQueueLinkIntegrity preservation
-- ============================================================================

/-- WS-L3/L3-B1: PopHead preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueuePopHead_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueuePopHead_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ st st' tid hObjInv hStep hInv).2.1

/-- WS-L3/L3-B2: Enqueue preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : dualQueueSystemInvariant st)
    (hFreshTid : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some enqueueTid ∧ ep.sendQ.tail ≠ some enqueueTid ∧
      ep.receiveQ.head ≠ some enqueueTid ∧ ep.receiveQ.tail ≠ some enqueueTid)
    (hTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          (if isReceiveQ then ep'.sendQ else ep'.receiveQ).tail ≠ some tailTid)) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueueEnqueue_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ enqueueTid st st' hStep hInv hObjInv hFreshTid hTailFresh).2.1

-- ============================================================================
-- WS-L3/L3-C2: ipcStateQueueConsistent preservation for queue operations
-- ============================================================================

/-- WS-L3/L3-C2: PopHead preserves ipcStateQueueConsistent. PopHead does not
modify any thread's ipcState and preserves all endpoints, so the forward
implication (blocked → endpoint exists) is maintained. -/
theorem endpointQueuePopHead_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  -- Step 1: find the pre-state TCB with same ipcState
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueuePopHead_tcb_ipcState_backward
    endpointId isReceiveQ st st' tid tid' tcb' hObjInv hStep hTcb'
  -- Step 2: apply pre-state invariant
  have hPre := hInv tid' tcb hTcb
  -- Step 3: show endpoints survive the operation
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp

/-- WS-L3/L3-C2: Enqueue preserves ipcStateQueueConsistent. Enqueue does not
modify any thread's ipcState and preserves all endpoints. -/
theorem endpointQueueEnqueue_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueueEnqueue_tcb_ipcState_backward
    endpointId isReceiveQ enqueueTid st st' tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — sub-operation helpers
-- ============================================================================

/-- WS-L3/L3-C3 helper: `ensureRunnable` preserves `ipcStateQueueConsistent`.
`ensureRunnable` only modifies the scheduler (run queue), not objects. -/
theorem ensureRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (ensureRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [ensureRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `removeRunnable` preserves `ipcStateQueueConsistent`.
`removeRunnable` only modifies the scheduler, not objects. -/
theorem removeRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (removeRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [removeRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `storeTcbIpcStateAndMessage` preserves
`ipcStateQueueConsistent` when the new ipcState satisfies the invariant
obligation in the pre-state. Specifically:
- If ipc = blockedOnSend/Receive/Call epId, then the endpoint at epId
  must exist in the pre-state (the operation preserves it).
- If ipc = ready/blockedOnReply/blockedOnNotification, no obligation. -/
theorem storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · -- Target TCB: ipcState was set to `ipc`
    have hIpcEq := storeTcbIpcStateAndMessage_ipcState_eq st st' tid ipc msg hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
  · -- Non-target TCB: object unchanged, pre-state invariant applies
    have hObjEq := storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbIpcState` preserves `ipcStateQueueConsistent`
under the same conditions as `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcState_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · have hIpcEq := storeTcbIpcState_ipcState_eq st st' tid ipc hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
  · have hObjEq := storeTcbIpcState_preserves_objects_ne st st' tid ipc tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbPendingMessage` preserves
`ipcStateQueueConsistent`. This operation only changes pendingMessage,
not ipcState, so the invariant is trivially preserved. -/
theorem storeTcbPendingMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := storeTcbPendingMessage_tcb_ipcState_backward st st' tid msg tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — high-level IPC ops
-- ============================================================================

/-- WS-L3/L3-C3: endpointSendDual preserves ipcStateQueueConsistent.
Handshake path: PopHead (preserves) → storeTcbIpcStateAndMessage to .ready
(removes obligation) → ensureRunnable (preserves).
Blocking path: Enqueue (preserves) → storeTcbIpcStateAndMessage to
.blockedOnSend endpointId (endpoint exists from initial lookup) →
removeRunnable (preserves). -/
theorem endpointSendDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvPop : stPop.objects.invExt :=
              endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg
                (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                  hObjInv hPop hInv) trivial
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false sender st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ sender st st1 endpointId ep hObjInv hEnq hObj)

/-- WS-L3/L3-C3: endpointReceiveDual preserves ipcStateQueueConsistent.
Rendezvous (call): PopHead → storeTcbIpcStateAndMessage(.blockedOnReply, trivial)
→ storeTcbPendingMessage (preserves).
Rendezvous (send): PopHead → storeTcbIpcStateAndMessage(.ready, trivial) →
ensureRunnable → storeTcbPendingMessage (preserves).
Blocking: Enqueue → storeTcbIpcState(.blockedOnReceive epId, endpoint exists)
→ removeRunnable (preserves). -/
theorem endpointReceiveDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver resultTid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (resultTid, st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨sender, senderTcb, stPop⟩ := triple
          have hObjInvPop : stPop.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st stPop sender senderTcb hObjInv hPop
          have hInvPop := endpointQueuePopHead_preserves_ipcStateQueueConsistent
            endpointId false st stPop sender senderTcb hObjInv hPop hInv
          -- Branch on senderWasCall
          split at hStep
          · -- Call path: storeTcbIpcStateAndMessage(.blockedOnReply) → storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage stPop sender (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              cases hPM : storeTcbPendingMessage st2 receiver senderTcb.pendingMessage with
              | error e => simp [hPM] at hStep
              | ok st3 =>
                simp only [hPM] at hStep
                have hEq : st3 = st' := by
                  have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                subst hEq
                have hObjInvMsg : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
                exact storeTcbPendingMessage_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvMsg hPM
                  (storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial)
          · -- Send path: storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage stPop sender .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              cases hPM : storeTcbPendingMessage (ensureRunnable st2 sender) receiver senderTcb.pendingMessage with
              | error e => simp [hPM] at hStep
              | ok st3 =>
                simp only [hPM] at hStep
                have hEq : st3 = st' := by
                  have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                subst hEq
                have hObjInvMsgS : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
                have hObjInvEns : (ensureRunnable st2 sender).objects.invExt :=
                  ensureRunnable_preserves_objects st2 sender ▸ hObjInvMsgS
                exact storeTcbPendingMessage_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvEns hPM
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _
                    (storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial))
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvEnqR : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvEnqR hIpc
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId true receiver st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ receiver st st1 endpointId ep hObjInv hEnq hObj)

/-- WS-L3/L3-C3: endpointReply preserves ipcStateQueueConsistent.
Reply sets target from blockedOnReply to .ready (removes obligation),
then ensureRunnable (preserves). The _fromTcb variant is rewritten to
the standard form via the equivalence theorem. -/
theorem endpointReply_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      -- Rewrite _fromTcb to standard form
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- Resolve authorization check first (split match replyTarget, then if)
      split at hStep
      · -- replyTarget = some expected
        split at hStep
        · -- authorized = true: now hStep has the store match
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep
            have hEq := (Prod.mk.inj (Except.ok.inj hStep)).2; rw [← hEq]
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
        · -- authorized = false → error
          simp at hStep
      · -- replyTarget = none: authorized = true directly
        cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
        | error e => simp [hStore] at hStep
        | ok st2 =>
          simp only [hStore] at hStep
          have hEq := (Prod.mk.inj (Except.ok.inj hStep)).2; rw [← hEq]
          exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
            storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpc] at hStep

-- ============================================================================
-- T4-A/B/C (M-IPC-1): ipcStateQueueConsistent preservation for compound ops
-- ============================================================================

/-- T4-A (M-IPC-1): storeObject on a notification preserves ipcStateQueueConsistent.
Notification objects are neither TCBs nor endpoints, so the invariant—which only
queries TCB ipcState and endpoint existence—is trivially preserved. -/
private theorem storeObject_notification_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : ∃ ntfn', st.objects[nid]? = some (.notification ntfn'))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn) st = .ok ((), st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid tcb hTcb
  have hNeTcb : tid.toObjId ≠ nid := by
    intro h; obtain ⟨n', hn'⟩ := hNtfn
    rw [h, storeObject_objects_eq st st' nid _ hObjInv hStore] at hTcb; cases hTcb
  rw [storeObject_objects_ne st st' nid tid.toObjId _ hNeTcb hObjInv hStore] at hTcb
  have hOrig := hInv tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnReceive epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnCall epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | ready | blockedOnReply _ _ | blockedOnNotification _ => trivial

/-- T4-C (M-IPC-1): notificationSignal preserves ipcStateQueueConsistent.
Signal either wakes a waiter (→ .ready, trivial) or accumulates a badge
(notification-only update, no TCB ipcState change). -/
theorem notificationSignal_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject (notification) → storeTcbIpcStateAndMessage (waiter, .ready) → ensureRunnable
        simp only [hWaiters] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          generalize hMsg : storeTcbIpcStateAndMessage pair1.2 waiter .ready _ = rMsg at hStep
          cases rMsg with
          | error e => simp at hStep
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv1 hMsg
                (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                  ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | nil =>
        -- Accumulate path: storeObject (notification) only
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_ipcStateQueueConsistent st st' notificationId _
          ⟨ntfn, hObj⟩ hObjInv hStep hInv

/-- T4-C (M-IPC-1): notificationWait preserves ipcStateQueueConsistent.
Wait either consumes a pending badge (→ .ready, trivial) or blocks the waiter
on the notification (→ .blockedOnNotification, which is _ => True). -/
theorem notificationWait_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (result : Option SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume path: storeObject (notification) → storeTcbIpcState (waiter, .ready)
        simp only [hBadge] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          cases hIpc : storeTcbIpcState pair1.2 waiter .ready with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨rfl, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
              (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | none =>
        -- Block path: lookupTcb → storeObject (notification) → storeTcbIpcState_fromTcb (.blockedOnNotification) → removeRunnable
        simp only [hBadge] at hStep
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep -- already waiting → error
          · generalize hStore1 : storeObject notificationId _ st = r1 at hStep
            cases r1 with
            | error e => simp at hStep
            | ok pair1 =>
              simp only [] at hStep
              have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
              have hNe : waiter.toObjId ≠ notificationId := by
                intro h; rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
              have hTcbObj' : pair1.2.objects[waiter.toObjId]? = some (.tcb tcb) := by
                rw [storeObject_objects_ne st pair1.2 notificationId waiter.toObjId _ hNe hObjInv hStore1]
                exact hTcbObj
              have hLookup' : lookupTcb pair1.2 waiter = some tcb := by
                unfold lookupTcb; split
                · -- isReserved: contradiction (original lookupTcb succeeded so not reserved)
                  rename_i hRes
                  unfold lookupTcb at hLookup; simp [hRes] at hLookup
                · rw [hTcbObj']
              rw [storeTcbIpcState_fromTcb_eq hLookup'] at hStep
              cases hIpc : storeTcbIpcState pair1.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp [hIpc] at hStep
              | ok st2 =>
                simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨rfl, rfl⟩ := hStep
                have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                  storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
                    (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                      ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial

/-- T4-A (M-IPC-1): endpointCall preserves ipcStateQueueConsistent.
The handshake path sets receiver to .ready (trivial) and caller to .blockedOnReply
(falls under _ => True). The blocking path sets caller to .blockedOnCall with
an endpoint existence obligation discharged by endpointQueueEnqueue_endpoint_forward. -/
theorem endpointCall_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: PopHead → storeTcbIpcStateAndMessage(receiver, .ready) → ensureRunnable →
        --                 storeTcbIpcState(caller, .blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 receiver _ _ hObjInvPop hMsg
            have hObjInvEns := ensureRunnable_preserves_objects st2 receiver ▸ hObjInvMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 receiver) caller (.blockedOnReply endpointId (some receiver)) with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvEns hIpc
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
                    storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg
                      (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                        hObjInv hPop hInv) trivial) trivial
      | none =>
        -- Blocking path: Enqueue → storeTcbIpcStateAndMessage(caller, .blockedOnCall) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false caller st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ caller st st1 endpointId ep hObjInv hEnq hObj)

/-- T4-B (M-IPC-1): endpointReplyRecv preserves ipcStateQueueConsistent.
ReplyRecv first replies (target → .ready, trivial obligation), then enters
the full endpointReceiveDual path, which has proven preservation. -/
theorem endpointReplyRecv_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpcS : tcb.ipcState with
    | blockedOnReply epId replyTarget' =>
      simp only [hIpcS] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- Resolve authorization
      split at hStep
      · -- replyTarget' = some expected
        split at hStep
        · -- authorized
          cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
            have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
            have hObjInvEns := ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
            have hInvEns := ensureRunnable_preserves_ipcStateQueueConsistent st1 replyTarget hInv1
            -- endpointReceiveDual on ensured state
            generalize hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = rRecv at hStep
            cases rRecv with
            | error e => simp at hStep
            | ok pair =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_preserves_ipcStateQueueConsistent _ _ _ _ pair.1 hInvEns hObjInvEns hRecv
        · simp at hStep -- unauthorized → error
      · -- replyTarget' = none (authorized unconditionally)
        cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
        | error e => simp [hStore] at hStep
        | ok st1 =>
          simp only [hStore] at hStep
          have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
          have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
          have hObjInvEns := ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
          have hInvEns := ensureRunnable_preserves_ipcStateQueueConsistent st1 replyTarget hInv1
          generalize hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = rRecv at hStep
          cases rRecv with
          | error e => simp at hStep
          | ok pair =>
            have hEq := Except.ok.inj hStep; obtain ⟨_, rfl⟩ := Prod.mk.inj hEq
            exact endpointReceiveDual_preserves_ipcStateQueueConsistent _ _ _ _ pair.1 hInvEns hObjInvEns hRecv
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpcS] at hStep

-- ============================================================================
-- M3-E4: dualQueueSystemInvariant preservation for WithCaps wrappers
-- ============================================================================

/-- M3-E4: ipcUnwrapCaps preserves dualQueueSystemInvariant.
ipcUnwrapCaps only modifies CNode objects and CDT — endpoint objects, TCB objects
(queue links), and scheduler state are all preserved. The CNode precondition is
established by `lookupCspaceRoot` which verifies receiverRoot is a CNode. -/
theorem ipcUnwrapCaps_preserves_dualQueueSystemInvariant
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode) (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    dualQueueSystemInvariant st' := by
  -- receiverRoot stays CNode throughout the operation
  have ⟨cn', hCn'⟩ := ipcUnwrapCaps_preserves_cnode_at_root msg senderRoot receiverRoot
    slotBase grantRight st st' summary cn hCn hObjInv hStep
  obtain ⟨hEpWf, hLink, hAcyclic⟩ := hInv
  -- Helper: transfer TCB preservation from st to st' for any oid
  have tcbTransfer : ∀ (oid : SeLe4n.ObjId) (tcb : TCB),
      st.objects[oid]? = some (KernelObject.tcb tcb) →
      st'.objects[oid]? = some (KernelObject.tcb tcb) :=
    fun oid tcb h => ipcUnwrapCaps_preserves_tcb_objects msg senderRoot receiverRoot slotBase
      grantRight st st' summary oid tcb h hObjInv hStep
  -- Helper: transfer object identity from st' to st for non-receiverRoot
  have objBack : ∀ oid, oid ≠ receiverRoot →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid hNe => ipcUnwrapCaps_preserves_objects_ne msg senderRoot receiverRoot slotBase
      grantRight st st' summary oid hNe hObjInv hStep
  have hLinkFwd := hLink.1
  have hLinkBwd := hLink.2
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: endpoint well-formedness
  · intro epId ep hEpSt'
    -- ep is the same in st (receiverRoot is CNode, can't be endpoint)
    have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
      by_cases hNe : epId = receiverRoot
      · subst hNe; simp [hCn'] at hEpSt'
      · rw [objBack epId hNe] at hEpSt'; exact hEpSt'
    -- dualQueueEndpointWellFormed in st, reduced via hEpPre
    have hWf := hEpWf epId ep hEpPre
    unfold dualQueueEndpointWellFormed at hWf ⊢
    simp only [hEpPre] at hWf; simp only [hEpSt']
    -- hWf : intrusiveQueueWellFormed ep.sendQ st ∧ intrusiveQueueWellFormed ep.receiveQ st
    -- Goal: intrusiveQueueWellFormed ep.sendQ st' ∧ intrusiveQueueWellFormed ep.receiveQ st'
    obtain ⟨⟨hS1, hS2, hS3⟩, ⟨hR1, hR2, hR3⟩⟩ := hWf
    exact ⟨⟨hS1, fun hd hHead => by
        obtain ⟨tcb, hTcb, hPrev⟩ := hS2 hd hHead
        exact ⟨tcb, tcbTransfer _ _ hTcb, hPrev⟩,
      fun tl hTail => by
        obtain ⟨tcb, hTcb, hNext⟩ := hS3 tl hTail
        exact ⟨tcb, tcbTransfer _ _ hTcb, hNext⟩⟩,
    ⟨hR1, fun hd hHead => by
        obtain ⟨tcb, hTcb, hPrev⟩ := hR2 hd hHead
        exact ⟨tcb, tcbTransfer _ _ hTcb, hPrev⟩,
      fun tl hTail => by
        obtain ⟨tcb, hTcb, hNext⟩ := hR3 tl hTail
        exact ⟨tcb, tcbTransfer _ _ hTcb, hNext⟩⟩⟩
  -- Part 2: TCB queue link integrity (forward + backward)
  · constructor
    · intro a tcbA hTcbA' b hNext
      have hTcbAPre : st.objects[a.toObjId]? = some (.tcb tcbA) := by
        by_cases hNe : a.toObjId = receiverRoot
        · subst hNe; simp [hCn'] at hTcbA'
        · rw [objBack _ hNe] at hTcbA'; exact hTcbA'
      obtain ⟨tcbB, hTcbB, hPrev⟩ := hLinkFwd a tcbA hTcbAPre b hNext
      exact ⟨tcbB, tcbTransfer _ _ hTcbB, hPrev⟩
    · intro b tcbB hTcbB' a hPrev
      have hTcbBPre : st.objects[b.toObjId]? = some (.tcb tcbB) := by
        by_cases hNe : b.toObjId = receiverRoot
        · subst hNe; simp [hCn'] at hTcbB'
        · rw [objBack _ hNe] at hTcbB'; exact hTcbB'
      obtain ⟨tcbA, hTcbA, hNext⟩ := hLinkBwd b tcbB hTcbBPre a hPrev
      exact ⟨tcbA, tcbTransfer _ _ hTcbA, hNext⟩
  -- Part 3: TCB queue chain acyclicity (only CNode at receiverRoot changes, not TCBs)
  · have hTransfer : ∀ a b, QueueNextPath st' a b → QueueNextPath st a b := by
      intro a b hp
      induction hp with
      | single x y tcbX hObj hNext =>
        have hObjPre : st.objects[x.toObjId]? = some (.tcb tcbX) := by
          by_cases hNe : x.toObjId = receiverRoot
          · subst hNe; simp [hCn'] at hObj
          · rw [objBack _ hNe] at hObj; exact hObj
        exact .single x y tcbX hObjPre hNext
      | cons x y z tcbX hObj hNext _ ih =>
        have hObjPre : st.objects[x.toObjId]? = some (.tcb tcbX) := by
          by_cases hNe : x.toObjId = receiverRoot
          · subst hNe; simp [hCn'] at hObj
          · rw [objBack _ hNe] at hObj; exact hObj
        exact .cons x y z tcbX hObjPre hNext ih
    intro t hp; exact hAcyclic t (hTransfer t t hp)

/-- M3-E4: endpointSendDualWithCaps preserves dualQueueSystemInvariant.
Composes endpointSendDual base preservation with ipcUnwrapCaps preservation.
The CNode precondition requires that when immediate rendezvous occurs, the
receiver's cspaceRoot points to an actual CNode in the intermediate state. -/
theorem endpointSendDualWithCaps_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : dualQueueSystemInvariant st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCnodeRoot : ∀ (stMid : SystemState) (recvRoot : SeLe4n.ObjId),
      endpointSendDual endpointId sender msg st = .ok ((), stMid) →
      ∃ cn, stMid.objects[recvRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
              senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    dualQueueSystemInvariant st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    simp only [hSend] at hStep
    have hInvMid := endpointSendDual_preserves_dualQueueSystemInvariant endpointId sender msg
      st stMid hObjInv hSend hInv hFreshSender hSendTailFresh
    have hObjInvMid : stMid.objects.invExt :=
      endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    -- All paths either return stMid directly or go through ipcUnwrapCaps
    -- Case-split on the objects to determine hasReceiver before touching hStep
    cases hObj : st.objects[endpointId]? with
    | none =>
      simp [hObj] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
    | some obj =>
      cases obj with
      | endpoint ep =>
        cases hHead : ep.receiveQ.head with
        | none =>
          simp [hObj, hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
        | some receiverId =>
          -- hasReceiver = true, guard = msg.caps.isEmpty
          by_cases hEmpty : msg.caps.isEmpty = true
          · simp [hObj, hHead, hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
          · -- Cap transfer path
            simp [hObj, hHead, hEmpty] at hStep
            cases hLookup : lookupCspaceRoot stMid receiverId with
            | none => simp [hLookup] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
            | some recvRoot =>
              simp only [hLookup] at hStep
              obtain ⟨cn, hCn⟩ := hCnodeRoot stMid recvRoot hSend
              exact ipcUnwrapCaps_preserves_dualQueueSystemInvariant msg senderCspaceRoot
                recvRoot receiverSlotBase _ stMid st' summary cn hCn hInvMid hObjInvMid hStep
      | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
        simp [hObj] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid

/-- M3-E4: endpointReceiveDualWithCaps preserves dualQueueSystemInvariant.
Composes endpointReceiveDual base preservation with ipcUnwrapCaps preservation. -/
theorem endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (summary : CapTransferSummary)
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hCnodeRoot : ∀ (stMid : SystemState),
      endpointReceiveDual endpointId receiver st = .ok (senderId, stMid) →
      ∃ cn, stMid.objects[receiverCspaceRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDualWithCaps endpointId receiver endpointRights
              receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    dualQueueSystemInvariant st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    simp only [hRecv] at hStep
    have hInvMid := endpointReceiveDual_preserves_dualQueueSystemInvariant endpointId receiver
      st stMid sid hObjInv hRecv hInv hFreshReceiver hRecvTailFresh
    have hObjInvMid : stMid.objects.invExt :=
      endpointReceiveDual_preserves_objects_invExt st stMid endpointId receiver sid hObjInv hRecv
    -- All paths return stMid (invariant holds) or go through ipcUnwrapCaps (compose)
    cases hTcb : stMid.objects[receiver.toObjId]? with
    | none => simp [hTcb] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
    | some obj =>
      simp only [hTcb] at hStep
      cases obj with
      | tcb receiverTcb =>
        cases hMsg : receiverTcb.pendingMessage with
        | none => simp [hMsg] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
        | some msg =>
          simp only [hMsg] at hStep
          by_cases hEmpty : msg.caps.isEmpty
          · simp [hEmpty] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
          · simp [hEmpty] at hStep
            -- U-H13: match on lookupCspaceRoot — none returns error, some proceeds
            cases hLookup : lookupCspaceRoot stMid sid with
            | none =>
              -- Missing CSpace root returns error, contradicting .ok
              simp only [hLookup] at hStep; contradiction
            | some senderRoot =>
              simp only [hLookup] at hStep
              -- ipcUnwrapCaps path
              split at hStep
              · -- ipcUnwrapCaps errored — contradiction with hStep : ... = .ok
                exact absurd hStep (by simp)
              · -- ipcUnwrapCaps succeeded
                rename_i hUnwrapResult
                obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep
                obtain ⟨cn, hCn⟩ := hCnodeRoot stMid hRecv
                exact ipcUnwrapCaps_preserves_dualQueueSystemInvariant msg _ receiverCspaceRoot
                  receiverSlotBase _ stMid _ _ cn hCn hInvMid hObjInvMid hUnwrapResult
      | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
        obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid

theorem endpointQueueRemoveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold endpointQueueRemoveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
        have hNeEpTid : endpointId ≠ tid.toObjId :=
          fun h => by rw [h] at hObj; rw [hTcbObj] at hObj; cases hObj
        have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
          fun t h => by rw [hObj] at h; cases h
        have hEpWf := hEpInv endpointId ep hObj
        unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
        cases hPPrev : tcb.queuePPrev with
        | none => simp [hPPrev] at hStep
        | some pprev =>
          simp only [hPPrev] at hStep
          -- isNone guard
          generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q at hStep
          split at hStep
          · simp at hStep
          · rename_i hNotIsNone
            -- pprevConsistent guard
            cases pprev with
            | endpointHead =>
              simp only [] at hStep
              split at hStep
              · simp at hStep
              · -- pprevConsistent passed: q.head = some tid ∧ tcb.queuePrev.isNone
                rename_i hConsist
                -- applyPrev: storeObject endpointId ep' st → st1
                cases hStoreEp1 : storeObject endpointId
                    (.endpoint (if isReceiveQ then { ep with receiveQ := { head := tcb.queueNext, tail := q.tail } }
                     else { ep with sendQ := { head := tcb.queueNext, tail := q.tail } })) st with
                | error e => simp [hStoreEp1] at hStep
                | ok pair1 =>
                  simp only [hStoreEp1] at hStep
                  -- Extract guard facts from pprevConsistent
                  have hQHeadTid : q.head = some tid := by simp_all
                  have hPrevNone : tcb.queuePrev = none := by simp_all
                  have hWfQ : intrusiveQueueWellFormed q st := by rw [← hQ]; cases isReceiveQ <;> simp_all
                  obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
                  obtain ⟨_, hTcbH, hPrevNone'⟩ := hHdBnd tid hQHeadTid
                  rw [hTcbObj] at hTcbH; cases hTcbH
                  -- Now case-split on tcb.queueNext (Path A vs Path B)
                  cases hNext : tcb.queueNext with
                  | none =>
                    -- PATH A: sole element removal (endpointHead, queueNext=none)
                    simp only [hNext, hQHeadTid] at hStep
                    generalize hStoreEp2 : storeObject endpointId _ pair1.2 = rEp2 at hStep
                    cases rEp2 with
                    | error e => simp at hStep
                    | ok pair3 =>
                      simp only [] at hStep
                      generalize hClear : storeTcbQueueLinks pair3.2 tid none none none = rCl at hStep
                      cases rCl with
                      | error e => simp at hStep
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                        obtain ⟨_, rfl⟩ := hStep
                        have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStoreEp1
                        have hObjInv3 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair3 hObjInv1 hStoreEp2
                        have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                          st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp hLink
                        have hPreEp2 : ∀ t : TCB, pair1.2.objects[endpointId]? ≠ some (.tcb t) := by
                          intro t h; rw [storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                        have hLink2 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                          pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 hLink1
                        have hTransport : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                            pair3.2.objects[x.toObjId]? = some (.tcb t) →
                            st.objects[x.toObjId]? = some (.tcb t) := by
                          intro x t h
                          have h1 : pair1.2.objects[x.toObjId]? = some (.tcb t) := by
                            by_cases hx : x.toObjId = endpointId
                            · rw [hx, storeObject_objects_eq pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2] at h; cases h
                            · rwa [storeObject_objects_ne pair1.2 pair3.2 endpointId x.toObjId _ hx hObjInv1 hStoreEp2] at h
                          by_cases hx : x.toObjId = endpointId
                          · rw [hx, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h1; cases h1
                          · rwa [storeObject_objects_ne st pair1.2 endpointId x.toObjId _ hx hObjInv hStoreEp1] at h1
                        have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                            pair3.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid := by
                          intro a tA hA hN
                          obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTransport a tA hA) tid hN
                          rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                        have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                            pair3.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some tid := by
                          intro b tB hB hP
                          obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTransport b tB hB) tid hP
                          rw [hTcbObj] at hA; cases hA; rw [hNext] at hN; exact absurd hN (by simp)
                        -- Acyclicity chain
                        have hAcycEp1 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                          st pair1.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp1 hAcyclic
                        have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                          pair1.2 pair3.2 endpointId _ (fun _ h => by cases h) hObjInv1 hStoreEp2 hAcycEp1
                        refine ⟨?_, storeTcbQueueLinks_clearing_preserves_linkInteg
                          pair3.2 st4 tid hObjInv3 hClear hLink2 hNoFwd hNoRev,
                          storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                          pair3.2 st4 tid none none hObjInv3 hClear hAcycEp3⟩
                        intro epId' ep' hObj'
                        have hObj1 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                          epId' ep' hObjInv3 hClear hObj'
                        unfold dualQueueEndpointWellFormed; rw [hObj']
                        by_cases hNe : epId' = endpointId
                        · rw [hNe] at hObj1
                          rw [storeObject_objects_eq pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2] at hObj1
                          cases hObj1
                          cases hRQ : isReceiveQ
                          · exact ⟨intrusiveQueueWellFormed_empty st4,
                              storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                                ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hEpWf.2))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                          · exact ⟨storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                                ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hEpWf.1))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                              intrusiveQueueWellFormed_empty st4⟩
                        · have hObjSt1 : pair1.2.objects[epId']? = some (.endpoint ep') := by
                            rwa [storeObject_objects_ne pair1.2 pair3.2 endpointId epId' _ hNe hObjInv1 hStoreEp2] at hObj1
                          have hObjSt : st.objects[epId']? = some (.endpoint ep') := by
                            rwa [storeObject_objects_ne st pair1.2 endpointId epId' _ hNe hObjInv hStoreEp1] at hObjSt1
                          have hWfPre := hEpInv epId' ep' hObjSt
                          unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt] at hWfPre
                          exact ⟨storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                              ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hWfPre.1))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                            storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                              ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hWfPre.2))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                  | some nextTid =>
                    -- PATH B: head removal with successor (endpointHead, queueNext=some nextTid)
                    simp only [hNext] at hStep
                    -- st2Result: lookupTcb pair1.2 nextTid → storeTcbQueueLinks
                    cases hLkN : lookupTcb pair1.2 nextTid with
                    | none => simp [hLkN] at hStep
                    | some nextTcb =>
                      simp only [hLkN] at hStep
                      generalize hStN : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext = rStN at hStep
                      cases rStN with
                      | error e => simp at hStep
                      | ok st2 =>
                        simp only [hQHeadTid] at hStep
                        generalize hStoreEp2 : storeObject endpointId _ st2 = rEp2 at hStep
                        cases rEp2 with
                        | error e => simp at hStep
                        | ok pair3 =>
                          simp only [] at hStep
                          generalize hClear : storeTcbQueueLinks pair3.2 tid none none none = rCl at hStep
                          cases rCl with
                          | error e => simp at hStep
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                            obtain ⟨_, rfl⟩ := hStep
                            -- Key intermediate facts
                            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStoreEp1
                            have hTransport1 : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                pair1.2.objects[x.toObjId]? = some (.tcb t) →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t h; by_cases hx : x.toObjId = endpointId
                              · rw [hx, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                              · rwa [storeObject_objects_ne st pair1.2 endpointId x.toObjId _ hx hObjInv hStoreEp1] at h
                            have hNeEpNext : endpointId ≠ nextTid.toObjId := by
                              intro h; have := lookupTcb_some_objects pair1.2 nextTid nextTcb hLkN
                              rw [← h, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at this; cases this
                            have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) :=
                              hTransport1 nextTid nextTcb (lookupTcb_some_objects pair1.2 nextTid nextTcb hLkN)
                            have hNextPrevB : nextTcb.queuePrev = some tid := by
                              obtain ⟨_, hB, hP⟩ := hLink.1 tid tcb hTcbObj nextTid hNext
                              rw [hNextTcbSt] at hB; cases hB; exact hP
                            have hNeHN : tid.toObjId ≠ nextTid.toObjId := by
                              intro h; have hEq : st.objects[nextTid.toObjId]? = some (.tcb tcb) := h ▸ hTcbObj
                              rw [hNextTcbSt] at hEq; cases hEq; rw [hPrevNone] at hNextPrevB; exact absurd hNextPrevB (by simp)
                            have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                              st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp hLink
                            have hObjInvSt2 := storeTcbQueueLinks_preserves_objects_invExt
                              pair1.2 st2 nextTid _ _ _ hObjInv1 hStN
                            have hPreEp2 : ∀ t : TCB, st2.objects[endpointId]? ≠ some (.tcb t) := by
                              intro t h
                              rw [storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                endpointId hNeEpNext hObjInv1 hStN,
                                storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                            have hObjInv3 := storeObject_preserves_objects_invExt' st2 endpointId _ pair3 hObjInvSt2 hStoreEp2
                            -- nextTid result in st2
                            have hNextResultB := storeTcbQueueLinks_result_tcb pair1.2 st2 nextTid _ _ _ hObjInv1 hStN
                            obtain ⟨origNextB, hOrigLkB, hNextSt2B⟩ := hNextResultB
                            rw [hLkN] at hOrigLkB; cases hOrigLkB
                            rw [hPrevNone] at hNextSt2B
                            -- nextTid in pair3.2 (preserved through storeObject)
                            have hNS3 : pair3.2.objects[nextTid.toObjId]? = some
                                (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                              rw [storeObject_objects_ne st2 pair3.2 endpointId nextTid.toObjId _
                                (Ne.symm hNeEpNext) hObjInvSt2 hStoreEp2]; exact hNextSt2B
                            -- hNoFwd/hNoRev for clearing step
                            have hTransport3 : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                pair3.2.objects[x.toObjId]? = some (.tcb t) →
                                x.toObjId ≠ nextTid.toObjId →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t h hxN
                              have h2 : st2.objects[x.toObjId]? = some (.tcb t) := by
                                by_cases hx : x.toObjId = endpointId
                                · rw [hx, storeObject_objects_eq st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2] at h; cases h
                                · rwa [storeObject_objects_ne st2 pair3.2 endpointId x.toObjId _ hx hObjInvSt2 hStoreEp2] at h
                              have h1 : pair1.2.objects[x.toObjId]? = some (.tcb t) := by
                                rwa [storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                  x.toObjId hxN hObjInv1 hStN] at h2
                              exact hTransport1 x t h1
                            have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                                pair3.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid := by
                              intro a tA hA hN
                              by_cases haN : a.toObjId = nextTid.toObjId
                              · have hNS3' := hNS3; rw [haN] at hA; rw [hNS3'] at hA; cases hA
                                simp [tcbWithQueueLinks] at hN
                                obtain ⟨_, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt tid hN
                                rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                              · have hA' := hTransport3 a tA hA haN
                                obtain ⟨_, hB, hP⟩ := hLink.1 a tA hA' tid hN
                                rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                            have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                                pair3.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some tid := by
                              intro b tB hB hP
                              by_cases hbN : b.toObjId = nextTid.toObjId
                              · rw [hbN] at hB; rw [hNS3] at hB; cases hB; simp [tcbWithQueueLinks] at hP
                              · have hB' := hTransport3 b tB hB hbN
                                obtain ⟨_, hA, hN⟩ := hLink.2 b tB hB' tid hP
                                rw [hTcbObj] at hA; cases hA; rw [hNext] at hN
                                exact absurd (congrArg ThreadId.toObjId (Option.some.inj hN).symm) hbN
                            -- TCB snapshots in st4
                            have hTidResult := storeTcbQueueLinks_result_tcb pair3.2 st4 tid none none none hObjInv3 hClear
                            obtain ⟨_, _, hTidSt4⟩ := hTidResult
                            have hObjInv4 := storeTcbQueueLinks_preserves_objects_invExt pair3.2 st4 tid none none none hObjInv3 hClear
                            have hNextSt4 : st4.objects[nextTid.toObjId]? = some
                                (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                              rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid none none none
                                nextTid.toObjId hNeHN.symm hObjInv3 hClear]; exact hNS3
                            -- Other TCBs in st4 = other TCBs in st
                            have hFwdOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                x.toObjId ≠ tid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                st.objects[x.toObjId]? = some (.tcb t) →
                                st4.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t hxT hxN ht
                              rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                x.toObjId hxT hObjInv3 hClear,
                                storeObject_objects_ne st2 pair3.2 endpointId x.toObjId _ ?_ hObjInvSt2 hStoreEp2,
                                storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                x.toObjId hxN hObjInv1 hStN,
                                storeObject_objects_ne st pair1.2 endpointId x.toObjId _ ?_ hObjInv hStoreEp1]; exact ht
                              · intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                              · intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                            have hBackOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                x.toObjId ≠ tid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                st4.objects[x.toObjId]? = some (.tcb t) →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t hxT hxN ht
                              have h3 : pair3.2.objects[x.toObjId]? = some (.tcb t) := by
                                rwa [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                  x.toObjId hxT hObjInv3 hClear] at ht
                              exact hTransport3 x t h3 hxN
                            -- iqwf transport helper
                            have hNextTailProp : ∀ (qq : IntrusiveQueue),
                                intrusiveQueueWellFormed qq st →
                                ∀ tl, qq.tail = some tl → tl.toObjId = nextTid.toObjId →
                                nextTcb.queueNext = none := by
                              intro qq hWfQQ tl hTl hEq
                              have hTlEq := threadId_toObjId_injective hEq; rw [hTlEq] at hTl
                              obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 nextTid hTl
                              rw [hNextTcbSt] at hT; cases hT; exact hN
                            have hIqwfTransport : ∀ (qq : IntrusiveQueue),
                                intrusiveQueueWellFormed qq st →
                                intrusiveQueueWellFormed qq st4 := by
                              intro qq hWfQQ
                              exact storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear qq
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2 hPreEp2 qq
                                  (storeTcbQueueLinks_preserves_iqwf pair1.2 st2 nextTid _ _ _ hObjInv1 hStN qq
                                    (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                      st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp qq hWfQQ)
                                    (fun _ _ _ => hPrevNone) (hNextTailProp qq hWfQQ)))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                            -- Acyclicity chain
                            have hAcycEp1 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                              st pair1.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp1 hAcyclic
                            have hAcycSt2 := storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
                              pair1.2 st2 nextTid _ _ nextTcb.queueNext hObjInv1 hStN
                              (fun tcb' h => by rw [hLkN] at h; cases h; rfl) hAcycEp1
                            have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                              st2 pair3.2 endpointId _ (fun _ h => by cases h) hObjInvSt2 hStoreEp2 hAcycSt2
                            have hAcycSt4 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                              pair3.2 st4 tid none none hObjInv3 hClear hAcycEp3
                            -- SPLIT
                            refine ⟨?_, ?_, hAcycSt4⟩
                            -- PART 1: Endpoint well-formedness
                            · intro epId' ep' hObj'
                              have hObj4 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                                epId' ep' hObjInv3 hClear hObj'
                              unfold dualQueueEndpointWellFormed; rw [hObj']
                              by_cases hNe : epId' = endpointId
                              · rw [hNe] at hObj4
                                rw [storeObject_objects_eq st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2] at hObj4; cases hObj4
                                have hWfNew : intrusiveQueueWellFormed
                                    { head := some nextTid, tail := q.tail } st4 := by
                                  refine ⟨⟨fun h => absurd h (by simp), fun h => absurd (hHT.2 h) (by rw [hQHeadTid]; simp)⟩, ?_, ?_⟩
                                  · intro hd hHdEq; cases hHdEq
                                    exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]⟩
                                  · intro tl hTl
                                    obtain ⟨tOrig, hTOrig, hTNextOrig⟩ := hTlBnd tl hTl
                                    by_cases htT : tl.toObjId = tid.toObjId
                                    · have := threadId_toObjId_injective htT; subst this
                                      rw [hTcbObj] at hTOrig; cases hTOrig
                                      rw [hNext] at hTNextOrig; exact absurd hTNextOrig (by simp)
                                    · by_cases htN : tl.toObjId = nextTid.toObjId
                                      · have := threadId_toObjId_injective htN; subst this
                                        rw [hNextTcbSt] at hTOrig; cases hTOrig
                                        exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]; exact hTNextOrig⟩
                                      · exact ⟨tOrig, hFwdOther tl tOrig htT htN hTOrig, hTNextOrig⟩
                                cases hRQ : isReceiveQ
                                · simp only [Bool.false_eq_true, ↓reduceIte] at hWfNew ⊢
                                  exact ⟨hWfNew, hIqwfTransport ep.receiveQ hEpWf.2⟩
                                · simp only [↓reduceIte] at hWfNew ⊢
                                  exact ⟨hIqwfTransport ep.sendQ hEpWf.1, hWfNew⟩
                              · have hObj4St2 : st2.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne st2 pair3.2 endpointId epId' _ hNe hObjInvSt2 hStoreEp2] at hObj4
                                have hObjPB := storeTcbQueueLinks_endpoint_backward pair1.2 st2 nextTid _ _ _
                                  epId' ep' hObjInv1 hStN hObj4St2
                                have hObjStOrig : st.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne st pair1.2 endpointId epId' _ hNe hObjInv hStoreEp1] at hObjPB
                                have hWfPre := hEpInv epId' ep' hObjStOrig
                                unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjStOrig] at hWfPre
                                exact ⟨hIqwfTransport ep'.sendQ hWfPre.1, hIqwfTransport ep'.receiveQ hWfPre.2⟩
                            -- PART 2: Link integrity
                            · constructor
                              · intro a tcbA hA b hNxt
                                by_cases haT : a.toObjId = tid.toObjId
                                · rw [haT] at hA; rw [hTidSt4] at hA; cases hA; simp [tcbWithQueueLinks] at hNxt
                                · by_cases haN : a.toObjId = nextTid.toObjId
                                  · rw [haN] at hA; rw [hNextSt4] at hA; cases hA
                                    simp [tcbWithQueueLinks] at hNxt
                                    obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                                    have hbT : b.toObjId ≠ tid.toObjId := by
                                      intro hh; have := threadId_toObjId_injective hh; subst this
                                      rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                                    have hbN : b.toObjId ≠ nextTid.toObjId := by
                                      intro hh; have hbEq := threadId_toObjId_injective hh
                                      rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNeHN
                                    exact ⟨tcbB, hFwdOther b tcbB hbT hbN hB, (threadId_toObjId_injective haN) ▸ hP⟩
                                  · have hA' := hBackOther a tcbA haT haN hA
                                    obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                    have hbT : b.toObjId ≠ tid.toObjId := by
                                      intro hh; have := threadId_toObjId_injective hh; subst this
                                      rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                                    have hbN : b.toObjId ≠ nextTid.toObjId := by
                                      intro hh; have hbEq := threadId_toObjId_injective hh
                                      rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haT
                                    exact ⟨tcbB, hFwdOther b tcbB hbT hbN hB, hP⟩
                              · intro b tcbB hB a hPrv
                                by_cases hbT : b.toObjId = tid.toObjId
                                · rw [hbT] at hB; rw [hTidSt4] at hB; cases hB; simp [tcbWithQueueLinks] at hPrv
                                · by_cases hbN : b.toObjId = nextTid.toObjId
                                  · rw [hbN] at hB; rw [hNextSt4] at hB; cases hB
                                    simp [tcbWithQueueLinks] at hPrv
                                  · have hB' := hBackOther b tcbB hbT hbN hB
                                    obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                    by_cases haT : a.toObjId = tid.toObjId
                                    · have haEq := threadId_toObjId_injective haT
                                      rw [haEq, hTcbObj] at hA; cases hA; rw [hNext] at hNxt
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                                    · by_cases haN : a.toObjId = nextTid.toObjId
                                      · have := threadId_toObjId_injective haN; subst this
                                        rw [hNextTcbSt] at hA; cases hA
                                        exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]; exact hNxt⟩
                                      · exact ⟨tcbA, hFwdOther a tcbA haT haN hA, hNxt⟩
            | tcbNext prevTid =>
              dsimp only at hStep
              split at hStep
              · simp at hStep
              · -- pprevConsistent for tcbNext: q.head ≠ some tid ∧ tcb.queuePrev = some prevTid
                have hQHeadNeTid : q.head ≠ some tid := by simp_all
                have hPrevSome : tcb.queuePrev = some prevTid := by simp_all
                have hWfQ : intrusiveQueueWellFormed q st := by rw [← hQ]; cases isReceiveQ <;> simp_all
                obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
                -- applyPrev: lookupTcb st prevTid → prevTcb → storeTcbQueueLinks
                cases hLookupP : lookupTcb st prevTid with
                | none => simp [hLookupP] at hStep
                | some prevTcb =>
                  simp only [hLookupP] at hStep
                  -- Guard: prevTcb.queueNext = some tid
                  split at hStep
                  · simp at hStep
                  · rename_i stAp heqAp
                    split at heqAp
                    · simp at heqAp
                    · cases hLinkP : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                      | error e => simp [hLinkP] at heqAp
                      | ok stPrev =>
                        simp [hLinkP] at heqAp; subst heqAp
                        have hPrevTcbObj := lookupTcb_some_objects st prevTid prevTcb hLookupP
                        have hPrevNextTid : prevTcb.queueNext = some tid := by
                          rename_i hGuard _ _; revert hGuard; simp_all
                        have hNeEpPrev : endpointId ≠ prevTid.toObjId :=
                          fun h => by rw [h] at hObj; rw [hPrevTcbObj] at hObj; cases hObj
                        have hObjInv1 := storeTcbQueueLinks_preserves_objects_invExt
                          st stPrev prevTid _ _ _ hObjInv hLinkP
                        cases hNext : tcb.queueNext with
                        | none =>
                          -- PATH C: tail removal (tcbNext, queueNext=none)
                          simp only [hNext] at hStep
                          generalize hStoreEpC : storeObject endpointId _ stPrev = rEpC at hStep
                          cases rEpC with
                          | error e => simp at hStep
                          | ok pair3 =>
                            simp only [] at hStep
                            generalize hClearC : storeTcbQueueLinks pair3.2 tid none none none = rClC at hStep
                            cases rClC with
                            | error e => simp at hStep
                            | ok st4 =>
                              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                              obtain ⟨_, rfl⟩ := hStep
                              -- Key facts
                              have hNePrevTid : prevTid.toObjId ≠ tid.toObjId := by
                                intro h
                                have hEq : st.objects[tid.toObjId]? = some (.tcb prevTcb) := h ▸ hPrevTcbObj
                                rw [hTcbObj] at hEq; cases hEq
                                rw [hPrevNextTid] at hNext; exact absurd hNext (by simp)
                              have hPreEpSt1 : ∀ t : TCB, stPrev.objects[endpointId]? ≠ some (.tcb t) := by
                                intro t h
                                rw [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                  endpointId hNeEpPrev hObjInv hLinkP] at h; exact absurd h (hPreEp t)
                              have hObjInv3 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair3 hObjInv1 hStoreEpC
                              -- prevTid result
                              have hPrevResult := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                              obtain ⟨origPrev, hOrigPrevLk, hPrevStPrev⟩ := hPrevResult
                              rw [hLookupP] at hOrigPrevLk; cases hOrigPrevLk
                              rw [hNext] at hPrevStPrev
                              -- prevTid in pair3.2
                              have hPrevSt3 : pair3.2.objects[prevTid.toObjId]? = some
                                  (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                rw [storeObject_objects_ne stPrev pair3.2 endpointId prevTid.toObjId _
                                  hNeEpPrev.symm hObjInv1 hStoreEpC]; exact hPrevStPrev
                              -- prevTid in st4
                              have hPrevSt4 : st4.objects[prevTid.toObjId]? = some
                                  (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                  prevTid.toObjId hNePrevTid hObjInv3 hClearC]; exact hPrevSt3
                              -- tid cleared
                              have hTidResult := storeTcbQueueLinks_result_tcb pair3.2 st4 tid none none none hObjInv3 hClearC
                              obtain ⟨_, _, hTidSt4⟩ := hTidResult
                              -- Transport: other TCBs in st4 = other TCBs in st
                              have hTransportC : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                  x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId →
                                  st.objects[x.toObjId]? = some (.tcb t) →
                                  st4.objects[x.toObjId]? = some (.tcb t) := by
                                intro x t hxT hxP ht
                                rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _ x.toObjId hxT hObjInv3 hClearC,
                                    storeObject_objects_ne stPrev pair3.2 endpointId x.toObjId _ ?_ hObjInv1 hStoreEpC,
                                    storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP]
                                exact ht
                                intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                              have hBackTransportC : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                  x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId →
                                  st4.objects[x.toObjId]? = some (.tcb t) →
                                  st.objects[x.toObjId]? = some (.tcb t) := by
                                intro x t hxT hxP ht
                                have h3 : pair3.2.objects[x.toObjId]? = some (.tcb t) := by
                                  rwa [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _ x.toObjId hxT hObjInv3 hClearC] at ht
                                have h1 : stPrev.objects[x.toObjId]? = some (.tcb t) := by
                                  by_cases hx : x.toObjId = endpointId
                                  · rw [hx, storeObject_objects_eq stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC] at h3; cases h3
                                  · rwa [storeObject_objects_ne stPrev pair3.2 endpointId x.toObjId _ hx hObjInv1 hStoreEpC] at h3
                                rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at h1
                              -- iqwf transport
                              have hIqwfTransportC : ∀ (qq : IntrusiveQueue),
                                  intrusiveQueueWellFormed qq st →
                                  intrusiveQueueWellFormed qq st4 := by
                                intro qq hWfQQ
                                exact storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClearC qq
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC hPreEpSt1 qq
                                    (storeTcbQueueLinks_preserves_iqwf st stPrev prevTid _ _ _ hObjInv hLinkP qq hWfQQ
                                      (fun hd hhd heq => by
                                        have hEq := threadId_toObjId_injective heq
                                        rw [hEq] at hhd
                                        obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 prevTid hhd
                                        rw [hPrevTcbObj] at hT
                                        have := KernelObject.tcb.inj (Option.some.inj hT)
                                        rw [this]; exact hP)
                                      (fun _ _ _ => hNext)))
                                  (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                              -- Acyclicity chain
                              have hLinkPNone : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev none = .ok stPrev := by
                                rw [hNext] at hLinkP; exact hLinkP
                              have hAcycSt1 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                st stPrev prevTid prevTcb.queuePrev prevTcb.queuePPrev hObjInv hLinkPNone hAcyclic
                              have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                                stPrev pair3.2 endpointId _ (fun _ h => by cases h) hObjInv1 hStoreEpC hAcycSt1
                              have hAcycSt4 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                pair3.2 st4 tid none none hObjInv3 hClearC hAcycEp3
                              -- Build link integrity for st4 directly
                              have hLinkSt4 : tcbQueueLinkIntegrity st4 := by
                                constructor
                                · intro a tcbA hA b hNxt
                                  by_cases haT : a.toObjId = tid.toObjId
                                  · rw [haT] at hA; rw [hTidSt4] at hA; cases hA; simp [tcbWithQueueLinks] at hNxt
                                  · by_cases haP : a.toObjId = prevTid.toObjId
                                    · rw [haP] at hA; rw [hPrevSt4] at hA; cases hA
                                      simp [tcbWithQueueLinks] at hNxt -- prevTid.next = none
                                    · have hA' := hBackTransportC a tcbA haT haP hA
                                      obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                      by_cases hbT : b.toObjId = tid.toObjId
                                      · have hB2 : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                        rw [hTcbObj] at hB2
                                        have := (KernelObject.tcb.inj (Option.some.inj hB2))
                                        rw [← this, hPrevSome] at hP
                                        exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haP
                                      · by_cases hbPP : b.toObjId = prevTid.toObjId
                                        · -- b = prevTid: return prevTid's modified TCB from st4
                                          -- tcbB = prevTcb, so hP : prevTcb.queuePrev = some a
                                          have hBSt4 : st4.objects[b.toObjId]? = some
                                              (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                            rw [hbPP]; exact hPrevSt4
                                          -- prevTcb = tcbB
                                          have hTcbBEq : prevTcb = tcbB := by
                                            have h := hbPP ▸ hB; rw [hPrevTcbObj] at h
                                            exact KernelObject.tcb.inj (Option.some.inj h)
                                          exact ⟨_, hBSt4, by simp [tcbWithQueueLinks]; rw [hTcbBEq]; exact hP⟩
                                        · exact ⟨tcbB, hTransportC b tcbB hbT hbPP hB, hP⟩
                                · intro b tcbB hB a hPrv
                                  by_cases hbT : b.toObjId = tid.toObjId
                                  · rw [hbT] at hB; rw [hTidSt4] at hB; cases hB; simp [tcbWithQueueLinks] at hPrv
                                  · by_cases hbP : b.toObjId = prevTid.toObjId
                                    · -- b is prevTid: extract tcbB = tcbWithQueueLinks prevTcb ... via transport
                                      have hB2 : st4.objects[prevTid.toObjId]? = some (.tcb tcbB) := by rw [← hbP]; exact hB
                                      rw [hPrevSt4] at hB2
                                      have hTcbBEq : tcbB = tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none :=
                                        (KernelObject.tcb.inj (Option.some.inj hB2)).symm
                                      rw [hTcbBEq] at hPrv; simp [tcbWithQueueLinks] at hPrv
                                      -- hPrv : prevTcb.queuePrev = some a
                                      obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 prevTid prevTcb hPrevTcbObj a hPrv
                                      have haT : a.toObjId ≠ tid.toObjId := by
                                        intro hh
                                        have hA2 : st.objects[tid.toObjId]? = some (.tcb tcbA) := hh ▸ hA
                                        rw [hTcbObj] at hA2
                                        have := KernelObject.tcb.inj (Option.some.inj hA2)
                                        rw [← this, hNext] at hNxt; exact absurd hNxt (by simp)
                                      have haP : a.toObjId ≠ prevTid.toObjId := by
                                        intro hh
                                        have hA2 : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := hh ▸ hA
                                        rw [hPrevTcbObj] at hA2
                                        have := KernelObject.tcb.inj (Option.some.inj hA2)
                                        rw [← this, hPrevNextTid] at hNxt
                                        exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt)) hNePrevTid.symm
                                      exact ⟨tcbA, hTransportC a tcbA haT haP hA,
                                        hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)⟩
                                    · have hB' := hBackTransportC b tcbB hbT hbP hB
                                      obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                      by_cases haT : a.toObjId = tid.toObjId
                                      · have hA2 : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                        rw [hTcbObj] at hA2
                                        have := (KernelObject.tcb.inj (Option.some.inj hA2))
                                        rw [← this, hNext] at hNxt
                                        exact absurd hNxt (by simp)
                                      · by_cases haP : a.toObjId = prevTid.toObjId
                                        · have hA2 : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                          rw [hPrevTcbObj] at hA2
                                          have hTcbEq := (KernelObject.tcb.inj (Option.some.inj hA2))
                                          -- hTcbEq : prevTcb = tcbA, hNxt : tcbA.queueNext = some b
                                          rw [← hTcbEq, hPrevNextTid] at hNxt
                                          -- hNxt : some tid = some b → tid = b → contradiction with hbT
                                          have := congrArg ThreadId.toObjId (Option.some.inj hNxt)
                                          exact absurd this.symm hbT
                                        · exact ⟨tcbA, hTransportC a tcbA haT haP hA, hNxt⟩
                              -- SPLIT
                              refine ⟨?_, hLinkSt4, hAcycSt4⟩
                              -- PART 1: Endpoint well-formedness
                              intro epId' ep' hObj'
                              have hObj4 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                                epId' ep' hObjInv3 hClearC hObj'
                              unfold dualQueueEndpointWellFormed; rw [hObj']
                              by_cases hNe : epId' = endpointId
                              · rw [hNe] at hObj4
                                rw [storeObject_objects_eq stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC] at hObj4; cases hObj4
                                -- Modified queue has tail = some prevTid
                                -- Need WF for {head=q.head, tail=some prevTid} in st4
                                have hQHeadSome : q.head ≠ none := by
                                  intro h; simp [h, Option.isNone] at hNotIsNone
                                have hWfNew : intrusiveQueueWellFormed { head := q.head, tail := some prevTid } st4 := by
                                  refine ⟨⟨fun h => absurd h hQHeadSome,
                                          fun h => absurd h (by simp)⟩, ?_, ?_⟩
                                  · intro hd hHdEq
                                    obtain ⟨tHd, hTHd, hPHd⟩ := hHdBnd hd hHdEq
                                    by_cases hdT : hd.toObjId = tid.toObjId
                                    · exact absurd hHdEq (by rw [threadId_toObjId_injective hdT]; exact hQHeadNeTid)
                                    · by_cases hdP : hd.toObjId = prevTid.toObjId
                                      · have := threadId_toObjId_injective hdP; subst this
                                        exact ⟨_, hPrevSt4, by simp [tcbWithQueueLinks]; rw [hPrevTcbObj] at hTHd; cases hTHd; exact hPHd⟩
                                      · exact ⟨tHd, hTransportC hd tHd hdT hdP hTHd, hPHd⟩
                                  · intro tl hTl; cases hTl
                                    exact ⟨_, hPrevSt4, by simp [tcbWithQueueLinks]⟩
                                have hIfSimp : (if q.head = some tid then { head := none, tail := some prevTid : IntrusiveQueue }
                                    else { head := q.head, tail := some prevTid }) =
                                    { head := q.head, tail := some prevTid } := by
                                  simp [hQHeadNeTid]
                                cases hRQ : isReceiveQ
                                · simp only [hIfSimp] at hWfNew ⊢
                                  exact ⟨hWfNew, hIqwfTransportC ep.receiveQ hEpWf.2⟩
                                · simp only [hIfSimp] at hWfNew ⊢
                                  exact ⟨hIqwfTransportC ep.sendQ hEpWf.1, hWfNew⟩
                              · have hObj4St1 : stPrev.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne stPrev pair3.2 endpointId epId' _ hNe hObjInv1 hStoreEpC] at hObj4
                                have hObjStOrig : st.objects[epId']? = some (.endpoint ep') :=
                                  storeTcbQueueLinks_endpoint_backward st stPrev prevTid _ _ _ epId' ep' hObjInv hLinkP hObj4St1
                                have hWfPre := hEpInv epId' ep' hObjStOrig
                                unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjStOrig] at hWfPre
                                exact ⟨hIqwfTransportC ep'.sendQ hWfPre.1, hIqwfTransportC ep'.receiveQ hWfPre.2⟩
                        | some nextTid =>
                          -- PATH D: mid-queue removal (tcbNext, queueNext=some nextTid)
                          simp only [hNext] at hStep
                          -- st2Result: lookupTcb stPrev nextTid → storeTcbQueueLinks
                          cases hLkN : lookupTcb stPrev nextTid with
                          | none => simp [hLkN] at hStep
                          | some nextTcb =>
                            simp only [hLkN] at hStep
                            generalize hStN : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext = rStN at hStep
                            cases rStN with
                            | error e => simp at hStep
                            | ok stNext =>
                              simp only [] at hStep
                              -- q' = {head = q.head, tail = q.tail} since q.head ≠ some tid
                              simp only [hQHeadNeTid, ↓reduceIte] at hStep
                              -- storeObject endpointId ep' stNext → pair4
                              generalize hStoreEpD : storeObject endpointId _ stNext = rEpD at hStep
                              cases rEpD with
                              | error e => simp at hStep
                              | ok pair4 =>
                                simp only [] at hStep
                                generalize hClearD : storeTcbQueueLinks pair4.2 tid none none none = rClD at hStep
                                cases rClD with
                                | error e => simp at hStep
                                | ok stF =>
                                  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                                  obtain ⟨_, rfl⟩ := hStep
                                  -- === PATH D KEY FACTS ===
                                  have hNePrevTid : prevTid.toObjId ≠ tid.toObjId := by
                                    intro h; apply hAcyclic prevTid
                                    have hPEq := threadId_toObjId_injective h
                                    exact .single prevTid prevTid prevTcb hPrevTcbObj (hPEq ▸ hPrevNextTid)
                                  -- prevTid ≠ nextTid from acyclicity
                                  have hNePrevNext : prevTid.toObjId ≠ nextTid.toObjId := by
                                    intro h
                                    have hEq : nextTid = prevTid := (threadId_toObjId_injective h).symm
                                    apply hAcyclic tid
                                    have hObj1 : st.objects[nextTid.toObjId]? = some (.tcb prevTcb) := by
                                      rw [← h]; exact hPrevTcbObj
                                    exact .cons tid nextTid tid tcb hTcbObj hNext
                                      (.single nextTid tid prevTcb hObj1 hPrevNextTid)
                                  have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
                                    have hN1 := lookupTcb_some_objects stPrev nextTid nextTcb hLkN
                                    rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                      nextTid.toObjId hNePrevNext.symm hObjInv hLinkP] at hN1
                                  have hNeEpNext : endpointId ≠ nextTid.toObjId := by
                                    intro h; rw [h] at hObj; rw [hNextTcbSt] at hObj; cases hObj
                                  have hNeNextTid : nextTid.toObjId ≠ tid.toObjId := by
                                    intro h
                                    -- nextTid = tid creates a self-loop
                                    have hEq := threadId_toObjId_injective h
                                    apply hAcyclic tid
                                    exact .single tid tid tcb hTcbObj (hEq ▸ hNext)
                                  -- nextTcb.queuePrev = some tid (from link integrity)
                                  have hNextPrev : nextTcb.queuePrev = some tid := by
                                    obtain ⟨_, hB, hP⟩ := hLink.1 tid tcb hTcbObj nextTid hNext
                                    rw [hNextTcbSt] at hB; cases hB; exact hP
                                  -- ObjInv chain
                                  have hObjInvSN := storeTcbQueueLinks_preserves_objects_invExt
                                    stPrev stNext nextTid _ _ _ hObjInv1 hStN
                                  have hPreEpSN : ∀ t : TCB, stNext.objects[endpointId]? ≠ some (.tcb t) := by
                                    intro t h
                                    rw [storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _
                                      endpointId hNeEpNext hObjInv1 hStN,
                                      storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                      endpointId hNeEpPrev hObjInv hLinkP] at h
                                    exact absurd h (hPreEp t)
                                  have hObjInv4 := storeObject_preserves_objects_invExt' stNext endpointId _ pair4 hObjInvSN hStoreEpD
                                  -- Acyclicity
                                  -- prevTid.next changed: some tid → some nextTid.
                                  -- In st, path was prevTid → tid → nextTid → ...
                                  -- Now: prevTid → nextTid → ...  (shortcut)
                                  -- This cannot create cycles: any cycle through prevTid→nextTid in new state
                                  -- means nextTid →⁺ prevTid exists, but then in st: tid → nextTid →⁺ prevTid → tid = cycle.
                                  -- Use storeTcbQueueLinks_preserveNext for nextTid (queueNext preserved)
                                  -- and a custom argument for prevTid (queueNext changed but shortcutting)
                                  -- Acyclicity: stPrev shortcutted prevTid→tid→nextTid to prevTid→nextTid
                                  have hAcycSPrev : tcbQueueChainAcyclic stPrev := by
                                    intro tidC hp
                                    have hTransfer : ∀ a b, QueueNextPath stPrev a b → QueueNextPath st a b := by
                                      intro a b hp'
                                      induction hp' with
                                      | single x y tX hObjX hNxtX =>
                                        by_cases hxP : x.toObjId = prevTid.toObjId
                                        · have hPR := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                          obtain ⟨origP, hOLkP, hPSP⟩ := hPR
                                          rw [hLookupP] at hOLkP; cases hOLkP
                                          rw [hxP] at hObjX; rw [hPSP] at hObjX; cases hObjX
                                          simp [tcbWithQueueLinks] at hNxtX
                                          -- hNxtX : tcb.queueNext = some y, hNext: tcb.queueNext = some nextTid
                                          have : some nextTid = some y := hNext ▸ hNxtX
                                          cases this -- y = nextTid
                                          exact .cons x tid nextTid prevTcb
                                            (by rw [hxP]; exact hPrevTcbObj)
                                            hPrevNextTid
                                            (.single tid nextTid tcb hTcbObj hNext)
                                        · exact .single x y tX
                                            (by rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hObjX)
                                            hNxtX
                                      | cons x y z tX hObjX hNxtX _ ih =>
                                        by_cases hxP : x.toObjId = prevTid.toObjId
                                        · have hPR := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                          obtain ⟨origP, hOLkP, hPSP⟩ := hPR
                                          rw [hLookupP] at hOLkP; cases hOLkP
                                          rw [hxP] at hObjX; rw [hPSP] at hObjX; cases hObjX
                                          simp [tcbWithQueueLinks] at hNxtX
                                          -- hNxtX : tcb.queueNext = some y, hNext: tcb.queueNext = some nextTid
                                          have : some nextTid = some y := hNext ▸ hNxtX
                                          cases this -- y = nextTid
                                          exact .cons x tid z prevTcb
                                            (by rw [hxP]; exact hPrevTcbObj)
                                            hPrevNextTid
                                            (.cons tid nextTid z tcb hTcbObj hNext ih)
                                        · exact .cons x y z tX
                                            (by rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hObjX)
                                            hNxtX ih
                                    exact hAcyclic tidC (hTransfer tidC tidC hp)
                                  have hAcycSN := storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
                                    stPrev stNext nextTid _ _ nextTcb.queueNext hObjInv1 hStN
                                    (fun t h => by rw [hLkN] at h; cases h; rfl) hAcycSPrev
                                  have hAcycEp4 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                                    stNext pair4.2 endpointId _ (fun _ h => by cases h) hObjInvSN hStoreEpD hAcycSN
                                  have hAcycSF := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                    pair4.2 stF tid none none hObjInv4 hClearD hAcycEp4
                                  -- prevTid result in stPrev
                                  have hPrevResult := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                  obtain ⟨origP, hOLkP, hPrevStPrev⟩ := hPrevResult
                                  rw [hLookupP] at hOLkP; cases hOLkP
                                  -- nextTid result in stNext
                                  have hNextResult := storeTcbQueueLinks_result_tcb stPrev stNext nextTid _ _ _ hObjInv1 hStN
                                  obtain ⟨origN, hOLkN, hNextStNext⟩ := hNextResult
                                  rw [hLkN] at hOLkN; cases hOLkN
                                  -- Transport helpers
                                  have hPreEpSt4 : ∀ t : TCB, pair4.2.objects[endpointId]? ≠ some (.tcb t) := by
                                    intro t h
                                    rw [storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at h; cases h
                                  -- TCB snapshots in stF
                                  -- prevTid in stF: unchanged from stPrev through stNext, pair4, then clearing tid
                                  have hPrevStF : stF.objects[prevTid.toObjId]? = some
                                      (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext)) := by
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _
                                      prevTid.toObjId hNePrevTid hObjInv4 hClearD,
                                      storeObject_objects_ne stNext pair4.2 endpointId prevTid.toObjId _
                                      hNeEpPrev.symm hObjInvSN hStoreEpD,
                                      storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _
                                      prevTid.toObjId hNePrevNext hObjInv1 hStN]
                                    exact hPrevStPrev
                                  -- nextTid in stF
                                  have hNextStF : stF.objects[nextTid.toObjId]? = some
                                      (.tcb (tcbWithQueueLinks nextTcb (some prevTid) (some (QueuePPrev.tcbNext prevTid)) nextTcb.queueNext)) := by
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _
                                      nextTid.toObjId hNeNextTid hObjInv4 hClearD,
                                      storeObject_objects_ne stNext pair4.2 endpointId nextTid.toObjId _
                                      hNeEpNext.symm hObjInvSN hStoreEpD]
                                    rw [hPrevSome] at hNextStNext; exact hNextStNext
                                  -- tid in stF
                                  have hTidResultF := storeTcbQueueLinks_result_tcb pair4.2 stF tid none none none hObjInv4 hClearD
                                  obtain ⟨_, _, hTidStF⟩ := hTidResultF
                                  -- Other TCBs transport
                                  have hFwdOtherD : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                      x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                      st.objects[x.toObjId]? = some (.tcb t) → stF.objects[x.toObjId]? = some (.tcb t) := by
                                    intro x t hxT hxP hxN ht
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _ x.toObjId hxT hObjInv4 hClearD,
                                        storeObject_objects_ne stNext pair4.2 endpointId x.toObjId _ ?_ hObjInvSN hStoreEpD,
                                        storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _ x.toObjId hxN hObjInv1 hStN,
                                        storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP]
                                    exact ht; intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                                  have hBackOtherD : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                      x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                      stF.objects[x.toObjId]? = some (.tcb t) → st.objects[x.toObjId]? = some (.tcb t) := by
                                    intro x t hxT hxP hxN ht
                                    have h4 : pair4.2.objects[x.toObjId]? = some (.tcb t) := by
                                      rwa [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _ x.toObjId hxT hObjInv4 hClearD] at ht
                                    have hSN : stNext.objects[x.toObjId]? = some (.tcb t) := by
                                      by_cases hx : x.toObjId = endpointId
                                      · rw [hx, storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at h4; cases h4
                                      · rwa [storeObject_objects_ne stNext pair4.2 endpointId x.toObjId _ hx hObjInvSN hStoreEpD] at h4
                                    have hSP : stPrev.objects[x.toObjId]? = some (.tcb t) := by
                                      rwa [storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _ x.toObjId hxN hObjInv1 hStN] at hSN
                                    rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hSP
                                  -- Link integrity for stF (directly constructed)
                                  have hLinkStF : tcbQueueLinkIntegrity stF := by
                                    constructor
                                    · -- Forward: a.queueNext = some b ⟹ b exists ∧ b.queuePrev = some a
                                      intro a tcbA hA b hNxt
                                      by_cases haT : a.toObjId = tid.toObjId
                                      · -- a = tid: cleared, queueNext = none → contradiction
                                        rw [haT] at hA; rw [hTidStF] at hA; cases hA
                                        simp [tcbWithQueueLinks] at hNxt
                                      · by_cases haP : a.toObjId = prevTid.toObjId
                                        · -- a = prevTid: queueNext = tcb.queueNext = some nextTid
                                          rw [haP] at hA; rw [hPrevStF] at hA; cases hA
                                          simp [tcbWithQueueLinks] at hNxt
                                          -- hNxt : tcb.queueNext = some b
                                          rw [hNext] at hNxt; cases hNxt
                                          -- b = nextTid, need stF[nextTid] with queuePrev = some prevTid
                                          refine ⟨_, hNextStF, ?_⟩
                                          simp [tcbWithQueueLinks]
                                          exact (threadId_toObjId_injective haP.symm)
                                        · by_cases haN : a.toObjId = nextTid.toObjId
                                          · -- a = nextTid: queueNext = nextTcb.queueNext (unchanged)
                                            rw [haN] at hA; rw [hNextStF] at hA; cases hA
                                            simp [tcbWithQueueLinks] at hNxt
                                            -- hNxt : nextTcb.queueNext = some b
                                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                                            by_cases hbT : b.toObjId = tid.toObjId
                                            · -- b = tid → tcb.queuePrev = some nextTid, but = some prevTid
                                              have hBT : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                              rw [hTcbObj] at hBT; cases hBT
                                              rw [hPrevSome] at hP
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNePrevNext
                                            · by_cases hbP : b.toObjId = prevTid.toObjId
                                              · -- b = prevTid → return modified prevTid TCB
                                                have hBP : st.objects[prevTid.toObjId]? = some (.tcb tcbB) := hbP ▸ hB
                                                rw [hPrevTcbObj] at hBP
                                                have hTcbBEq := KernelObject.tcb.inj (Option.some.inj hBP)
                                                refine ⟨_, hbP ▸ hPrevStF, ?_⟩
                                                simp [tcbWithQueueLinks]
                                                rw [hTcbBEq, show a = nextTid from threadId_toObjId_injective haN]
                                                exact hP
                                              · by_cases hbN : b.toObjId = nextTid.toObjId
                                                · -- b = nextTid → nextTcb.queueNext = some nextTid → self-loop
                                                  have hBN : st.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                                  rw [hNextTcbSt] at hBN; cases hBN
                                                  -- nextTcb.queueNext = some nextTid → self-loop → contradiction
                                                  rw [show b = nextTid from threadId_toObjId_injective hbN] at hNxt
                                                  exact absurd (.single nextTid nextTid nextTcb hNextTcbSt hNxt) (hAcyclic nextTid)
                                                · exact ⟨tcbB, hFwdOtherD b tcbB hbT hbP hbN hB,
                                                    hP.trans (congrArg some (threadId_toObjId_injective haN).symm)⟩
                                          · -- a = other: back-transport to st, use original link, forward-transport
                                            have hA' := hBackOtherD a tcbA haT haP haN hA
                                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                            by_cases hbT : b.toObjId = tid.toObjId
                                            · -- b = tid: tcb.queuePrev = some a, but = some prevTid, a ≠ prevTid
                                              have hBT : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                              rw [hTcbObj] at hBT; cases hBT
                                              rw [hPrevSome] at hP
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haP
                                            · by_cases hbP : b.toObjId = prevTid.toObjId
                                              · -- b = prevTid: return modified prevTid TCB
                                                have hBP : st.objects[prevTid.toObjId]? = some (.tcb tcbB) := hbP ▸ hB
                                                rw [hPrevTcbObj] at hBP
                                                have hTcbBEq := KernelObject.tcb.inj (Option.some.inj hBP)
                                                refine ⟨_, hbP ▸ hPrevStF, ?_⟩
                                                simp [tcbWithQueueLinks]; rw [hTcbBEq]; exact hP
                                              · by_cases hbN : b.toObjId = nextTid.toObjId
                                                · -- b = nextTid: nextTcb.queuePrev = some tid, not some a
                                                  have hBN : st.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                                  rw [hNextTcbSt] at hBN; cases hBN
                                                  rw [hNextPrev] at hP
                                                  exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haT
                                                · exact ⟨tcbB, hFwdOtherD b tcbB hbT hbP hbN hB, hP⟩
                                    · -- Reverse: b.queuePrev = some a ⟹ a exists ∧ a.queueNext = some b
                                      intro b tcbB hB a hPrv
                                      by_cases hbT : b.toObjId = tid.toObjId
                                      · -- b = tid: cleared, queuePrev = none → contradiction
                                        rw [hbT] at hB; rw [hTidStF] at hB; cases hB
                                        simp [tcbWithQueueLinks] at hPrv
                                      · by_cases hbP : b.toObjId = prevTid.toObjId
                                        · -- b = prevTid: queuePrev = prevTcb.queuePrev (unchanged)
                                          rw [hbP] at hB; rw [hPrevStF] at hB; cases hB
                                          simp [tcbWithQueueLinks] at hPrv
                                          -- hPrv : prevTcb.queuePrev = some a
                                          obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 prevTid prevTcb hPrevTcbObj a hPrv
                                          by_cases haT : a.toObjId = tid.toObjId
                                          · -- a = tid: tcb.queueNext = some prevTid, but = some nextTid
                                            have hAT : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                            rw [hTcbObj] at hAT; cases hAT
                                            rw [hNext] at hNxt
                                            exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt)) hNePrevNext.symm
                                          · by_cases haP : a.toObjId = prevTid.toObjId
                                            · -- a = prevTid: prevTcb.queueNext = some prevTid, but = some tid
                                              have hAP : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                              rw [hPrevTcbObj] at hAP; cases hAP
                                              rw [hPrevNextTid] at hNxt
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hNePrevTid
                                            · by_cases haN : a.toObjId = nextTid.toObjId
                                              · -- a = nextTid: return modified nextTid TCB
                                                have hAN : st.objects[nextTid.toObjId]? = some (.tcb tcbA) := haN ▸ hA
                                                rw [hNextTcbSt] at hAN; cases hAN
                                                refine ⟨_, haN ▸ hNextStF, ?_⟩
                                                simp [tcbWithQueueLinks]
                                                exact hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)
                                              · exact ⟨tcbA, hFwdOtherD a tcbA haT haP haN hA,
                                                  hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)⟩
                                        · by_cases hbN : b.toObjId = nextTid.toObjId
                                          · -- b = nextTid: queuePrev = some prevTid, so a = prevTid
                                            have hBN : stF.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                            rw [hNextStF] at hBN
                                            have hTcbBEq := (KernelObject.tcb.inj (Option.some.inj hBN)).symm
                                            rw [hTcbBEq] at hPrv; simp [tcbWithQueueLinks] at hPrv
                                            -- hPrv : prevTid = a
                                            subst hPrv
                                            -- need stF[prevTid].queueNext = some nextTid
                                            refine ⟨_, hPrevStF, ?_⟩
                                            simp [tcbWithQueueLinks]
                                            rw [hNext]; exact congrArg some (threadId_toObjId_injective hbN.symm)
                                          · -- b = other: back-transport to st, use original link, forward-transport
                                            have hB' := hBackOtherD b tcbB hbT hbP hbN hB
                                            obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                            by_cases haT : a.toObjId = tid.toObjId
                                            · -- a = tid: tcb.queueNext = some b, but = some nextTid, b ≠ nextTid
                                              have hAT : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                              rw [hTcbObj] at hAT; cases hAT
                                              rw [hNext] at hNxt
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                                            · by_cases haP : a.toObjId = prevTid.toObjId
                                              · -- a = prevTid: prevTcb.queueNext = some b, but = some tid, b ≠ tid
                                                have hAP : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                                rw [hPrevTcbObj] at hAP; cases hAP
                                                rw [hPrevNextTid] at hNxt
                                                exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbT
                                              · by_cases haN : a.toObjId = nextTid.toObjId
                                                · -- a = nextTid: return modified nextTid TCB
                                                  have hAN : st.objects[nextTid.toObjId]? = some (.tcb tcbA) := haN ▸ hA
                                                  rw [hNextTcbSt] at hAN; cases hAN
                                                  refine ⟨_, haN ▸ hNextStF, ?_⟩
                                                  simp [tcbWithQueueLinks]; exact hNxt
                                                · exact ⟨tcbA, hFwdOtherD a tcbA haT haP haN hA, hNxt⟩
                                  have hIqwfD : ∀ (qq : IntrusiveQueue), intrusiveQueueWellFormed qq st → intrusiveQueueWellFormed qq stF := by
                                    intro qq hWfQQ
                                    exact storeTcbQueueLinks_preserves_iqwf pair4.2 stF tid none none none hObjInv4 hClearD qq
                                      (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                        stNext pair4.2 endpointId _ hObjInvSN hStoreEpD hPreEpSN qq
                                        (storeTcbQueueLinks_preserves_iqwf stPrev stNext nextTid _ _ _ hObjInv1 hStN qq
                                          (storeTcbQueueLinks_preserves_iqwf st stPrev prevTid _ _ _ hObjInv hLinkP qq hWfQQ
                                            (fun hd hhd heq => by
                                              rw [(threadId_toObjId_injective heq)] at hhd
                                              obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 prevTid hhd
                                              rw [hPrevTcbObj] at hT
                                              have := KernelObject.tcb.inj (Option.some.inj hT); rw [this]; exact hP)
                                            (fun tl htl heq => by
                                              rw [(threadId_toObjId_injective heq)] at htl
                                              obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 prevTid htl
                                              rw [hPrevTcbObj] at hT
                                              have := KernelObject.tcb.inj (Option.some.inj hT)
                                              rw [← this] at hN; rw [hPrevNextTid] at hN; exact absurd hN (by simp)))
                                          (fun hd hhd heq => by
                                            rw [(threadId_toObjId_injective heq)] at hhd
                                            obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 nextTid hhd
                                            rw [hNextTcbSt] at hT
                                            have hEq := KernelObject.tcb.inj (Option.some.inj hT)
                                            rw [← hEq] at hP; rw [hNextPrev] at hP; exact absurd hP (by simp))
                                          (fun tl htl heq => by
                                            rw [(threadId_toObjId_injective heq)] at htl
                                            obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 nextTid htl
                                            rw [hNextTcbSt] at hT
                                            have := KernelObject.tcb.inj (Option.some.inj hT); rw [this]; exact hN)))
                                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                                  have hEpWfD : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                                      stF.objects[epId']? = some (.endpoint ep') →
                                      dualQueueEndpointWellFormed epId' stF := by
                                    intro epId' ep' hObj'
                                    have hObjP4 := storeTcbQueueLinks_endpoint_backward pair4.2 stF tid none none none
                                      epId' ep' hObjInv4 hClearD hObj'
                                    unfold dualQueueEndpointWellFormed; rw [hObj']
                                    by_cases hNe : epId' = endpointId
                                    · -- Same endpoint: queue unchanged (head=q.head, tail=q.tail)
                                      rw [hNe] at hObjP4
                                      rw [storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at hObjP4
                                      cases hObjP4
                                      -- The stored endpoint has q' = {head=q.head, tail=q.tail} = q by η
                                      -- The stored queue q' = {head=q.head, tail=q.tail} = q by η
                                      -- So both sendQ and receiveQ of stored ep are original
                                      cases hRQ : isReceiveQ
                                      · -- isReceiveQ = false: sendQ modified (to q'), receiveQ unchanged
                                        simp only [Bool.false_eq_true, ↓reduceIte]
                                        refine ⟨hIqwfD _ ?_, hIqwfD ep.receiveQ hEpWf.2⟩
                                        rw [← hQ]; simp only [hRQ, Bool.false_eq_true, ↓reduceIte]; exact hEpWf.1
                                      · -- isReceiveQ = true: receiveQ modified (to q'), sendQ unchanged
                                        simp only [↓reduceIte]
                                        refine ⟨hIqwfD ep.sendQ hEpWf.1, hIqwfD _ ?_⟩
                                        rw [← hQ]; simp only [hRQ, ↓reduceIte]; exact hEpWf.2
                                    · -- Other endpoint: back-transport to original state
                                      have hObjSN : stNext.objects[epId']? = some (.endpoint ep') := by
                                        rwa [storeObject_objects_ne stNext pair4.2 endpointId epId' _ hNe hObjInvSN hStoreEpD] at hObjP4
                                      have hObjSP : stPrev.objects[epId']? = some (.endpoint ep') :=
                                        storeTcbQueueLinks_endpoint_backward stPrev stNext nextTid _ _ _ epId' ep' hObjInv1 hStN hObjSN
                                      have hObjOrig : st.objects[epId']? = some (.endpoint ep') :=
                                        storeTcbQueueLinks_endpoint_backward st stPrev prevTid _ _ _ epId' ep' hObjInv hLinkP hObjSP
                                      have hWfPre := hEpInv epId' ep' hObjOrig
                                      unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjOrig] at hWfPre
                                      exact ⟨hIqwfD ep'.sendQ hWfPre.1, hIqwfD ep'.receiveQ hWfPre.2⟩
                                  exact ⟨hEpWfD, hLinkStF, hAcycSF⟩

end SeLe4n.Kernel
