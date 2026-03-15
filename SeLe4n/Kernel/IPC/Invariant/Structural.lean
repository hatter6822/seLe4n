/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation

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
  obtain ⟨hEp, hLink⟩ := hInv
  refine ⟨?_, ensureRunnable_preserves_tcbQueueLinkIntegrity st tid hLink⟩
  intro epId ep hObj; rw [ensureRunnable_preserves_objects] at hObj
  exact ensureRunnable_preserves_dualQueueEndpointWellFormed st tid epId (hEp epId ep hObj)

/-- WS-H5: removeRunnable preserves dualQueueSystemInvariant. -/
private theorem removeRunnable_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (removeRunnable st tid) := by
  obtain ⟨hEp, hLink⟩ := hInv
  refine ⟨?_, removeRunnable_preserves_tcbQueueLinkIntegrity st tid hLink⟩
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
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid hd.toObjId _ hEq hStore]; exact hT, hP⟩
  · intro tl hTl
    obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hNextEq ▸ hN⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid tl.toObjId _ hEq hStore]; exact hT, hN⟩

/-- WS-H5: storeObject of a TCB-variant with preserved queue links maintains
tcbQueueLinkIntegrity. -/
private theorem storeObject_tcb_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hPrevEq : tcb'.queuePrev = tcb.queuePrev)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid
    · rw [hEqA, storeObject_objects_eq st st' tid _ hStore] at hA; cases hA
      -- tA = tcb', tA.queueNext = tcb'.queueNext = tcb.queueNext
      rw [hNextEq] at hN
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tcb (hEqA ▸ hTcbPre) b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore]; exact hB, hP⟩
    · rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore] at hA
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid
    · rw [hEqB, storeObject_objects_eq st st' tid _ hStore] at hB; cases hB
      rw [hPrevEq] at hP
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tcb (hEqB ▸ hTcbPre) a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore]; exact hA, hN⟩
    · rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore] at hB
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore]; exact hA, hN⟩

-- ---- Helper: storeObject endpoint preserves queue invariant properties ----

/-- WS-H5: Storing an endpoint preserves tcbQueueLinkIntegrity (no TCB is modified). -/
private theorem storeObject_endpoint_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    have hA' := tcb_lookup_of_endpoint_store st st' epId a.toObjId tA epNew hStore hA
    obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA' b hN
    have : b.toObjId ≠ epId := fun h => absurd (h ▸ hB) (hPreEp tB)
    exact ⟨tB, by rw [storeObject_objects_ne st st' epId b.toObjId _ this hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    have hB' := tcb_lookup_of_endpoint_store st st' epId b.toObjId tB epNew hStore hB
    obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB' a hP
    have : a.toObjId ≠ epId := fun h => absurd (h ▸ hA) (hPreEp tA)
    exact ⟨tA, by rw [storeObject_objects_ne st st' epId a.toObjId _ this hStore]; exact hA, hN⟩

/-- WS-H5: Storing an endpoint preserves intrusiveQueueWellFormed.
Boundary TCBs can't be at the endpoint ObjId (they are TCBs, not endpoints). -/
private theorem storeObject_endpoint_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    have : hd.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId hd.toObjId _ this hStore]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    have : tl.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId tl.toObjId _ this hStore]; exact hT, hN⟩

-- ---- Derived frame lemmas for storeTcbIpcState, storeTcbIpcStateAndMessage, storeTcbPendingMessage ----

/-- WS-H5: storeTcbIpcState preserves dualQueueSystemInvariant.
storeTcbIpcState uses { tcb with ipcState := ipc }, preserving queue links. -/
private theorem storeTcbIpcState_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
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
                       tid.toObjId tcb { tcb with ipcState := ipc } hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbIpcStateAndMessage preserves dualQueueSystemInvariant. -/
private theorem storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
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
                       tid.toObjId tcb _ hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbPendingMessage preserves dualQueueSystemInvariant. -/
private theorem storeTcbPendingMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
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
                       tid.toObjId tcb _ hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

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
                st st1 target .ready (some msg) hStore hInv
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
      exact ⟨tcb, rfl, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

/-- Helper: storeTcbQueueLinks preserves intrusiveQueueWellFormed when
the new link values are compatible with the queue's head/tail boundaries.
Clearing (all none) is always compatible. -/
private theorem storeTcbQueueLinks_preserves_iqwf
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st)
    (hHeadOk : ∀ hd, q.head = some hd → hd.toObjId = tid.toObjId → prev = none)
    (hTailOk : ∀ tl, q.tail = some tl → tl.toObjId = tid.toObjId → next = none) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  obtain ⟨origTcb, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid prev pprev next hStep
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hHeadOk hd hHd hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        hd.toObjId hEq hStep]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hTailOk tl hTl hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        tl.toObjId hEq hStep]; exact hT, hN⟩

/-- Helper: Clearing all queue links preserves tcbQueueLinkIntegrity when
no other TCB's forward/reverse links point to the cleared thread. -/
private theorem storeTcbQueueLinks_clearing_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid none none none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none none none hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none a.toObjId hEqA hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        b.toObjId hNeB hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none b.toObjId hEqB hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        a.toObjId hNeA hStep]; exact hA, hN⟩

/-- Helper: storeTcbQueueLinks with prev=none and next=none (arbitrary pprev)
preserves tcbQueueLinkIntegrity when no external refs point to the modified thread.
This generalizes storeTcbQueueLinks_clearing_preserves_linkInteg to allow non-none pprev,
since tcbQueueLinkIntegrity only inspects queuePrev and queueNext. -/
private theorem storeTcbQueueLinks_noprevnext_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (hStep : storeTcbQueueLinks st tid none pprev none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none pprev none hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none a.toObjId hEqA hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        b.toObjId hNeB hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none b.toObjId hEqB hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        a.toObjId hNeA hStep]; exact hA, hN⟩

/-- Helper: Two-step storeTcbQueueLinks append-to-tail preserves tcbQueueLinkIntegrity.
Step 1 sets old tail's next to newTid. Step 2 sets newTid's prev to tailTid.
The resulting forward link (tailTid→newTid) is matched by the reverse (newTid→tailTid). -/
private theorem storeTcbQueueLinks_append_tail_preserves_linkInteg
    (st1 st2 stF : SystemState) (tailTid newTid : SeLe4n.ThreadId)
    (prevT : Option SeLe4n.ThreadId) (pprevT pprevN : Option QueuePPrev)
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
    st1 st2 tailTid prevT pprevT (some newTid) hStep1
  obtain ⟨origNew, hLookupNew2, hNewStF⟩ := storeTcbQueueLinks_result_tcb
    st2 stF newTid (some tailTid) pprevN none hStep2
  -- tailTid's TCB in stF is preserved from st2 (step 2 only modifies newTid)
  have hTailStF : stF.objects[tailTid.toObjId]? =
      some (.tcb (tcbWithQueueLinks origTail prevT pprevT (some newTid))) := by
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      tailTid.toObjId hNe hStep2]
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
      oid hne2 hStep2]
    rw [storeTcbQueueLinks_preserves_objects_ne st1 st2 tailTid prevT pprevT (some newTid)
      oid hne1 hStep1]
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

-- ---- WS-H5: Dual-queue preservation for queue operations ----

/-- WS-H5: endpointQueuePopHead preserves dualQueueSystemInvariant. -/
theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
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
                  st pair.2 endpointId _ hStoreEp hPreEp hLink
                have hTransport : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                    pair.2.objects[x.toObjId]? = some (.tcb t) →
                    st.objects[x.toObjId]? = some (.tcb t) := by
                  intro x t h
                  by_cases hx : x.toObjId = endpointId
                  · rw [hx, storeObject_objects_eq st pair.2 endpointId _ hStoreEp] at h; cases h
                  · rwa [storeObject_objects_ne st pair.2 endpointId x.toObjId _ hx hStoreEp] at h
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
                refine ⟨?_, storeTcbQueueLinks_clearing_preserves_linkInteg
                  pair.2 st3 headTid hSt2 hLink1 hNoFwd1 hNoRev1⟩
                intro epId' ep' hObj'
                have hObj1 := storeTcbQueueLinks_endpoint_backward pair.2 st3 headTid none none none
                  epId' ep' hSt2 hObj'
                unfold dualQueueEndpointWellFormed; rw [hObj']
                by_cases hNe : epId' = endpointId
                · rw [hNe] at hObj1
                  rw [storeObject_objects_eq st pair.2 endpointId _ hStoreEp] at hObj1; cases hObj1
                  cases hRQ : isReceiveQ
                  · -- isReceiveQ = false: sendQ was emptied, receiveQ preserved
                    exact ⟨intrusiveQueueWellFormed_empty st3,
                      storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                        ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hStoreEp hPreEp _ hEpWf.2)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                  · -- isReceiveQ = true: receiveQ was emptied, sendQ preserved
                    exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                        ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hStoreEp hPreEp _ hEpWf.1)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                      intrusiveQueueWellFormed_empty st3⟩
                · have hObjSt : st.objects[epId']? = some (.endpoint ep') := by
                    rwa [storeObject_objects_ne st pair.2 endpointId epId' _ hNe hStoreEp] at hObj1
                  have hWfPre := hEpInv epId' ep' hObjSt
                  unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt] at hWfPre
                  exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                      ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hStoreEp hPreEp _ hWfPre.1)
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                    storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                      ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hStoreEp hPreEp _ hWfPre.2)
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
                      rw [← h, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at this; cases this
                    have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
                      have := lookupTcb_some_objects pairB.2 nextTid nextTcb hLkN
                      rwa [storeObject_objects_ne st pairB.2 endpointId nextTid.toObjId _
                        (Ne.symm hNeEpNextB) hStoreEpB] at this
                    have hNextPrevB : nextTcb.queuePrev = some headTid := by
                      obtain ⟨_, hB, hP⟩ := hLink.1 headTid headTcb hHeadTcb nextTid hNext
                      rw [hNextTcbSt] at hB; cases hB; exact hP
                    have hNeHN : headTid.toObjId ≠ nextTid.toObjId := by
                      intro h
                      have hEq : st.objects[nextTid.toObjId]? = some (.tcb headTcb) := h ▸ hHeadTcb
                      rw [hNextTcbSt] at hEq; cases hEq
                      rw [hPrevNone] at hNextPrevB; exact absurd hNextPrevB (by simp)
                    have hLink1B := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                      st pairB.2 endpointId _ hStoreEpB hPreEp hLink
                    have hTransportB : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        pairB.2.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t h
                      by_cases hx : x.toObjId = endpointId
                      · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at h; cases h
                      · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hStoreEpB] at h
                    -- nextTid in st2 (after storeTcbQueueLinks nextTid)
                    have hNextResultB := storeTcbQueueLinks_result_tcb pairB.2 st2 nextTid none
                        (some QueuePPrev.endpointHead) nextTcb.queueNext hStN
                    obtain ⟨origNextB, hOrigLkB, hNextSt2B⟩ := hNextResultB
                    -- origNextB = nextTcb since both come from lookupTcb pairB.2 nextTid
                    rw [hLkN] at hOrigLkB; cases hOrigLkB
                    -- Now origNextB is replaced by nextTcb everywhere
                    -- nextTid in st3 (preserved by clearing headTid)
                    have hNextSt3 : st3.objects[nextTid.toObjId]? = some
                        (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _
                        nextTid.toObjId hNeHN.symm hClH]; exact hNextSt2B
                    -- headTid in st3 (cleared)
                    have hHeadResultB := storeTcbQueueLinks_result_tcb st2 st3 headTid none none none hClH
                    obtain ⟨_, _, hHeadSt3B⟩ := hHeadResultB
                    -- headTid in st2 (unchanged from st by storeObject + storeTcbQueueLinks nextTid)
                    have hHeadSt2 : st2.objects[headTid.toObjId]? = some (.tcb headTcb) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _
                        headTid.toObjId hNeHN hStN]
                      rwa [storeObject_objects_ne st pairB.2 endpointId headTid.toObjId _
                        hNeEpHead.symm hStoreEpB]
                    -- Transport: other TCBs in st3 = TCBs in st
                    have hFwdOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st.objects[x.toObjId]? = some (.tcb t) →
                        st3.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hClH,
                          storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hStN]
                      rw [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ ?_ hStoreEpB]; exact ht
                      intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                    have hBackOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st3.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      have h1 : st2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hClH] at ht
                      have h2 : pairB.2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hStN] at h1
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
                              tl.toObjId htN hStN]
                            rw [storeObject_objects_ne st pairB.2 endpointId tl.toObjId _ ?_ hStoreEpB]
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
                    -- SPLIT: endpoint well-formedness ∧ link integrity
                    refine ⟨?_, ?_⟩
                    -- PART 1: Endpoint well-formedness
                    · intro epId' ep' hObj'
                      have hObjSt2 := storeTcbQueueLinks_endpoint_backward st2 st3 headTid _ _ _
                        epId' ep' hClH hObj'
                      have hObjPB := storeTcbQueueLinks_endpoint_backward pairB.2 st2 nextTid _ _ _
                        epId' ep' hStN hObjSt2
                      unfold dualQueueEndpointWellFormed; rw [hObj']
                      by_cases hNe : epId' = endpointId
                      · rw [hNe] at hObjPB
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at hObjPB
                        cases hObjPB
                        cases hRQ : isReceiveQ
                        · -- false: sendQ = new queue, receiveQ unchanged
                          simp only [hRQ, Bool.false_eq_true, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ unchanged
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              ep.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                                ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hStoreEpB hPreEp _ hEpWf.2)
                                (fun _ _ _ => rfl) (hNextTailProp ep.receiveQ hEpWf.2))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                        · -- true: receiveQ = new queue, sendQ unchanged
                          simp only [hRQ, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ unchanged
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              ep.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                                ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hStoreEpB hPreEp _ hEpWf.1)
                                (fun _ _ _ => rfl) (hNextTailProp ep.sendQ hEpWf.1))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                      · have hObjSt' : st.objects[epId']? = some (.endpoint ep') := by
                          rw [storeObject_objects_ne st pairB.2 endpointId epId' _ hNe hStoreEpB] at hObjPB
                          exact hObjPB
                        have hWfPre := hEpInv epId' ep' hObjSt'
                        unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt'] at hWfPre
                        exact ⟨storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                            ep'.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                              ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hStoreEpB hPreEp _ hWfPre.1)
                              (fun _ _ _ => rfl) (hNextTailProp ep'.sendQ hWfPre.1))
                            (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                          storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                            ep'.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                              ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hStoreEpB hPreEp _ hWfPre.2)
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
  obtain ⟨hEpInv, hLink⟩ := hInv
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
                    st pairA.2 endpointId _ hStoreEp hPreEp hLink
                  have hTA : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                      pairA.2.objects[x.toObjId]? = some (.tcb t) →
                      st.objects[x.toObjId]? = some (.tcb t) := by
                    intro x t h; by_cases hx : x.toObjId = endpointId
                    · rw [hx, storeObject_objects_eq st pairA.2 endpointId _ hStoreEp] at h; cases h
                    · rwa [storeObject_objects_ne st pairA.2 endpointId x.toObjId _ hx hStoreEp] at h
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
                    pairA.2 stA enqueueTid none (some QueuePPrev.endpointHead) none hSt2
                  have hQT : ∀ q, intrusiveQueueWellFormed q pairA.2 →
                      intrusiveQueueWellFormed q stA :=
                    fun q hWf => storeTcbQueueLinks_preserves_iqwf pairA.2 stA enqueueTid
                      none (some QueuePPrev.endpointHead) none hSt2 q hWf
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                  refine ⟨?_, storeTcbQueueLinks_noprevnext_preserves_linkInteg
                    pairA.2 stA enqueueTid (some QueuePPrev.endpointHead) hSt2 hLink1 hNoFwd hNoRev⟩
                  intro epId' ep'A hObj'A
                  have hObj1A := storeTcbQueueLinks_endpoint_backward pairA.2 stA enqueueTid
                    none (some QueuePPrev.endpointHead) none epId' ep'A hSt2 hObj'A
                  unfold dualQueueEndpointWellFormed; rw [hObj'A]
                  by_cases hNeA : epId' = endpointId
                  · rw [hNeA] at hObj1A
                    rw [storeObject_objects_eq st pairA.2 endpointId _ hStoreEp] at hObj1A
                    simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hObj1A
                    subst hObj1A
                    have hSing : intrusiveQueueWellFormed
                        { head := some enqueueTid, tail := some enqueueTid } stA :=
                      ⟨Iff.rfl,
                       fun hd hhd => by simp at hhd; subst hhd; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩,
                       fun tl htl => by simp at htl; subst htl; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩⟩
                    cases isReceiveQ
                    · exact ⟨hSing, hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hEpWf.2)⟩
                    · exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hEpWf.1), hSing⟩
                  · rw [storeObject_objects_ne st pairA.2 endpointId epId' _ hNeA hStoreEp] at hObj1A
                    have hWfOrig := hEpInv epId' ep'A hObj1A
                    unfold dualQueueEndpointWellFormed at hWfOrig; rw [hObj1A] at hWfOrig
                    exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hWfOrig.1),
                      hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hWfOrig.2)⟩
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
                        st pairB.2 endpointId _ hStoreEpB hPreEp hLink
                      have hTcbBack : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                          pairB.2.objects[x.toObjId]? = some (.tcb t) →
                          st.objects[x.toObjId]? = some (.tcb t) := by
                        intro x t h; by_cases hx : x.toObjId = endpointId
                        · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at h; cases h
                        · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hStoreEpB] at h
                      have hTailInPB : pairB.2.objects[tailTid.toObjId]? = some (.tcb tailTcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId tailTid.toObjId _
                          hNeTailEp hStoreEpB]; exact hTailTcbObj
                      have hEnqInPB : pairB.2.objects[enqueueTid.toObjId]? = some (.tcb tcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId enqueueTid.toObjId _
                          (Ne.symm hNeEpTid) hStoreEpB]; exact hTcbObj
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
                      have hLinkFinal := storeTcbQueueLinks_append_tail_preserves_linkInteg
                        pairB.2 st2B st3B tailTid enqueueTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some (QueuePPrev.tcbNext tailTid))
                        hSt2B hSt3B hNeTailEnq hLink1
                        (fun t h => by rw [hTailInPB] at h; cases h; rfl)
                        (fun t h => by rw [hTailInPB] at h; cases h; exact hTailNextNone)
                        hNoFwd hNoRev
                      -- Endpoint well-formedness transport
                      obtain ⟨origEnq2, _, hEnqSt3⟩ := storeTcbQueueLinks_result_tcb
                        st2B st3B enqueueTid (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hSt3B
                      -- Transport iqwf through both steps for unmodified queues
                      have hQT : ∀ q, intrusiveQueueWellFormed q pairB.2 →
                          (∀ hd, q.head = some hd → hd.toObjId = tailTid.toObjId → tailTcb.queuePrev = none) →
                          (∀ tl, q.tail = some tl → tl.toObjId ≠ tailTid.toObjId) →
                          (∀ hd, q.head = some hd → hd.toObjId ≠ enqueueTid.toObjId) →
                          intrusiveQueueWellFormed q st3B := by
                        intro q hWf hH1 hT1 hH2
                        exact storeTcbQueueLinks_preserves_iqwf st2B st3B enqueueTid
                          (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hSt3B q
                          (storeTcbQueueLinks_preserves_iqwf pairB.2 st2B tailTid
                            tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) hSt2B q hWf
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
                          st pairB.2 endpointId _ hStoreEpB hPreEp q hWfSt)
                          (hHeadTailPrev q hWfSt) hT1 hH2
                      refine ⟨?_, hLinkFinal⟩
                      intro epId' ep'F hObj'F
                      have hObj'2 := storeTcbQueueLinks_endpoint_backward st2B st3B enqueueTid
                        (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none epId' ep'F hSt3B hObj'F
                      have hObj'1 := storeTcbQueueLinks_endpoint_backward pairB.2 st2B tailTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) epId' ep'F hSt2B hObj'2
                      unfold dualQueueEndpointWellFormed; rw [hObj'F]
                      by_cases hNeEp : epId' = endpointId
                      · -- Same endpoint (modified)
                        rw [hNeEp] at hObj'1
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at hObj'1
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
                              this hStoreEpB]; exact hT, hP⟩
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
                          rwa [storeObject_objects_ne st pairB.2 endpointId epId' _ hNeEp hStoreEpB] at hObj'1
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
            exact ensureRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueuePopHead_preserves_dualQueueSystemInvariant _ _ _ _ _ hPop hInv))
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
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshSender hSendTailFresh))

/-- WS-H5: endpointReceiveDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointReceiveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
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
            _ _ _ _ _ hPop hInv
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
                exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant _ _ _ _ hMsg
                  (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                    _ _ _ _ _ hStore hInv1)
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
                exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant _ _ _ _ hMsg
                  (ensureRunnable_preserves_dualQueueSystemInvariant _ _
                    (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                      _ _ _ _ _ hStore hInv1))
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
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcState_preserves_dualQueueSystemInvariant _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshReceiver hRecvTailFresh))

/-- WS-H12a: endpointReplyRecv preserves dualQueueSystemInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation.
Freshness preconditions are transported through the reply phase since
storeTcbIpcStateAndMessage and ensureRunnable do not modify endpoint objects. -/
theorem endpointReplyRecv_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
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
      have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hMsg hInv
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
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId ep hMsg hEp)
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
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep hMsg hEp)
          hTail epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hMsg hEp')
      exact endpointReceiveDual_preserves_dualQueueSystemInvariant _ _ _ stR.2 stR.1
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)
        hInv2 hFreshReceiver' hRecvTailFresh'

/-- WS-H5: endpointCall preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointCall_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
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
            _ _ _ _ _ hPop hInv
          cases hStore1 : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hStore1] at hStep
          | ok st2 =>
            simp only [hStore1] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              _ _ _ _ _ hStore1 hInv1
            have hInv3 := ensureRunnable_preserves_dualQueueSystemInvariant st2 pair.1 hInv2
            cases hStore2 : storeTcbIpcState (ensureRunnable st2 pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hStore2] at hStep
            | ok st3 =>
              simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_dualQueueSystemInvariant _ _
                (storeTcbIpcState_preserves_dualQueueSystemInvariant _ _ _ _ hStore2 hInv3)
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
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshCaller hSendTailFresh))

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
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hRegCtx : ∀ tid tcb, st.scheduler.current = some tid → tid.toObjId = oid →
      st.objects[oid]? = some (.tcb tcb) →
      ∃ tcb', obj = .tcb tcb' ∧ tcb'.registerContext = tcb.registerContext) :
    contextMatchesCurrent st' := by
  simp only [storeObject] at hStore
  obtain ⟨_, rfl⟩ := hStore
  simp only [contextMatchesCurrent] at hInv ⊢
  cases hCur : st.scheduler.current with
  | none => trivial
  | some tid =>
    simp only [hCur] at hInv ⊢
    -- currentThreadValid guarantees the current thread has a TCB
    simp only [currentThreadValid, hCur] at hValid
    obtain ⟨curTcb, hCurTcb⟩ := hValid
    rw [HashMap_getElem?_insert]
    by_cases hEq : oid == tid.toObjId
    · have hEq' : oid = tid.toObjId := beq_iff_eq.mp hEq
      simp only [hEq, ite_true]
      -- Current thread has a TCB, so use hRegCtx
      have hCurTcb' : st.objects[oid]? = some (.tcb curTcb) := hEq' ▸ hCurTcb
      obtain ⟨tcb', hNew, hReg⟩ := hRegCtx tid curTcb hCur hEq'.symm hCurTcb'
      rw [hNew]; simp only []; rw [hReg]
      simp only [hCurTcb] at hInv; exact hInv
    · simp only [hEq]; exact hInv

/-- WS-H12c: IPC TCB stores preserve `contextMatchesCurrent`. -/
private theorem storeTcbIpcState_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
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
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc }, rfl, rfl⟩)

private theorem storeTcbIpcStateAndMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
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
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc, pendingMessage := msg }, rfl, rfl⟩)

private theorem storeTcbPendingMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
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
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hStore
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
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hStore
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
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj
            cases hObj; simp at hMsg
            -- pendingMessage is preserved: { tcb with ipcState := ipc }.pendingMessage = tcb.pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeTcbIpcStateAndMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
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
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeTcbPendingMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbPendingMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
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
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeObject for endpoint preserves allPendingMessagesBounded.
Endpoints don't carry pending messages, so the TCB predicate is unaffected. -/
theorem storeObject_endpoint_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hStore] at hObj
    exact hInv t tcb msg hObjPre hMsg

/-- WS-H12e: storeTcbQueueLinks preserves allPendingMessagesBounded.
Queue link updates only change `queuePrev`/`queueNext`/`queuePPrev`,
not `pendingMessage`. -/
theorem storeTcbQueueLinks_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
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
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj
            cases hObj; simp [tcbWithQueueLinks] at hMsg
            -- pendingMessage is preserved: queue link updates don't change pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeObject for notification preserves allPendingMessagesBounded.
Notifications are not TCBs, so no TCB's pendingMessage is affected. -/
theorem storeObject_notification_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStore : storeObject oid (.notification ntfn) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hStore] at hObj
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
                st pair.2 notificationId _ hStore hInv
              cases hIpc : storeTcbIpcState pair.2 waiter .ready with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  have hInv2 := storeTcbIpcState_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter _ hIpc hInv1
                  exact ensureRunnable_preserves_allPendingMessagesBounded st'' waiter hInv2
      | nil =>
          simp only [hWaiters] at hStep
          exact storeObject_notification_preserves_allPendingMessagesBounded
            st st' notificationId _ hStep hInv

/-- WS-H12e: notificationWait preserves allPendingMessagesBounded.
notificationWait stores a notification object and calls storeTcbIpcState +
ensureRunnable/removeRunnable. None of these modify any TCB's pendingMessage. -/
theorem notificationWait_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : allPendingMessagesBounded st)
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
                st pair.2 notificationId _ hStore hInv
              cases hIpc : storeTcbIpcState pair.2 waiter .ready with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  exact storeTcbIpcState_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter _ hIpc hInv1
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
                    have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hStore
                    simp only [storeTcbIpcState_fromTcb_eq hLk']
                    have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                      st pair.2 notificationId _ hStore hInv
                    cases hIpc : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
                    | error e => simp
                    | ok st'' =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have hInv2 := storeTcbIpcState_preserves_allPendingMessagesBounded
                          pair.2 st'' waiter _ hIpc hInv1
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
                      st st1 target _ _ (by intro m hm; cases hm; exact hMsgBounded) hStore hInv)
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
                    st st1 target _ _ (by intro m hm; cases hm; exact hMsgBounded) hStore hInv)

-- ============================================================================
-- WS-H12e: Composed ipcInvariantFull preservation theorems
-- ============================================================================

/-- WS-H12e: notificationSignal preserves the full IPC invariant.
The `dualQueueSystemInvariant` post-state is a hypothesis because notification
operations store notification objects (not endpoint/TCB queue links) and the
dual-queue frame lemma for notification stores is independently derivable. -/
theorem notificationSignal_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBadge' : badgeWellFormed st')
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨notificationSignal_preserves_ipcInvariant st st' notificationId badge hInv.1 hStep,
   hDualQueue',
   notificationSignal_preserves_allPendingMessagesBounded st st' notificationId badge hInv.2.2.1 hStep,
   hBadge'⟩

/-- WS-H12e: notificationWait preserves the full IPC invariant.
See `notificationSignal_preserves_ipcInvariantFull` for hypothesis rationale. -/
theorem notificationWait_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBadge' : badgeWellFormed st')
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariantFull st' :=
  ⟨notificationWait_preserves_ipcInvariant st st' notificationId waiter result hInv.1 hStep,
   hDualQueue',
   notificationWait_preserves_allPendingMessagesBounded st st' notificationId waiter result hInv.2.2.1 hStep,
   hBadge'⟩

/-- WS-H12e: endpointReply preserves the full IPC invariant.
The `dualQueueSystemInvariant` post-state hypothesis is needed because
`endpointReply` modifies TCB queue links via `storeTcbIpcStateAndMessage`;
the dual-queue preservation follows from `endpointReply_preserves_dualQueueSystemInvariant`
(which requires additional freshness hypotheses). -/
theorem endpointReply_preserves_ipcInvariantFull
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReply_preserves_ipcInvariant st st' replier target msg hInv.1 hStep,
   hDualQueue',
   endpointReply_preserves_allPendingMessagesBounded st st' replier target msg hInv.2.2.1 hStep,
   hBadge'⟩

/-- WS-H12e: endpointSendDual preserves the full IPC invariant.
Composes `endpointSendDual_preserves_ipcInvariant` (from existing proof surface),
`dualQueueSystemInvariant` (from caller — requires freshness hypotheses), and
`allPendingMessagesBounded` (from caller — the bounds check at entry ensures
any stored message satisfies `bounded`; see `endpointSendDual_message_bounded`). -/
theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDual_preserves_ipcInvariant st st' endpointId sender msg hInv.1 hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- WS-H12e: endpointReceiveDual preserves the full IPC invariant. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDual_preserves_ipcInvariant st st' endpointId receiver senderId hInv.1 hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- WS-H12e: endpointCall preserves the full IPC invariant. -/
theorem endpointCall_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointCall_preserves_ipcInvariant st st' endpointId caller msg hInv.1 hStep,
   hDualQueue', hBounded', hBadge'⟩

/-- WS-H12e: endpointReplyRecv preserves the full IPC invariant. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReplyRecv_preserves_ipcInvariant st st' endpointId receiver replyTarget msg hInv.1 hStep,
   hDualQueue', hBounded', hBadge'⟩

-- ============================================================================
-- WS-L3/L3-B: Standalone tcbQueueLinkIntegrity preservation
-- ============================================================================

/-- WS-L3/L3-B1: PopHead preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueuePopHead_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueuePopHead_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ st st' tid hStep hInv).2

/-- WS-L3/L3-B2: Enqueue preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
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
    endpointId isReceiveQ enqueueTid st st' hStep hInv hFreshTid hTailFresh).2

-- ============================================================================
-- WS-L3/L3-C2: ipcStateQueueConsistent preservation for queue operations
-- ============================================================================

/-- WS-L3/L3-C2: PopHead preserves ipcStateQueueConsistent. PopHead does not
modify any thread's ipcState and preserves all endpoints, so the forward
implication (blocked → endpoint exists) is maintained. -/
theorem endpointQueuePopHead_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  -- Step 1: find the pre-state TCB with same ipcState
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueuePopHead_tcb_ipcState_backward
    endpointId isReceiveQ st st' tid tid' tcb' hStep hTcb'
  -- Step 2: apply pre-state invariant
  have hPre := hInv tid' tcb hTcb
  -- Step 3: show endpoints survive the operation
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hStep hEp

/-- WS-L3/L3-C2: Enqueue preserves ipcStateQueueConsistent. Enqueue does not
modify any thread's ipcState and preserves all endpoints. -/
theorem endpointQueueEnqueue_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueueEnqueue_tcb_ipcState_backward
    endpointId isReceiveQ enqueueTid st st' tid' tcb' hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hStep hEp

end SeLe4n.Kernel
