-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# WS-RR RR7.22 (residual) — the cancellation sweep's queue shape

`cancelIpcBlocking`'s blocked-on-endpoint arm is
`restoreToReadyCancelled (removeFromAllEndpointQueues st v) v`, and it is the
half of RR7.22 finding 4 the splice engine does **not** cover: the sweep is a
fold over the whole object store rather than the four-shape splice, so every
queue-shape conjunct has to be re-argued over it.

## The fact the bundle does not entail

`ipcInvariantFull` constrains a queue only at its **boundaries**
(`intrusiveQueueWellFormed`: head and tail exist, agree on emptiness, and carry
no predecessor / successor) plus doubly-linked integrity and acyclicity.  It says
nothing about **connectivity** — that the `queueNext` chain from a head reaches
the tail.  The sweep advances a head to the removed thread's `queueNext` and
retreats a tail to its `queuePrev` unconditionally, so on a bundle-satisfying
state where the removed thread heads a queue with `queueNext = none` while the
tail is a *different* thread, the result is `head = none, tail = some x` — P1
violated.

Such a state is admitted by the bundle (a `.ready` thread whose `queueNext`
points at the tail satisfies membership for the tail, and
`queueNextBlockingMatch`'s catch-all admits a `.ready` source), and it is very
likely unreachable — no transition creates it — but unreachability is not proved
anywhere, and the bundle is what a preservation proof may assume.

So the missing fact is **stated**, as `sweptThreadBoundaryCoherent`, in exactly
the way RR7.22 stated `splicePredecessorBlocked` rather than assuming it away.  A
caller discharges it from a reachability witness for the queue it is cancelling
out of.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- §1  The coherence hypothesis
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the boundary the swept thread occupies is
coherent — if it heads a queue with no successor it is also the tail, and if it
tails a queue with no predecessor it is also the head.

Two clauses rather than four because it is stated per queue; the state-level
form below applies it to both sides of every endpoint. -/
def queueBoundaryCoherentAt (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  (q.head = some tid → tcb.queueNext = none → q.tail = some tid) ∧
  (q.tail = some tid → tcb.queuePrev = none → q.head = some tid)

/-- **WS-RR RR7.22 (residual)**: the state-level form of the coherence
hypothesis — every endpoint, both queues. -/
def sweptThreadBoundaryCoherent (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) → lookupTcb st tid = some tcb →
      queueBoundaryCoherentAt ep.sendQ tid tcb ∧ queueBoundaryCoherentAt ep.receiveQ tid tcb

/-- A thread that occupies no boundary of a queue satisfies the coherence
condition vacuously — the common case, and the reason the hypothesis costs a
caller nothing on the endpoints it is not cancelling out of. -/
theorem queueBoundaryCoherentAt_of_off_boundary (q : IntrusiveQueue)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hH : q.head ≠ some tid) (hT : q.tail ≠ some tid) :
    queueBoundaryCoherentAt q tid tcb :=
  ⟨fun h _ => absurd h hH, fun h _ => absurd h hT⟩

-- ============================================================================
-- §2  The swept queue is well-formed
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the queue the sweep installs is well-formed in
the state the sweep produces.

The four boundary cases are the four ways the swept thread can sit in a queue,
and each is closed by a different fact:

* **head and tail** — the boundary conjuncts themselves give both of the swept
  thread's links as `none`, so the new queue is empty;
* **head only** — coherence forbids `queueNext = none` there, so the new head is
  a real thread, and P1 at the pre-state keeps the tail non-empty;
* **tail only** — coherence forbids `queuePrev = none`, dually;
* **neither** — the queue is untouched.

P2 and P3 then follow from the *skip* the splice installed: the promoted
successor's `queuePrev` is the swept thread's own (`none`, because it headed the
queue), and the promoted predecessor's `queueNext` is the swept thread's own
(`none`, because it tailed it).  A boundary that did **not** move keeps its
field because the only threads the splice rewrites are the swept thread's two
neighbours, and a neighbour at a boundary would contradict that boundary's own
conjunct. -/
theorem sweptQueue_wellFormed
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (q : IntrusiveQueue)
    (hInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st) (hAcyc : tcbQueueChainAcyclic st)
    (hLookup : lookupTcb st v = some tcbV)
    (hWF : intrusiveQueueWellFormed q st)
    (hCoh : queueBoundaryCoherentAt q v tcbV) :
    intrusiveQueueWellFormed (removeThreadFromQueue (spliceOutMidQueueNode st v) q v)
      (removeFromAllEndpointQueues st v) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hVSplice : lookupTcb (spliceOutMidQueueNode st v) v = some tcbV :=
    lookupTcb_of_objects_of_not_reserved _ v tcbV
      (spliceOutMidQueueNode_victim_tcb st v tcbV hInv hLink hAcyc hLookup)
      (lookupTcb_some_not_reserved st v tcbV hLookup)
  -- The swept queue, spelled out.
  have hQ : removeThreadFromQueue (spliceOutMidQueueNode st v) q v =
      { head := if q.head = some v then tcbV.queueNext else q.head,
        tail := if q.tail = some v then tcbV.queuePrev else q.tail } :=
    removeThreadFromQueue_tcb_present _ q v tcbV hVSplice
  -- Carry a TCB from `st` to the swept state, keeping one link field.
  have carryPrev : ∀ (k : SeLe4n.ObjId) (t0 : TCB), st.objects[k]? = some (.tcb t0) →
      (∀ n, tcbV.queueNext = some n → n.toObjId ≠ k) →
      ∃ t', (removeFromAllEndpointQueues st v).objects[k]? = some (.tcb t') ∧
        t'.queuePrev = t0.queuePrev := by
    intro k t0 hk hNe
    obtain ⟨t1, h1, hp⟩ := spliceOutMidQueueNode_queuePrev_frame st v tcbV k t0 hInv hLookup hk hNe
    exact ⟨t1, removeFromAllEndpointQueues_tcb_frame st v hExt1 k t1 h1, hp⟩
  have carryNext : ∀ (k : SeLe4n.ObjId) (t0 : TCB), st.objects[k]? = some (.tcb t0) →
      (∀ p, tcbV.queuePrev = some p → p.toObjId ≠ k) →
      ∃ t', (removeFromAllEndpointQueues st v).objects[k]? = some (.tcb t') ∧
        t'.queueNext = t0.queueNext := by
    intro k t0 hk hNe
    obtain ⟨t1, h1, hp⟩ := spliceOutMidQueueNode_queueNext_frame st v tcbV k t0 hInv hLookup hk hNe
    exact ⟨t1, removeFromAllEndpointQueues_tcb_frame st v hExt1 k t1 h1, hp⟩
  -- The victim's own boundary facts, when it occupies one.
  have hVPrevNone : q.head = some v → tcbV.queuePrev = none := by
    intro hh
    obtain ⟨t, ht, hp⟩ := hWF.2.1 v hh
    rw [hVObj] at ht
    obtain rfl : t = tcbV := (KernelObject.tcb.inj (Option.some.inj ht)).symm
    exact hp
  have hVNextNone : q.tail = some v → tcbV.queueNext = none := by
    intro ht
    obtain ⟨t, ht', hn⟩ := hWF.2.2 v ht
    rw [hVObj] at ht'
    obtain rfl : t = tcbV := (KernelObject.tcb.inj (Option.some.inj ht')).symm
    exact hn
  rw [hQ]
  refine ⟨?_, ?_, ?_⟩
  · -- P1: head and tail agree on emptiness
    by_cases hh : q.head = some v <;> by_cases ht : q.tail = some v
    · simp only [if_pos hh, if_pos ht, hVPrevNone hh, hVNextNone ht]
    · simp only [if_pos hh, if_neg ht]
      constructor
      · intro hn; exact absurd (hCoh.1 hh hn) ht
      · intro hn
        have hx : q.head = none := hWF.1.mpr hn
        rw [hh] at hx
        cases hx
    · simp only [if_neg hh, if_pos ht]
      constructor
      · intro hn
        have hx : q.tail = none := hWF.1.mp hn
        rw [ht] at hx
        cases hx
      · intro hn; exact absurd (hCoh.2 ht hn) hh
    · simp only [if_neg hh, if_neg ht]; exact hWF.1
  · -- P2: the head has no predecessor
    intro hd hhd
    by_cases hh : q.head = some v
    · rw [if_pos hh] at hhd
      obtain ⟨tHd, hHd, hHdPrev⟩ := hLink.1 v tcbV hVObj hd hhd
      obtain ⟨t1, h1, hp⟩ :=
        spliceOutMidQueueNode_next_queuePrev st v tcbV hd tHd hInv hLookup hhd hHd
      exact ⟨t1, removeFromAllEndpointQueues_tcb_frame st v hExt1 hd.toObjId t1 h1,
        by rw [hp]; exact hVPrevNone hh⟩
    · rw [if_neg hh] at hhd
      obtain ⟨t0, h0, hp0⟩ := hWF.2.1 hd hhd
      refine carryPrev hd.toObjId t0 h0 ?_ |>.imp (fun t' h => ⟨h.1, by rw [h.2]; exact hp0⟩)
      intro n hn hEq
      obtain ⟨tN, hN, hNPrev⟩ := hLink.1 v tcbV hVObj n hn
      rw [hEq, h0] at hN
      have hEqT : tN = t0 := (KernelObject.tcb.inj (Option.some.inj hN)).symm
      rw [hEqT, hp0] at hNPrev
      cases hNPrev
  · -- P3: the tail has no successor
    intro tl htl
    by_cases ht : q.tail = some v
    · rw [if_pos ht] at htl
      obtain ⟨tTl, hTl, hTlNext⟩ := hLink.2 v tcbV hVObj tl htl
      obtain ⟨t1, h1, hn⟩ :=
        spliceOutMidQueueNode_prev_queueNext st v tcbV tl tTl hInv hLookup htl hTl
      exact ⟨t1, removeFromAllEndpointQueues_tcb_frame st v hExt1 tl.toObjId t1 h1,
        by rw [hn]; exact hVNextNone ht⟩
    · rw [if_neg ht] at htl
      obtain ⟨t0, h0, hn0⟩ := hWF.2.2 tl htl
      refine carryNext tl.toObjId t0 h0 ?_ |>.imp (fun t' h => ⟨h.1, by rw [h.2]; exact hn0⟩)
      intro pv hp hEq
      obtain ⟨tP, hP, hPNext⟩ := hLink.2 v tcbV hVObj pv hp
      rw [hEq, h0] at hP
      have hEqT : tP = t0 := (KernelObject.tcb.inj (Option.some.inj hP)).symm
      rw [hEqT, hn0] at hPNext
      cases hPNext

-- ============================================================================
-- §3  What the restore installs
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the TCB `restoreToReadyStaging` installs, named
so proofs can quantify over it. -/
def restoredTcb (tcb : TCB) (frame : Option Architecture.SyscallReturnFrame) : TCB :=
  let cleared : TCB := { tcb with
      ipcState := .ready
      queuePrev := none
      queueNext := none
      queuePPrev := none
      pendingReceiveReply := none }
  match frame with
  | some f => cleared.withReturnFrame f
  | none => cleared

/-- The restore *is* that store.  `rfl`, the pin. -/
theorem restoreToReadyStaging_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    Lifecycle.Suspend.restoreToReadyStaging st tid frame =
      (match st.getTcb? tid with
       | some tcb =>
         { st with objects := st.objects.insert tid.toObjId (.tcb (restoredTcb tcb frame)) }
       | none => st) := rfl

/-- **The complete description**: the restored TCB is the original with exactly
six fields rewritten — the five the clear names, and `registerContext`, which the
staged frame owns and which no invariant conjunct reads.  Stated as one record
update rather than as a list of fields that agree, so a field added to `TCB` is
covered by construction. -/
theorem restoredTcb_eq (tcb : TCB) (frame : Option Architecture.SyscallReturnFrame) :
    restoredTcb tcb frame =
      { tcb with
          ipcState := .ready
          queuePrev := none
          queueNext := none
          queuePPrev := none
          pendingReceiveReply := none
          registerContext := (restoredTcb tcb frame).registerContext } := by
  unfold restoredTcb; cases frame <;> rfl

@[simp] theorem restoredTcb_ipcState (tcb : TCB)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoredTcb tcb frame).ipcState = .ready := by
  unfold restoredTcb; cases frame <;> rfl

@[simp] theorem restoredTcb_queuePrev (tcb : TCB)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoredTcb tcb frame).queuePrev = none := by
  unfold restoredTcb; cases frame <;> rfl

@[simp] theorem restoredTcb_queueNext (tcb : TCB)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoredTcb tcb frame).queueNext = none := by
  unfold restoredTcb; cases frame <;> rfl

@[simp] theorem restoredTcb_queuePPrev (tcb : TCB)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoredTcb tcb frame).queuePPrev = none := by
  unfold restoredTcb; cases frame <;> rfl

@[simp] theorem restoredTcb_pendingReceiveReply (tcb : TCB)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoredTcb tcb frame).pendingReceiveReply = none := by
  unfold restoredTcb; cases frame <;> rfl

theorem restoreToReadyStaging_objects_self (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcb : TCB)
    (hInv : st.objects.invExt) (hTcb : st.getTcb? tid = some tcb) :
    (Lifecycle.Suspend.restoreToReadyStaging st tid frame).objects[tid.toObjId]?
      = some (.tcb (restoredTcb tcb frame)) := by
  rw [restoreToReadyStaging_eq, hTcb]
  exact RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv

theorem restoreToReadyStaging_objects_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (k : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hNe : k ≠ tid.toObjId) :
    (Lifecycle.Suspend.restoreToReadyStaging st tid frame).objects[k]? = st.objects[k]? := by
  rw [restoreToReadyStaging_eq]
  cases hTcb : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    show (st.objects.insert tid.toObjId (KernelObject.tcb (restoredTcb tcb frame))).get? k
        = st.objects[k]?
    exact RHTable.getElem?_insert_ne st.objects tid.toObjId k _
      (by simpa using fun h => hNe h.symm) hInv

-- ============================================================================
-- §4  The composite, and its TCB readings
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the state `cancelIpcBlocking`'s blocked arm
produces before the deschedule — sweep, then restore.

Parameterised by the staged frame so the plain restore (`resumeThread`'s
spelling) and the cancellation restore (`.ipcCancelled`) are one subject; the
queue shape does not depend on which frame is staged, and saying so once is what
keeps the two spellings from acquiring two answers. -/
def sweptAndRestored (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) : SystemState :=
  Lifecycle.Suspend.restoreToReadyStaging (removeFromAllEndpointQueues st v) v frame

/-- Away from the swept thread, the composite's TCB readings are the splice's —
the sweep writes only endpoints and the restore writes only the swept thread. -/
theorem sweptAndRestored_tcb_iff (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t : TCB) (hNe : k ≠ v.toObjId) :
    ((sweptAndRestored st v frame).objects[k]? = some (.tcb t)) ↔
      ((spliceOutMidQueueNode st v).objects[k]? = some (.tcb t)) := by
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  unfold sweptAndRestored
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt2 hNe]
  exact ⟨fun h => removeFromAllEndpointQueues_tcb_source st v hExt1 k t h,
    fun h => removeFromAllEndpointQueues_tcb_frame st v hExt1 k t h⟩

/-- At the swept thread, the composite holds the restored TCB — every link
`none`, `ipcState` `.ready`. -/
theorem sweptAndRestored_victim_tcb (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    (sweptAndRestored st v frame).objects[v.toObjId]? = some (.tcb (restoredTcb tcbV frame)) := by
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  have h1 : (spliceOutMidQueueNode st v).objects[v.toObjId]? = some (.tcb tcbV) :=
    spliceOutMidQueueNode_victim_tcb st v tcbV hInv hLink hAcyc hLookup
  have h2 : (removeFromAllEndpointQueues st v).objects[v.toObjId]? = some (.tcb tcbV) :=
    removeFromAllEndpointQueues_tcb_frame st v hExt1 v.toObjId tcbV h1
  exact restoreToReadyStaging_objects_self _ v frame tcbV hExt2
    ((SystemState.getTcb?_eq_some_iff _ v tcbV).mpr h2)

-- ============================================================================
-- §5  Doubly-linked integrity across the composite
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the composite preserves `tcbQueueLinkIntegrity`.

Note *where* it holds: at the swept state alone it does **not** — the splice
takes the thread out of the chain while its own links still name its old
neighbours, so `v.queueNext = some n` with `n.queuePrev = v.queuePrev` is a live
counterexample.  The restore is what repairs it, by clearing all three of the
swept thread's links, which is why this is stated over the composite and not
over `removeFromAllEndpointQueues`.

The case analysis is four-way in each direction, and every branch closes by
contradicting one of: acyclicity (a thread is not its own neighbour), the
uniqueness forward integrity forces (a target has exactly one source), or the
case hypothesis itself. -/
theorem sweptAndRestored_tcbQueueLinkIntegrity
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    tcbQueueLinkIntegrity (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hIff : ∀ (a : SeLe4n.ThreadId) (t : TCB), a ≠ v →
      (((sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb t)) ↔
        ((spliceOutMidQueueNode st v).objects[a.toObjId]? = some (.tcb t))) := by
    intro a t hav
    exact sweptAndRestored_tcb_iff st v frame hInv a.toObjId t
      (fun h => hav (SeLe4n.ThreadId.toObjId_injective _ _ h))
  -- The swept thread is not its own neighbour.
  have hNextNeV : ∀ n, tcbV.queueNext = some n → n ≠ v := by
    intro n hn hEq
    rw [hEq] at hn
    exact hAcyc v (.single v v tcbV hVObj hn)
  have hPrevNeV : ∀ p, tcbV.queuePrev = some p → p ≠ v := by
    intro p hp hEq
    rw [hEq] at hp
    obtain ⟨tA, hA, hAN⟩ := hLink.2 v tcbV hVObj v hp
    rw [hVObj] at hA
    have hEqT : tA = tcbV := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hEqT] at hAN
    exact hAcyc v (.single v v tcbV hVObj hAN)
  -- Pull a non-swept TCB back to the pre-state, keeping one link field.
  have nextOf : ∀ (a : SeLe4n.ThreadId) (tA : TCB), a ≠ v →
      (∀ p, tcbV.queuePrev = some p → p.toObjId ≠ a.toObjId) →
      (sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb tA) →
      ∃ t0, st.objects[a.toObjId]? = some (.tcb t0) ∧ tA.queueNext = t0.queueNext := by
    intro a tA hav hNe hA
    obtain ⟨t0, h0, _⟩ := spliceOutMidQueueNode_tcb_backward st v a.toObjId tA hInv
      ((hIff a tA hav).mp hA)
    obtain ⟨t1, h1, hf⟩ := spliceOutMidQueueNode_queueNext_frame st v tcbV a.toObjId t0
      hInv hLookup h0 hNe
    rw [(hIff a tA hav).mp hA] at h1
    have : t1 = tA := (KernelObject.tcb.inj (Option.some.inj h1)).symm
    exact ⟨t0, h0, by rw [← this]; exact hf⟩
  have prevOf : ∀ (a : SeLe4n.ThreadId) (tA : TCB), a ≠ v →
      (∀ n, tcbV.queueNext = some n → n.toObjId ≠ a.toObjId) →
      (sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb tA) →
      ∃ t0, st.objects[a.toObjId]? = some (.tcb t0) ∧ tA.queuePrev = t0.queuePrev := by
    intro a tA hav hNe hA
    obtain ⟨t0, h0, _⟩ := spliceOutMidQueueNode_tcb_backward st v a.toObjId tA hInv
      ((hIff a tA hav).mp hA)
    obtain ⟨t1, h1, hf⟩ := spliceOutMidQueueNode_queuePrev_frame st v tcbV a.toObjId t0
      hInv hLookup h0 hNe
    rw [(hIff a tA hav).mp hA] at h1
    have : t1 = tA := (KernelObject.tcb.inj (Option.some.inj h1)).symm
    exact ⟨t0, h0, by rw [← this]; exact hf⟩
  refine ⟨?_, ?_⟩
  · -- forward: a live `queueNext` has a reciprocal `queuePrev`
    intro a tA hA b hAB
    by_cases hav : a = v
    · rw [hav, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hA
      have hEqT : restoredTcb tcbV frame = tA := KernelObject.tcb.inj (Option.some.inj hA)
      rw [← hEqT, restoredTcb_queueNext] at hAB
      cases hAB
    · by_cases hprev : tcbV.queuePrev = some a
      · obtain ⟨tA0, hA0, _⟩ := hLink.2 v tcbV hVObj a hprev
        obtain ⟨t1, h1, hf⟩ := spliceOutMidQueueNode_prev_queueNext st v tcbV a tA0
          hInv hLookup hprev hA0
        rw [(hIff a tA hav).mp hA] at h1
        have hEqT : t1 = tA := (KernelObject.tcb.inj (Option.some.inj h1)).symm
        rw [hEqT] at hf
        rw [hf] at hAB
        obtain ⟨tB0, hB0, _⟩ := hLink.1 v tcbV hVObj b hAB
        obtain ⟨t2, h2, hg⟩ := spliceOutMidQueueNode_next_queuePrev st v tcbV b tB0
          hInv hLookup hAB hB0
        exact ⟨t2, (hIff b t2 (hNextNeV b hAB)).mpr h2, by rw [hg]; exact hprev⟩
      · obtain ⟨t0, h0, hf⟩ := nextOf a tA hav
          (fun p hp hEq => hprev (by
            rw [hp]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq))) hA
        rw [hf] at hAB
        obtain ⟨tB0, hB0, hBP⟩ := hLink.1 a t0 h0 b hAB
        have hbv : b ≠ v := by
          intro hEq
          rw [hEq, hVObj] at hB0
          have hx : tB0 = tcbV := (KernelObject.tcb.inj (Option.some.inj hB0)).symm
          rw [hx] at hBP
          exact hprev hBP
        have hbn : ∀ n, tcbV.queueNext = some n → n.toObjId ≠ b.toObjId := by
          intro n hn hEq
          obtain ⟨tN, hN, hNP⟩ := hLink.1 v tcbV hVObj n hn
          rw [hEq, hB0] at hN
          have hx : tN = tB0 := (KernelObject.tcb.inj (Option.some.inj hN)).symm
          rw [hx, hBP] at hNP
          exact hav (Option.some.inj hNP)
        obtain ⟨t2, h2, hg⟩ := spliceOutMidQueueNode_queuePrev_frame st v tcbV b.toObjId tB0
          hInv hLookup hB0 hbn
        exact ⟨t2, (hIff b t2 hbv).mpr h2, by rw [hg]; exact hBP⟩
  · -- reverse: a live `queuePrev` has a reciprocal `queueNext`
    intro b tB hB a hBA
    by_cases hbv : b = v
    · rw [hbv, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hB
      have hEqT : restoredTcb tcbV frame = tB := KernelObject.tcb.inj (Option.some.inj hB)
      rw [← hEqT, restoredTcb_queuePrev] at hBA
      cases hBA
    · by_cases hnext : tcbV.queueNext = some b
      · obtain ⟨tB0, hB0, _⟩ := hLink.1 v tcbV hVObj b hnext
        obtain ⟨t1, h1, hg⟩ := spliceOutMidQueueNode_next_queuePrev st v tcbV b tB0
          hInv hLookup hnext hB0
        rw [(hIff b tB hbv).mp hB] at h1
        have hEqT : t1 = tB := (KernelObject.tcb.inj (Option.some.inj h1)).symm
        rw [hEqT] at hg
        rw [hg] at hBA
        obtain ⟨tA0, hA0, _⟩ := hLink.2 v tcbV hVObj a hBA
        obtain ⟨t2, h2, hf⟩ := spliceOutMidQueueNode_prev_queueNext st v tcbV a tA0
          hInv hLookup hBA hA0
        exact ⟨t2, (hIff a t2 (hPrevNeV a hBA)).mpr h2, by rw [hf]; exact hnext⟩
      · obtain ⟨t0, h0, hg⟩ := prevOf b tB hbv
          (fun n hn hEq => hnext (by
            rw [hn]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq))) hB
        rw [hg] at hBA
        obtain ⟨tA0, hA0, hAN⟩ := hLink.2 b t0 h0 a hBA
        have hav : a ≠ v := by
          intro hEq
          rw [hEq, hVObj] at hA0
          have hx : tA0 = tcbV := (KernelObject.tcb.inj (Option.some.inj hA0)).symm
          rw [hx] at hAN
          exact hnext hAN
        have hap : ∀ p, tcbV.queuePrev = some p → p.toObjId ≠ a.toObjId := by
          intro p hp hEq
          obtain ⟨tP, hP, hPN⟩ := hLink.2 v tcbV hVObj p hp
          rw [hEq, hA0] at hP
          have hx : tP = tA0 := (KernelObject.tcb.inj (Option.some.inj hP)).symm
          rw [hx, hAN] at hPN
          exact hbv (Option.some.inj hPN)
        obtain ⟨t2, h2, hf⟩ := spliceOutMidQueueNode_queueNext_frame st v tcbV a.toObjId tA0
          hInv hLookup hA0 hap
        exact ⟨t2, (hIff a t2 hav).mpr h2, by rw [hf]; exact hAN⟩

-- ============================================================================
-- §6  Acyclicity across the composite
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: every `queueNext` edge the composite has is an
edge of the pre-state, **or** the skip the splice installed — and a skip is a
two-edge path in the pre-state.

This is the whole content of acyclicity preservation: the composite adds no
reachability the pre-state did not already have. -/
theorem sweptAndRestored_edge_source
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (x y : SeLe4n.ThreadId) (tX : TCB)
    (hX : (sweptAndRestored st v frame).objects[x.toObjId]? = some (.tcb tX))
    (hXY : tX.queueNext = some y) :
    (∃ t0, st.objects[x.toObjId]? = some (.tcb t0) ∧ t0.queueNext = some y) ∨
      (∃ t0, st.objects[x.toObjId]? = some (.tcb t0) ∧ t0.queueNext = some v ∧
        tcbV.queueNext = some y) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hIff : ∀ (a : SeLe4n.ThreadId) (t : TCB), a ≠ v →
      (((sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb t)) ↔
        ((spliceOutMidQueueNode st v).objects[a.toObjId]? = some (.tcb t))) := by
    intro a t hav
    exact sweptAndRestored_tcb_iff st v frame hInv a.toObjId t
      (fun h => hav (SeLe4n.ThreadId.toObjId_injective _ _ h))
  by_cases hxv : x = v
  · exfalso
    rw [hxv, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hX
    have hEqT : restoredTcb tcbV frame = tX := KernelObject.tcb.inj (Option.some.inj hX)
    rw [← hEqT, restoredTcb_queueNext] at hXY
    cases hXY
  · by_cases hprev : tcbV.queuePrev = some x
    · obtain ⟨tX0, hX0, hXv⟩ := hLink.2 v tcbV hVObj x hprev
      obtain ⟨t1, h1, hf⟩ := spliceOutMidQueueNode_prev_queueNext st v tcbV x tX0
        hInv hLookup hprev hX0
      rw [(hIff x tX hxv).mp hX] at h1
      have hEqT : t1 = tX := (KernelObject.tcb.inj (Option.some.inj h1)).symm
      rw [hEqT] at hf
      exact Or.inr ⟨tX0, hX0, hXv, by rw [← hf]; exact hXY⟩
    · obtain ⟨t0, h0, _⟩ := spliceOutMidQueueNode_tcb_backward st v x.toObjId tX hInv
        ((hIff x tX hxv).mp hX)
      obtain ⟨t1, h1, hf⟩ := spliceOutMidQueueNode_queueNext_frame st v tcbV x.toObjId t0
        hInv hLookup h0
        (fun p hp hEq => hprev (by
          rw [hp]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
      rw [(hIff x tX hxv).mp hX] at h1
      have hEqT : t1 = tX := (KernelObject.tcb.inj (Option.some.inj h1)).symm
      rw [hEqT] at hf
      exact Or.inl ⟨t0, h0, by rw [← hf]; exact hXY⟩

/-- **WS-RR RR7.22 (residual)**: reachability in the composite is reachability in
the pre-state. -/
theorem sweptAndRestored_path_transport
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    {x y : SeLe4n.ThreadId} (h : QueueNextPath (sweptAndRestored st v frame) x y) :
    QueueNextPath st x y := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  induction h with
  | single a b tA hA hAB =>
    rcases sweptAndRestored_edge_source st v frame tcbV hInv hLink hAcyc hLookup a b tA hA hAB with
      ⟨t0, h0, hn⟩ | ⟨t0, h0, hn, hv⟩
    · exact .single a b t0 h0 hn
    · exact .cons a v b t0 h0 hn (.single v b tcbV hVObj hv)
  | cons a b c tA hA hAB _ ih =>
    rcases sweptAndRestored_edge_source st v frame tcbV hInv hLink hAcyc hLookup a b tA hA hAB with
      ⟨t0, h0, hn⟩ | ⟨t0, h0, hn, hv⟩
    · exact .cons a b c t0 h0 hn ih
    · exact .cons a v c t0 h0 hn (.cons v b c tcbV hVObj hv ih)

/-- **WS-RR RR7.22 (residual)**: the composite preserves `tcbQueueChainAcyclic`. -/
theorem sweptAndRestored_tcbQueueChainAcyclic
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    tcbQueueChainAcyclic (sweptAndRestored st v frame) := fun a hPath =>
  hAcyc a (sweptAndRestored_path_transport st v frame tcbV hInv hLink hAcyc hLookup hPath)

-- ============================================================================
-- §7  The dual-queue invariant, assembled
-- ============================================================================

/-- Well-formedness of a queue whose boundaries are not the rewritten thread
transfers across a rewrite of that thread alone. -/
theorem intrusiveQueueWellFormed_transfer_off_boundary
    (q : IntrusiveQueue) (s2 s3 : SystemState) (v : SeLe4n.ThreadId)
    (hHead : q.head ≠ some v) (hTail : q.tail ≠ some v)
    (hAgree : ∀ k : SeLe4n.ObjId, k ≠ v.toObjId → s3.objects[k]? = s2.objects[k]?)
    (h : intrusiveQueueWellFormed q s2) : intrusiveQueueWellFormed q s3 := by
  refine ⟨h.1, ?_, ?_⟩
  · intro hd hhd
    obtain ⟨t, ht, hp⟩ := h.2.1 hd hhd
    exact ⟨t, by
      rw [hAgree hd.toObjId (fun hEq => hHead (by
        rw [hhd]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))]
      exact ht, hp⟩
  · intro tl htl
    obtain ⟨t, ht, hn⟩ := h.2.2 tl htl
    exact ⟨t, by
      rw [hAgree tl.toObjId (fun hEq => hTail (by
        rw [htl]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))]
      exact ht, hn⟩

/-- **WS-RR RR7.22 (residual)**: the composite preserves the whole dual-queue
system invariant.

The three components come from three different places, which is the shape of the
argument rather than an accident: the per-endpoint queues from §2 (transferred
across the restore, which touches only the swept thread and so cannot move a
boundary that §1's sweep result already says is not it), doubly-linked integrity
from §5, and acyclicity from §6.

`hCoh` is the fact the bundle does not entail; see the module header. -/
theorem sweptAndRestored_dualQueueSystemInvariant
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hDual : dualQueueSystemInvariant st)
    (hLookup : lookupTcb st v = some tcbV)
    (hCoh : sweptThreadBoundaryCoherent st v) :
    dualQueueSystemInvariant (sweptAndRestored st v frame) := by
  obtain ⟨hEps, hLink, hAcyc⟩ := hDual
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  have hVSplice : lookupTcb (spliceOutMidQueueNode st v) v = some tcbV :=
    lookupTcb_of_objects_of_not_reserved _ v tcbV
      (spliceOutMidQueueNode_victim_tcb st v tcbV hInv hLink hAcyc hLookup)
      (lookupTcb_some_not_reserved st v tcbV hLookup)
  -- The swept thread is not its own neighbour, in the spliced state.
  have hSelfNext : ∀ tcb, lookupTcb (spliceOutMidQueueNode st v) v = some tcb →
      tcb.queueNext ≠ some v := by
    intro tcb ht hn
    rw [hVSplice] at ht
    have : tcb = tcbV := (Option.some.inj ht).symm
    rw [this] at hn
    exact hAcyc v (.single v v tcbV hVObj hn)
  have hSelfPrev : ∀ tcb, lookupTcb (spliceOutMidQueueNode st v) v = some tcb →
      tcb.queuePrev ≠ some v := by
    intro tcb ht hp
    rw [hVSplice] at ht
    have hx : tcb = tcbV := (Option.some.inj ht).symm
    rw [hx] at hp
    obtain ⟨tA, hA, hAN⟩ := hLink.2 v tcbV hVObj v hp
    rw [hVObj] at hA
    have hy : tA = tcbV := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hy] at hAN
    exact hAcyc v (.single v v tcbV hVObj hAN)
  -- Away from the swept thread the restore changes nothing.
  have hAgree : ∀ k : SeLe4n.ObjId, k ≠ v.toObjId →
      (sweptAndRestored st v frame).objects[k]? = (removeFromAllEndpointQueues st v).objects[k]? :=
    fun k hk => restoreToReadyStaging_objects_ne _ v frame k hExt2 hk
  refine ⟨?_, sweptAndRestored_tcbQueueLinkIntegrity st v frame tcbV hInv hLink hAcyc hLookup,
    sweptAndRestored_tcbQueueChainAcyclic st v frame tcbV hInv hLink hAcyc hLookup⟩
  intro epId ep hEp
  -- The endpoint key is not the swept thread's.
  have hEpNe : epId ≠ v.toObjId := by
    intro hEq
    rw [hEq, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hEp
    cases hEp
  have hEp2 : (removeFromAllEndpointQueues st v).objects[epId]? = some (.endpoint ep) := by
    rw [← hAgree epId hEpNe]; exact hEp
  obtain ⟨ep0, hEp0⟩ :=
    removeFromAllEndpointQueues_endpoint_source st v hExt1 epId ep hEp2
  have hEp0St : st.objects[epId]? = some (.endpoint ep0) :=
    (spliceOutMidQueueNode_nonTcb st v hInv epId (.endpoint ep0) (by simp)).mp hEp0
  obtain ⟨_, hVal⟩ := removeFromAllEndpointQueues_endpoint_value st v hExt1 epId ep0 hEp0
  obtain ⟨hS, hR⟩ := hVal ep hEp2
  obtain ⟨_, hOff⟩ := removeFromAllEndpointQueues_off_boundary st v hExt1 hSelfNext hSelfPrev
    epId ep0 hEp0
  obtain ⟨hSH, hST, hRH, hRT⟩ := hOff ep hEp2
  have hWF0 := hEps epId ep0 hEp0St
  unfold dualQueueEndpointWellFormed at hWF0
  rw [hEp0St] at hWF0
  obtain ⟨hWFS, hWFR⟩ := hWF0
  obtain ⟨hCohS, hCohR⟩ := hCoh epId ep0 tcbV hEp0St hLookup
  unfold dualQueueEndpointWellFormed
  rw [hEp]
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact intrusiveQueueWellFormed_transfer_off_boundary _ _ _ v (by rw [← hS]; exact hSH)
      (by rw [← hS]; exact hST) hAgree
      (sweptQueue_wellFormed st v tcbV ep0.sendQ hInv hLink hAcyc hLookup hWFS hCohS)
  · rw [hR]
    exact intrusiveQueueWellFormed_transfer_off_boundary _ _ _ v (by rw [← hR]; exact hRH)
      (by rw [← hR]; exact hRT) hAgree
      (sweptQueue_wellFormed st v tcbV ep0.receiveQ hInv hLink hAcyc hLookup hWFR hCohR)

end SeLe4n.Kernel
