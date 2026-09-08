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

## The facts the bundle does not entail

`ipcInvariantFull` constrains a queue only at its **boundaries**
(`intrusiveQueueWellFormed`: head and tail exist, agree on emptiness, and carry
no predecessor / successor), plus doubly-linked integrity, acyclicity, and two
*local* blocking facts about heads and successors.  It says nothing about
**connectivity** — that the `queueNext` chain from a head is the queue's
membership and ends at the tail.  Every gap below is one consequence of that:

* **P1 at a moved boundary** (`sweptThreadBoundaryCoherent`).  The sweep advances
  a head to the removed thread's `queueNext` and retreats a tail to its
  `queuePrev` unconditionally, so on a bundle-satisfying state where the removed
  thread heads a queue with `queueNext = none` while the tail is a *different*
  thread, the result is `head = none, tail = some x` — P1 violated.

* **The blocking state of a promoted tail** (`sweptPredecessorBlocked`).
  `endpointQueueTailBlockedConsistent` constrains the tail; when the swept thread
  *was* the tail its predecessor is promoted into that position, and no conjunct
  says a `queuePrev` is blocked on the endpoint the queue belongs to —
  `queueNextTargetBlocked` propagates blockedness only *forwards*.

* **The membership witness of a promoted successor** (`sweptSuccessorAnchored`).
  `ipcStateQueueMembershipConsistent`'s witness for a blocked thread is *any*
  thread whose `queueNext` names it — not necessarily one in the queue.  So a
  `.ready` thread may be the sole witness for a blocked successor while the queue
  is empty (`queueNextBlockingMatch`'s catch-all admits a `.ready` source), and
  sweeping it leaves the successor blocked, unqueued and unwitnessed.

Each such state is admitted by the bundle and each is very likely unreachable —
no transition creates one — but unreachability is not proved anywhere, and the
bundle is what a preservation proof may assume.

So the three missing facts are **stated**, as the clauses of
`sweptThreadQueueCoherent`, in exactly the way RR7.22 stated
`splicePredecessorBlocked` rather than assuming them away.  A caller discharges
them from a reachability witness for the queue it is cancelling out of.
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

/-- **WS-RR RR7.22 (residual)**: the swept thread's predecessor is blocked on the
endpoint whose queue the swept thread tails.

The sweep promotes that predecessor to tail, and `endpointQueueTailBlockedConsistent`
demands the tail be blocked there.  Nothing in the bundle says so:
`queueNextTargetBlocked` carries blockedness *forwards* along `queueNext`, and a
tail has no successor to carry it from.  This is the sweep's counterpart of
RR7.22's `splicePredecessorBlocked`. -/
def sweptPredecessorBlocked (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) → lookupTcb st tid = some tcb →
    ∀ (p : SeLe4n.ThreadId), tcb.queuePrev = some p →
      ∀ pTcb, st.objects[p.toObjId]? = some (.tcb pTcb) →
        (ep.sendQ.tail = some tid →
          pTcb.ipcState = .blockedOnSend epId ∨ pTcb.ipcState = .blockedOnCall epId) ∧
        (ep.receiveQ.tail = some tid → pTcb.ipcState = .blockedOnReceive epId)

/-- **WS-RR RR7.22 (residual)**: the swept thread's successor is anchored — when
the swept thread has a successor but no predecessor, the swept thread heads the
endpoint queue that successor's blocking state names.

That is what makes the splice's promotion re-head the queue *at* the successor.
Without it the successor's only membership witness under
`ipcStateQueueMembershipConsistent` may be the swept thread itself — the witness
clause accepts any thread whose `queueNext` names it, in the queue or not — and
the sweep then leaves it blocked with no witness at all. -/
def sweptSuccessorAnchored (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ (tcb : TCB), lookupTcb st tid = some tcb →
    tcb.queuePrev = none →
    ∀ (n : SeLe4n.ThreadId), tcb.queueNext = some n →
      ∀ (nTcb : TCB), st.objects[n.toObjId]? = some (.tcb nTcb) →
        ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          st.objects[epId]? = some (.endpoint ep) →
          ((nTcb.ipcState = .blockedOnSend epId ∨ nTcb.ipcState = .blockedOnCall epId) →
            ep.sendQ.head = some tid) ∧
          (nTcb.ipcState = .blockedOnReceive epId → ep.receiveQ.head = some tid)

/-- **WS-RR RR7.22 (residual)**: the three queue-coherence facts the sweep needs
and `ipcInvariantFull` does not entail, as one hypothesis.

Named fields rather than an anonymous conjunction so each obligation is citable
where it is discharged, and so a result that needs only one of them can take that
one — see the module header for why each is missing. -/
structure sweptThreadQueueCoherent (st : SystemState) (tid : SeLe4n.ThreadId) : Prop where
  /-- The swept thread's queue boundaries are coherent with its own links. -/
  boundary : sweptThreadBoundaryCoherent st tid
  /-- The predecessor the sweep promotes to tail is blocked on that endpoint. -/
  predecessorBlocked : sweptPredecessorBlocked st tid
  /-- The successor the sweep promotes to head is one the swept thread headed for. -/
  successorAnchored : sweptSuccessorAnchored st tid

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

-- ============================================================================
-- §8  The composite's pullback and the reusable frames
-- ============================================================================

/-- **The composite's TCB pullback** — the single lever every non-queue conjunct
uses.  Away from the swept thread a TCB is a queue-link rewrite of the one the
pre-state held; at the swept thread it is the restored TCB.

Both alternatives are *complete* descriptions of the post-state TCB, not lists of
fields that happen to agree, so a conjunct that reads a field this operation does
not touch discharges by `rfl` and a field added to `TCB` is covered by
construction. -/
theorem sweptAndRestored_tcb_pullback
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (sweptAndRestored st v frame).objects[k]? = some (.tcb tA)) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧
      ((k ≠ v.toObjId ∧ tcbQueueLinkRewrite tA t0) ∨
        (k = v.toObjId ∧ tA = restoredTcb t0 frame)) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  by_cases hk : k = v.toObjId
  · subst hk
    rw [sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at h
    have hEqT : restoredTcb tcbV frame = tA := KernelObject.tcb.inj (Option.some.inj h)
    exact ⟨tcbV, hVObj, Or.inr ⟨rfl, hEqT.symm⟩⟩
  · obtain ⟨t0, h0, hr⟩ := spliceOutMidQueueNode_tcb_backward st v k tA hInv
      ((sweptAndRestored_tcb_iff st v frame hInv k tA hk).mp h)
    exact ⟨t0, h0, Or.inl ⟨hk, hr⟩⟩

/-- The endpoint sweep writes only endpoints, so a non-endpoint reading is the
input's, in both directions. -/
theorem removeFromAllEndpointQueues_nonEndpoint (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (o : KernelObject) (hNotEp : ∀ e, o ≠ .endpoint e) :
    ((removeFromAllEndpointQueues st tid).objects[k]? = some o) ↔
      ((spliceOutMidQueueNode st tid).objects[k]? = some o) := by
  rw [removeFromAllEndpointQueues_eq_fold]
  exact (RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧
      (acc.objects[k]? = some o ↔ (spliceOutMidQueueNode st tid).objects[k]? = some o))
    hExt ⟨hExt, Iff.rfl⟩
    (by
      rintro acc k' v' hGet ⟨hE, hA⟩
      unfold endpointSweepBody
      cases v' with
      | endpoint ep =>
        simp only
        split
        · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
          by_cases hK : k' = k
          · subst hK
            constructor
            · intro hx
              have hx' : (acc.objects.insert k' _).get? k' = some o := hx
              rw [RHTable.getElem?_insert_self acc.objects k' _ hE] at hx'
              exact absurd (Option.some.inj hx').symm (hNotEp _)
            · intro hx
              have hx2 : (spliceOutMidQueueNode st tid).objects.get? k' = some o := hx
              rw [hGet] at hx2
              exact absurd (Option.some.inj hx2).symm (hNotEp ep)
          · constructor
            · intro hx
              have hx' : (acc.objects.insert k' _).get? k = some o := hx
              rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE] at hx'
              exact hA.mp hx'
            · intro hx
              show (acc.objects.insert k' _).get? k = some o
              rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE]
              exact hA.mpr hx
        · exact ⟨hE, hA⟩
      | _ => exact ⟨hE, hA⟩)).2

/-- The composite leaves every object that is neither a TCB nor an endpoint
exactly as it found it — which is what carries the notification, CNode, Reply and
SchedContext conjuncts across without an argument of their own. -/
theorem sweptAndRestored_nonTcbNonEndpoint
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotTcb : ∀ t, o ≠ .tcb t) (hNotEp : ∀ e, o ≠ .endpoint e) :
    ((sweptAndRestored st v frame).objects[k]? = some o) ↔ (st.objects[k]? = some o) := by
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  by_cases hkv : k = v.toObjId
  · subst hkv
    constructor
    · intro hx
      rw [sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb _)
    · intro hx
      rw [lookupTcb_some_objects st v tcbV hLookup] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb tcbV)
  · unfold sweptAndRestored
    rw [restoreToReadyStaging_objects_ne _ v frame k hExt2 hkv]
    exact (removeFromAllEndpointQueues_nonEndpoint st v hExt1 k o hNotEp).trans
      (spliceOutMidQueueNode_nonTcb st v hInv k o hNotTcb)

/-- The composite touches no scheduler state. -/
theorem sweptAndRestored_scheduler_eq (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (sweptAndRestored st v frame).scheduler = st.scheduler := by
  unfold sweptAndRestored
  rw [Lifecycle.Suspend.restoreToReadyStaging_scheduler_eq,
    removeFromAllEndpointQueues_scheduler_eq]

/-- The mid-queue splice, read forwards: every pre-state TCB survives it as a
queue-link rewrite of itself. -/
theorem spliceOutMidQueueNode_tcb_forward (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (h : st.objects[k]? = some (.tcb t0)) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      tcbQueueLinkRewrite t' t0 := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact ⟨t0, h, tcbQueueLinkRewrite.refl t0⟩
  · rename_i tcb hT
    obtain ⟨t1, h1, hc1⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
      (fun p => { p with queueNext := tcb.queueNext }) hInv k t0 h
    obtain ⟨t2, h2, hc2⟩ := queueNeighbourPatch_tcb_forward _ tcb.queueNext
      (fun n => { n with queuePrev := tcb.queuePrev })
      (queueNeighbourPatch_invExt _ _ _ hInv) k t1 h1
    have r1 : tcbQueueLinkRewrite t1 t0 := by
      rcases hc1 with rfl | rfl
      · exact tcbQueueLinkRewrite.refl _
      · exact ⟨t0.queuePrev, t0.queuePPrev, tcb.queueNext, rfl⟩
    have r2 : tcbQueueLinkRewrite t2 t1 := by
      rcases hc2 with rfl | rfl
      · exact tcbQueueLinkRewrite.refl _
      · exact ⟨tcb.queuePrev, t1.queuePPrev, t1.queueNext, rfl⟩
    exact ⟨t2, h2, r2.trans r1⟩

/-- The composite, read forwards away from the swept thread. -/
theorem sweptAndRestored_tcb_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) (t0 : TCB) (hkv : k ≠ v.toObjId)
    (h : st.objects[k]? = some (.tcb t0)) :
    ∃ t', (sweptAndRestored st v frame).objects[k]? = some (.tcb t') ∧
      tcbQueueLinkRewrite t' t0 := by
  obtain ⟨t1, h1, hr⟩ := spliceOutMidQueueNode_tcb_forward st v hInv k t0 h
  exact ⟨t1, (sweptAndRestored_tcb_iff st v frame hInv k t1 hkv).mpr h1, hr⟩

/-- The composite rebinds no SchedContext. -/
theorem sweptAndRestored_sameSchedContextBindings
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    sameSchedContextBindings st (sweptAndRestored st v frame) := by
  intro tid tcb' hTcb'
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  refine ⟨t0, h0, ?_⟩
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · rfl
  · rw [restoredTcb_eq]

/-- The composite frames every thread's timeout budget. -/
theorem sweptAndRestored_timeoutBudgetFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    timeoutBudgetFrame st (sweptAndRestored st v frame) := by
  intro tid tcb' hTcb'
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  refine ⟨t0, h0, ?_⟩
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · rfl
  · rw [restoredTcb_eq]

/-- The composite frames the passive-server-idle reading.

The swept thread is the only thread whose `ipcState` moves, and it moves to
`.ready`, which `passiveServerIdleAllowed` admits — so the frame's pullback,
which fires only on threads in a **non**-allowed state, never reaches it. -/
theorem sweptAndRestored_passiveServerIdleFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV) :
    passiveServerIdleFrame st (sweptAndRestored st v frame) := by
  have hSched := sweptAndRestored_scheduler_eq st v frame
  refine ⟨fun tid tcb' hTcb' hUnbound hNotQ hNotCur hNA => ?_⟩
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨t0, h0, hUnbound, by rw [hSched] at hNotQ; exact hNotQ,
      by rw [hSched] at hNotCur; exact hNotCur, rfl⟩
  · exact absurd (by rw [restoredTcb_ipcState]; exact Or.inl rfl) hNA

/-- The composite frames the donation-owner reading, given that the swept thread
is not itself a donation owner — which the blocked-on-endpoint arm supplies,
since an owner is `.blockedOnReply`. -/
theorem sweptAndRestored_donationOwnerFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt) :
    donationOwnerFrame st (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨?_, ?_⟩
  · intro scId sc hsc
    exact (sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
      scId.toObjId (.schedContext sc) (by simp) (by simp)).mpr hsc
  · intro owner ownerTcb hOwner hUnbound hBlocked
    have hne : owner.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hOwner
      have hx : ownerTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hOwner)).symm
      obtain ⟨ep, rt, hb⟩ := hBlocked
      rw [hx] at hb
      exact hNotReply ep rt hb
    obtain ⟨t1, h1, hr⟩ := sweptAndRestored_tcb_forward st v frame hInv
      owner.toObjId ownerTcb hne hOwner
    obtain ⟨qp, qpp, qn, rfl⟩ := hr
    exact ⟨_, h1, hUnbound, hBlocked⟩

/-- The composite frames the reply linkage, given that the swept thread holds no
reply object — which the blocked-on-endpoint arm supplies, since a linked thread
is `.blockedOnReply` by reciprocity. -/
theorem sweptAndRestored_replyLinkageFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hUnlinked : tcbV.replyObject = none) :
    replyLinkageFrame st (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨replyLinkageFrame.callerAgree_of_objectAgree (fun rid r => ?_), ?_, ?_⟩
  · exact sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
      rid.toObjId (.reply r) (by simp) (by simp)
  · intro tid tcb' hTcb'
    obtain ⟨t0, h0, hcase⟩ :=
      sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
    refine ⟨t0, h0, ?_⟩
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
    · rfl
    · rw [restoredTcb_eq]
  · intro tid tcb rid hTcb hRO
    have hne : tid.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hTcb
      have hx : tcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hTcb)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    obtain ⟨t1, h1, hr⟩ := sweptAndRestored_tcb_forward st v frame hInv
      tid.toObjId tcb hne hTcb
    obtain ⟨qp, qpp, qn, rfl⟩ := hr
    exact ⟨_, h1, rfl, fun ep rt hb => ⟨ep, rt, hb⟩⟩

-- ============================================================================
-- §9  The composite's endpoint reading
-- ============================================================================

/-- **The composite's endpoint reading**, in the form every queue-shape conjunct
consumes: each queue is the pre-state's with the swept thread's boundary
occurrences advanced past it, and nothing else moved. -/
theorem sweptAndRestored_endpoint_queues
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (epId : SeLe4n.ObjId) (ep : Endpoint)
    (h : (sweptAndRestored st v frame).objects[epId]? = some (.endpoint ep)) :
    ∃ ep0, st.objects[epId]? = some (.endpoint ep0) ∧
      ep.sendQ =
        { head := if ep0.sendQ.head = some v then tcbV.queueNext else ep0.sendQ.head,
          tail := if ep0.sendQ.tail = some v then tcbV.queuePrev else ep0.sendQ.tail } ∧
      ep.receiveQ =
        { head := if ep0.receiveQ.head = some v then tcbV.queueNext else ep0.receiveQ.head,
          tail := if ep0.receiveQ.tail = some v then tcbV.queuePrev else ep0.receiveQ.tail } := by
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  have hVSplice : lookupTcb (spliceOutMidQueueNode st v) v = some tcbV :=
    lookupTcb_of_objects_of_not_reserved _ v tcbV
      (spliceOutMidQueueNode_victim_tcb st v tcbV hInv hLink hAcyc hLookup)
      (lookupTcb_some_not_reserved st v tcbV hLookup)
  have hEpNe : epId ≠ v.toObjId := by
    intro hEq
    rw [hEq, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at h
    cases h
  have h2 : (removeFromAllEndpointQueues st v).objects[epId]? = some (.endpoint ep) := by
    unfold sweptAndRestored at h
    rwa [restoreToReadyStaging_objects_ne _ v frame epId hExt2 hEpNe] at h
  obtain ⟨ep0, hEp0⟩ := removeFromAllEndpointQueues_endpoint_source st v hExt1 epId ep h2
  obtain ⟨_, hVal⟩ := removeFromAllEndpointQueues_endpoint_value st v hExt1 epId ep0 hEp0
  obtain ⟨hS, hR⟩ := hVal ep h2
  refine ⟨ep0, (spliceOutMidQueueNode_nonTcb st v hInv epId (.endpoint ep0) (by simp)).mp hEp0,
    ?_, ?_⟩
  · rw [hS]; exact removeThreadFromQueue_tcb_present _ ep0.sendQ v tcbV hVSplice
  · rw [hR]; exact removeThreadFromQueue_tcb_present _ ep0.receiveQ v tcbV hVSplice


-- ============================================================================
-- §10  The sharp pointwise reading, and the transports the conjuncts consume
-- ============================================================================

/-- A neighbour patch's TCB reading at any key, in closed form: the update fires
exactly at the patch's own target. -/
theorem queueNeighbourPatch_tcb_value (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (a : SeLe4n.ThreadId) (t0 : TCB)
    (hk : objs[a.toObjId]? = some (.tcb t0)) :
    (queueNeighbourPatch objs nid? upd)[a.toObjId]? =
      some (.tcb (if nid? = some a then upd t0 else t0)) := by
  by_cases hn : nid? = some a
  · rw [if_pos hn, queueNeighbourPatch_at_self' objs nid? a upd hInv t0 hn hk]
  · rw [if_neg hn]
    rw [queueNeighbourPatch_at_other objs nid? upd hInv a.toObjId
      (by
        intro nid hEq hObj
        exact hn (by rw [hEq, SeLe4n.ThreadId.toObjId_injective _ _ hObj]))]
    exact hk

/-- **The splice's sharp pointwise reading.**  The two patches commute at every
key but the swept thread's two neighbours, so one closed record describes the
whole operation: a thread's `queueNext` is rewritten exactly when it is the swept
thread's predecessor, its `queuePrev` exactly when it is the successor, and every
other field is untouched.

This is the description `tcbQueueLinkRewrite` under-approximates.  The weak form
is what the framing conjuncts need (they only ask that the *other* fields agree);
the sharp form is what the queue-shape conjuncts need, because they ask what the
rewritten links actually became. -/
theorem spliceOutMidQueueNode_tcb_value (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcbV)
    (a : SeLe4n.ThreadId) (t0 : TCB)
    (hPre : st.objects[a.toObjId]? = some (.tcb t0)) :
    (spliceOutMidQueueNode st tid).objects[a.toObjId]? =
      some (.tcb { t0 with
        queueNext := if tcbV.queuePrev = some a then tcbV.queueNext else t0.queueNext,
        queuePrev := if tcbV.queueNext = some a then tcbV.queuePrev else t0.queuePrev }) := by
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  have h1 := queueNeighbourPatch_tcb_value st.objects tcbV.queuePrev
    (fun p => { p with queueNext := tcbV.queueNext }) hInv a t0 hPre
  have h2 := queueNeighbourPatch_tcb_value
    (queueNeighbourPatch st.objects tcbV.queuePrev (fun p => { p with queueNext := tcbV.queueNext }))
    tcbV.queueNext (fun n => { n with queuePrev := tcbV.queuePrev })
    (queueNeighbourPatch_invExt _ _ _ hInv) a _ h1
  rw [h2]
  by_cases hp : tcbV.queuePrev = some a <;> by_cases hnx : tcbV.queueNext = some a <;>
    simp [hp, hnx]

/-- The composite's sharp pointwise reading away from the swept thread — the
sweep writes only endpoints and the restore only the swept thread, so the splice's
reading survives both. -/
theorem sweptAndRestored_tcb_value (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (a : SeLe4n.ThreadId) (t0 : TCB) (hav : a ≠ v)
    (hPre : st.objects[a.toObjId]? = some (.tcb t0)) :
    (sweptAndRestored st v frame).objects[a.toObjId]? =
      some (.tcb { t0 with
        queueNext := if tcbV.queuePrev = some a then tcbV.queueNext else t0.queueNext,
        queuePrev := if tcbV.queueNext = some a then tcbV.queuePrev else t0.queuePrev }) :=
  (sweptAndRestored_tcb_iff st v frame hInv a.toObjId _
    (fun hEq => hav (SeLe4n.ThreadId.toObjId_injective _ _ hEq))).mpr
    (spliceOutMidQueueNode_tcb_value st v tcbV hInv hLookup a t0 hPre)

/-- The swept thread points at nothing in the post-state: the restore cleared its
links. -/
theorem sweptAndRestored_not_victim_of_next
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (a b : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : (sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb tcbA))
    (hNext : tcbA.queueNext = some b) : a ≠ v := by
  intro hav
  subst hav
  rw [sweptAndRestored_victim_tcb st a frame tcbV hInv hLink hAcyc hLookup] at hA
  have hx : tcbA = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hA)).symm
  rw [hx, restoredTcb_queueNext] at hNext
  cases hNext

/-- Nothing in the post-state points at the swept thread.  Either the pointer is
the skip the splice installed — which would make the swept thread its own
successor — or it is a pre-state edge, whose source link integrity identifies as
the swept thread's predecessor, and that source was patched. -/
theorem sweptAndRestored_no_next_to_victim
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (a b : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : (sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb tcbA))
    (hNext : tcbA.queueNext = some b) : b ≠ v := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  intro hbv
  subst hbv
  by_cases hav : a = b
  · subst hav
    rw [sweptAndRestored_victim_tcb st a frame tcbV hInv hLink hAcyc hLookup] at hA
    have hx : tcbA = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hx, restoredTcb_queueNext] at hNext
    cases hNext
  · obtain ⟨t0, h0, _⟩ :=
      sweptAndRestored_tcb_pullback st b frame tcbV hInv hLink hAcyc hLookup a.toObjId tcbA hA
    rw [sweptAndRestored_tcb_value st b frame tcbV hInv hLookup a t0 hav h0] at hA
    have hx : tcbA = _ := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hx] at hNext
    simp only at hNext
    by_cases hp : tcbV.queuePrev = some a
    · rw [if_pos hp] at hNext
      exact hAcyc b (.single b b tcbV hVObj hNext)
    · rw [if_neg hp] at hNext
      obtain ⟨tB, hB, hBP⟩ := hLink.1 a t0 h0 b hNext
      rw [hVObj] at hB
      have hy : tB = tcbV := (KernelObject.tcb.inj (Option.some.inj hB)).symm
      rw [hy] at hBP
      exact hp hBP

/-- Away from the swept thread the composite does not move a thread's blocking
state — it only relinks. -/
theorem sweptAndRestored_tcb_ipcState
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (a : SeLe4n.ThreadId) (tA t0 : TCB) (hav : a ≠ v)
    (hA : (sweptAndRestored st v frame).objects[a.toObjId]? = some (.tcb tA))
    (h0 : st.objects[a.toObjId]? = some (.tcb t0)) :
    tA.ipcState = t0.ipcState := by
  rw [sweptAndRestored_tcb_value st v frame tcbV hInv hLookup a t0 hav h0] at hA
  have hx : tA = _ := (KernelObject.tcb.inj (Option.some.inj hA)).symm
  rw [hx]

/-- The sweep turns endpoints into endpoints: the body's write at an endpoint key
is itself an endpoint, and every other write is elsewhere. -/
theorem removeFromAllEndpointQueues_endpoint_forward (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (ep0 : Endpoint)
    (h : (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint ep0)) :
    ∃ ep, (removeFromAllEndpointQueues st tid).objects[k]? = some (.endpoint ep) := by
  rw [removeFromAllEndpointQueues_eq_fold]
  exact (RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ ∃ ep, acc.objects[k]? = some (.endpoint ep))
    hExt ⟨hExt, ep0, h⟩
    (by
      rintro acc k' v' hGet ⟨hE, e, hA⟩
      unfold endpointSweepBody
      cases v' with
      | endpoint ep =>
        simp only
        split
        · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
          by_cases hK : k' = k
          · subst hK
            exact ⟨_, RHTable.getElem?_insert_self acc.objects k' _ hE⟩
          · refine ⟨e, ?_⟩
            show (acc.objects.insert k' _).get? k = _
            rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE]
            exact hA
        · exact ⟨hE, e, hA⟩
      | _ => exact ⟨hE, e, hA⟩)).2

/-- **The composite's endpoint reading, read forwards** — the direction a
conjunct that starts from a *pre-state* endpoint needs.  The queue shapes are
`sweptAndRestored_endpoint_queues`'s, transported through the identification of
the two endpoints at the same key. -/
theorem sweptAndRestored_endpoint_forward
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (epId : SeLe4n.ObjId) (ep0 : Endpoint)
    (h : st.objects[epId]? = some (.endpoint ep0)) :
    ∃ ep, (sweptAndRestored st v frame).objects[epId]? = some (.endpoint ep) ∧
      ep.sendQ =
        { head := if ep0.sendQ.head = some v then tcbV.queueNext else ep0.sendQ.head,
          tail := if ep0.sendQ.tail = some v then tcbV.queuePrev else ep0.sendQ.tail } ∧
      ep.receiveQ =
        { head := if ep0.receiveQ.head = some v then tcbV.queueNext else ep0.receiveQ.head,
          tail := if ep0.receiveQ.tail = some v then tcbV.queuePrev else ep0.receiveQ.tail } := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hExt1 : (spliceOutMidQueueNode st v).objects.invExt :=
    spliceOutMidQueueNode_preserves_objects_invExt st v hInv
  have hExt2 : (removeFromAllEndpointQueues st v).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt st v hInv
  have hEpNe : epId ≠ v.toObjId := by
    intro hEq
    rw [hEq, hVObj] at h
    cases h
  have hSp : (spliceOutMidQueueNode st v).objects[epId]? = some (.endpoint ep0) :=
    (spliceOutMidQueueNode_nonTcb st v hInv epId (.endpoint ep0) (by simp)).mpr h
  obtain ⟨ep, hEp⟩ := removeFromAllEndpointQueues_endpoint_forward st v hExt1 epId ep0 hSp
  have hPost : (sweptAndRestored st v frame).objects[epId]? = some (.endpoint ep) := by
    unfold sweptAndRestored
    rw [restoreToReadyStaging_objects_ne _ v frame epId hExt2 hEpNe]
    exact hEp
  obtain ⟨ep0', hEp0', hS, hR⟩ :=
    sweptAndRestored_endpoint_queues st v frame tcbV hInv hLink hAcyc hLookup epId ep hPost
  rw [h] at hEp0'
  have hx : ep0' = ep0 := (KernelObject.endpoint.inj (Option.some.inj hEp0')).symm
  rw [hx] at hS hR
  exact ⟨ep, hPost, hS, hR⟩

/-- **WS-RR RR7.22 (residual)**: a blocked thread's membership witness survives
the sweep, per queue.

Four cases, and only the last needs a hypothesis.  A thread that *was* the head
stays the head (it is not the swept thread, so the promotion does not fire on it).
A witness other than the swept thread keeps its link — unless it is the swept
thread's predecessor, in which case link integrity says its link named the swept
thread rather than this thread, so that case is vacuous.  A witness that *is* the
swept thread hands its link to its own predecessor when it has one; when it has
none, `sweptSuccessorAnchored` is what says the queue was headed there, so the
promotion re-heads it at this thread. -/
theorem sweptAndRestored_membership_witness
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (tid : SeLe4n.ThreadId) (hidv : tid ≠ v) (q0 : IntrusiveQueue)
    (hAnchor : tcbV.queuePrev = none → tcbV.queueNext = some tid → q0.head = some v)
    (hPre : q0.head = some tid ∨
      ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ TCB.queueNext prevTcb = some tid) :
    (if q0.head = some v then tcbV.queueNext else q0.head) = some tid ∨
      ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        (sweptAndRestored st v frame).objects[prev.toObjId]? = some (.tcb prevTcb) ∧
        TCB.queueNext prevTcb = some tid := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  rcases hPre with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
  · left
    rw [if_neg (by rw [hHd]; intro h; exact hidv (Option.some.inj h))]
    exact hHd
  · by_cases hpv : prev = v
    · have hEqT : prevTcb = tcbV := by
        rw [hpv, hVObj] at hPrev
        exact (KernelObject.tcb.inj (Option.some.inj hPrev)).symm
      rw [hEqT] at hPN
      cases hq : tcbV.queuePrev with
      | none =>
        left
        rw [if_pos (hAnchor hq hPN)]
        exact hPN
      | some p =>
        right
        obtain ⟨pTcb, hP, hPNext⟩ := hLink.2 v tcbV hVObj p hq
        have hpv2 : p ≠ v := by
          intro h
          rw [h, hVObj] at hP
          have hy : pTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hP)).symm
          rw [hy] at hPNext
          exact hAcyc v (.single v v tcbV hVObj hPNext)
        refine ⟨p, _,
          sweptAndRestored_tcb_value st v frame tcbV hInv hLookup p pTcb hpv2 hP, ?_⟩
        show (if tcbV.queuePrev = some p then tcbV.queueNext else pTcb.queueNext) = some tid
        rw [if_pos hq]
        exact hPN
    · right
      by_cases hpp : tcbV.queuePrev = some prev
      · exfalso
        obtain ⟨tA, hA, hAN⟩ := hLink.2 v tcbV hVObj prev hpp
        rw [hPrev] at hA
        have hx : tA = prevTcb := (KernelObject.tcb.inj (Option.some.inj hA)).symm
        rw [hx, hPN] at hAN
        exact hidv (Option.some.inj hAN)
      · refine ⟨prev, _,
          sweptAndRestored_tcb_value st v frame tcbV hInv hLookup prev prevTcb hpv hPrev, ?_⟩
        show (if tcbV.queuePrev = some prev then tcbV.queueNext else prevTcb.queueNext) = some tid
        rw [if_neg hpp]
        exact hPN

-- ============================================================================
-- §11  The conjuncts of `ipcInvariantFull`, one at a time
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: notifications are untouched. -/
theorem sweptAndRestored_ipcInvariant
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : ipcInvariant st) : ipcInvariant (sweptAndRestored st v frame) := by
  intro oid ntfn hN
  exact h oid ntfn ((sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
    oid (.notification ntfn) (by simp) (by simp)).mp hN)

/-- **WS-RR RR7.22 (residual)**: badges at rest live in notifications and CNodes,
neither of which the composite writes. -/
theorem sweptAndRestored_badgeWellFormed
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : badgeWellFormed st) : badgeWellFormed (sweptAndRestored st v frame) := by
  refine ⟨?_, ?_⟩
  · intro oid ntfn badge hN hB
    exact h.1 oid ntfn badge
      ((sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
        oid (.notification ntfn) (by simp) (by simp)).mp hN) hB
  · intro oid cn slot cap badge hC hL hB
    exact h.2 oid cn slot cap badge
      ((sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
        oid (.cnode cn) (by simp) (by simp)).mp hC) hL hB

/-- **WS-RR RR7.22 (residual)**: no message is written, so every bound carries
back to the thread the pullback names. -/
theorem sweptAndRestored_allPendingMessagesBounded
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (sweptAndRestored st v frame) := by
  intro tid tcb' msg hTcb' hMsg
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · exact h tid t0 msg h0 hMsg
  · exact h tid t0 msg h0 (by rw [restoredTcb_eq] at hMsg; exact hMsg)

/-- **WS-RR RR7.22 (residual)**: the swept thread lands in `.ready`, whose arm is
`True`; every other thread keeps both its blocking state and its message. -/
theorem sweptAndRestored_blockedThreadsPendingMessageConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent (sweptAndRestored st v frame) := by
  intro tid tcb' hTcb'
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · exact h tid t0 h0
  · rw [restoredTcb_eq]
    simp only

/-- **WS-RR RR7.22 (residual)**: a `.blockedOnReply` thread in the post-state was
one in the pre-state — the swept thread is not, since it is `.ready`. -/
theorem sweptAndRestored_blockedOnReplyHasTarget
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (sweptAndRestored st v frame) := by
  intro tid tcb' epId rt hTcb' hBlocked
  obtain ⟨t0, h0, hcase⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
  rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
  · exact h tid t0 epId rt h0 hBlocked
  · rw [restoredTcb_ipcState] at hBlocked
    cases hBlocked

/-- **WS-RR RR7.22 (residual)**: no SchedContext is rebound, so a post-state
donation cycle is a pre-state one. -/
theorem sweptAndRestored_donationChainAcyclic
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : donationChainAcyclic st) :
    donationChainAcyclic (sweptAndRestored st v frame) := by
  have hBind := sweptAndRestored_sameSchedContextBindings st v frame tcbV hInv hLink hAcyc hLookup
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  obtain ⟨tc1, hP1, hEq1⟩ := hBind tid1 tcb1 h1
  obtain ⟨tc2, hP2, hEq2⟩ := hBind tid2 tcb2 h2
  exact h tid1 tid2 tc1 tc2 scId1 scId2 hP1 hP2
    (by rw [hEq1]; exact hB1) (by rw [hEq2]; exact hB2)

/-- **WS-RR RR7.22 (residual)**: the composite preserves forward blocking
propagation.

A post-state edge is either a pre-state edge, where the conjunct applies
directly, or the skip the splice installed — and a skip is a two-edge pre-state
path through the swept thread, so the conjunct applies twice and composes.  That
composition is why this conjunct, and not `queueNextBlockingConsistent`, is the
one the argument is stated on: `queueNextBlockingMatch`'s catch-all makes it
non-transitive through a swept thread in a non-blocking state. -/
theorem sweptAndRestored_queueNextTargetBlocked
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hTgt : queueNextTargetBlocked st) :
    queueNextTargetBlocked (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  intro a b tcbA tcbB hA hB hNext
  have hav : a ≠ v :=
    sweptAndRestored_not_victim_of_next st v frame tcbV hInv hLink hAcyc hLookup a b tcbA hA hNext
  have hbv : b ≠ v :=
    sweptAndRestored_no_next_to_victim st v frame tcbV hInv hLink hAcyc hLookup a b tcbA hA hNext
  obtain ⟨t0b, h0b, _⟩ :=
    sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup b.toObjId tcbB hB
  have hbIp : tcbB.ipcState = t0b.ipcState :=
    sweptAndRestored_tcb_ipcState st v frame tcbV hInv hLookup b tcbB t0b hbv hB h0b
  rcases sweptAndRestored_edge_source st v frame tcbV hInv hLink hAcyc hLookup a b tcbA hA hNext
    with ⟨t0a, h0a, hE⟩ | ⟨t0a, h0a, hEv, hVb⟩
  · have haIp : tcbA.ipcState = t0a.ipcState :=
      sweptAndRestored_tcb_ipcState st v frame tcbV hInv hLookup a tcbA t0a hav hA h0a
    rw [haIp, hbIp]
    exact hTgt a b t0a t0b h0a h0b hE
  · have haIp : tcbA.ipcState = t0a.ipcState :=
      sweptAndRestored_tcb_ipcState st v frame tcbV hInv hLookup a tcbA t0a hav hA h0a
    have h1 := hTgt a v t0a tcbV h0a hVObj hEv
    have h2 := hTgt v b tcbV t0b hVObj h0b hVb
    rw [haIp, hbIp]
    exact ⟨fun ep h => h2.1 ep (h1.1 ep h), fun ep h => h2.2 ep (h1.2 ep h)⟩

/-- **WS-RR RR7.22 (residual)**: cross-queue links stay excluded.  Read off the
forward propagation above, one blocking state at a time. -/
theorem sweptAndRestored_queueNextBlockingConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hTgt : queueNextTargetBlocked st) :
    queueNextBlockingConsistent (sweptAndRestored st v frame) := by
  intro a b tcbA tcbB hA hB hNext
  have hT := sweptAndRestored_queueNextTargetBlocked st v frame tcbV hInv hLink hAcyc hLookup hTgt
    a b tcbA tcbB hA hB hNext
  unfold queueNextBlockingMatch
  cases hIA : tcbA.ipcState with
  | blockedOnSend ep =>
    rcases hT.2 ep (Or.inl hIA) with h | h <;> rw [h] <;> rfl
  | blockedOnCall ep =>
    rcases hT.2 ep (Or.inr hIA) with h | h <;> rw [h] <;> rfl
  | blockedOnReceive ep =>
    rw [hT.1 ep hIA]
  | _ => simp

/-- **WS-RR RR7.22 (residual)**: no thread appears twice.

The self-loop clause is the edge decomposition again: a post-state self-loop is
either a pre-state self-loop or a two-edge cycle through the swept thread, and
acyclicity refuses the latter.  The head-disjointness clause is the one place the
sweep could genuinely create an overlap — promoting the swept thread's successor
into a head that the *other* queue already holds — and the two blocking conjuncts
refuse it: the promoted thread would have to be blocked on both sides of the same
endpoint at once. -/
theorem sweptAndRestored_endpointQueueNoDup
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hNoDup : endpointQueueNoDup st) (hHead : queueHeadBlockedConsistent st)
    (hTgt : queueNextTargetBlocked st) :
    endpointQueueNoDup (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  intro oid ep hEp
  obtain ⟨ep0, hEp0, hS, hR⟩ :=
    sweptAndRestored_endpoint_queues st v frame tcbV hInv hLink hAcyc hLookup oid ep hEp
  refine ⟨?_, ?_⟩
  · intro tid tcb hTcb hSelf
    rcases sweptAndRestored_edge_source st v frame tcbV hInv hLink hAcyc hLookup
      tid tid tcb hTcb hSelf with ⟨t0, h0, hE⟩ | ⟨t0, h0, hEv, hVb⟩
    · exact (hNoDup oid ep0 hEp0).1 tid t0 h0 hE
    · exact hAcyc tid (.cons tid v tid t0 h0 hEv (.single v tid tcbV hVObj hVb))
  · have hSH : ep.sendQ.head =
        (if ep0.sendQ.head = some v then tcbV.queueNext else ep0.sendQ.head) := by rw [hS]
    have hRH : ep.receiveQ.head =
        (if ep0.receiveQ.head = some v then tcbV.queueNext else ep0.receiveQ.head) := by rw [hR]
    rw [hSH, hRH]
    by_cases hsv : ep0.sendQ.head = some v <;> by_cases hrv : ep0.receiveQ.head = some v
    · exfalso
      rcases (hNoDup oid ep0 hEp0).2 with h | h | h
      · rw [h] at hsv; cases hsv
      · rw [h] at hrv; cases hrv
      · exact h (by rw [hsv, hrv])
    · rw [if_pos hsv, if_neg hrv]
      cases hn : tcbV.queueNext with
      | none => exact Or.inl rfl
      | some w =>
        refine Or.inr (Or.inr ?_)
        intro hEq
        obtain ⟨tW, hW, _⟩ := hLink.1 v tcbV hVObj w hn
        have hRecv : tW.ipcState = .blockedOnReceive oid :=
          (hHead oid ep0 w tW hEp0 hW).1 hEq.symm
        have hSend := (hHead oid ep0 v tcbV hEp0 hVObj).2 hsv
        rcases (hTgt v w tcbV tW hVObj hW hn).2 oid hSend with h | h <;> rw [hRecv] at h <;> cases h
    · rw [if_neg hsv, if_pos hrv]
      cases hn : tcbV.queueNext with
      | none => exact Or.inr (Or.inl rfl)
      | some w =>
        refine Or.inr (Or.inr ?_)
        intro hEq
        obtain ⟨tW, hW, _⟩ := hLink.1 v tcbV hVObj w hn
        have hSendW := (hHead oid ep0 w tW hEp0 hW).2 hEq
        have hRecvV := (hHead oid ep0 v tcbV hEp0 hVObj).1 hrv
        have hRecvW := (hTgt v w tcbV tW hVObj hW hn).1 oid hRecvV
        rcases hSendW with h | h <;> rw [hRecvW] at h <;> cases h
    · rw [if_neg hsv, if_neg hrv]
      exact (hNoDup oid ep0 hEp0).2

/-- **WS-RR RR7.22 (residual)**: every blocked thread still sits in the queue its
blocking state names.  The three blocking arms are the witness lemma applied to
the queue each one names; the swept thread itself lands in `.ready`, whose arm is
`True`. -/
theorem sweptAndRestored_ipcStateQueueMembershipConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hMem : ipcStateQueueMembershipConsistent st)
    (hAnchor : sweptSuccessorAnchored st v) :
    ipcStateQueueMembershipConsistent (sweptAndRestored st v frame) := by
  intro tid tcb' hTcb'
  by_cases hidv : tid = v
  · rw [hidv, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hTcb'
    have hx : tcb' = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hTcb')).symm
    rw [hx, restoredTcb_ipcState]
    trivial
  · obtain ⟨t0, h0, _⟩ :=
      sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
    have hIp : tcb'.ipcState = t0.ipcState :=
      sweptAndRestored_tcb_ipcState st v frame tcbV hInv hLookup tid tcb' t0 hidv hTcb' h0
    have hPre := hMem tid t0 h0
    rw [hIp]
    cases hI : t0.ipcState with
    | blockedOnSend epId =>
      rw [hI] at hPre
      obtain ⟨ep0, hEp0, hW⟩ := hPre
      obtain ⟨ep, hEp, hS, _⟩ :=
        sweptAndRestored_endpoint_forward st v frame tcbV hInv hLink hAcyc hLookup epId ep0 hEp0
      refine ⟨ep, hEp, ?_⟩
      have hSH : ep.sendQ.head =
          (if ep0.sendQ.head = some v then tcbV.queueNext else ep0.sendQ.head) := by rw [hS]
      rw [hSH]
      exact sweptAndRestored_membership_witness st v frame tcbV hInv hLink hAcyc hLookup
        tid hidv ep0.sendQ
        (fun hq hn => (hAnchor tcbV hLookup hq tid hn t0 h0 epId ep0 hEp0).1 (Or.inl hI)) hW
    | blockedOnCall epId =>
      rw [hI] at hPre
      obtain ⟨ep0, hEp0, hW⟩ := hPre
      obtain ⟨ep, hEp, hS, _⟩ :=
        sweptAndRestored_endpoint_forward st v frame tcbV hInv hLink hAcyc hLookup epId ep0 hEp0
      refine ⟨ep, hEp, ?_⟩
      have hSH : ep.sendQ.head =
          (if ep0.sendQ.head = some v then tcbV.queueNext else ep0.sendQ.head) := by rw [hS]
      rw [hSH]
      exact sweptAndRestored_membership_witness st v frame tcbV hInv hLink hAcyc hLookup
        tid hidv ep0.sendQ
        (fun hq hn => (hAnchor tcbV hLookup hq tid hn t0 h0 epId ep0 hEp0).1 (Or.inr hI)) hW
    | blockedOnReceive epId =>
      rw [hI] at hPre
      obtain ⟨ep0, hEp0, hW⟩ := hPre
      obtain ⟨ep, hEp, _, hR⟩ :=
        sweptAndRestored_endpoint_forward st v frame tcbV hInv hLink hAcyc hLookup epId ep0 hEp0
      refine ⟨ep, hEp, ?_⟩
      have hRH : ep.receiveQ.head =
          (if ep0.receiveQ.head = some v then tcbV.queueNext else ep0.receiveQ.head) := by rw [hR]
      rw [hRH]
      exact sweptAndRestored_membership_witness st v frame tcbV hInv hLink hAcyc hLookup
        tid hidv ep0.receiveQ
        (fun hq hn => (hAnchor tcbV hLookup hq tid hn t0 h0 epId ep0 hEp0).2 hI) hW
    | _ => trivial

/-- **WS-RR RR7.22 (residual)**: caller/Reply reciprocity survives.

The swept thread holds no Reply object at all — `replyObject_none_of_not_blockedOnReply`
derives that from the conjunct itself given that the thread being cancelled is
blocked on an endpoint rather than on a reply — so no Reply names it, and the one
clause the restore could break (a named caller must be `.blockedOnReply`, and the
swept thread becomes `.ready`) has no instance. -/
theorem sweptAndRestored_replyCallerLinkage
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt)
    (h : replyCallerLinkage st) :
    replyCallerLinkage (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hUnlinked : tcbV.replyObject = none :=
    replyObject_none_of_not_blockedOnReply st h v tcbV hVObj hNotReply
  have hRep : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      (sweptAndRestored st v frame).objects[rid.toObjId]? = some (.reply r) ↔
        st.objects[rid.toObjId]? = some (.reply r) :=
    fun rid r => sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
      rid.toObjId (.reply r) (by simp) (by simp)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro tid tcb' rid hTcb' hRO
    obtain ⟨t0, h0, hcase⟩ :=
      sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hTcb'
    have hROpre : t0.replyObject = some rid := by
      rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
      · exact hRO
      · rw [restoredTcb_eq] at hRO; exact hRO
    obtain ⟨r, hr, hrc⟩ := h.1.1 tid t0 rid h0 hROpre
    exact ⟨r, (hRep rid r).mpr hr, hrc⟩
  · intro rid r tid hr hrc
    obtain ⟨t0, h0, hRO, ep, rt, hBlk⟩ := h.1.2 rid r tid ((hRep rid r).mp hr) hrc
    have hidv : tid ≠ v := by
      intro hEq
      rw [hEq, hVObj] at h0
      have hx : t0 = tcbV := (KernelObject.tcb.inj (Option.some.inj h0)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    obtain ⟨t1, h1, hrw⟩ :=
      sweptAndRestored_tcb_forward st v frame hInv tid.toObjId t0
        (fun hEq => hidv (SeLe4n.ThreadId.toObjId_injective _ _ hEq)) h0
    obtain ⟨qp, qpp, qn, rfl⟩ := hrw
    exact ⟨_, h1, hRO, ep, rt, hBlk⟩
  · intro tid tcb' ep rt hTcb' hBlk
    by_cases hidv : tid = v
    · exfalso
      rw [hidv, sweptAndRestored_victim_tcb st v frame tcbV hInv hLink hAcyc hLookup] at hTcb'
      have hx : tcb' = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hTcb')).symm
      rw [hx, restoredTcb_ipcState] at hBlk
      cases hBlk
    · obtain ⟨t0, h0, hcase⟩ :=
        sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup
          tid.toObjId tcb' hTcb'
      have hIp : tcb'.ipcState = t0.ipcState :=
        sweptAndRestored_tcb_ipcState st v frame tcbV hInv hLookup tid tcb' t0 hidv hTcb' h0
      obtain ⟨rid, hrid⟩ := h.2 tid t0 ep rt h0 (by rw [← hIp]; exact hBlk)
      refine ⟨rid, ?_⟩
      rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨hEq, _⟩
      · exact hrid
      · exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ hEq) hidv

/-- **WS-RR RR7.22 (residual)**: the server-first receive stash stays well formed.

The restore *clears* the swept thread's stash, so both clauses lose an instance
rather than gaining one: the well-formedness clause is vacuous there, and the
injectivity clause can no longer be witnessed by it. -/
theorem sweptAndRestored_pendingReceiveReplyWellFormed
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed (sweptAndRestored st v frame) := by
  -- Away from the swept thread the stash and the blocking state both survive; at the
  -- swept thread the restore clears the stash, so both clauses are vacuous there.
  have hPull : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB) (rid : SeLe4n.ReplyId),
      (sweptAndRestored st v frame).getTcb? tid = some tcb' →
      tcb'.pendingReceiveReply = some rid →
      ∃ t0, st.getTcb? tid = some t0 ∧ t0.pendingReceiveReply = some rid ∧
        tcb'.ipcState = t0.ipcState := by
    intro tid tcb' rid hTcb' hStash
    have hObj : (sweptAndRestored st v frame).objects[tid.toObjId]? = some (.tcb tcb') :=
      (SystemState.getTcb?_eq_some_iff _ tid tcb').mp hTcb'
    obtain ⟨t0, h0, hcase⟩ :=
      sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc hLookup tid.toObjId tcb' hObj
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ tid t0).mpr h0, hStash, rfl⟩
    · rw [restoredTcb_pendingReceiveReply] at hStash
      cases hStash
  refine ⟨?_, ?_⟩
  · intro tid tcb' rid hTcb' hStash
    obtain ⟨t0, h0, hStash0, hIp⟩ := hPull tid tcb' rid hTcb' hStash
    obtain ⟨⟨ep, hEp⟩, r, hr, hrc⟩ := h.1 tid t0 rid h0 hStash0
    refine ⟨⟨ep, by rw [hIp]; exact hEp⟩, r, ?_, hrc⟩
    exact (SystemState.getReply?_eq_some_iff (sweptAndRestored st v frame) rid r).mpr
      ((sweptAndRestored_nonTcbNonEndpoint st v frame tcbV hInv hLink hAcyc hLookup
        rid.toObjId (.reply r) (by simp) (by simp)).mpr
        ((SystemState.getReply?_eq_some_iff st rid r).mp hr))
  · intro tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hs1 hs2
    obtain ⟨t1, ht1, hst1, _⟩ := hPull tid₁ tcb₁ rid h1 hs1
    obtain ⟨t2, ht2, hst2, _⟩ := hPull tid₂ tcb₂ rid h2 hs2
    exact h.2 tid₁ tid₂ t1 t2 rid ht1 ht2 hst1 hst2

/-- **WS-RR RR7.22 (residual)**: a queue head still carries the blocking state its
side demands.

A promoted head is the swept thread's successor, and forward propagation carries
the swept thread's own head-blocking state onto it; a head that was not promoted
kept its state and its position.  Neither case can be the swept thread itself,
because nothing in the post-state points at it. -/
theorem sweptAndRestored_queueHeadBlockedConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hHead : queueHeadBlockedConsistent st) (hTgt : queueNextTargetBlocked st) :
    queueHeadBlockedConsistent (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hPromNeV : ∀ (q : IntrusiveQueue) (x : SeLe4n.ThreadId),
      (if q.head = some v then tcbV.queueNext else q.head) = some x → x ≠ v := by
    intro q x hx hEq
    by_cases hc : q.head = some v
    · rw [if_pos hc, hEq] at hx
      exact hAcyc v (.single v v tcbV hVObj hx)
    · rw [if_neg hc, hEq] at hx
      exact hc hx
  intro epId ep hd tcbHd hEp hHd
  obtain ⟨ep0, hEp0, hS, hR⟩ :=
    sweptAndRestored_endpoint_queues st v frame tcbV hInv hLink hAcyc hLookup epId ep hEp
  constructor
  · intro hRHead
    rw [hR] at hRHead
    have hdv : hd ≠ v := hPromNeV ep0.receiveQ hd hRHead
    obtain ⟨t0, h0, hcase⟩ := sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc
      hLookup hd.toObjId tcbHd hHd
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨hEq, _⟩
    · by_cases hc : ep0.receiveQ.head = some v
      · rw [if_pos hc] at hRHead
        exact (hTgt v hd tcbV t0 hVObj h0 hRHead).1 epId
          ((hHead epId ep0 v tcbV hEp0 hVObj).1 hc)
      · rw [if_neg hc] at hRHead
        exact (hHead epId ep0 hd t0 hEp0 h0).1 hRHead
    · exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ hEq) hdv
  · intro hSHead
    rw [hS] at hSHead
    have hdv : hd ≠ v := hPromNeV ep0.sendQ hd hSHead
    obtain ⟨t0, h0, hcase⟩ := sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc
      hLookup hd.toObjId tcbHd hHd
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨hEq, _⟩
    · by_cases hc : ep0.sendQ.head = some v
      · rw [if_pos hc] at hSHead
        exact (hTgt v hd tcbV t0 hVObj h0 hSHead).2 epId
          ((hHead epId ep0 v tcbV hEp0 hVObj).2 hc)
      · rw [if_neg hc] at hSHead
        exact (hHead epId ep0 hd t0 hEp0 h0).2 hSHead
    · exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ hEq) hdv

/-- **WS-RR RR7.22 (residual)**: a queue tail still carries the blocking state its
side demands.

Dual to the head, and this is where `sweptPredecessorBlocked` is spent: a
promoted tail is the swept thread's *predecessor*, and no conjunct propagates
blockedness backwards along `queueNext`. -/
theorem sweptAndRestored_endpointQueueTailBlockedConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hAcyc : tcbQueueChainAcyclic st) (hLookup : lookupTcb st v = some tcbV)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hPred : sweptPredecessorBlocked st v) :
    endpointQueueTailBlockedConsistent (sweptAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hPromNeV : ∀ (q : IntrusiveQueue) (x : SeLe4n.ThreadId),
      (if q.tail = some v then tcbV.queuePrev else q.tail) = some x → x ≠ v := by
    intro q x hx hEq
    by_cases hc : q.tail = some v
    · rw [if_pos hc, hEq] at hx
      obtain ⟨tA, hA, hAN⟩ := hLink.2 v tcbV hVObj v hx
      rw [hVObj] at hA
      have hy : tA = tcbV := (KernelObject.tcb.inj (Option.some.inj hA)).symm
      rw [hy] at hAN
      exact hAcyc v (.single v v tcbV hVObj hAN)
    · rw [if_neg hc, hEq] at hx
      exact hc hx
  intro epId ep tl tcbTl hEp hTl
  obtain ⟨ep0, hEp0, hS, hR⟩ :=
    sweptAndRestored_endpoint_queues st v frame tcbV hInv hLink hAcyc hLookup epId ep hEp
  constructor
  · intro hRTail
    rw [hR] at hRTail
    have htv : tl ≠ v := hPromNeV ep0.receiveQ tl hRTail
    obtain ⟨t0, h0, hcase⟩ := sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc
      hLookup tl.toObjId tcbTl hTl
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨hEq, _⟩
    · by_cases hc : ep0.receiveQ.tail = some v
      · rw [if_pos hc] at hRTail
        exact (hPred epId ep0 tcbV hEp0 hLookup tl hRTail t0 h0).2 hc
      · rw [if_neg hc] at hRTail
        exact (hTail epId ep0 tl t0 hEp0 h0).1 hRTail
    · exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ hEq) htv
  · intro hSTail
    rw [hS] at hSTail
    have htv : tl ≠ v := hPromNeV ep0.sendQ tl hSTail
    obtain ⟨t0, h0, hcase⟩ := sweptAndRestored_tcb_pullback st v frame tcbV hInv hLink hAcyc
      hLookup tl.toObjId tcbTl hTl
    rcases hcase with ⟨_, qp, qpp, qn, rfl⟩ | ⟨hEq, _⟩
    · by_cases hc : ep0.sendQ.tail = some v
      · rw [if_pos hc] at hSTail
        exact (hPred epId ep0 tcbV hEp0 hLookup tl hSTail t0 h0).1 hc
      · rw [if_neg hc] at hSTail
        exact (hTail epId ep0 tl t0 hEp0 h0).2 hSTail
    · exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ hEq) htv

-- ============================================================================
-- §12  The keystone: the whole bundle
-- ============================================================================

/-- **WS-RR RR7.22 (residual) — the keystone**: the swept-and-restored composite
preserves the whole of `ipcInvariantFull`.

Three hypotheses beyond the bundle, and each is a fact about the thread being
cancelled rather than about the operation:

* `hAllBudgetsNone` — the timeout-budget discipline every IPC bundle in the tree
  takes, and the only way to establish `blockedThreadTimeoutConsistent` on a
  post-state where a thread has *left* a blocking state.  Transporting the
  conjunct itself is impossible here: it says a budget-carrying thread is
  blocked, and the swept thread becomes `.ready`.
* `hNotReply` — the swept thread is not `.blockedOnReply`.  Supplied by the
  cancellation arm, which fires only on the four endpoint/notification blocking
  states, and it is what makes the donation-owner and reply-linkage frames
  available: `replyObject_none_of_not_blockedOnReply` turns it into "holds no
  Reply", from the bundle's own reciprocity.
* `hCoh` — the three queue-coherence facts of §1, which `ipcInvariantFull` does
  not entail.  See the module header.

`hInv` (the object-store extension invariant) is not part of the bundle and is
carried separately, exactly as `sweptAndRestored_dualQueueSystemInvariant` carries
it.

The `_preserves_ipcInvariantFull` suffix is not a stylistic choice: it is the name
`scripts/check_ipc_invariant_dethreading.py` **derives** the bundle family from, so
a whole-bundle result spelled any other way would be invisible to the gate that
holds every such statement de-threaded.  The per-conjunct results above are named
for the conjunct they establish, because they are not members of that family. -/
theorem sweptAndRestored_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt)
    (hCoh : sweptThreadQueueCoherent st v) :
    ipcInvariantFull (sweptAndRestored st v frame) := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hBlkMsg, hNoDup, hMem, hQNB, hQHB, hTimeout,
    hDonAcyc, hDonOwner, hPassive, hDonBudget, hBlkReply, hReplyLink, hStash,
    hDonUnique, hTailBlk, hTgt⟩ := hBundle
  have hLink : tcbQueueLinkIntegrity st := hDual.2.1
  have hAcyc : tcbQueueChainAcyclic st := hDual.2.2
  have hBind := sweptAndRestored_sameSchedContextBindings st v frame tcbV hInv hLink hAcyc hLookup
  refine ⟨sweptAndRestored_ipcInvariant st v frame tcbV hInv hLink hAcyc hLookup hIpc,
    sweptAndRestored_dualQueueSystemInvariant st v frame tcbV hInv hDual hLookup hCoh.boundary,
    sweptAndRestored_allPendingMessagesBounded st v frame tcbV hInv hLink hAcyc hLookup hBnd,
    sweptAndRestored_badgeWellFormed st v frame tcbV hInv hLink hAcyc hLookup hBadge,
    sweptAndRestored_blockedThreadsPendingMessageConsistent st v frame tcbV hInv hLink hAcyc
      hLookup hBlkMsg,
    sweptAndRestored_endpointQueueNoDup st v frame tcbV hInv hLink hAcyc hLookup hNoDup hQHB hTgt,
    sweptAndRestored_ipcStateQueueMembershipConsistent st v frame tcbV hInv hLink hAcyc hLookup
      hMem hCoh.successorAnchored,
    sweptAndRestored_queueNextBlockingConsistent st v frame tcbV hInv hLink hAcyc hLookup hTgt,
    sweptAndRestored_queueHeadBlockedConsistent st v frame tcbV hInv hLink hAcyc hLookup hQHB hTgt,
    blockedThreadTimeoutConsistent_of_frame
      (sweptAndRestored_timeoutBudgetFrame st v frame tcbV hInv hLink hAcyc hLookup)
      hAllBudgetsNone,
    sweptAndRestored_donationChainAcyclic st v frame tcbV hInv hLink hAcyc hLookup hDonAcyc,
    donationOwnerValid_of_frames hBind
      (sweptAndRestored_donationOwnerFrame st v frame tcbV hInv hLink hAcyc hLookup hNotReply)
      hDonOwner,
    passiveServerIdle_of_frame
      (sweptAndRestored_passiveServerIdleFrame st v frame tcbV hInv hLink hAcyc hLookup) hPassive,
    donationBudgetTransfer_of_sameSchedContextBindings hBind hDonBudget,
    sweptAndRestored_blockedOnReplyHasTarget st v frame tcbV hInv hLink hAcyc hLookup hBlkReply,
    sweptAndRestored_replyCallerLinkage st v frame tcbV hInv hLink hAcyc hLookup hNotReply
      hReplyLink,
    sweptAndRestored_pendingReceiveReplyWellFormed st v frame tcbV hInv hLink hAcyc hLookup hStash,
    donationOwnerUnique_of_sameSchedContextBindings hBind hDonUnique,
    sweptAndRestored_endpointQueueTailBlockedConsistent st v frame tcbV hInv hLink hAcyc hLookup
      hTailBlk hCoh.predecessorBlocked,
    sweptAndRestored_queueNextTargetBlocked st v frame tcbV hInv hLink hAcyc hLookup hTgt⟩

-- ============================================================================
-- §13  The live operation: `cancelIpcBlocking`'s endpoint arm
-- ============================================================================

/-- The cancellation's endpoint arm **is** the swept-and-restored composite —
`rfl`, so the two cannot drift.  `sweptAndRestored`'s `frame` argument is the
`.ipcCancelled` frame WS-RR RR7.14 stages there. -/
theorem cancelIpcBlocking_endpoint_arm_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (epId : SeLe4n.ObjId)
    (hBlocked : tcb.ipcState = .blockedOnSend epId ∨ tcb.ipcState = .blockedOnReceive epId ∨
      tcb.ipcState = .blockedOnCall epId) :
    Lifecycle.Suspend.cancelIpcBlocking st tid tcb =
      sweptAndRestored st tid (some Architecture.cancelledIpcFrame) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking sweptAndRestored
  rcases hBlocked with h | h | h <;> rw [h] <;> rfl

/-- **WS-RR RR7.22 (residual)**: the cancellation's endpoint arm preserves
`ipcInvariantFull`.

This is the arm the register named: `cancelIpcBlockingOnCore`'s blocked-on-endpoint
path runs the whole-object-store sweep rather than the four-shape splice RR7.22
covered, so none of the splice engine's results applied to it.  `hNotReply` is
discharged here rather than assumed — a thread blocked on an endpoint is not
blocked on a reply. -/
theorem cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (epId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnSend epId ∨ tcbV.ipcState = .blockedOnReceive epId ∨
      tcbV.ipcState = .blockedOnCall epId)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hCoh : sweptThreadQueueCoherent st v) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV epId hBlocked]
  refine sweptAndRestored_preserves_ipcInvariantFull st v _ tcbV hInv hLookup hBundle hAllBudgetsNone
    ?_ hCoh
  intro ep rt hEq
  rcases hBlocked with h | h | h <;> rw [h] at hEq <;> cases hEq

end SeLe4n.Kernel
