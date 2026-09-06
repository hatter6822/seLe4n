-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.IPC.Invariant.Structural.PerOperation
import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership

/-!
# WS-RR RR7.22 — the endpoint queue splice, decomposed once

`endpointQueueRemoveDual` is the mid-queue removal behind two live cross-core
operations (bound-notification delivery and IPC cancellation), and it had
preservation lemmas for exactly two of `ipcInvariantFull`'s twenty conjuncts.
The register's finding 4 asks for the rest.

The obstacle was never the individual conjuncts — the primitive layer
(`storeObject_endpoint_preserves_*`, `storeTcbQueueLinks_preserves_*`) is
complete — it was that every one of them had to re-derive the same
four-leaf case analysis over the operation's branches, at ~130 lines each.
This module derives that analysis **once**, as `SpliceShape`, and every
conjunct proof then consumes four short branches.

## The shape

`endpointQueueRemoveDual endpointId isReceiveQ tid` is one of four programs,
selected by the removed thread's `queuePPrev` (is it the queue head?) and its
`queueNext` (does it have a successor?).  Every branch ends by clearing the
removed thread's own links, and every branch writes the endpoint exactly once
or twice.  `SpliceShape` names all four with their intermediate states, their
step equations, and the queue each branch installs — so a conjunct proof reads
off what it needs instead of re-running `unfold`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

-- ============================================================================
-- §1  The four branches of the splice
-- ============================================================================

/-- WS-RR RR7.22: the queue an endpoint carries on the side the splice acts on. -/
def spliceQueue (isReceiveQ : Bool) (ep : Endpoint) : IntrusiveQueue :=
  if isReceiveQ then ep.receiveQ else ep.sendQ

/-- WS-RR RR7.22: the endpoint that results from installing `q` on the spliced
side, leaving the other side untouched. -/
def spliceEndpoint (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) : Endpoint :=
  if isReceiveQ then { ep with receiveQ := q } else { ep with sendQ := q }

/-- The spliced side of `spliceEndpoint` is the queue it was given. -/
theorem spliceQueue_spliceEndpoint (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    spliceQueue isReceiveQ (spliceEndpoint isReceiveQ ep q) = q := by
  unfold spliceQueue spliceEndpoint; cases isReceiveQ <;> rfl

/-- The **other** side of `spliceEndpoint` is untouched.  Stated as the pair of
head projections, which is what the queue-shape conjuncts read. -/
theorem spliceEndpoint_other_heads (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    (isReceiveQ = true →
        (spliceEndpoint isReceiveQ ep q).sendQ = ep.sendQ) ∧
      (isReceiveQ = false →
        (spliceEndpoint isReceiveQ ep q).receiveQ = ep.receiveQ) := by
  unfold spliceEndpoint; cases isReceiveQ <;> exact ⟨by simp, by simp⟩

-- ============================================================================
-- §2  `SpliceShape` — the four branches, named once
-- ============================================================================

/-- WS-RR RR7.22: the four programs `endpointQueueRemoveDual` can be.

Which one runs is decided by the removed thread's `queuePPrev` (is it the
queue head?) and its `queueNext` (does it have a successor?).  Every branch
carries its intermediate states, its step equations with the *literal*
arguments the operation passes, and the pre-state facts the operation's own
consistency guards establish — the head/tail relation, the predecessor's
forward link, the successor's TCB.

A consumer of this inductive never unfolds `endpointQueueRemoveDual` again.
That is the whole point: eighteen conjunct proofs were each re-deriving the
same case analysis at ~130 lines, and the analysis is a property of the
operation, not of the conjunct. -/
inductive SpliceShape (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) : Prop
  /-- The removed thread is the queue **head** and has **no** successor: the
  queue empties.  Two endpoint writes (the operation stages the head clear and
  then the tail clear) and the link clear. -/
  | headLast (ep : Endpoint) (tcb : TCB) (s1 s2 : SystemState)
      (hEp : st.objects[endpointId]? = some (.endpoint ep))
      (hTcb : lookupTcb st tid = some tcb)
      (hPPrev : tcb.queuePPrev = some .endpointHead)
      (hPrevNone : tcb.queuePrev = none)
      (hHead : (spliceQueue isReceiveQ ep).head = some tid)
      (hTailSome : (spliceQueue isReceiveQ ep).tail.isSome = true)
      (hNext : tcb.queueNext = none)
      (hStore1 : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep
            { head := none, tail := (spliceQueue isReceiveQ ep).tail })) st = .ok ((), s1))
      (hStore2 : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep { head := none, tail := none })) s1
            = .ok ((), s2))
      (hClear : storeTcbQueueLinks s2 tid none none none = .ok st')
  /-- The removed thread is the queue **head** and **has** a successor: the
  successor becomes the head.  Endpoint write, successor relink, endpoint
  write, link clear. -/
  | headMore (ep : Endpoint) (tcb nextTcb : TCB) (nextTid : SeLe4n.ThreadId)
      (s1 s2 s3 : SystemState)
      (hEp : st.objects[endpointId]? = some (.endpoint ep))
      (hTcb : lookupTcb st tid = some tcb)
      (hPPrev : tcb.queuePPrev = some .endpointHead)
      (hPrevNone : tcb.queuePrev = none)
      (hHead : (spliceQueue isReceiveQ ep).head = some tid)
      (hTailSome : (spliceQueue isReceiveQ ep).tail.isSome = true)
      (hNext : tcb.queueNext = some nextTid)
      (hStore1 : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep
            { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail })) st = .ok ((), s1))
      (hNextTcb : lookupTcb s1 nextTid = some nextTcb)
      (hRelink : storeTcbQueueLinks s1 nextTid none (some .endpointHead) nextTcb.queueNext
          = .ok s2)
      (hStore2 : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep
            { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail })) s2 = .ok ((), s3))
      (hClear : storeTcbQueueLinks s3 tid none none none = .ok st')
  /-- The removed thread is **mid-queue** and has **no** successor: its
  predecessor becomes the tail.  Predecessor relink, endpoint write, link
  clear. -/
  | midLast (ep : Endpoint) (tcb prevTcb : TCB) (prevTid : SeLe4n.ThreadId)
      (s1 s2 : SystemState)
      (hEp : st.objects[endpointId]? = some (.endpoint ep))
      (hTcb : lookupTcb st tid = some tcb)
      (hPPrev : tcb.queuePPrev = some (.tcbNext prevTid))
      (hPrev : tcb.queuePrev = some prevTid)
      (hHeadNe : (spliceQueue isReceiveQ ep).head ≠ some tid)
      (hHeadSome : (spliceQueue isReceiveQ ep).head.isSome = true)
      (hTailSome : (spliceQueue isReceiveQ ep).tail.isSome = true)
      (hNext : tcb.queueNext = none)
      (hPrevTcb : lookupTcb st prevTid = some prevTcb)
      (hPrevNext : prevTcb.queueNext = some tid)
      (hRelink : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev none = .ok s1)
      (hStore : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep
            { head := (spliceQueue isReceiveQ ep).head, tail := some prevTid })) s1 = .ok ((), s2))
      (hClear : storeTcbQueueLinks s2 tid none none none = .ok st')
  /-- The removed thread is **mid-queue** and **has** a successor: the queue's
  head and tail are both unchanged and only the two neighbours relink. -/
  | midMore (ep : Endpoint) (tcb prevTcb nextTcb : TCB)
      (prevTid nextTid : SeLe4n.ThreadId) (s1 s2 s3 : SystemState)
      (hEp : st.objects[endpointId]? = some (.endpoint ep))
      (hTcb : lookupTcb st tid = some tcb)
      (hPPrev : tcb.queuePPrev = some (.tcbNext prevTid))
      (hPrev : tcb.queuePrev = some prevTid)
      (hHeadNe : (spliceQueue isReceiveQ ep).head ≠ some tid)
      (hHeadSome : (spliceQueue isReceiveQ ep).head.isSome = true)
      (hTailSome : (spliceQueue isReceiveQ ep).tail.isSome = true)
      (hNext : tcb.queueNext = some nextTid)
      (hPrevTcb : lookupTcb st prevTid = some prevTcb)
      (hPrevNext : prevTcb.queueNext = some tid)
      (hRelinkPrev : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev
          (some nextTid) = .ok s1)
      (hNextTcb : lookupTcb s1 nextTid = some nextTcb)
      (hRelinkNext : storeTcbQueueLinks s1 nextTid (some prevTid) (some (.tcbNext prevTid))
          nextTcb.queueNext = .ok s2)
      (hStore : storeObject endpointId
          (.endpoint (spliceEndpoint isReceiveQ ep
            { head := (spliceQueue isReceiveQ ep).head,
              tail := (spliceQueue isReceiveQ ep).tail })) s2 = .ok ((), s3))
      (hClear : storeTcbQueueLinks s3 tid none none none = .ok st')

-- ============================================================================
-- §3  The derivation: every successful splice is one of the four
-- ============================================================================

/-- WS-RR RR7.22: a successful `endpointQueueRemoveDual` **is** one of the four
programs `SpliceShape` names.

This is the case analysis every conjunct proof used to re-derive.  It is run
once here; §4 onward reads its branches. -/
theorem endpointQueueRemoveDual_shape
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    SpliceShape endpointId isReceiveQ tid st st' := by
  unfold endpointQueueRemoveDual at hStep
  revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          rw [show (if isReceiveQ then ep.receiveQ else ep.sendQ)
                = spliceQueue isReceiveQ ep from rfl]
          cases hEmpty : ((spliceQueue isReceiveQ ep).head.isNone
              || (spliceQueue isReceiveQ ep).tail.isNone) with
          | true => simp
          | false =>
            simp only [Bool.false_eq_true, if_false]
            have hTailSome : (spliceQueue isReceiveQ ep).tail.isSome = true := by
              simp only [Bool.or_eq_false_iff] at hEmpty
              cases hT : (spliceQueue isReceiveQ ep).tail with
              | none => rw [hT] at hEmpty; simp at hEmpty
              | some _ => rfl
            have hHeadSome : (spliceQueue isReceiveQ ep).head.isSome = true := by
              simp only [Bool.or_eq_false_iff] at hEmpty
              cases hH : (spliceQueue isReceiveQ ep).head with
              | none => rw [hH] at hEmpty; simp at hEmpty
              | some _ => rfl
            cases pprev with
            | endpointHead =>
              simp only []
              cases hCons : (decide ((spliceQueue isReceiveQ ep).head = some tid)
                  && tcb.queuePrev.isNone) with
              | false => simp
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, if_false]
                simp only [Bool.and_eq_true, decide_eq_true_eq,
                  Option.isNone_iff_eq_none] at hCons
                obtain ⟨hHead, hPrevNone⟩ := hCons
                cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore1 : storeObject endpointId _ st with
                  | error e => simp
                  | ok pair1 =>
                    simp only []
                    rw [if_pos hHead]
                    cases hStore2 : storeObject endpointId _ pair1.2 with
                    | error e => simp
                    | ok pair2 =>
                      simp only []
                      cases hClear : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        rintro ⟨-, rfl⟩
                        exact .headLast ep tcb pair1.2 pair2.2 hObj hLookup hPPrev hPrevNone
                          hHead hTailSome hNext
                          hStore1 hStore2 hClear
                | some nextTid =>
                  simp only []
                  cases hStore1 : storeObject endpointId _ st with
                  | error e => simp
                  | ok pair1 =>
                    simp only []
                    cases hNextTcb : lookupTcb pair1.2 nextTid with
                    | none => simp
                    | some nextTcb =>
                      simp only []
                      rw [hPrevNone]
                      cases hRelink : storeTcbQueueLinks pair1.2 nextTid none
                          (some .endpointHead) nextTcb.queueNext with
                      | error e => simp
                      | ok s2 =>
                        simp only []
                        rw [if_pos hHead]
                        cases hStore2 : storeObject endpointId _ s2 with
                        | error e => simp
                        | ok pair2 =>
                          simp only []
                          cases hClear : storeTcbQueueLinks pair2.2 tid none none none with
                          | error e => simp
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                            rintro ⟨-, rfl⟩
                            exact .headMore ep tcb nextTcb nextTid pair1.2 s2 pair2.2
                              hObj hLookup hPPrev hPrevNone hHead hTailSome hNext
                              hStore1 hNextTcb hRelink hStore2 hClear
            | tcbNext prevTid =>
              simp only []
              cases hCons : (decide ((spliceQueue isReceiveQ ep).head ≠ some tid)
                  && decide (tcb.queuePrev = some prevTid)) with
              | false => simp
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, if_false]
                simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hCons
                obtain ⟨hHeadNe, hPrev⟩ := hCons
                cases hPrevTcb : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                  simp only []
                  by_cases hPN : prevTcb.queueNext = some tid
                  · rw [if_neg (not_not_intro hPN)]
                    cases hNext : tcb.queueNext with
                    | none =>
                      simp only []
                      cases hRelink : storeTcbQueueLinks st prevTid prevTcb.queuePrev
                          prevTcb.queuePPrev none with
                      | error e => simp
                      | ok s1 =>
                        simp only []
                        rw [if_neg hHeadNe]
                        cases hStore : storeObject endpointId _ s1 with
                        | error e => simp
                        | ok pair2 =>
                          simp only []
                          cases hClear : storeTcbQueueLinks pair2.2 tid none none none with
                          | error e => simp
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                            rintro ⟨-, rfl⟩
                            exact .midLast ep tcb prevTcb prevTid s1 pair2.2 hObj hLookup
                              hPPrev hPrev hHeadNe hHeadSome hTailSome hNext hPrevTcb hPN
                              hRelink hStore hClear
                    | some nextTid =>
                      simp only []
                      cases hRelinkPrev : storeTcbQueueLinks st prevTid prevTcb.queuePrev
                          prevTcb.queuePPrev (some nextTid) with
                      | error e => simp
                      | ok s1 =>
                        simp only []
                        cases hNextTcb : lookupTcb s1 nextTid with
                        | none => simp
                        | some nextTcb =>
                          simp only []
                          rw [hPrev]
                          cases hRelinkNext : storeTcbQueueLinks s1 nextTid (some prevTid)
                              (some (.tcbNext prevTid)) nextTcb.queueNext with
                          | error e => simp
                          | ok s2 =>
                            simp only []
                            rw [if_neg hHeadNe]
                            cases hStore : storeObject endpointId _ s2 with
                            | error e => simp
                            | ok pair2 =>
                              simp only []
                              cases hClear : storeTcbQueueLinks pair2.2 tid none none none with
                              | error e => simp
                              | ok st4 =>
                                simp only [Except.ok.injEq, Prod.mk.injEq]
                                rintro ⟨-, rfl⟩
                                exact .midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2
                                  pair2.2 hObj hLookup hPPrev hPrev hHeadNe hHeadSome
                                  hTailSome hNext hPrevTcb hPN hRelinkPrev hNextTcb
                                  hRelinkNext hStore hClear
                  · rw [if_pos hPN]
                    simp

-- ============================================================================
-- §4  Carrying a predicate across the splice
-- ============================================================================

/-- WS-RR RR7.22: the pre-state facts every splice step needs — the object
store's external invariant, and the endpoint still being an endpoint. -/
def SpliceCtx (endpointId : SeLe4n.ObjId) (s : SystemState) : Prop :=
  s.objects.invExt ∧ ∃ ep : Endpoint, s.objects[endpointId]? = some (.endpoint ep)

theorem SpliceCtx.store {endpointId : SeLe4n.ObjId} {s s' : SystemState} {epNew : Endpoint}
    (hCtx : SpliceCtx endpointId s)
    (hStore : storeObject endpointId (.endpoint epNew) s = .ok ((), s')) :
    SpliceCtx endpointId s' :=
  ⟨storeObject_preserves_objects_invExt' s endpointId _ ((), s') hCtx.1 hStore,
   epNew, storeObject_objects_eq' s endpointId _ ((), s') hCtx.1 hStore⟩

theorem SpliceCtx.links {endpointId : SeLe4n.ObjId} {s s' : SystemState}
    {t : SeLe4n.ThreadId} {qp : Option SeLe4n.ThreadId} {qpp : Option QueuePPrev}
    {qn : Option SeLe4n.ThreadId}
    (hCtx : SpliceCtx endpointId s)
    (hStep : storeTcbQueueLinks s t qp qpp qn = .ok s') :
    SpliceCtx endpointId s' :=
  ⟨storeTcbQueueLinks_preserves_objects_invExt s s' t qp qpp qn hCtx.1 hStep,
   hCtx.2.elim fun ep hEp =>
     storeTcbQueueLinks_endpoint_forward s s' t qp qpp qn endpointId ep hCtx.1 hStep hEp⟩

/-- WS-RR RR7.22: **the frame carrier.**  A predicate preserved by an endpoint
write at `endpointId` and by any TCB queue-link write is preserved by the whole
splice.

This is what turns the twelve conjuncts that read no queue field into two-line
proofs.  It deliberately quantifies the endpoint write over an **arbitrary**
new endpoint, which is exactly why it does not serve the queue-shape conjuncts:
for those, *which* queue is installed is the content, and they get their own
proofs in §6.  Over-approximating here would be unsound, not merely weak. -/
theorem SpliceShape.carry {P : SystemState → Prop}
    {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {st st' : SystemState}
    (hStoreP : ∀ (s s' : SystemState) (epOld epNew : Endpoint),
      s.objects[endpointId]? = some (.endpoint epOld) → s.objects.invExt →
      storeObject endpointId (.endpoint epNew) s = .ok ((), s') → P s → P s')
    (hLinksP : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId)
      (qp : Option SeLe4n.ThreadId) (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId),
      s.objects.invExt → storeTcbQueueLinks s t qp qpp qn = .ok s' → P s → P s')
    (hObjInv : st.objects.invExt)
    (hShape : SpliceShape endpointId isReceiveQ tid st st')
    (hP : P st) : P st' := by
  -- One `SpliceCtx` per step, threaded; each step consumes the previous state's.
  have step : ∀ {s s' : SystemState} {epNew : Endpoint}, SpliceCtx endpointId s →
      storeObject endpointId (.endpoint epNew) s = .ok ((), s') → P s →
      SpliceCtx endpointId s' ∧ P s' := by
    intro s s' epNew hCtx hStore hPs
    exact ⟨hCtx.store hStore,
      hCtx.2.elim fun epOld hEp => hStoreP s s' epOld epNew hEp hCtx.1 hStore hPs⟩
  have link : ∀ {s s' : SystemState} {t : SeLe4n.ThreadId} {qp : Option SeLe4n.ThreadId}
      {qpp : Option QueuePPrev} {qn : Option SeLe4n.ThreadId}, SpliceCtx endpointId s →
      storeTcbQueueLinks s t qp qpp qn = .ok s' → P s → SpliceCtx endpointId s' ∧ P s' := by
    intro s s' t qp qpp qn hCtx hStep hPs
    exact ⟨hCtx.links hStep, hLinksP s s' t qp qpp qn hCtx.1 hStep hPs⟩
  cases hShape with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have h0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    obtain ⟨c1, p1⟩ := step h0 hStore1 hP
    obtain ⟨c2, p2⟩ := step c1 hStore2 p1
    exact (link c2 hClear p2).2
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hStore1 _ hRelink
      hStore2 hClear =>
    have h0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    obtain ⟨c1, p1⟩ := step h0 hStore1 hP
    obtain ⟨c2, p2⟩ := link c1 hRelink p1
    obtain ⟨c3, p3⟩ := step c2 hStore2 p2
    exact (link c3 hClear p3).2
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ _ _ _ _ _ _ hRelink hStore hClear =>
    have h0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    obtain ⟨c1, p1⟩ := link h0 hRelink hP
    obtain ⟨c2, p2⟩ := step c1 hStore p1
    exact (link c2 hClear p2).2
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ _ _ _
      hRelinkPrev _ hRelinkNext hStore hClear =>
    have h0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    obtain ⟨c1, p1⟩ := link h0 hRelinkPrev hP
    obtain ⟨c2, p2⟩ := link c1 hRelinkNext p1
    obtain ⟨c3, p3⟩ := step c2 hStore p2
    exact (link c3 hClear p3).2

/-- WS-RR RR7.22: the carrier, applied straight to the operation. -/
theorem endpointQueueRemoveDual_carry {P : SystemState → Prop}
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStoreP : ∀ (s s' : SystemState) (epOld epNew : Endpoint),
      s.objects[endpointId]? = some (.endpoint epOld) → s.objects.invExt →
      storeObject endpointId (.endpoint epNew) s = .ok ((), s') → P s → P s')
    (hLinksP : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId)
      (qp : Option SeLe4n.ThreadId) (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId),
      s.objects.invExt → storeTcbQueueLinks s t qp qpp qn = .ok s' → P s → P s')
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hP : P st) : P st' :=
  SpliceShape.carry hStoreP hLinksP hObjInv
    (endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep) hP

-- ============================================================================
-- §5  The two primitive frames the queue-link write did not have
-- ============================================================================

/-- WS-RR RR7.22: a queue-link write frames `passiveServerIdle`.

`storeObject_modifiedTcb_passiveServerIdleFrame` carries the side condition
`passiveServerIdleAllowed newTcb.ipcState ∨ origTcb.schedContextBinding ≠
.unbound`, which a general TCB store needs because it may change the thread's
`ipcState`.  A queue-link write cannot: it rewrites three link fields and
nothing else, so the frame holds outright. -/
theorem storeTcbQueueLinks_passiveServerIdleFrame
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    passiveServerIdleFrame st st' := by
  have hSched := storeTcbQueueLinks_scheduler_eq st st' tid prev pprev next hStep
  refine ⟨fun t tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' _ => ?_⟩
  obtain ⟨tcbPre, hPre, hIpc⟩ :=
    storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep t tcb' hTcb'
  obtain ⟨tcbB, hB, hBind⟩ :=
    storeTcbQueueLinks_sameSchedContextBindings st st' tid prev pprev next hObjInv hStep t tcb' hTcb'
  have hSame : tcbB = tcbPre := by
    rw [hB] at hPre; exact KernelObject.tcb.inj (Option.some.inj hPre)
  subst hSame
  refine ⟨tcbB, hB, by rw [hBind]; exact hUnbound', ?_, ?_, hIpc⟩
  · rw [hSched] at hNotInQ'; exact hNotInQ'
  · rw [hSched] at hNotCurrent'; exact hNotCurrent'

-- ============================================================================
-- §6  The relations the splice carries end to end
-- ============================================================================
--
-- Each is proved by instantiating `endpointQueueRemoveDual_carry` at
-- `P := fun s => <relation> st s`, with the relation's own `refl` for the
-- pre-state and its `trans` for each step.  A relation with `refl` and `trans`
-- is exactly what the carrier needs; nothing here re-derives the case split.

/-- WS-RR RR7.22: the splice rebinds no SchedContext. -/
theorem endpointQueueRemoveDual_sameSchedContextBindings
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    sameSchedContextBindings st st' :=
  endpointQueueRemoveDual_carry (P := fun s => sameSchedContextBindings st s)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      hP.trans (storeObject_endpoint_sameSchedContextBindings' s endpointId epNew ((), s')
        hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (storeTcbQueueLinks_sameSchedContextBindings s s' t qp qpp qn hInvS hStore))
    hObjInv hStep (sameSchedContextBindings.refl st)

/-- WS-RR RR7.22: the splice frames the donation-owner reading. -/
theorem endpointQueueRemoveDual_donationOwnerFrame
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    donationOwnerFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => donationOwnerFrame st s)
    endpointId isReceiveQ tid st st'
    (fun s s' epOld epNew hEpOld hInvS hStore hP =>
      hP.trans (storeObject_endpoint_donationOwnerFrame' s endpointId epOld
        (.endpoint epNew) ((), s') hEpOld hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (storeTcbQueueLinks_donationOwnerFrame s s' t qp qpp qn hInvS hStore))
    hObjInv hStep (donationOwnerFrame.refl st)

/-- WS-RR RR7.22: the splice frames the passive-server-idle reading. -/
theorem endpointQueueRemoveDual_passiveServerIdleFrame
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    passiveServerIdleFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => passiveServerIdleFrame st s)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      hP.trans (storeObject_oldNonTcb_passiveServerIdleFrame s s' endpointId (.endpoint epNew)
        (fun _ => by simp) hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (storeTcbQueueLinks_passiveServerIdleFrame s s' t qp qpp qn hInvS hStore))
    hObjInv hStep (passiveServerIdleFrame.refl st)

/-- WS-RR RR7.22: the splice frames every thread's timeout budget. -/
theorem endpointQueueRemoveDual_timeoutBudgetFrame
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    timeoutBudgetFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => timeoutBudgetFrame st s)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      hP.trans (storeObject_endpoint_timeoutBudgetFrame' s endpointId epNew ((), s')
        hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (storeTcbQueueLinks_timeoutBudgetFrame s s' t qp qpp qn hInvS hStore))
    hObjInv hStep (timeoutBudgetFrame.refl st)

/-- WS-RR RR7.22: the splice creates, destroys and rewrites no Reply object,
and moves no thread's reply link. -/
theorem endpointQueueRemoveDual_replyLinkageFrame
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    replyLinkageFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => replyLinkageFrame st s)
    endpointId isReceiveQ tid st st'
    (fun s s' epOld epNew hEpOld hInvS hStore hP =>
      hP.trans (storeObject_endpoint_replyLinkageFrame' s endpointId epOld epNew ((), s')
        hEpOld hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (storeTcbQueueLinks_replyLinkageFrame s s' t qp qpp qn hInvS hStore))
    hObjInv hStep (replyLinkageFrame.refl st)

-- ============================================================================
-- §7  The conjuncts the splice frames
-- ============================================================================
--
-- Twelve of `ipcInvariantFull`'s twenty conjuncts read no queue field: the
-- pending-message bounds, badge well-formedness, the reply linkage, the
-- donation quartet, the timeout consistency and the passive-server reading.
-- Each is two or three lines here, because §4's carrier already did the work.

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_allPendingMessagesBounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) : allPendingMessagesBounded st' :=
  endpointQueueRemoveDual_carry (P := allPendingMessagesBounded)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      storeObject_endpoint_preserves_allPendingMessagesBounded s s' endpointId epNew
        hInvS hStore hP)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_allPendingMessagesBounded s s' t qp qpp qn hInvS hStore hP)
    hObjInv hStep hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_badgeWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : badgeWellFormed st) : badgeWellFormed st' :=
  endpointQueueRemoveDual_carry (P := badgeWellFormed)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      storeObject_endpoint_preserves_badgeWellFormed s s' endpointId epNew hP hInvS hStore)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_badgeWellFormed s s' t qp qpp qn hP hInvS hStore)
    hObjInv hStep hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' :=
  endpointQueueRemoveDual_carry (P := blockedThreadsPendingMessageConsistent)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent s s' endpointId
        (.endpoint epNew) (fun _ => by simp) hInvS hStore hP)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_blockedThreadsPendingMessageConsistent s s' t qp qpp qn
        hInvS hStore hP)
    hObjInv hStep hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : blockedOnReplyHasTarget st) : blockedOnReplyHasTarget st' :=
  endpointQueueRemoveDual_carry (P := blockedOnReplyHasTarget)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      storeObject_endpoint_preserves_blockedOnReplyHasTarget' s endpointId epNew ((), s')
        hInvS hP hStore)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_blockedOnReplyHasTarget s s' t qp qpp qn hInvS hP hStore)
    hObjInv hStep hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : pendingReceiveReplyWellFormed st) : pendingReceiveReplyWellFormed st' :=
  endpointQueueRemoveDual_carry (P := pendingReceiveReplyWellFormed)
    endpointId isReceiveQ tid st st'
    (fun s s' epOld epNew hEpOld hInvS hStore hP =>
      storeObject_endpoint_preserves_pendingReceiveReplyWellFormed' s endpointId epNew epOld
        ((), s') hInvS hEpOld hP hStore)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed s s' t qp qpp qn
        hInvS hP hStore)
    hObjInv hStep hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : blockedOnReplyHasReplyObject st) : blockedOnReplyHasReplyObject st' :=
  endpointQueueRemoveDual_carry (P := blockedOnReplyHasReplyObject)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      storeObject_endpoint_preserves_blockedOnReplyHasReplyObject s s' endpointId epNew
        hInvS hP hStore)
    (fun s s' t qp qpp qn hInvS hStore hP =>
      storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject s s' t qp qpp qn
        hInvS hP hStore)
    hObjInv hStep hInv

/-- WS-RR RR7.22: the reply linkage, from the reply-linkage frame plus the
reply-object conjunct. -/
theorem endpointQueueRemoveDual_preserves_replyCallerLinkage
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : replyCallerLinkage st) : replyCallerLinkage st' :=
  ⟨replyCallerLinkageReciprocal_of_frame
      (endpointQueueRemoveDual_replyLinkageFrame st st' endpointId isReceiveQ tid hObjInv hStep)
      hInv.1,
   endpointQueueRemoveDual_preserves_blockedOnReplyHasReplyObject st st' endpointId
     isReceiveQ tid hObjInv hStep hInv.2⟩

/-- WS-RR RR7.22: every post-state TCB of a splice came from a pre-state TCB
with the same `ipcState`.

The queue-link writes rewrite three fields and the endpoint write is not a TCB
write at all, so no thread's blocking state moves.  Stated as its own relation
because two conjuncts below need it and because it has the `refl`/`trans` shape
`endpointQueueRemoveDual_carry` consumes. -/
def ipcStateFrame (st st' : SystemState) : Prop :=
  ∀ (t : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[t.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState

theorem ipcStateFrame.refl (st : SystemState) : ipcStateFrame st st :=
  fun _ tcb' h => ⟨tcb', h, rfl⟩

theorem ipcStateFrame.trans {st st' st'' : SystemState}
    (h1 : ipcStateFrame st st') (h2 : ipcStateFrame st' st'') : ipcStateFrame st st'' := by
  intro t tcb'' h
  obtain ⟨tcb', h', hEq'⟩ := h2 t tcb'' h
  obtain ⟨tcb, hPre, hEq⟩ := h1 t tcb' h'
  exact ⟨tcb, hPre, hEq.trans hEq'⟩

/-- WS-RR RR7.22: an endpoint write is not a TCB write, so it frames every
thread's `ipcState`. -/
theorem storeObject_endpoint_ipcStateFrame
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    ipcStateFrame st st' := by
  intro t tcb' hTcb'
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid (.endpoint ep) hObjInv hStore] at hTcb'
    exact absurd (Option.some.inj hTcb') (by simp)
  · rw [storeObject_objects_ne st st' oid t.toObjId (.endpoint ep) hEq hObjInv hStore] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

/-- WS-RR RR7.22: the splice frames every thread's `ipcState`. -/
theorem endpointQueueRemoveDual_ipcStateFrame
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ipcStateFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => ipcStateFrame st s)
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP =>
      hP.trans (storeObject_endpoint_ipcStateFrame s s' endpointId epNew hInvS hStore))
    (fun s s' t qp qpp qn hInvS hStore hP =>
      hP.trans (fun y tcb' hy =>
        storeTcbQueueLinks_tcb_ipcState_backward s s' t qp qpp qn hInvS hStore y tcb' hy))
    hObjInv hStep (ipcStateFrame.refl st)

/-- WS-RR RR7.22: the timeout consistency.

Proved **outright**, not under `allTimeoutBudgetsNone`: the splice frames every
thread's timeout budget and blocking state, and carries every SchedContext
forward, which is exactly what the conjunct reads.  The pre-existing
rendezvous-level lemmas assume the budget-free deployment because their
transitions genuinely rewrite `ipcState`; this one does not. -/
theorem endpointQueueRemoveDual_preserves_blockedThreadTimeoutConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : blockedThreadTimeoutConsistent st) : blockedThreadTimeoutConsistent st' := by
  have hBudget := endpointQueueRemoveDual_timeoutBudgetFrame st st' endpointId isReceiveQ tid
    hObjInv hStep
  have hIpc := endpointQueueRemoveDual_ipcStateFrame st st' endpointId isReceiveQ tid
    hObjInv hStep
  have hSc := (endpointQueueRemoveDual_donationOwnerFrame st st' endpointId isReceiveQ tid
    hObjInv hStep).scForward
  intro t tcb' scId hTcb' hBudget'
  obtain ⟨tcbB, hB, hBEq⟩ := hBudget t tcb' hTcb'
  obtain ⟨tcbI, hI, hIEq⟩ := hIpc t tcb' hTcb'
  have hSame : tcbI = tcbB := by
    rw [hI] at hB; exact KernelObject.tcb.inj (Option.some.inj hB)
  subst hSame
  obtain ⟨⟨sc, hScPre⟩, hBlk⟩ := hInv t tcbI scId hI (by rw [hBEq]; exact hBudget')
  exact ⟨⟨sc, hSc scId sc hScPre⟩, by rw [← hIEq]; exact hBlk⟩

/-- WS-RR RR7.22: the passive-server reading, from its frame. -/
theorem endpointQueueRemoveDual_preserves_passiveServerIdle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : passiveServerIdle st) : passiveServerIdle st' :=
  passiveServerIdle_of_frame
    (endpointQueueRemoveDual_passiveServerIdleFrame st st' endpointId isReceiveQ tid
      hObjInv hStep)
    hInv

/-- WS-RR RR7.22: the donation quartet.  `donationOwnerValid` needs both
donation relations; the other three fall out of it and of the bindings. -/
theorem endpointQueueRemoveDual_preserves_donationOwnerValid
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : donationOwnerValid st) : donationOwnerValid st' :=
  donationOwnerValid_of_frames
    (endpointQueueRemoveDual_sameSchedContextBindings st st' endpointId isReceiveQ tid
      hObjInv hStep)
    (endpointQueueRemoveDual_donationOwnerFrame st st' endpointId isReceiveQ tid hObjInv hStep)
    hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_donationBudgetTransfer
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : donationBudgetTransfer st) : donationBudgetTransfer st' :=
  donationBudgetTransfer_of_sameSchedContextBindings
    (endpointQueueRemoveDual_sameSchedContextBindings st st' endpointId isReceiveQ tid
      hObjInv hStep)
    hInv

/-- WS-RR RR7.22 -/
theorem endpointQueueRemoveDual_preserves_donationOwnerUnique
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : donationOwnerUnique st) : donationOwnerUnique st' :=
  donationOwnerUnique_of_sameSchedContextBindings
    (endpointQueueRemoveDual_sameSchedContextBindings st st' endpointId isReceiveQ tid
      hObjInv hStep)
    hInv

/-- WS-RR RR7.22: acyclicity comes from the owner validity it is implied by,
not from a separate argument. -/
theorem endpointQueueRemoveDual_preserves_donationChainAcyclic
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : donationOwnerValid st) : donationChainAcyclic st' :=
  donationOwnerValid_implies_donationChainAcyclic st'
    (endpointQueueRemoveDual_preserves_donationOwnerValid st st' endpointId isReceiveQ tid
      hObjInv hStep hInv)

-- ============================================================================
-- §8  The queue-shape conjuncts: the intra-queue blocking propagation
-- ============================================================================

/-- WS-RR RR7.22: the strict propagation implies the compatibility relation.

`queueNextTargetBlocked` is the strict form and `queueNextBlockingMatch` the
permissive one; this is the arrow between them, and it is what lets the splice
re-establish the permissive conjunct at the link it patches (the compatibility
relation is not transitive on its own — its catch-all admits an unblocked
middle — so composing across the removed thread has to go through the strict
form). -/
theorem queueNextBlockingMatch_of_targetBlocked (s1 s2 : ThreadIpcState)
    (h1 : ∀ ep, s1 = .blockedOnReceive ep → s2 = .blockedOnReceive ep)
    (h2 : ∀ ep, (s1 = .blockedOnSend ep ∨ s1 = .blockedOnCall ep) →
      (s2 = .blockedOnSend ep ∨ s2 = .blockedOnCall ep)) :
    queueNextBlockingMatch s1 s2 := by
  unfold queueNextBlockingMatch
  cases hs1 : s1 with
  | ready => cases s2 <;> exact True.intro
  | blockedOnSend ep =>
    rcases h2 ep (Or.inl hs1) with h | h <;> rw [h]
  | blockedOnCall ep =>
    rcases h2 ep (Or.inr hs1) with h | h <;> rw [h]
  | blockedOnReceive ep => rw [h1 ep hs1]
  | blockedOnReply _ _ => cases s2 <;> exact True.intro
  | blockedOnNotification _ => cases s2 <;> exact True.intro

/-- WS-RR RR7.22: the splice preserves the strict intra-queue blocking
propagation.

The only link it *creates* is the predecessor's new `queueNext`, which points
at the removed thread's successor.  The pre-state relates predecessor to
removed thread and removed thread to successor; composing the two is the whole
argument, and it is why this conjunct needs the strict form rather than the
permissive one. -/
theorem endpointQueueRemoveDual_preserves_queueNextTargetBlocked
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : queueNextTargetBlocked st) : queueNextTargetBlocked st' := by
  -- The clear of the removed thread's own links creates no link at all.
  have clear : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId), s.objects.invExt →
      storeTcbQueueLinks s t none none none = .ok s' →
      queueNextTargetBlocked s → queueNextTargetBlocked s' :=
    fun s s' t hi h hP =>
      storeTcbQueueLinks_preserves_queueNextTargetBlocked s s' t none none none hP hi h
        (fun _ _ _ hNone => by cases hNone)
  -- Relinking the successor reinstalls the link it already had.
  have relinkNext : ∀ (s s' : SystemState) (n : SeLe4n.ThreadId) (nTcb : TCB)
      (qp : Option SeLe4n.ThreadId) (qpp : Option QueuePPrev),
      s.objects.invExt → lookupTcb s n = some nTcb →
      storeTcbQueueLinks s n qp qpp nTcb.queueNext = .ok s' →
      queueNextTargetBlocked s → queueNextTargetBlocked s' := by
    intro s s' n nTcb qp qpp hi hLk h hP
    refine storeTcbQueueLinks_preserves_queueNextTargetBlocked s s' n qp qpp nTcb.queueNext
      hP hi h ?_
    intro b tcbN tcbB hEq hN hB
    have hSame : tcbN = nTcb := by
      rw [lookupTcb_some_objects s n nTcb hLk] at hN
      exact (KernelObject.tcb.inj (Option.some.inj hN)).symm
    subst hSame
    exact hP n b tcbN tcbB hN hB hEq
  have epStore : ∀ (s s' : SystemState) (e : SeLe4n.ObjId) (ep : Endpoint), s.objects.invExt →
      storeObject e (.endpoint ep) s = .ok ((), s') →
      queueNextTargetBlocked s → queueNextTargetBlocked s' :=
    fun s s' e ep hi h hP =>
      storeObject_endpoint_preserves_queueNextTargetBlocked s s' e ep hP hi h
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.store hStore2
    exact clear _ _ _ c2.1 hClear (epStore _ _ _ _ c1.1 hStore2 (epStore _ _ _ _ c0.1 hStore1 hInv))
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hStore1 hNextTcb hRelink
      hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    have c3 := c2.store hStore2
    exact clear _ _ _ c3.1 hClear
      (epStore _ _ _ _ c2.1 hStore2
        (relinkNext _ _ _ _ _ _ c1.1 hNextTcb hRelink (epStore _ _ _ _ c0.1 hStore1 hInv)))
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ _ _ _ hNext hPrevTcb hPrevNext
      hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have h1 : queueNextTargetBlocked s1 :=
      storeTcbQueueLinks_preserves_queueNextTargetBlocked st s1 prevTid prevTcb.queuePrev
        prevTcb.queuePPrev none hInv hObjInv hRelink (fun _ _ _ hNone => by cases hNone)
    have c1 := c0.links hRelink
    have c2 := c1.store hStore
    exact clear _ _ _ c2.1 hClear (epStore _ _ _ _ c1.1 hStore h1)
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hNext
      hPrevTcb hPrevNext hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hTcbObj := lookupTcb_some_objects st tid tcb hTcb
    have hPrevObj := lookupTcb_some_objects st prevTid prevTcb hPrevTcb
    -- The one created link: predecessor → successor, composed through the removed thread.
    have h1 : queueNextTargetBlocked s1 := by
      refine storeTcbQueueLinks_preserves_queueNextTargetBlocked st s1 prevTid
        prevTcb.queuePrev prevTcb.queuePPrev (some nextTid) hInv hObjInv hRelinkPrev ?_
      intro b tcbP tcbB hEq hP hB
      obtain rfl : b = nextTid := (Option.some.inj hEq).symm
      have hSame : tcbP = prevTcb := by
        rw [hPrevObj] at hP; exact (KernelObject.tcb.inj (Option.some.inj hP)).symm
      subst hSame
      obtain ⟨hMid1, hMid2⟩ := hInv prevTid tid tcbP tcb hP hTcbObj hPrevNext
      obtain ⟨hNxt1, hNxt2⟩ := hInv tid b tcb tcbB hTcbObj hB hNext
      exact ⟨fun e h => hNxt1 e (hMid1 e h), fun e h => hNxt2 e (hMid2 e h)⟩
    have c1 := c0.links hRelinkPrev
    have h2 := relinkNext _ _ _ _ _ _ c1.1 hNextTcb hRelinkNext h1
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    exact clear _ _ _ c3.1 hClear (epStore _ _ _ _ c2.1 hStore h2)

/-- WS-RR RR7.22: the splice preserves the permissive intra-queue compatibility
relation.

It needs the **strict** propagation of the pre-state as well as the permissive
conjunct, and that is not slack: the compatibility relation's catch-all admits
an unblocked middle, so `match(prev, tid)` and `match(tid, next)` do not
compose.  The bundle supplies both. -/
theorem endpointQueueRemoveDual_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : queueNextBlockingConsistent st)
    (hTarget : queueNextTargetBlocked st) : queueNextBlockingConsistent st' := by
  have clear : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId), s.objects.invExt →
      storeTcbQueueLinks s t none none none = .ok s' →
      queueNextBlockingConsistent s → queueNextBlockingConsistent s' :=
    fun s s' t hi h hP =>
      storeTcbQueueLinks_preserves_queueNextBlockingConsistent s s' t none none none hP hi h
        (fun _ _ _ hNone => by cases hNone)
  have relinkNext : ∀ (s s' : SystemState) (n : SeLe4n.ThreadId) (nTcb : TCB)
      (qp : Option SeLe4n.ThreadId) (qpp : Option QueuePPrev),
      s.objects.invExt → lookupTcb s n = some nTcb →
      storeTcbQueueLinks s n qp qpp nTcb.queueNext = .ok s' →
      queueNextBlockingConsistent s → queueNextBlockingConsistent s' := by
    intro s s' n nTcb qp qpp hi hLk h hP
    refine storeTcbQueueLinks_preserves_queueNextBlockingConsistent s s' n qp qpp
      nTcb.queueNext hP hi h ?_
    intro b tcbN tcbB hEq hN hB
    have hSame : tcbN = nTcb := by
      rw [lookupTcb_some_objects s n nTcb hLk] at hN
      exact (KernelObject.tcb.inj (Option.some.inj hN)).symm
    subst hSame
    exact hP n b tcbN tcbB hN hB hEq
  have epStore : ∀ (s s' : SystemState) (e : SeLe4n.ObjId) (ep : Endpoint), s.objects.invExt →
      storeObject e (.endpoint ep) s = .ok ((), s') →
      queueNextBlockingConsistent s → queueNextBlockingConsistent s' :=
    fun s s' e ep hi h hP =>
      storeObject_endpoint_preserves_queueNextBlockingConsistent s s' e ep hP hi h
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.store hStore2
    exact clear _ _ _ c2.1 hClear (epStore _ _ _ _ c1.1 hStore2 (epStore _ _ _ _ c0.1 hStore1 hInv))
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hStore1 hNextTcb hRelink
      hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    have c3 := c2.store hStore2
    exact clear _ _ _ c3.1 hClear
      (epStore _ _ _ _ c2.1 hStore2
        (relinkNext _ _ _ _ _ _ c1.1 hNextTcb hRelink (epStore _ _ _ _ c0.1 hStore1 hInv)))
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ _ _ _ hNext hPrevTcb hPrevNext
      hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have h1 : queueNextBlockingConsistent s1 :=
      storeTcbQueueLinks_preserves_queueNextBlockingConsistent st s1 prevTid prevTcb.queuePrev
        prevTcb.queuePPrev none hInv hObjInv hRelink (fun _ _ _ hNone => by cases hNone)
    have c1 := c0.links hRelink
    have c2 := c1.store hStore
    exact clear _ _ _ c2.1 hClear (epStore _ _ _ _ c1.1 hStore h1)
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hNext
      hPrevTcb hPrevNext hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hTcbObj := lookupTcb_some_objects st tid tcb hTcb
    have hPrevObj := lookupTcb_some_objects st prevTid prevTcb hPrevTcb
    have h1 : queueNextBlockingConsistent s1 := by
      refine storeTcbQueueLinks_preserves_queueNextBlockingConsistent st s1 prevTid
        prevTcb.queuePrev prevTcb.queuePPrev (some nextTid) hInv hObjInv hRelinkPrev ?_
      intro b tcbP tcbB hEq hP hB
      obtain rfl : b = nextTid := (Option.some.inj hEq).symm
      have hSame : tcbP = prevTcb := by
        rw [hPrevObj] at hP; exact (KernelObject.tcb.inj (Option.some.inj hP)).symm
      subst hSame
      obtain ⟨hMid1, hMid2⟩ := hTarget prevTid tid tcbP tcb hP hTcbObj hPrevNext
      obtain ⟨hNxt1, hNxt2⟩ := hTarget tid b tcb tcbB hTcbObj hB hNext
      exact queueNextBlockingMatch_of_targetBlocked tcbP.ipcState tcbB.ipcState
        (fun e h => hNxt1 e (hMid1 e h)) (fun e h => hNxt2 e (hMid2 e h))
    have c1 := c0.links hRelinkPrev
    have h2 := relinkNext _ _ _ _ _ _ c1.1 hNextTcb hRelinkNext h1
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    exact clear _ _ _ c3.1 hClear (epStore _ _ _ _ c2.1 hStore h2)

-- ============================================================================
-- §9  The queue-shape conjuncts: the head and tail boundaries
-- ============================================================================

/-- The spliced endpoint's receive-queue head. -/
theorem spliceEndpoint_receiveQ_head (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    (spliceEndpoint isReceiveQ ep q).receiveQ.head
      = if isReceiveQ then q.head else ep.receiveQ.head := by
  unfold spliceEndpoint; cases isReceiveQ <;> rfl

/-- The spliced endpoint's send-queue head. -/
theorem spliceEndpoint_sendQ_head (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    (spliceEndpoint isReceiveQ ep q).sendQ.head
      = if isReceiveQ then ep.sendQ.head else q.head := by
  unfold spliceEndpoint; cases isReceiveQ <;> rfl

/-- The spliced endpoint's receive-queue tail. -/
theorem spliceEndpoint_receiveQ_tail (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    (spliceEndpoint isReceiveQ ep q).receiveQ.tail
      = if isReceiveQ then q.tail else ep.receiveQ.tail := by
  unfold spliceEndpoint; cases isReceiveQ <;> rfl

/-- The spliced endpoint's send-queue tail. -/
theorem spliceEndpoint_sendQ_tail (isReceiveQ : Bool) (ep : Endpoint) (q : IntrusiveQueue) :
    (spliceEndpoint isReceiveQ ep q).sendQ.tail
      = if isReceiveQ then ep.sendQ.tail else q.tail := by
  unfold spliceEndpoint; cases isReceiveQ <;> rfl

/-- WS-RR RR7.22: what it means for a thread to be blocked on the side of
`endpointId` the splice is acting on.  Written as the two guarded implications
rather than an `if` in `Prop`, so a caller discharges the branch it is in. -/
def spliceSideBlocked (isReceiveQ : Bool) (endpointId : SeLe4n.ObjId)
    (s : ThreadIpcState) : Prop :=
  (isReceiveQ = true → s = .blockedOnReceive endpointId)
    ∧ (isReceiveQ = false → s = .blockedOnSend endpointId ∨ s = .blockedOnCall endpointId)

/-- WS-RR RR7.22: the removed thread is blocked on the side being spliced, in
every branch that makes it the queue head. -/
theorem spliceSideBlocked_of_head {isReceiveQ : Bool} {endpointId : SeLe4n.ObjId}
    {st : SystemState} {ep : Endpoint} {hd : SeLe4n.ThreadId} {tcb : TCB}
    (hInv : queueHeadBlockedConsistent st)
    (hEp : st.objects[endpointId]? = some (.endpoint ep))
    (hTcb : st.objects[hd.toObjId]? = some (.tcb tcb))
    (hHead : (spliceQueue isReceiveQ ep).head = some hd) :
    spliceSideBlocked isReceiveQ endpointId tcb.ipcState := by
  obtain ⟨hR, hS⟩ := hInv endpointId ep hd tcb hEp hTcb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h; exact hR (by simpa [spliceQueue] using hHead)
  · subst h; exact hS (by simpa [spliceQueue] using hHead)

/-- WS-RR RR7.22: side-blockedness travels along a `queueNext` link, by the
strict propagation. -/
theorem spliceSideBlocked_next {isReceiveQ : Bool} {endpointId : SeLe4n.ObjId}
    {sA sB : ThreadIpcState}
    (h : spliceSideBlocked isReceiveQ endpointId sA)
    (h1 : ∀ e, sA = .blockedOnReceive e → sB = .blockedOnReceive e)
    (h2 : ∀ e, (sA = .blockedOnSend e ∨ sA = .blockedOnCall e) →
      (sB = .blockedOnSend e ∨ sB = .blockedOnCall e)) :
    spliceSideBlocked isReceiveQ endpointId sB :=
  ⟨fun hr => h1 endpointId (h.1 hr), fun hs => h2 endpointId (h.2 hs)⟩

/-- WS-RR RR7.22: a queue-link write frames every thread's `ipcState`, packaged
as the relation. -/
theorem storeTcbQueueLinks_ipcStateFrame
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ipcStateFrame st st' :=
  fun y tcb' hy =>
    storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep y tcb' hy

/-- WS-RR RR7.22: the splice preserves the queue **head** blocking consistency.

Two of the four branches install a new head: the head-removal branch promotes
the removed thread's successor, and that successor's blockedness is not a
consequence of the head conjunct alone — it comes from the strict propagation
along the link the removed thread held.  The other two branches leave both
heads where they were. -/
theorem endpointQueueRemoveDual_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : queueHeadBlockedConsistent st)
    (hTarget : queueNextTargetBlocked st) : queueHeadBlockedConsistent st' := by
  have linkStep : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (qp : Option SeLe4n.ThreadId)
      (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId), s.objects.invExt →
      storeTcbQueueLinks s t qp qpp qn = .ok s' →
      queueHeadBlockedConsistent s → queueHeadBlockedConsistent s' :=
    fun s s' t qp qpp qn hi h hP =>
      storeTcbQueueLinks_preserves_queueHeadBlockedConsistent s s' t qp qpp qn hP hi h
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ hHead _ _ hStore1 hStore2 hClear =>
    -- Both endpoint writes install an *empty* head on the spliced side.
    have vac : ∀ (s s' : SystemState) (q' : IntrusiveQueue), q'.head = none →
        s.objects.invExt → ipcStateFrame st s →
        storeObject endpointId (.endpoint (spliceEndpoint isReceiveQ ep q')) s = .ok ((), s') →
        queueHeadBlockedConsistent s → queueHeadBlockedConsistent s' := by
      intro s s' q' hEmpty hi hFrame hStore hP
      refine storeObject_endpoint_preserves_queueHeadBlockedConsistent s s' endpointId
        (spliceEndpoint isReceiveQ ep q') hi hP hStore ?_
      intro hd tcbS hTcbS
      obtain ⟨tcbPre, hPre, hIpcEq⟩ := hFrame hd tcbS hTcbS
      obtain ⟨hR0, hS0⟩ := hInv endpointId ep hd tcbPre hEp hPre
      refine ⟨fun hR => ?_, fun hS => ?_⟩
      · rw [spliceEndpoint_receiveQ_head] at hR
        cases hB : isReceiveQ
        · rw [hB] at hR; simp only [Bool.false_eq_true, if_false] at hR
          exact hIpcEq ▸ hR0 hR
        · rw [hB] at hR; simp only [if_true, hEmpty] at hR; cases hR
      · rw [spliceEndpoint_sendQ_head] at hS
        cases hB : isReceiveQ
        · rw [hB] at hS; simp only [Bool.false_eq_true, if_false, hEmpty] at hS; cases hS
        · rw [hB] at hS; simp only [if_true] at hS
          exact hIpcEq ▸ hS0 hS
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.store hStore2
    have f1 : ipcStateFrame st s1 :=
      storeObject_endpoint_ipcStateFrame st s1 endpointId _ c0.1 hStore1
    have f2 : ipcStateFrame st s2 :=
      f1.trans (storeObject_endpoint_ipcStateFrame s1 s2 endpointId _ c1.1 hStore2)
    exact linkStep _ _ _ _ _ _ c2.1 hClear
      (vac _ _ _ rfl c1.1 f1 hStore2 (vac _ _ _ rfl c0.1 (ipcStateFrame.refl st) hStore1 hInv))
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ hHead _ hNext hStore1 hNextTcb
      hRelink hStore2 hClear =>
    -- The successor is promoted to head; its blockedness comes from the link.
    have hTcbObj := lookupTcb_some_objects st tid tcb hTcb
    have hSideTid : spliceSideBlocked isReceiveQ endpointId tcb.ipcState :=
      spliceSideBlocked_of_head hInv hEp hTcbObj hHead
    have promoted : ∀ (s s' : SystemState), s.objects.invExt → ipcStateFrame st s →
        storeObject endpointId (.endpoint (spliceEndpoint isReceiveQ ep
          { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail })) s = .ok ((), s') →
        queueHeadBlockedConsistent s → queueHeadBlockedConsistent s' := by
      intro s s' hi hFrame hStore hP
      refine storeObject_endpoint_preserves_queueHeadBlockedConsistent s s' endpointId _ hi hP
        hStore ?_
      intro hd tcbS hTcbS
      obtain ⟨tcbPre, hPre, hIpcEq⟩ := hFrame hd tcbS hTcbS
      obtain ⟨hR0, hS0⟩ := hInv endpointId ep hd tcbPre hEp hPre
      have hPromoted : hd = nextTid →
          spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState := by
        rintro rfl
        obtain ⟨h1, h2⟩ := hTarget tid hd tcb tcbPre hTcbObj hPre hNext
        exact spliceSideBlocked_next hSideTid h1 h2
      refine ⟨fun hR => ?_, fun hS => ?_⟩
      · rw [spliceEndpoint_receiveQ_head] at hR
        cases hB : isReceiveQ
        · rw [hB] at hR; simp only [Bool.false_eq_true, if_false] at hR
          exact hIpcEq ▸ hR0 hR
        · rw [hB] at hR; simp only [if_true] at hR
          exact hIpcEq ▸ (hPromoted (Option.some.inj hR).symm).1 hB
      · rw [spliceEndpoint_sendQ_head] at hS
        cases hB : isReceiveQ
        · rw [hB] at hS; simp only [Bool.false_eq_true, if_false] at hS
          exact hIpcEq ▸ (hPromoted (Option.some.inj hS).symm).2 hB
        · rw [hB] at hS; simp only [if_true] at hS
          exact hIpcEq ▸ hS0 hS
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    have c3 := c2.store hStore2
    have f1 : ipcStateFrame st s1 :=
      storeObject_endpoint_ipcStateFrame st s1 endpointId _ c0.1 hStore1
    have f2 : ipcStateFrame st s2 :=
      f1.trans (storeTcbQueueLinks_ipcStateFrame s1 s2 nextTid _ _ _ c1.1 hRelink)
    exact linkStep _ _ _ _ _ _ c3.1 hClear
      (promoted _ _ c2.1 f2 hStore2
        (linkStep _ _ _ _ _ _ c1.1 hRelink
          (promoted _ _ c0.1 (ipcStateFrame.refl st) hStore1 hInv)))
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ hHeadNe hHeadSome _ _ _ _
      hRelink hStore hClear =>
    -- The head does not move.
    have keep : ∀ (s s' : SystemState) (tl : Option SeLe4n.ThreadId), s.objects.invExt →
        ipcStateFrame st s →
        storeObject endpointId (.endpoint (spliceEndpoint isReceiveQ ep
          { head := (spliceQueue isReceiveQ ep).head, tail := tl })) s = .ok ((), s') →
        queueHeadBlockedConsistent s → queueHeadBlockedConsistent s' := by
      intro s s' tl hi hFrame hStore hP
      refine storeObject_endpoint_preserves_queueHeadBlockedConsistent s s' endpointId _ hi hP
        hStore ?_
      intro hd tcbS hTcbS
      obtain ⟨tcbPre, hPre, hIpcEq⟩ := hFrame hd tcbS hTcbS
      obtain ⟨hR0, hS0⟩ := hInv endpointId ep hd tcbPre hEp hPre
      refine ⟨fun hR => ?_, fun hS => ?_⟩
      · rw [spliceEndpoint_receiveQ_head] at hR
        cases hB : isReceiveQ
        · rw [hB] at hR; simp only [Bool.false_eq_true, if_false] at hR
          exact hIpcEq ▸ hR0 hR
        · rw [hB] at hR; simp only [if_true] at hR
          exact hIpcEq ▸ (spliceSideBlocked_of_head hInv hEp hPre hR).1 rfl
      · rw [spliceEndpoint_sendQ_head] at hS
        cases hB : isReceiveQ
        · rw [hB] at hS; simp only [Bool.false_eq_true, if_false] at hS
          exact hIpcEq ▸ (spliceSideBlocked_of_head hInv hEp hPre hS).2 rfl
        · rw [hB] at hS; simp only [if_true] at hS
          exact hIpcEq ▸ hS0 hS
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelink
    have c2 := c1.store hStore
    have f1 : ipcStateFrame st s1 :=
      storeTcbQueueLinks_ipcStateFrame st s1 prevTid _ _ _ c0.1 hRelink
    exact linkStep _ _ _ _ _ _ c2.1 hClear
      (keep _ _ _ c1.1 f1 hStore (linkStep _ _ _ _ _ _ c0.1 hRelink hInv))
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ hHeadNe hHeadSome
      _ _ _ _ hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    have keep : ∀ (s s' : SystemState) (tl : Option SeLe4n.ThreadId), s.objects.invExt →
        ipcStateFrame st s →
        storeObject endpointId (.endpoint (spliceEndpoint isReceiveQ ep
          { head := (spliceQueue isReceiveQ ep).head, tail := tl })) s = .ok ((), s') →
        queueHeadBlockedConsistent s → queueHeadBlockedConsistent s' := by
      intro s s' tl hi hFrame hStore hP
      refine storeObject_endpoint_preserves_queueHeadBlockedConsistent s s' endpointId _ hi hP
        hStore ?_
      intro hd tcbS hTcbS
      obtain ⟨tcbPre, hPre, hIpcEq⟩ := hFrame hd tcbS hTcbS
      obtain ⟨hR0, hS0⟩ := hInv endpointId ep hd tcbPre hEp hPre
      refine ⟨fun hR => ?_, fun hS => ?_⟩
      · rw [spliceEndpoint_receiveQ_head] at hR
        cases hB : isReceiveQ
        · rw [hB] at hR; simp only [Bool.false_eq_true, if_false] at hR
          exact hIpcEq ▸ hR0 hR
        · rw [hB] at hR; simp only [if_true] at hR
          exact hIpcEq ▸ (spliceSideBlocked_of_head hInv hEp hPre hR).1 rfl
      · rw [spliceEndpoint_sendQ_head] at hS
        cases hB : isReceiveQ
        · rw [hB] at hS; simp only [Bool.false_eq_true, if_false] at hS
          exact hIpcEq ▸ (spliceSideBlocked_of_head hInv hEp hPre hS).2 rfl
        · rw [hB] at hS; simp only [if_true] at hS
          exact hIpcEq ▸ hS0 hS
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelinkPrev
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    have f1 : ipcStateFrame st s1 :=
      storeTcbQueueLinks_ipcStateFrame st s1 prevTid _ _ _ c0.1 hRelinkPrev
    have f2 : ipcStateFrame st s2 :=
      f1.trans (storeTcbQueueLinks_ipcStateFrame s1 s2 nextTid _ _ _ c1.1 hRelinkNext)
    exact linkStep _ _ _ _ _ _ c3.1 hClear
      (keep _ _ _ c2.1 f2 hStore
        (linkStep _ _ _ _ _ _ c1.1 hRelinkNext
          (linkStep _ _ _ _ _ _ c0.1 hRelinkPrev hInv)))

-- ============================================================================
-- §10  Reachable queue members are blocked — and the one fact the bundle
--      does not entail
-- ============================================================================

/-- WS-RR RR7.22: side-blockedness propagates along a whole `queueNext` chain.

`Defs.lean` states, in the docstring of `queueNextTargetBlocked`, that together
with `queueHeadBlockedConsistent` it "yields *every reachable queue member is
blocked*".  Nothing stated it.  This does, by induction on the path; the link
integrity supplies the intermediate TCB the strict propagation needs. -/
theorem spliceSideBlocked_along_path {st : SystemState} {isReceiveQ : Bool}
    {endpointId : SeLe4n.ObjId}
    (hTarget : queueNextTargetBlocked st) (hLink : tcbQueueLinkIntegrity st) :
    ∀ {a b : SeLe4n.ThreadId}, QueueNextPath st a b →
      ∀ (tcbA tcbB : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
        st.objects[b.toObjId]? = some (.tcb tcbB) →
        spliceSideBlocked isReceiveQ endpointId tcbA.ipcState →
        spliceSideBlocked isReceiveQ endpointId tcbB.ipcState := by
  intro a b hPath
  induction hPath with
  | single x y tcbX hX hNext =>
    intro tcbA tcbB hA hB hBlocked
    have hSame : tcbX = tcbA := by
      rw [hA] at hX; exact (KernelObject.tcb.inj (Option.some.inj hX)).symm
    subst hSame
    obtain ⟨h1, h2⟩ := hTarget x y tcbX tcbB hX hB hNext
    exact spliceSideBlocked_next hBlocked h1 h2
  | cons x y z tcbX hX hNext _ ih =>
    intro tcbA tcbB hA hB hBlocked
    have hSame : tcbX = tcbA := by
      rw [hA] at hX; exact (KernelObject.tcb.inj (Option.some.inj hX)).symm
    subst hSame
    obtain ⟨tcbY, hY, _⟩ := hLink.1 x tcbX hX y hNext
    obtain ⟨h1, h2⟩ := hTarget x y tcbX tcbY hX hY hNext
    exact ih tcbY tcbB hY hB (spliceSideBlocked_next hBlocked h1 h2)

/-- WS-RR RR7.22: **the one fact about a splice that `ipcInvariantFull` does not
entail.**

When the removed thread has a predecessor and *no* successor, the splice makes
that predecessor the queue's new tail, and `endpointQueueTailBlockedConsistent`
then demands the predecessor be blocked on that endpoint's side.  The bundle
does not give it: `queueNextTargetBlocked` propagates blockedness *forwards*
along a link, `queueHeadBlockedConsistent` constrains only the head, and
`tcbQueueLinkIntegrity` says nothing about `ipcState`.  A state in which an
unblocked thread's `queueNext` points into a queue satisfies every conjunct and
would break the tail one after the splice.

So it is stated, not assumed away.  `splicePredecessorBlocked_of_head` shows it
is vacuous whenever the removed thread is the head (the only case the current
live callers can reach without a reachability witness), and
`splicePredecessorBlocked_of_path` discharges it from one — the predecessor
being reachable from the queue head, which is what an intact queue means. -/
def splicePredecessorBlocked (isReceiveQ : Bool) (endpointId : SeLe4n.ObjId)
    (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ (tcb : TCB), lookupTcb st tid = some tcb → tcb.queueNext = none →
    ∀ (p : SeLe4n.ThreadId), tcb.queuePPrev = some (.tcbNext p) →
      ∀ (pTcb : TCB), lookupTcb st p = some pTcb →
        spliceSideBlocked isReceiveQ endpointId pTcb.ipcState

/-- WS-RR RR7.22: vacuous when the removed thread is the queue head — it then
has no predecessor to promote. -/
theorem splicePredecessorBlocked_of_head (isReceiveQ : Bool) (endpointId : SeLe4n.ObjId)
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb0 : TCB)
    (hTcb : lookupTcb st tid = some tcb0)
    (hPPrev : tcb0.queuePPrev = some .endpointHead) :
    splicePredecessorBlocked isReceiveQ endpointId st tid := by
  intro tcb hTcb' _ p hP _ _
  have hSame : tcb = tcb0 := by rw [hTcb] at hTcb'; exact (Option.some.inj hTcb').symm
  subst hSame
  rw [hPPrev] at hP
  cases hP

/-- WS-RR RR7.22: discharged by a reachability witness — the predecessor is
reachable from the queue head, which is what an intact queue means. -/
theorem splicePredecessorBlocked_of_path (isReceiveQ : Bool) (endpointId : SeLe4n.ObjId)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ep : Endpoint) (hd : SeLe4n.ThreadId)
    (hInv : queueHeadBlockedConsistent st) (hTarget : queueNextTargetBlocked st)
    (hLink : tcbQueueLinkIntegrity st)
    (hEp : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : (spliceQueue isReceiveQ ep).head = some hd)
    (hReach : ∀ (tcb : TCB), lookupTcb st tid = some tcb →
      ∀ p : SeLe4n.ThreadId, tcb.queuePPrev = some (.tcbNext p) →
        p = hd ∨ QueueNextPath st hd p) :
    splicePredecessorBlocked isReceiveQ endpointId st tid := by
  intro tcb hTcb _ p hP pTcb hPTcb
  have hPObj := lookupTcb_some_objects st p pTcb hPTcb
  rcases hReach tcb hTcb p hP with rfl | hPath
  · exact spliceSideBlocked_of_head hInv hEp hPObj hHead
  · obtain ⟨hdTcb, hHd⟩ : ∃ t, st.objects[hd.toObjId]? = some (.tcb t) := by
      cases hPath with
      | single _ _ t h _ => exact ⟨t, h⟩
      | cons _ _ _ t h _ _ => exact ⟨t, h⟩
    exact spliceSideBlocked_along_path hTarget hLink hPath hdTcb pTcb hHd hPObj
      (spliceSideBlocked_of_head hInv hEp hHd hHead)

/-- WS-RR RR7.22: the splice preserves the queue **tail** blocking consistency,
under the one hypothesis the bundle does not supply.

Three of the four branches leave the spliced side's tail where it was, or empty
it; only the mid-queue removal of a thread with no successor promotes the
predecessor to tail, and that is exactly what `splicePredecessorBlocked`
covers.  See its docstring for why the bundle cannot. -/
theorem endpointQueueRemoveDual_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : endpointQueueTailBlockedConsistent st)
    (hPred : splicePredecessorBlocked isReceiveQ endpointId st tid) :
    endpointQueueTailBlockedConsistent st' := by
  have linkStep : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (qp : Option SeLe4n.ThreadId)
      (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId), s.objects.invExt →
      storeTcbQueueLinks s t qp qpp qn = .ok s' →
      endpointQueueTailBlockedConsistent s → endpointQueueTailBlockedConsistent s' :=
    fun s s' t qp qpp qn hi h hP =>
      storeTcbQueueLinks_preserves_endpointQueueTailBlockedConsistent s s' t qp qpp qn hP hi h
  -- The generic endpoint write: the spliced side's new tail must be side-blocked
  -- in the splice's pre-state; the other side is `ep`'s own and comes from `hInv`.
  have epStore : ∀ (ep : Endpoint) (s s' : SystemState) (q' : IntrusiveQueue),
      st.objects[endpointId]? = some (.endpoint ep) → s.objects.invExt →
      ipcStateFrame st s →
      (∀ tl tcbPre, q'.tail = some tl → st.objects[tl.toObjId]? = some (.tcb tcbPre) →
        spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState) →
      storeObject endpointId (.endpoint (spliceEndpoint isReceiveQ ep q')) s = .ok ((), s') →
      endpointQueueTailBlockedConsistent s → endpointQueueTailBlockedConsistent s' := by
    intro ep s s' q' hEp hi hFrame hNew hStore hP
    refine storeObject_endpoint_preserves_endpointQueueTailBlockedConsistent s s' endpointId _
      hi hP hStore ?_
    intro tl tcbS hTcbS
    obtain ⟨tcbPre, hPre, hIpcEq⟩ := hFrame tl tcbS hTcbS
    obtain ⟨hR0, hS0⟩ := hInv endpointId ep tl tcbPre hEp hPre
    refine ⟨fun hR => ?_, fun hS => ?_⟩
    · rw [spliceEndpoint_receiveQ_tail] at hR
      cases hB : isReceiveQ
      · rw [hB] at hR; simp only [Bool.false_eq_true, if_false] at hR
        exact hIpcEq ▸ hR0 hR
      · rw [hB] at hR; simp only [if_true] at hR
        exact hIpcEq ▸ (hNew tl tcbPre hR hPre).1 hB
    · rw [spliceEndpoint_sendQ_tail] at hS
      cases hB : isReceiveQ
      · rw [hB] at hS; simp only [Bool.false_eq_true, if_false] at hS
        exact hIpcEq ▸ (hNew tl tcbPre hS hPre).2 hB
      · rw [hB] at hS; simp only [if_true] at hS
        exact hIpcEq ▸ hS0 hS
  -- The unchanged-tail obligation: the spliced side's tail is `ep`'s own.
  have keepTail : ∀ (ep : Endpoint) (q' : IntrusiveQueue),
      st.objects[endpointId]? = some (.endpoint ep) →
      q'.tail = (spliceQueue isReceiveQ ep).tail →
      ∀ tl tcbPre, q'.tail = some tl →
        st.objects[tl.toObjId]? = some (.tcb tcbPre) →
        spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState := by
    intro ep q' hEp hTailEq tl tcbPre hTail' hPre
    rw [hTailEq] at hTail'
    have hTail := hTail'
    obtain ⟨hR0, hS0⟩ := hInv endpointId ep tl tcbPre hEp hPre
    exact ⟨fun h => hR0 (by simpa [spliceQueue, h] using hTail),
      fun h => hS0 (by simpa [spliceQueue, h] using hTail)⟩
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.store hStore2
    have f1 : ipcStateFrame st s1 :=
      storeObject_endpoint_ipcStateFrame st s1 endpointId _ c0.1 hStore1
    exact linkStep _ _ _ _ _ _ c2.1 hClear
      (epStore ep _ _ { head := none, tail := none } hEp c1.1 f1
        (fun _ _ h _ => by cases h) hStore2
        (epStore ep _ _ { head := none, tail := (spliceQueue isReceiveQ ep).tail } hEp c0.1
          (ipcStateFrame.refl st) (keepTail ep _ hEp rfl) hStore1 hInv))
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hStore1 hNextTcb hRelink
      hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    have c3 := c2.store hStore2
    have f1 : ipcStateFrame st s1 :=
      storeObject_endpoint_ipcStateFrame st s1 endpointId _ c0.1 hStore1
    have f2 : ipcStateFrame st s2 :=
      f1.trans (storeTcbQueueLinks_ipcStateFrame s1 s2 nextTid _ _ _ c1.1 hRelink)
    exact linkStep _ _ _ _ _ _ c3.1 hClear
      (epStore ep _ _ { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail } hEp
        c2.1 f2 (keepTail ep _ hEp rfl) hStore2
        (linkStep _ _ _ _ _ _ c1.1 hRelink
          (epStore ep _ _ { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail } hEp
            c0.1 (ipcStateFrame.refl st) (keepTail ep _ hEp rfl) hStore1 hInv)))
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb hPPrev _ _ _ _ hNext hPrevTcb _
      hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelink
    have c2 := c1.store hStore
    have f1 : ipcStateFrame st s1 :=
      storeTcbQueueLinks_ipcStateFrame st s1 prevTid _ _ _ c0.1 hRelink
    -- The promoted tail: the predecessor, covered by the stated hypothesis.
    have hNewTail : ∀ tl tcbPre, (some prevTid : Option SeLe4n.ThreadId) = some tl →
        st.objects[tl.toObjId]? = some (.tcb tcbPre) →
        spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState := by
      intro tl tcbPre hEq hPre
      have hEq' : tl = prevTid := (Option.some.inj hEq).symm
      rw [hEq'] at hPre
      have hSame : tcbPre = prevTcb := by
        rw [lookupTcb_some_objects st prevTid prevTcb hPrevTcb] at hPre
        exact (KernelObject.tcb.inj (Option.some.inj hPre)).symm
      rw [hSame]
      exact hPred tcb hTcb hNext prevTid hPPrev prevTcb hPrevTcb
    exact linkStep _ _ _ _ _ _ c2.1 hClear
      (epStore ep _ _ { head := (spliceQueue isReceiveQ ep).head, tail := some prevTid } hEp
        c1.1 f1 hNewTail hStore
        (linkStep _ _ _ _ _ _ c0.1 hRelink hInv))
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ _ _ _
      hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelinkPrev
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    have f1 : ipcStateFrame st s1 :=
      storeTcbQueueLinks_ipcStateFrame st s1 prevTid _ _ _ c0.1 hRelinkPrev
    have f2 : ipcStateFrame st s2 :=
      f1.trans (storeTcbQueueLinks_ipcStateFrame s1 s2 nextTid _ _ _ c1.1 hRelinkNext)
    exact linkStep _ _ _ _ _ _ c3.1 hClear
      (epStore ep _ _ (spliceQueue isReceiveQ ep) hEp c2.1 f2 (keepTail ep _ hEp rfl) hStore
        (linkStep _ _ _ _ _ _ c1.1 hRelinkNext
          (linkStep _ _ _ _ _ _ c0.1 hRelinkPrev hInv)))

-- ============================================================================
-- §11  `endpointQueueNoDup` is a consequence, not a separate obligation
-- ============================================================================

/-- WS-RR RR7.22: `endpointQueueNoDup` follows from the dual-queue invariant and
the head conjunct — no transition needs to re-establish it separately.

Its two clauses are exactly (a) the no-self-loop consequence of
`tcbQueueChainAcyclic` and (b) head disjointness, and (b) is *implied* by the
head conjunct: a thread that headed both queues of one endpoint would have to be
`.blockedOnReceive` and `.blockedOnSend`/`.blockedOnCall` on it at once.  The
queue well-formedness supplies the head's TCB, which is what makes the
contradiction reachable.

Stated here because the splice is where it was needed, and proved in general
because it is a fact about states, not about the splice. -/
theorem endpointQueueNoDup_of_dualQueue_of_headBlocked (st : SystemState)
    (hDual : dualQueueSystemInvariant st) (hHead : queueHeadBlockedConsistent st) :
    endpointQueueNoDup st := by
  intro oid ep hEp
  refine ⟨fun t tcb hTcb => tcbQueueChainAcyclic_no_self_loop hDual.2.2 t tcb hTcb, ?_⟩
  cases hS : ep.sendQ.head with
  | none => exact Or.inl rfl
  | some hs =>
    cases hR : ep.receiveQ.head with
    | none => exact Or.inr (Or.inl rfl)
    | some hr =>
      refine Or.inr (Or.inr ?_)
      intro hEq
      obtain rfl : hs = hr := Option.some.inj hEq
      have hWf := hDual.1 oid ep hEp
      unfold dualQueueEndpointWellFormed at hWf
      rw [hEp] at hWf
      obtain ⟨tcbHd, hTcbHd, _⟩ := hWf.2.2.1 hs hR
      obtain ⟨hRecv, hSend⟩ := hHead oid ep hs tcbHd hEp hTcbHd
      have hIsRecv := hRecv hR
      rcases hSend hS with h | h <;> rw [hIsRecv] at h <;> cases h

/-- WS-RR RR7.22: the splice's own corollary. -/
theorem endpointQueueRemoveDual_preserves_endpointQueueNoDup
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hDual : dualQueueSystemInvariant st)
    (hHead : queueHeadBlockedConsistent st)
    (hTarget : queueNextTargetBlocked st) : endpointQueueNoDup st' :=
  endpointQueueNoDup_of_dualQueue_of_headBlocked st'
    (endpointQueueRemoveDual_preserves_dualQueueSystemInvariant endpointId isReceiveQ tid
      st st' hObjInv hStep hDual)
    (endpointQueueRemoveDual_preserves_queueHeadBlockedConsistent st st' endpointId
      isReceiveQ tid hObjInv hStep hHead hTarget)

-- ============================================================================
-- §12  Transport for the membership witness
-- ============================================================================

/-- WS-RR RR7.22: a `queueNext` witness pointing at anything but the removed
thread survives the splice.

The only `queueNext` fields the splice rewrites are the removed thread's (to
`none`), its predecessor's (to the removed thread's own successor) and its
successor's (to the value it already had).  So a pre-state link `p → t2`
survives whenever `p` is not the removed thread and `t2` is not either: the
predecessor's old link pointed *at* the removed thread, so `t2 ≠ tid` already
rules that case out.  Both side conditions are therefore exactly the ones the
membership conjunct's relaxation supplies. -/
theorem endpointQueueRemoveDual_queueNext_witness
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (p t2 : SeLe4n.ThreadId) (pTcb : TCB)
    (hP : st.objects[p.toObjId]? = some (.tcb pTcb))
    (hNext : pTcb.queueNext = some t2)
    (hT2 : t2 ≠ tid) (hPNe : p ≠ tid) :
    ∃ pTcb', st'.objects[p.toObjId]? = some (.tcb pTcb') ∧ pTcb'.queueNext = some t2 := by
  -- One step of a queue-link write: the link survives unless this is the very
  -- thread being rewritten, in which case the new value must agree.
  have linkStep : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (qp : Option SeLe4n.ThreadId)
      (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId) (q : SeLe4n.ThreadId) (qTcb : TCB),
      s.objects.invExt → storeTcbQueueLinks s t qp qpp qn = .ok s' →
      s.objects[q.toObjId]? = some (.tcb qTcb) → qTcb.queueNext = some t2 →
      (q = t → qn = some t2) →
      ∃ qTcb', s'.objects[q.toObjId]? = some (.tcb qTcb') ∧ qTcb'.queueNext = some t2 := by
    intro s s' t qp qpp qn q qTcb hi hStore hQ hQN hAgree
    by_cases hqt : q = t
    · subst hqt
      obtain ⟨orig, hOrig, hAt⟩ := storeTcbQueueLinks_result_tcb s s' q qp qpp qn hi hStore
      exact ⟨tcbWithQueueLinks orig qp qpp qn, hAt, by
        show qn = some t2
        exact hAgree rfl⟩
    · refine ⟨qTcb, ?_, hQN⟩
      rw [storeTcbQueueLinks_preserves_objects_ne s s' t qp qpp qn q.toObjId
        (fun h => hqt (SeLe4n.ThreadId.toObjId_injective _ _ h)) hi hStore]
      exact hQ
  -- One step of an endpoint write: TCBs are untouched.
  have epStep : ∀ (s s' : SystemState) (ep' e : Endpoint) (q : SeLe4n.ThreadId) (qTcb : TCB),
      s.objects.invExt → s.objects[endpointId]? = some (.endpoint e) →
      storeObject endpointId (.endpoint ep') s = .ok ((), s') →
      s.objects[q.toObjId]? = some (.tcb qTcb) →
      s'.objects[q.toObjId]? = some (.tcb qTcb) := by
    intro s s' ep' e q qTcb hi hEp hStore hQ
    have hNe : q.toObjId ≠ endpointId := by
      intro h; rw [h, hEp] at hQ; cases hQ
    rw [storeObject_objects_ne s s' endpointId q.toObjId (.endpoint ep') hNe hi hStore]
    exact hQ
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.store hStore2
    have h1 := epStep st s1 _ ep p pTcb c0.1 hEp hStore1 hP
    have h2 := epStep s1 s2 _ _ p pTcb c1.1 c1.2.choose_spec hStore2 h1
    exact linkStep s2 st' tid none none none p pTcb c2.1 hClear h2 hNext
      (fun h => absurd h hPNe)
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ _ _ hNextEq hStore1 hNextTcb
      hRelink hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    have c3 := c2.store hStore2
    have h1 := epStep st s1 _ ep p pTcb c0.1 hEp hStore1 hP
    obtain ⟨q2, hq2, hqn2⟩ := linkStep s1 s2 nextTid none (some .endpointHead)
      nextTcb.queueNext p pTcb c1.1 hRelink h1 hNext
      (by
        rintro rfl
        have : pTcb = nextTcb := by
          rw [lookupTcb_some_objects s1 p nextTcb hNextTcb] at h1
          exact (KernelObject.tcb.inj (Option.some.inj h1)).symm
        rw [← this]; exact hNext)
    have h3 := epStep s2 s3 _ _ p q2 c2.1 c2.2.choose_spec hStore2 hq2
    exact linkStep s3 st' tid none none none p q2 c3.1 hClear h3 hqn2
      (fun h => absurd h hPNe)
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ _ _ _ hNextEq hPrevTcb hPrevNext
      hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelink
    have c2 := c1.store hStore
    obtain ⟨q1, hq1, hqn1⟩ := linkStep st s1 prevTid prevTcb.queuePrev prevTcb.queuePPrev
      none p pTcb hObjInv hRelink hP hNext
      (by
        rintro rfl
        have : pTcb = prevTcb := by
          rw [lookupTcb_some_objects st p prevTcb hPrevTcb] at hP
          exact (KernelObject.tcb.inj (Option.some.inj hP)).symm
        subst this
        rw [hPrevNext] at hNext
        exact absurd (Option.some.inj hNext).symm hT2)
    have h2 := epStep s1 s2 _ _ p q1 c1.1 c1.2.choose_spec hStore hq1
    exact linkStep s2 st' tid none none none p q1 c2.1 hClear h2 hqn1
      (fun h => absurd h hPNe)
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hNextEq
      hPrevTcb hPrevNext hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelinkPrev
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    obtain ⟨q1, hq1, hqn1⟩ := linkStep st s1 prevTid prevTcb.queuePrev prevTcb.queuePPrev
      (some nextTid) p pTcb hObjInv hRelinkPrev hP hNext
      (by
        rintro rfl
        have : pTcb = prevTcb := by
          rw [lookupTcb_some_objects st p prevTcb hPrevTcb] at hP
          exact (KernelObject.tcb.inj (Option.some.inj hP)).symm
        subst this
        rw [hPrevNext] at hNext
        exact absurd (Option.some.inj hNext).symm hT2)
    obtain ⟨q2, hq2, hqn2⟩ := linkStep s1 s2 nextTid (some prevTid) (some (.tcbNext prevTid))
      nextTcb.queueNext p q1 c1.1 hRelinkNext hq1 hqn1
      (by
        rintro rfl
        have : q1 = nextTcb := by
          rw [lookupTcb_some_objects s1 p nextTcb hNextTcb] at hq1
          exact (KernelObject.tcb.inj (Option.some.inj hq1)).symm
        rw [← this]; exact hqn1)
    have h3 := epStep s2 s3 _ _ p q2 c2.1 c2.2.choose_spec hStore hq2
    exact linkStep s3 st' tid none none none p q2 c3.1 hClear h3 hqn2
      (fun h => absurd h hPNe)

/-- WS-RR RR7.22: every endpoint survives the splice as an endpoint. -/
theorem endpointQueueRemoveDual_endpoint_forward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    ∃ ep', st'.objects[oid]? = some (.endpoint ep') :=
  endpointQueueRemoveDual_carry (P := fun s => ∃ e : Endpoint, s.objects[oid]? = some (.endpoint e))
    endpointId isReceiveQ tid st st'
    (fun s s' _ epNew _ hInvS hStore hP => by
      by_cases hEq : oid = endpointId
      · exact ⟨epNew, by rw [hEq]; exact storeObject_objects_eq s s' endpointId _ hInvS hStore⟩
      · obtain ⟨e, he⟩ := hP
        exact ⟨e, by
          rw [storeObject_objects_ne s s' endpointId oid (.endpoint epNew) hEq hInvS hStore]
          exact he⟩)
    (fun s s' t qp qpp qn hInvS hStore hP => by
      obtain ⟨e, he⟩ := hP
      have hNe : oid ≠ t.toObjId := by
        intro h
        obtain ⟨orig, hOrig, _⟩ := storeTcbQueueLinks_result_tcb s s' t qp qpp qn hInvS hStore
        rw [h, lookupTcb_some_objects s t orig hOrig] at he; cases he
      exact ⟨e, by
        rw [storeTcbQueueLinks_preserves_objects_ne s s' t qp qpp qn oid hNe hInvS hStore]
        exact he⟩)
    hObjInv hStep ⟨ep, hEp⟩

/-- WS-RR RR7.22: an endpoint other than the spliced one is untouched. -/
theorem endpointQueueRemoveDual_endpoint_forward_ne
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    st'.objects[oid]? = some (.endpoint ep) := by
  obtain ⟨ep', hEp'⟩ :=
    endpointQueueRemoveDual_endpoint_forward st st' endpointId isReceiveQ tid oid ep
      hObjInv hStep hEp
  have hBack := endpointQueueRemoveDual_endpoint_backward_ne st st' endpointId isReceiveQ tid
    oid ep' hNe hObjInv hStep hEp'
  rw [hEp] at hBack
  rw [hEp', (KernelObject.endpoint.inj (Option.some.inj hBack))]

-- ============================================================================
-- §13  The membership conjunct, relaxed at the removed thread
-- ============================================================================

/-- WS-RR RR7.22: the endpoint the splice leaves behind, and the two things a
membership witness needs to know about it.

`headFacts` says: the untouched side of the endpoint is *literally* unchanged;
the spliced side's head either did not move or was the removed thread; and when
the removed thread was the head **and** had a successor, that successor is the
new head.  Those three are exactly the cases a head-shaped membership witness
splits into. -/
theorem endpointQueueRemoveDual_headFacts
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (ep0 : Endpoint) (hEp0 : st.objects[endpointId]? = some (.endpoint ep0)) :
    ∃ ep1, st'.objects[endpointId]? = some (.endpoint ep1)
      ∧ (isReceiveQ = true → ep1.sendQ = ep0.sendQ)
      ∧ (isReceiveQ = false → ep1.receiveQ = ep0.receiveQ)
      ∧ ((spliceQueue isReceiveQ ep1).head = (spliceQueue isReceiveQ ep0).head
          ∨ (spliceQueue isReceiveQ ep0).head = some tid)
      ∧ (∀ n : SeLe4n.ThreadId, (∃ tcb0, lookupTcb st tid = some tcb0 ∧ tcb0.queueNext = some n) →
          (spliceQueue isReceiveQ ep0).head = some tid →
          (spliceQueue isReceiveQ ep1).head = some n) := by
  have finalEp : ∀ (s s' s'' : SystemState) (ep1 : Endpoint), s.objects.invExt →
      storeObject endpointId (.endpoint ep1) s = .ok ((), s') →
      storeTcbQueueLinks s' tid none none none = .ok s'' →
      s''.objects[endpointId]? = some (.endpoint ep1) := by
    intro s s' s'' ep1 hi hStore hClear
    have hAt : s'.objects[endpointId]? = some (.endpoint ep1) :=
      storeObject_objects_eq s s' endpointId _ hi hStore
    have hi' : s'.objects.invExt := storeObject_preserves_objects_invExt s s' endpointId _ hi hStore
    have hNe : endpointId ≠ tid.toObjId := by
      intro h
      obtain ⟨orig, hOrig, _⟩ := storeTcbQueueLinks_result_tcb s' s'' tid none none none hi' hClear
      rw [h, lookupTcb_some_objects s' tid orig hOrig] at hAt; cases hAt
    rw [storeTcbQueueLinks_preserves_objects_ne s' s'' tid none none none endpointId hNe hi'
      hClear]
    exact hAt
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ hHead _ hNext hStore1 hStore2 hClear =>
    obtain rfl : ep0 = ep := by
      rw [hEp0] at hEp; exact KernelObject.endpoint.inj (Option.some.inj hEp)
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep0, hEp0⟩
    have c1 := c0.store hStore1
    refine ⟨_, finalEp s1 s2 st' _ c1.1 hStore2 hClear, ?_, ?_, Or.inr hHead, ?_⟩
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · rintro n ⟨tcb0, hTcb0, hN⟩ _
      rw [hTcb] at hTcb0
      obtain rfl : tcb0 = tcb := (Option.some.inj hTcb0).symm
      rw [hNext] at hN; cases hN
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ hHead _ hNext hStore1 hNextTcb
      hRelink hStore2 hClear =>
    obtain rfl : ep0 = ep := by
      rw [hEp0] at hEp; exact KernelObject.endpoint.inj (Option.some.inj hEp)
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep0, hEp0⟩
    have c1 := c0.store hStore1
    have c2 := c1.links hRelink
    refine ⟨_, finalEp s2 s3 st' _ c2.1 hStore2 hClear, ?_, ?_, Or.inr hHead, ?_⟩
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · rintro n ⟨tcb0, hTcb0, hN⟩ _
      rw [hTcb] at hTcb0
      obtain rfl : tcb0 = tcb := (Option.some.inj hTcb0).symm
      rw [hNext] at hN
      obtain rfl : n = nextTid := (Option.some.inj hN).symm
      rw [spliceQueue_spliceEndpoint]
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ hHeadNe _ _ hNext hPrevTcb _
      hRelink hStore hClear =>
    obtain rfl : ep0 = ep := by
      rw [hEp0] at hEp; exact KernelObject.endpoint.inj (Option.some.inj hEp)
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep0, hEp0⟩
    have c1 := c0.links hRelink
    refine ⟨_, finalEp s1 s2 st' _ c1.1 hStore hClear, ?_, ?_,
      Or.inl (by rw [spliceQueue_spliceEndpoint]), ?_⟩
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · rintro n ⟨tcb0, hTcb0, hN⟩ hHd
      exact absurd hHd hHeadNe
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ hHeadNe _ _ _ _ _
      hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    obtain rfl : ep0 = ep := by
      rw [hEp0] at hEp; exact KernelObject.endpoint.inj (Option.some.inj hEp)
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep0, hEp0⟩
    have c1 := c0.links hRelinkPrev
    have c2 := c1.links hRelinkNext
    refine ⟨_, finalEp s2 s3 st' _ c2.1 hStore hClear, ?_, ?_,
      Or.inl (by rw [spliceQueue_spliceEndpoint]), ?_⟩
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · intro h; unfold spliceEndpoint; rw [h]; rfl
    · rintro n ⟨tcb0, hTcb0, hN⟩ hHd
      exact absurd hHd hHeadNe

/-- WS-RR RR7.22: when the removed thread had a successor, either something in
the post-state still points at that successor (the mid-queue removal repoints
the predecessor), or the removed thread was the queue head (and the successor is
promoted to head instead).

This is the disjunction the membership witness needs when the *removed* thread
was what made a blocked thread reachable: the splice does not orphan the
successor, it either relinks it or promotes it. -/
theorem endpointQueueRemoveDual_successor_rehomed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hAcyclic : tcbQueueChainAcyclic st)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (n : SeLe4n.ThreadId)
    (hSucc : ∃ tcb0, lookupTcb st tid = some tcb0 ∧ tcb0.queueNext = some n) :
    (∃ (p : SeLe4n.ThreadId) (pTcb : TCB),
        st'.objects[p.toObjId]? = some (.tcb pTcb) ∧ pTcb.queueNext = some n)
      ∨ (∀ ep0, st.objects[endpointId]? = some (.endpoint ep0) →
          (spliceQueue isReceiveQ ep0).head = some tid) := by
  obtain ⟨tcb0, hTcb0, hN⟩ := hSucc
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast _ tcb _ _ _ hTcb _ _ _ _ hNext _ _ _ =>
    rw [hTcb] at hTcb0
    obtain rfl : tcb0 = tcb := (Option.some.inj hTcb0).symm
    rw [hNext] at hN; cases hN
  | headMore ep tcb _ _ _ _ _ hEp hTcb _ _ hHead _ _ _ _ _ _ _ =>
    refine Or.inr (fun ep0 hEp0 => ?_)
    obtain rfl : ep0 = ep := by
      rw [hEp0] at hEp; exact KernelObject.endpoint.inj (Option.some.inj hEp)
    exact hHead
  | midLast _ tcb _ _ _ _ _ hTcb _ _ _ _ _ hNext _ _ _ _ _ =>
    rw [hTcb] at hTcb0
    obtain rfl : tcb0 = tcb := (Option.some.inj hTcb0).symm
    rw [hNext] at hN; cases hN
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ _ _ _ hNext
      hPrevTcb hPrevNext hRelinkPrev hNextTcb hRelinkNext hStore hClear =>
    rw [hTcb] at hTcb0
    obtain rfl : tcb0 = tcb := (Option.some.inj hTcb0).symm
    rw [hNext] at hN
    obtain rfl : n = nextTid := (Option.some.inj hN).symm
    have hTcbObj := lookupTcb_some_objects st tid tcb0 hTcb
    have hPrevObj := lookupTcb_some_objects st prevTid prevTcb hPrevTcb
    -- The predecessor is neither the removed thread (that would be a self-loop)
    -- nor the successor (that would be a two-cycle).
    have hPrevNeTid : prevTid ≠ tid := fun hEq =>
      tcbQueueChainAcyclic_no_self_loop hAcyclic tid prevTcb (by rw [← hEq]; exact hPrevObj)
        hPrevNext
    have hPrevNeNext : prevTid ≠ n := fun hEq =>
      tcbQueueChainAcyclic_no_two_cycle hAcyclic tid prevTid tcb0 prevTcb hTcbObj hPrevObj
        (by rw [hNext, hEq]) hPrevNext
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have c1 := c0.links hRelinkPrev
    have c2 := c1.links hRelinkNext
    have c3 := c2.store hStore
    obtain ⟨orig, hOrig, hAt1⟩ := storeTcbQueueLinks_result_tcb st s1 prevTid
      prevTcb.queuePrev prevTcb.queuePPrev (some n) hObjInv hRelinkPrev
    refine Or.inl ⟨prevTid,
      tcbWithQueueLinks orig prevTcb.queuePrev prevTcb.queuePPrev (some n), ?_, rfl⟩
    have hAt2 : s2.objects[prevTid.toObjId]?
        = some (.tcb (tcbWithQueueLinks orig prevTcb.queuePrev prevTcb.queuePPrev (some n))) := by
      rw [storeTcbQueueLinks_preserves_objects_ne s1 s2 n _ _ _ prevTid.toObjId
        (fun h => hPrevNeNext (SeLe4n.ThreadId.toObjId_injective _ _ h)) c1.1 hRelinkNext]
      exact hAt1
    have hNeEp : prevTid.toObjId ≠ endpointId := by
      intro h; rw [h, hEp] at hPrevObj; cases hPrevObj
    have hAt3 : s3.objects[prevTid.toObjId]?
        = some (.tcb (tcbWithQueueLinks orig prevTcb.queuePrev prevTcb.queuePPrev (some n))) := by
      rw [storeObject_objects_ne s2 s3 endpointId prevTid.toObjId _ hNeEp c2.1 hStore]
      exact hAt2
    rw [storeTcbQueueLinks_preserves_objects_ne s3 st' tid none none none prevTid.toObjId
      (fun h => hPrevNeTid (SeLe4n.ThreadId.toObjId_injective _ _ h)) c3.1 hClear]
    exact hAt3

/-- The spliced side's head, as the branch on the side selector. -/
theorem spliceQueue_head (b : Bool) (ep : Endpoint) :
    (spliceQueue b ep).head = if b then ep.receiveQ.head else ep.sendQ.head := by
  unfold spliceQueue; cases b <;> rfl

/-- WS-RR RR7.22: a successful splice had an endpoint at the key it spliced. -/
theorem endpointQueueRemoveDual_pre_endpoint
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∃ ep, st.objects[endpointId]? = some (.endpoint ep) := by
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep _ _ _ hEp => exact ⟨ep, hEp⟩
  | headMore ep _ _ _ _ _ _ hEp => exact ⟨ep, hEp⟩
  | midLast ep _ _ _ _ _ hEp => exact ⟨ep, hEp⟩
  | midMore ep _ _ _ _ _ _ _ _ hEp => exact ⟨ep, hEp⟩

/-- WS-RR RR7.22: a successful splice looked the removed thread up. -/
theorem endpointQueueRemoveDual_pre_tcb
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∃ tcb, lookupTcb st tid = some tcb := by
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast _ tcb _ _ _ hTcb => exact ⟨tcb, hTcb⟩
  | headMore _ tcb _ _ _ _ _ _ hTcb => exact ⟨tcb, hTcb⟩
  | midLast _ tcb _ _ _ _ _ hTcb => exact ⟨tcb, hTcb⟩
  | midMore _ tcb _ _ _ _ _ _ _ _ hTcb => exact ⟨tcb, hTcb⟩

/-- WS-RR RR7.22: the membership conjunct with one thread excused.

The same shape `storeTcbReceiveComplete_partial_preserves_ipcStateQueueMembershipConsistent`
already consumes; naming it makes the splice's post-state statable in one
predicate instead of an inline four-armed match at every call site. -/
def ipcStateQueueMembershipConsistentExcept (st : SystemState) (ex : SeLe4n.ThreadId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (KernelObject.tcb tcb) →
    tid.toObjId ≠ ex.toObjId →
    match tcb.ipcState with
    | .blockedOnSend epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnReceive epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnCall epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | _ => True

/-- The full conjunct is the relaxed one at every thread. -/
theorem ipcStateQueueMembershipConsistentExcept_of_full {st : SystemState}
    (h : ipcStateQueueMembershipConsistent st) (ex : SeLe4n.ThreadId) :
    ipcStateQueueMembershipConsistentExcept st ex :=
  fun tid tcb hTcb _ => h tid tcb hTcb

/-- WS-RR RR7.22: the splice preserves the membership conjunct **everywhere but
at the removed thread**.

That relaxation is the honest statement and not a weakening: the splice takes
the removed thread out of its queue and does *not* touch its `ipcState`, so the
full conjunct is false of the post-state by construction.  The composite
operations restore it at that thread in their next step — the bound delivery
writes `.ready` there — and `storeTcbReceiveComplete_partial_preserves_…`
consumes exactly this shape.

Three facts carry the witness across: a `queueNext` link pointing at anything
but the removed thread survives (§12), the endpoint's untouched side is
literally unchanged and its spliced side's head either stays or was the removed
thread (`headFacts`), and a thread made reachable *by* the removed thread is
either relinked by the predecessor or promoted to head (`successor_rehomed`). -/
theorem endpointQueueRemoveDual_preserves_ipcStateQueueMembershipConsistent_except
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hAcyclic : tcbQueueChainAcyclic st)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : ipcStateQueueMembershipConsistent st)
    (hHeadInv : queueHeadBlockedConsistent st)
    (hTarget : queueNextTargetBlocked st) :
    ipcStateQueueMembershipConsistentExcept st' tid := by
  intro t2 tcb2 hT2 hNe
  have hT2ne : t2 ≠ tid := fun h => hNe (by rw [h])
  obtain ⟨tcbPre, hPre, hIpcEq⟩ :=
    endpointQueueRemoveDual_ipcStateFrame st st' endpointId isReceiveQ tid hObjInv hStep
      t2 tcb2 hT2
  obtain ⟨epMain, hEpMain⟩ :=
    endpointQueueRemoveDual_pre_endpoint st st' endpointId isReceiveQ tid hStep
  obtain ⟨tcbTid, hTcbTid⟩ :=
    endpointQueueRemoveDual_pre_tcb st st' endpointId isReceiveQ tid hStep
  obtain ⟨ep1, hEp1, hSendSame, hRecvSame, hHeadCase, hPromote⟩ :=
    endpointQueueRemoveDual_headFacts st st' endpointId isReceiveQ tid hObjInv hStep
      epMain hEpMain
  -- The witness transfer, uniform in the side selector.
  have core : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (useRecv : Bool),
      st.objects[epId]? = some (.endpoint ep) →
      ((if useRecv then ep.receiveQ.head else ep.sendQ.head) = some t2 ∨
        ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ prevTcb.queueNext = some t2) →
      (spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState →
        epId = endpointId ∧ useRecv = isReceiveQ) →
      ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
        ((if useRecv then ep'.receiveQ.head else ep'.sendQ.head) = some t2 ∨
          ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
            st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ prevTcb.queueNext = some t2) := by
    intro epId ep useRecv hEpId hWit hArm
    -- The head of the spliced side promotes the removed thread's successor.
    have viaRemoved : ∀ (pTcb : TCB), st.objects[tid.toObjId]? = some (.tcb pTcb) →
        pTcb.queueNext = some t2 →
        (∃ (prev : SeLe4n.ThreadId) (pT : TCB),
            st'.objects[prev.toObjId]? = some (.tcb pT) ∧ pT.queueNext = some t2)
          ∨ ((spliceQueue isReceiveQ ep1).head = some t2 ∧ epId = endpointId
              ∧ useRecv = isReceiveQ) := by
      intro pTcb hPrevAt hPrevNext
      have hLk : lookupTcb st tid = some pTcb := by
        have hObjTid := lookupTcb_some_objects st tid tcbTid hTcbTid
        rw [hPrevAt] at hObjTid
        rw [hTcbTid, KernelObject.tcb.inj (Option.some.inj hObjTid)]
      rcases endpointQueueRemoveDual_successor_rehomed st st' endpointId isReceiveQ tid
        hObjInv hAcyclic hStep t2 ⟨pTcb, hLk, hPrevNext⟩ with hRe | hHd
      · exact Or.inl hRe
      · have hHead := hHd epMain hEpMain
        have hSideTid : spliceSideBlocked isReceiveQ endpointId pTcb.ipcState :=
          spliceSideBlocked_of_head hHeadInv hEpMain hPrevAt hHead
        obtain ⟨h1, h2⟩ := hTarget tid t2 pTcb tcbPre hPrevAt hPre hPrevNext
        have hSideT2 : spliceSideBlocked isReceiveQ endpointId tcbPre.ipcState :=
          spliceSideBlocked_next hSideTid h1 h2
        obtain ⟨hE, hU⟩ := hArm hSideT2
        exact Or.inr ⟨hPromote t2 ⟨pTcb, hLk, hPrevNext⟩ hHead, hE, hU⟩
    by_cases hEpEq : epId = endpointId
    · subst hEpEq
      obtain rfl : ep = epMain := by
        rw [hEpMain] at hEpId
        exact (KernelObject.endpoint.inj (Option.some.inj hEpId)).symm
      refine ⟨ep1, hEp1, ?_⟩
      rcases hWit with hHeadW | ⟨prev, prevTcb, hPrev, hPrevNext⟩
      · left
        by_cases hSide : useRecv = isReceiveQ
        · subst hSide
          have hOld : (spliceQueue useRecv ep).head = some t2 := by
            rw [spliceQueue_head]; exact hHeadW
          rcases hHeadCase with hKeep | hWasTid
          · rw [← spliceQueue_head]; rw [hKeep]; exact hOld
          · rw [hWasTid] at hOld
            exact absurd (Option.some.inj hOld).symm hT2ne
        · cases hB : isReceiveQ
          · have : useRecv = true := by
              cases hU : useRecv
              · exact absurd (by rw [hU, hB]) hSide
              · rfl
            subst this
            rw [hRecvSame hB]
            exact hHeadW
          · have : useRecv = false := by
              cases hU : useRecv
              · rfl
              · exact absurd (by rw [hU, hB]) hSide
            subst this
            rw [hSendSame hB]
            exact hHeadW
      · by_cases hPt : prev = tid
        · subst hPt
          rcases viaRemoved prevTcb hPrev hPrevNext with hRe | ⟨hHd, _, hU⟩
          · exact Or.inr hRe
          · left; subst hU; rw [← spliceQueue_head]; exact hHd
        · exact Or.inr (endpointQueueRemoveDual_queueNext_witness st st' _ _ _
            hObjInv hStep prev t2 prevTcb hPrev hPrevNext hT2ne hPt |>.elim
            fun pT hpT => ⟨prev, pT, hpT.1, hpT.2⟩)
    · refine ⟨ep, endpointQueueRemoveDual_endpoint_forward_ne st st' endpointId isReceiveQ tid
        epId ep hEpEq hObjInv hStep hEpId, ?_⟩
      rcases hWit with hHeadW | ⟨prev, prevTcb, hPrev, hPrevNext⟩
      · exact Or.inl hHeadW
      · by_cases hPt : prev = tid
        · subst hPt
          rcases viaRemoved prevTcb hPrev hPrevNext with hRe | ⟨_, hE, _⟩
          · exact Or.inr hRe
          · exact absurd hE hEpEq
        · exact Or.inr (endpointQueueRemoveDual_queueNext_witness st st' _ _ _
            hObjInv hStep prev t2 prevTcb hPrev hPrevNext hT2ne hPt |>.elim
            fun pT hpT => ⟨prev, pT, hpT.1, hpT.2⟩)
  have hW := hInv t2 tcbPre hPre
  rw [← hIpcEq]
  cases hIpc : tcbPre.ipcState with
  | ready => exact True.intro
  | blockedOnReply _ _ => exact True.intro
  | blockedOnNotification _ => exact True.intro
  | blockedOnSend epId =>
    rw [hIpc] at hW
    obtain ⟨ep, hEpId, hWit⟩ := hW
    exact core epId ep false hEpId hWit (by
      intro hSide
      cases hB : isReceiveQ
      · rcases hSide.2 hB with h | h
        · exact ⟨(ThreadIpcState.blockedOnSend.inj (hIpc ▸ h)), rfl⟩
        · exact absurd (hIpc ▸ h) (by simp)
      · exact absurd (hSide.1 hB) (by rw [hIpc]; simp))
  | blockedOnCall epId =>
    rw [hIpc] at hW
    obtain ⟨ep, hEpId, hWit⟩ := hW
    exact core epId ep false hEpId hWit (by
      intro hSide
      cases hB : isReceiveQ
      · rcases hSide.2 hB with h | h
        · exact absurd (hIpc ▸ h) (by simp)
        · exact ⟨(ThreadIpcState.blockedOnCall.inj (hIpc ▸ h)), rfl⟩
      · exact absurd (hSide.1 hB) (by rw [hIpc]; simp))
  | blockedOnReceive epId =>
    rw [hIpc] at hW
    obtain ⟨ep, hEpId, hWit⟩ := hW
    exact core epId ep true hEpId hWit (by
      intro hSide
      cases hB : isReceiveQ
      · rcases hSide.2 hB with h | h <;> exact absurd (hIpc ▸ h) (by simp)
      · exact ⟨(ThreadIpcState.blockedOnReceive.inj (hIpc ▸ hSide.1 hB)), rfl⟩)

-- ============================================================================
-- §14  The capstone: what a bare splice leaves behind
-- ============================================================================

/-- WS-RR RR7.22: **`ipcInvariantFull` with the membership conjunct relaxed at
one thread — the honest post-state of a bare queue splice.**

The splice removes a thread from its endpoint queue and deliberately does *not*
touch its `ipcState`; the composite operations that use it write that thread's
state in their very next step (the bound delivery makes it `.ready`).  So no
state between the two satisfies `ipcInvariantFull`, exactly as no state between
a reply and its donation return satisfies it — and this predicate stands to the
splice as `ipcInvariantFullExceptDonationOwner` stands to the bare reply.

New code must not state a splice bundle that threads the *full* membership
conjunct on the post-state: it would be vacuous rather than conditional. -/
def ipcInvariantFullExceptMembership (st : SystemState) (ex : SeLe4n.ThreadId) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ blockedThreadsPendingMessageConsistent st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistentExcept st ex ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  blockedOnReplyHasTarget st ∧ replyCallerLinkage st ∧
  pendingReceiveReplyWellFormed st ∧ donationOwnerUnique st ∧
  endpointQueueTailBlockedConsistent st ∧
  queueNextTargetBlocked st

/-- WS-RR RR7.22 — **the capstone finding 4 asks for.**

A bare endpoint splice takes `ipcInvariantFull` to the whole bundle with the
membership conjunct relaxed at the removed thread, under one stated hypothesis:
`splicePredecessorBlocked`, which the bundle genuinely does not entail (see its
docstring) and which is vacuous whenever the removed thread is the queue head.

Nineteen conjuncts come out unconditional.  The twentieth is relaxed rather
than assumed, which is what makes this statement true of the state the
operation actually produces. -/
theorem endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : ipcInvariantFull st)
    (hPred : splicePredecessorBlocked isReceiveQ endpointId st tid) :
    ipcInvariantFullExceptMembership st' tid := by
  refine ⟨endpointQueueRemoveDual_preserves_ipcInvariant st st' endpointId isReceiveQ tid
      hInv.ipcInvariant hObjInv hStep,
    endpointQueueRemoveDual_preserves_dualQueueSystemInvariant endpointId isReceiveQ tid
      st st' hObjInv hStep hInv.dualQueueSystemInvariant,
    endpointQueueRemoveDual_preserves_allPendingMessagesBounded st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.allPendingMessagesBounded,
    endpointQueueRemoveDual_preserves_badgeWellFormed st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.badgeWellFormed,
    endpointQueueRemoveDual_preserves_blockedThreadsPendingMessageConsistent st st'
      endpointId isReceiveQ tid hObjInv hStep hInv.blockedThreadsPendingMessageConsistent,
    endpointQueueRemoveDual_preserves_endpointQueueNoDup st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.dualQueueSystemInvariant hInv.queueHeadBlockedConsistent
      hInv.queueNextTargetBlocked,
    endpointQueueRemoveDual_preserves_ipcStateQueueMembershipConsistent_except st st'
      endpointId isReceiveQ tid hObjInv hInv.dualQueueSystemInvariant.2.2 hStep
      hInv.ipcStateQueueMembershipConsistent hInv.queueHeadBlockedConsistent
      hInv.queueNextTargetBlocked,
    endpointQueueRemoveDual_preserves_queueNextBlockingConsistent st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.queueNextBlockingConsistent
      hInv.queueNextTargetBlocked,
    endpointQueueRemoveDual_preserves_queueHeadBlockedConsistent st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.queueHeadBlockedConsistent
      hInv.queueNextTargetBlocked,
    endpointQueueRemoveDual_preserves_blockedThreadTimeoutConsistent st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.blockedThreadTimeoutConsistent,
    endpointQueueRemoveDual_preserves_donationChainAcyclic st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.donationOwnerValid,
    endpointQueueRemoveDual_preserves_donationOwnerValid st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.donationOwnerValid,
    endpointQueueRemoveDual_preserves_passiveServerIdle st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.passiveServerIdle,
    endpointQueueRemoveDual_preserves_donationBudgetTransfer st st' endpointId isReceiveQ
      tid hObjInv hStep hInv.donationBudgetTransfer,
    endpointQueueRemoveDual_preserves_blockedOnReplyHasTarget st st' endpointId isReceiveQ
      tid hObjInv hStep hInv.blockedOnReplyHasTarget,
    endpointQueueRemoveDual_preserves_replyCallerLinkage st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.replyCallerLinkage,
    endpointQueueRemoveDual_preserves_pendingReceiveReplyWellFormed st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.pendingReceiveReplyWellFormed,
    endpointQueueRemoveDual_preserves_donationOwnerUnique st st' endpointId isReceiveQ tid
      hObjInv hStep hInv.donationOwnerUnique,
    endpointQueueRemoveDual_preserves_endpointQueueTailBlockedConsistent st st' endpointId
      isReceiveQ tid hObjInv hStep hInv.endpointQueueTailBlockedConsistent hPred,
    endpointQueueRemoveDual_preserves_queueNextTargetBlocked st st' endpointId isReceiveQ
      tid hObjInv hStep hInv.queueNextTargetBlocked⟩


-- ============================================================================
-- §7  WS-RR RR7.22 (residual) — the receive-completing store closes the splice
-- ============================================================================
--
-- §6 established what a bare splice leaves: `ipcInvariantFullExceptMembership`,
-- the bundle with the membership conjunct relaxed exactly at the removed thread,
-- because `endpointQueueRemoveDual` deliberately does not touch that thread's
-- `ipcState`.  Every composite that uses the splice writes it in the very next
-- step, and this is that step's side of the contract: the store that sets the
-- removed thread `.ready` **restores** the relaxed conjunct and carries the other
-- nineteen, so the pair closes back to the full bundle.
--
-- Without this the splice engine was a payoff nobody could spend: RR7.22 landed
-- the twenty-conjunct carriage and its two live consumers stayed at the weaker
-- `ipcInvariant`, which is the residual this section removes.

/-- **WS-RR RR7.22 (residual)**: the receive-completing store turns the splice's
relaxed bundle back into the full one.

`storeTcbReceiveComplete st tid msg` rewrites exactly `tid`'s TCB — `ipcState :=
.ready`, the delivered message, and the cleared server-first stash — so it is the
step that discharges the very conjunct the splice relaxed at `tid`: a `.ready`
thread owes no queue membership.

The hypotheses are all facts about the *pre*-state, and each is discharged at the
composites by the splice that produced it.

* `hMsgBounded` — the delivered message is bounded, so the store cannot install
  an oversized `pendingMessage`.
* `hAllNone` is `allTimeoutBudgetsNone`, the discipline every IPC bundle here
  carries.  A store that unblocks a thread cannot preserve the weaker,
  seL4-faithful `blockedThreadTimeoutConsistent` on its own — the conclusion's
  "is blocked" clause is exactly what it falsifies — so the family establishes
  the conjunct from the strong form instead, uniformly.
* `hNotReply` — `tid` was not `.blockedOnReply`.  A donation *owner* must be
  blocked on reply (`donationOwnerValid`), so making an owner `.ready` would
  break that conjunct.

`tid` holding no reply object is **derived**, not demanded: the bundle's own
`replyCallerLinkageReciprocal` sends a `replyObject` forward to a Reply and that
Reply's `caller` back to a `.blockedOnReply` thread, so `hNotReply` already
forbids the link.  Taking it as a hypothesis would have made every caller
re-run that two-step argument.
* `hNotHead`, `hNotTail`, `hNoIncoming` — three readings of one fact, *`tid` is
  out of every endpoint queue*: it heads none, tails none, and nothing's
  `queueNext` points at it.  Three rather than one because the three conjuncts
  that need it read the queues three different ways; the splice establishes all
  three, which is exactly why this step composes with it and with nothing else.

Together with `endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership`
this closes the pair: splice relaxes at `tid`, store restores at `tid`, and the
twenty conjuncts hold of the composite's post-state. -/
theorem storeTcbReceiveComplete_closes_exceptMembership
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
    (hAllNone : allTimeoutBudgetsNone st)
    (hNotReply : ∀ (tcb : TCB), st.objects[tid.toObjId]? = some (.tcb tcb) →
      ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid)
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid)
    (hNoIncoming : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid)
    (hExcept : ipcInvariantFullExceptMembership st tid)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨hIpc, hDual, hBounded, hBadge, hPend, hNoDup, hMemExcept, hQNB, hQHB,
    hTimeout, _hAcyc, hOwnerValid, hPassive, hBudget, hReplyTarget, hReplyLink,
    hStash, hUnique, hTail, hQNT⟩ := hExcept
  -- `tid` carries no reply object: a `replyObject` forces a reciprocal `caller`
  -- back-link, and the backward clause makes that caller `.blockedOnReply` —
  -- which `hNotReply` denies.
  have hUnlinked : ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.replyObject = none := by
    intro tcb hTcb
    cases hR : tcb.replyObject with
    | none => rfl
    | some rid =>
      obtain ⟨r, hr, hCaller⟩ := hReplyLink.1.1 tid tcb rid hTcb hR
      obtain ⟨tcb2, hTcb2, _, ep, rt, hBlocked⟩ := hReplyLink.1.2 rid r tid hr hCaller
      rw [hTcb] at hTcb2
      have hEq : tcb2 = tcb := (KernelObject.tcb.inj (Option.some.inj hTcb2)).symm
      exact ((hNotReply tcb hTcb ep rt) (by rw [← hEq]; exact hBlocked)).elim
  have hSame := storeTcbReceiveComplete_sameSchedContextBindings st st' tid msg hObjInv hStep
  have hOwnerFrame :=
    storeTcbReceiveComplete_donationOwnerFrame st st' tid msg hNotReply hObjInv hStep
  have hOwnerValid' : donationOwnerValid st' :=
    donationOwnerValid_of_frames hSame hOwnerFrame hOwnerValid
  exact ⟨storeTcbReceiveComplete_preserves_ipcInvariant st st' tid msg hIpc hObjInv hStep,
    storeTcbReceiveComplete_preserves_dualQueueSystemInvariant st st' tid msg hObjInv hStep hDual,
    storeTcbReceiveComplete_preserves_allPendingMessagesBounded st st' tid msg hMsgBounded
      hObjInv hStep hBounded,
    storeTcbReceiveComplete_preserves_badgeWellFormed st st' tid msg hBadge hObjInv hStep,
    storeTcbReceiveComplete_preserves_blockedThreadsPendingMessageConsistent st st' tid msg
      hObjInv hStep hPend,
    storeTcbReceiveComplete_preserves_endpointQueueNoDup st st' tid msg hNoDup hObjInv hStep,
    storeTcbReceiveComplete_partial_preserves_ipcStateQueueMembershipConsistent st st' tid msg
      hMemExcept hObjInv hStep,
    storeTcbReceiveComplete_preserves_queueNextBlockingConsistent st st' tid msg hQNB hObjInv
      hStep,
    storeTcbReceiveComplete_preserves_queueHeadBlockedConsistent st st' tid msg hQHB hObjInv
      hStep hNotHead,
    blockedThreadTimeoutConsistent_of_frame
      (storeTcbReceiveComplete_timeoutBudgetFrame st st' tid msg hObjInv hStep) hAllNone,
    donationOwnerValid_implies_donationChainAcyclic st' hOwnerValid',
    hOwnerValid',
    passiveServerIdle_of_frame
      (storeTcbReceiveComplete_passiveServerIdleFrame st st' tid msg hObjInv hStep) hPassive,
    donationBudgetTransfer_of_sameSchedContextBindings hSame hBudget,
    storeTcbReceiveComplete_preserves_blockedOnReplyHasTarget st st' tid msg hObjInv
      hReplyTarget hStep,
    ⟨replyCallerLinkageReciprocal_of_frame
        (storeTcbReceiveComplete_replyLinkageFrame_of_unlinked st st' tid msg hUnlinked
          hObjInv hStep)
        hReplyLink.1,
      storeTcbReceiveComplete_nonBlocked_preserves_blockedOnReplyHasReplyObject st st' tid msg
        hObjInv hReplyLink.2 hStep⟩,
    storeTcbReceiveComplete_preserves_pendingReceiveReplyWellFormed st st' tid msg hObjInv
      hStash hStep,
    donationOwnerUnique_of_sameSchedContextBindings hSame hUnique,
    storeTcbReceiveComplete_preserves_endpointQueueTailBlockedConsistent st st' tid msg hTail
      hObjInv hStep hNotTail,
    storeTcbReceiveComplete_preserves_queueNextTargetBlocked st st' tid msg hQNT hObjInv hStep
      hNoIncoming⟩

-- ============================================================================
-- §8  WS-RR RR7.22 (residual) — the removed thread is detached
-- ============================================================================
--
-- §7's keystone takes three pre-state facts — the stored thread heads no queue,
-- tails no queue, and is nothing's `queueNext` — because the three conjuncts
-- that a `.ready` rewrite could break read the queues three different ways.
-- This section discharges all three at the state a splice produces, which is
-- what makes the pair compose: the splice is precisely the operation that
-- detaches, so it is the only operation the store closes with.

/-- The endpoint the splice's last store installs is the one the post-state
carries: every branch ends `store endpoint; clear the removed thread's links`,
and a link clear writes a TCB, never the endpoint.

Shared by `endpointQueueRemoveDual_headFacts` and the boundary result below —
one statement rather than two copies of the same three-line argument. -/
theorem spliceFinalEndpoint (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (s s' s'' : SystemState) (ep1 : Endpoint)
    (hi : s.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep1) s = .ok ((), s'))
    (hClear : storeTcbQueueLinks s' tid none none none = .ok s'') :
    s''.objects[endpointId]? = some (.endpoint ep1) := by
  have hAt : s'.objects[endpointId]? = some (.endpoint ep1) :=
    storeObject_objects_eq s s' endpointId _ hi hStore
  have hi' : s'.objects.invExt := storeObject_preserves_objects_invExt s s' endpointId _ hi hStore
  have hNe : endpointId ≠ tid.toObjId := by
    intro h
    obtain ⟨orig, hOrig, _⟩ := storeTcbQueueLinks_result_tcb s' s'' tid none none none hi' hClear
    rw [h, lookupTcb_some_objects s' tid orig hOrig] at hAt; cases hAt
  rw [storeTcbQueueLinks_preserves_objects_ne s' s'' tid none none none endpointId hNe hi' hClear]
  exact hAt

/-- WS-RR RR7.22 (residual): the splice ends by clearing the removed thread's
three queue links, so its post-state TCB carries all three as `none`.

Every branch of `SpliceShape` finishes with the same
`storeTcbQueueLinks _ tid none none none`; this reads that off once, rather than
each consumer re-running the four-way case analysis to see it. -/
theorem endpointQueueRemoveDual_removed_links_cleared
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧
      tcb'.queuePrev = none ∧ tcb'.queuePPrev = none ∧ tcb'.queueNext = none := by
  have clear : ∀ s : SystemState, SpliceCtx endpointId s →
      storeTcbQueueLinks s tid none none none = .ok st' →
      ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧
        tcb'.queuePrev = none ∧ tcb'.queuePPrev = none ∧ tcb'.queueNext = none := by
    intro s hCtx hClear
    obtain ⟨orig, _, hAt⟩ := storeTcbQueueLinks_result_tcb s st' tid none none none hCtx.1 hClear
    exact ⟨_, hAt, rfl, rfl, rfl⟩
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp _ _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    exact clear s2 ((c0.store hStore1).store hStore2) hClear
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp _ _ _ _ _ _ hStore1 _ hRelink hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    exact clear s3 (((c0.store hStore1).links hRelink).store hStore2) hClear
  | midLast ep tcb prevTcb prevTid s1 s2 hEp _ _ _ _ _ _ _ _ _ hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    exact clear s2 ((c0.links hRelink).store hStore) hClear
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp _ _ _ _ _ _ _ _ _
      hRelinkPrev _ hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    exact clear s3 (((c0.links hRelinkPrev).links hRelinkNext).store hStore) hClear

/-- WS-RR RR7.22 (residual): **nothing points at the removed thread** after the
splice.

The argument is one line of the doubly-linked discipline rather than a fourth
case analysis: the splice clears the removed thread's `queuePrev`, and forward
integrity says a live `a.queueNext = some tid` forces `tid.queuePrev = some a`.
So the cleared back-link *is* the absence of every incoming link — which is
exactly why the operation clears all three fields and not only the forward one.

`tcbQueueLinkIntegrity st'` is discharged at the composites from the splice's
own `dualQueueSystemInvariant` result. -/
theorem endpointQueueRemoveDual_removed_no_incoming
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st')
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      st'.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid := by
  obtain ⟨tcbT, hTcbT, hPrevNone, _, _⟩ :=
    endpointQueueRemoveDual_removed_links_cleared st st' endpointId isReceiveQ tid hObjInv hStep
  intro a tcbA hA hNext
  obtain ⟨tcbB, hB, hBack⟩ := hLink.1 a tcbA hA tid hNext
  rw [hTcbT] at hB
  obtain rfl : tcbB = tcbT := (KernelObject.tcb.inj (Option.some.inj hB)).symm
  rw [hPrevNone] at hBack
  cases hBack

/-- The spliced side of an endpoint is well-formed when the system's dual-queue
invariant holds — the side selector chosen once instead of at every use. -/
theorem spliceQueue_wellFormed_of_dual {st : SystemState} {endpointId : SeLe4n.ObjId}
    {ep : Endpoint} (isReceiveQ : Bool)
    (hDual : dualQueueSystemInvariant st)
    (hEp : st.objects[endpointId]? = some (.endpoint ep)) :
    intrusiveQueueWellFormed (spliceQueue isReceiveQ ep) st := by
  have h := hDual.1 endpointId ep hEp
  unfold dualQueueEndpointWellFormed at h
  rw [hEp] at h
  unfold spliceQueue
  cases isReceiveQ
  · simpa using h.1
  · simpa using h.2

/-- WS-RR RR7.22 (residual): the removed thread is **neither boundary** of the
spliced queue afterwards.

Four branches, each closed by a fact the shape already carries:

* `headLast` installs the empty queue, so neither boundary is anything;
* `headMore` promotes the successor — distinct from the removed thread by
  acyclicity — and keeps a tail that cannot be the removed thread, since a tail
  has no successor (`intrusiveQueueWellFormed` P3) and this branch's removed
  thread has one;
* `midLast` keeps a head the branch's own guard says is not the removed thread,
  and installs the predecessor as tail — distinct by acyclicity again;
* `midMore` keeps both, the head by that same guard and the tail by P3.

Note which invariant does the work: acyclicity for the two *promoted*
neighbours, and the tail boundary for the two *retained* tails.  Neither
substitutes for the other. -/
theorem endpointQueueRemoveDual_removed_not_boundary
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hDual : dualQueueSystemInvariant st)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (ep' : Endpoint) (hEp' : st'.objects[endpointId]? = some (.endpoint ep')) :
    (spliceQueue isReceiveQ ep').head ≠ some tid ∧
      (spliceQueue isReceiveQ ep').tail ≠ some tid := by
  -- A thread whose `queueNext` names itself closes a one-step cycle.
  have noSelf : ∀ (x : SeLe4n.ThreadId) (xt : TCB), st.objects[x.toObjId]? = some (.tcb xt) →
      xt.queueNext ≠ some x := by
    intro x xt hX hSelf
    exact hDual.2.2 x (.single x x xt hX hSelf)
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid hStep with
  | headLast ep tcb s1 s2 hEp hTcb _ _ _ _ _ hStore1 hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hFinal := spliceFinalEndpoint endpointId tid s1 s2 st' _
      (c0.store hStore1).1 hStore2 hClear
    rw [hEp'] at hFinal
    obtain rfl : ep' = spliceEndpoint isReceiveQ ep { head := none, tail := none } :=
      KernelObject.endpoint.inj (Option.some.inj hFinal)
    rw [spliceQueue_spliceEndpoint]
    exact ⟨by simp, by simp⟩
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp hTcb _ _ hHead _ hNext hStore1 _ hRelink
      hStore2 hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hFinal := spliceFinalEndpoint endpointId tid s2 s3 st' _
      ((c0.store hStore1).links hRelink).1 hStore2 hClear
    rw [hEp'] at hFinal
    obtain rfl : ep' = spliceEndpoint isReceiveQ ep
        { head := some nextTid, tail := (spliceQueue isReceiveQ ep).tail } :=
      KernelObject.endpoint.inj (Option.some.inj hFinal)
    have hTcbObj := lookupTcb_some_objects st tid tcb hTcb
    rw [spliceQueue_spliceEndpoint]
    refine ⟨?_, ?_⟩
    · intro h
      exact noSelf tid tcb hTcbObj (by
        rw [hNext]
        exact congrArg some (Option.some.inj h))
    · intro hT
      obtain ⟨tl, hTl, hTlNext⟩ :=
        (spliceQueue_wellFormed_of_dual isReceiveQ hDual hEp).2.2 tid hT
      rw [hTcbObj] at hTl
      obtain rfl : tl = tcb := (KernelObject.tcb.inj (Option.some.inj hTl)).symm
      rw [hNext] at hTlNext
      cases hTlNext
  | midLast ep tcb prevTcb prevTid s1 s2 hEp hTcb _ _ hHeadNe _ _ hNext hPrevTcb hPrevNext
      hRelink hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hFinal := spliceFinalEndpoint endpointId tid s1 s2 st' _
      (c0.links hRelink).1 hStore hClear
    rw [hEp'] at hFinal
    obtain rfl : ep' = spliceEndpoint isReceiveQ ep
        { head := (spliceQueue isReceiveQ ep).head, tail := some prevTid } :=
      KernelObject.endpoint.inj (Option.some.inj hFinal)
    rw [spliceQueue_spliceEndpoint]
    refine ⟨hHeadNe, ?_⟩
    intro h
    obtain rfl : prevTid = tid := Option.some.inj h
    exact noSelf prevTid prevTcb (lookupTcb_some_objects st prevTid prevTcb hPrevTcb) hPrevNext
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp hTcb _ _ hHeadNe _ _ hNext
      hPrevTcb _ hRelinkPrev _ hRelinkNext hStore hClear =>
    have c0 : SpliceCtx endpointId st := ⟨hObjInv, ep, hEp⟩
    have hFinal := spliceFinalEndpoint endpointId tid s2 s3 st' _
      ((c0.links hRelinkPrev).links hRelinkNext).1 hStore hClear
    rw [hEp'] at hFinal
    obtain rfl : ep' = spliceEndpoint isReceiveQ ep
        { head := (spliceQueue isReceiveQ ep).head, tail := (spliceQueue isReceiveQ ep).tail } :=
      KernelObject.endpoint.inj (Option.some.inj hFinal)
    rw [spliceQueue_spliceEndpoint]
    refine ⟨hHeadNe, ?_⟩
    intro hT
    obtain ⟨tl, hTl, hTlNext⟩ :=
      (spliceQueue_wellFormed_of_dual isReceiveQ hDual hEp).2.2 tid hT
    rw [lookupTcb_some_objects st tid tcb hTcb] at hTl
    obtain rfl : tl = tcb := (KernelObject.tcb.inj (Option.some.inj hTl)).symm
    rw [hNext] at hTlNext
    cases hTlNext

/-- WS-RR RR7.22 (residual): **the three detachment facts §7's keystone asks
for**, at the state a receive-side splice produces.

The three are three readings of one fact — the removed thread is out of every
endpoint queue — and each is closed by a different invariant of the post-state,
which is why they are three hypotheses rather than one:

* **heads and tails elsewhere** fall to `queueHeadBlockedConsistent` /
  `endpointQueueTailBlockedConsistent`, which the splice preserves: a boundary
  of `e`'s receive queue is `.blockedOnReceive e`, and the removed thread is
  still `.blockedOnReceive endpointId`, so no other endpoint can hold it and no
  *send* queue can hold it at all;
* **the spliced queue's own boundaries** fall to §8's shape result, the only
  place the four programs are read;
* **incoming links** fall to the cleared back-link.

So the only endpoint this has to look at structurally is the one the splice
touched, and the only structural fact it needs about the others is the one the
bundle already carries. -/
theorem endpointQueueRemoveDual_removed_detached
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hDual : dualQueueSystemInvariant st)
    (hStep : endpointQueueRemoveDual endpointId true tid st = .ok ((), st'))
    (tcbPost : TCB)
    (hTid : st'.objects[tid.toObjId]? = some (.tcb tcbPost))
    (hState : tcbPost.ipcState = .blockedOnReceive endpointId)
    (hQHB : queueHeadBlockedConsistent st')
    (hQTB : endpointQueueTailBlockedConsistent st')
    (hLink : tcbQueueLinkIntegrity st') :
    (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
        ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) ∧
    (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
        ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) ∧
    (∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
        st'.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid) := by
  refine ⟨?_, ?_, endpointQueueRemoveDual_removed_no_incoming st st' endpointId true tid
    hObjInv hLink hStep⟩
  · intro e ep hEp
    constructor
    · intro hHd
      have hIpc := (hQHB e ep tid tcbPost hEp hTid).1 hHd
      rw [hState] at hIpc
      obtain rfl : endpointId = e := by cases hIpc; rfl
      exact (endpointQueueRemoveDual_removed_not_boundary st st' endpointId true tid hObjInv hDual
        hStep ep hEp).1 (by simpa [spliceQueue] using hHd)
    · intro hHd
      have hIpc := (hQHB e ep tid tcbPost hEp hTid).2 hHd
      rw [hState] at hIpc
      cases hIpc with
      | inl h => cases h
      | inr h => cases h
  · intro e ep hEp
    constructor
    · intro hTl
      have hIpc := (hQTB e ep tid tcbPost hEp hTid).1 hTl
      rw [hState] at hIpc
      obtain rfl : endpointId = e := by cases hIpc; rfl
      exact (endpointQueueRemoveDual_removed_not_boundary st st' endpointId true tid hObjInv hDual
        hStep ep hEp).2 (by simpa [spliceQueue] using hTl)
    · intro hTl
      have hIpc := (hQTB e ep tid tcbPost hEp hTid).2 hTl
      rw [hState] at hIpc
      cases hIpc with
      | inl h => cases h
      | inr h => cases h

end SeLe4n.Kernel
