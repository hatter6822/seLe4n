-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.Scheduler.IdleThread
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# The per-core idle enqueue — one body for the kernel model and the boot

`enqueueIdleThreadOnCore` makes core `c`'s idle thread *available in its run
queue*: it stores the queued idle TCB at `(idleThreadId c).toObjId` and
`remove`s-then-`insert`s `idleThreadId c` into core `c`'s run queue at the idle
priority.  It is the WS-SM SM5.E.3 run-queue primitive, and since `v0.35.68` it
is also **what the production boot runs**: `Platform.Boot.enqueueIdleThread ist c`
is this operation on `ist.state`, with the intermediate state's four structural
witnesses carried by the theorems in §3 below.

**Why this module exists.**  Until `v0.35.68` the boot had a second body for the
same operation — `Builder.createObject` for the TCB and a hand-written run-queue
write — held to this one by a docstring sentence (*"mirrors
`enqueueIdleThreadOnCore` … definitionally parallel"*), which was true of
`objects` and the run queue and false of the bookkeeping: the builder skips
`asidTable` (and, until `v0.35.78`, the capability-reference table), the store
maintains it.  Two bodies for one
question is the duplication this project spends its length retiring, and the
boot's *only* reason to differ was that the kernel-model definition lived in a
staged module (`Scheduler/Operations/PerCoreIdle.lean`) that itself imports
`Platform.Boot`, so the boot could not reach it.  The definition and the frames
the boot needs therefore live here, in a production module upstream of the boot;
`PerCoreIdle` keeps the scheduler-level SM5.E theorems and consumes this.

What is stated here is exactly what is stated over `Model` vocabulary: the
definitional frames (§1), the object-store frames and the run-queue
well-formedness (§2), and the four `IntermediateState` witnesses plus the index
bound the boot's capacity theorem reads (§3).  The per-core scheduler-invariant
preservation surface (`runnableThreadsAreTCBsOnCore`, `queueCurrentConsistentOnCore`,
…) and the SM5.E.6 keystone stay with the per-core invariant vocabulary in
`PerCoreIdle`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  `enqueueIdleThreadOnCore` and its definitional frames
-- ============================================================================

/-- WS-SM SM5.E.3 (run-queue form, plan §3.5): make core `c`'s idle thread
*available in its run queue*.

The SM4.G boot installer (`installIdleThread`) makes idle `c` the **current**
thread on core `c` (`current = some (idleThreadId c)`, run queue empty); the
production scheduler (`scheduleEffectiveOnCore`) then models a subsequently-idle
core as `current = none`.  For `chooseThreadOnCore` — which reads only the run
queue — to *fall back to idle*, the idle thread must be a run-queue *member*.
`enqueueIdleThreadOnCore` is the primitive that ensures this: it (a) creates /
refreshes the idle TCB in the object store at `(idleThreadId c).toObjId` — through
the pure store `SystemState.withObjectStored` (`v0.35.67`), because the key may
hold nothing and a store is what registers a new object in `objectIndex`,
`objectIndexSet` and the kind table; the raw insert it replaced left a fixture's
idle thread outside the index, which no boot state is — and (b) `remove`s then
re-`insert`s `idleThreadId c` into core `c`'s run queue at the idle priority `⟨0⟩`
(`= (queuedIdleThread c).priority`, which equals its effective run-queue priority
since idle carries no PIP boost).

The `remove`-then-`insert` (rather than a bare `insert`) is deliberate: a
*re-enqueue* of an already-resident idle thread must refresh its priority bucket
to `0`, but `RunQueue.insert` is an identity for existing members — a bare insert
would leave a stale `byPriority` bucket if idle were ever resident at a non-`0`
priority, so bucket-first selection could pick idle ahead of lower-bucket user
threads.  `remove`-then-`insert` makes the refresh sound for *every* prior state
(the membership set is unchanged — still `runQueue ∪ {idle}` — only idle's bucket
is canonicalised to `0`).

**It deliberately does not write `currentOnCore`** (`enqueueIdleThreadOnCore_currentOnCore`).
Writing both would make a boot state violate `queueCurrentConsistent`, which
says a core's current thread is *not* also queued — the dequeue-on-dispatch
discipline.  Enqueuing without dispatching is the correct boot posture: every
core comes up with a dispatchable idle thread waiting, and the core's first
scheduling point (`chooseThreadOnCore`, reached from its bring-up reschedule or
its first timer tick) selects it, dequeues it and sets `current`.

**This is the production boot's idle install** (`v0.35.68`):
`Platform.Boot.enqueueIdleThread ist c` has `state := enqueueIdleThreadOnCore
ist.state c` (`enqueueIdleThread_state`, by `rfl`), so the kernel model and the
boot share one body and the boot's structural witnesses are §3's theorems.

Footprint: WRITES the object-store slot `(idleThreadId c).toObjId` and core
`c`'s run-queue slot.  Every other object-store key and every other core's
scheduler slot is framed out (the lemmas below).  The store's index bookkeeping
is the object store's own, guarded by the table-level `objStore` lock the
footprint (`enqueueIdleThreadOnCoreLockSet`, `PerCoreIdle`) already names in
write mode — no finer lock exists for it, and none is declared elsewhere.
Mirrors the SM5.C `enqueueRunnableOnCore` shape; the difference is that idle
threads are created here (they need not pre-exist), so there is no
`getTcb?`-resolves precondition and no fail-closed branch. -/
def enqueueIdleThreadOnCore (st : SystemState) (c : CoreId) : SystemState :=
  ((st.runRemoveOnCore c (idleThreadId c)).withObjectStored (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c))).runEnqueueOnCore c (idleThreadId c)
    (queuedIdleThread c).priority

/-- WS-ZA ZA4.5: off the run-queue links, the enqueue's object store is the bare
store of the queued idle TCB — the unlink and the append write only TCB
run-queue fields. -/
theorem enqueueIdleThreadOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (enqueueIdleThreadOnCore st c).objectsAgreeOffRunLinks
      (st.withObjectStored (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c))) :=
  (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _).trans
    ((SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c _).withObjectStored
      (SystemState.runRemoveOnCore_objects_invExt _ _ _ hInv) hInv _ _)

/-- WS-ZA ZA4.5: the idle enqueue keeps every run queue in agreement with the
threads' links, provided no other core's queue holds core `c`'s idle thread:
the removal leaves it on no queue, the store writes a TCB claiming no place,
and the append is the proven link append. -/
theorem enqueueIdleThreadOnCore_runQueueRefined (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hOther : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains (idleThreadId c) = false) :
    (enqueueIdleThreadOnCore st c).runQueueRefined := by
  have hR1 := SystemState.runRemoveOnCore_refined (c := c) (t := idleThreadId c) hR
  have hInv1 := SystemState.runRemoveOnCore_objects_invExt st c (idleThreadId c) hInv
  have hGone : ∀ c', ((st.runRemoveOnCore c (idleThreadId c)).scheduler.runQueueOnCore c').contains
      (idleThreadId c) = false := by
    intro c'
    by_cases hc : c' = c
    · subst hc
      rw [SystemState.runRemoveOnCore_runQueueOnCore_self, RunQueue.contains_remove]
      simp
    · rw [SystemState.runRemoveOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc)]
      exact hOther c' hc
  have hR2 := SystemState.withObjectStored_tcb_runQueueRefined (t := queuedIdleThread c) hInv1 rfl
    (fun c' => by rw [(hR1 c').contains]; exact hGone c') hR1
  unfold enqueueIdleThreadOnCore
  refine SystemState.runEnqueueOnCore_refined hR2 ?_ (fun c' _ => ?_)
  · unfold SystemState.getTcb?
    rw [SystemState.withObjectStored_objects_self _ _ _ hInv1]
    rfl
  · rw [SystemState.withObjectStored_scheduler]
    exact hGone c'

/-- WS-SM SM5.E.3: the idle-enqueue's scheduler write.  The ghost queue is
`remove`-then-`insert`, so a *re-enqueue* of an already-resident idle thread
refreshes its priority bucket to `0` rather than leaving a stale bucket
(`RunQueue.insert` is an identity for existing members); core `c`'s ends are the
append's over the unlinked state (WS-ZA ZA4.5). -/
theorem enqueueIdleThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c
        (((st.runRemoveOnCore c (idleThreadId c)).withObjectStored (idleThreadId c).toObjId
          (KernelObject.tcb (queuedIdleThread c))).runEnqueueEnds c (idleThreadId c)
            (queuedIdleThread c).priority)).setRunQueueOnCore c
        (((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
          (queuedIdleThread c).priority) := by
  simp only [enqueueIdleThreadOnCore, SystemState.runEnqueueOnCore_scheduler,
    SystemState.withObjectStored_scheduler, SystemState.runRemoveOnCore_scheduler,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  rw [SchedulerState.setRunQueueOnCore_setRunQueueEndsOnCore,
    SchedulerState.setRunQueueOnCore_setRunQueueOnCore,
    SchedulerState.setRunQueueEndsOnCore_setRunQueueEndsOnCore]

/-- The enqueue frames the machine state: the store writes the object tables,
the link writes the object store and the scheduler. -/
theorem enqueueIdleThreadOnCore_machine (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).machine = st.machine := by
  simp only [enqueueIdleThreadOnCore, SystemState.runEnqueueOnCore_machine]
  rw [storeObject_machine_eq _ _ _ _ (SystemState.storeObject_eq_withObjectStored _ _ _),
    SystemState.runRemoveOnCore_machine]

/-- WS-SM SM5.E.3: after the enqueue, core `c`'s run queue is the old one with
the idle thread inserted. -/
theorem enqueueIdleThreadOnCore_runQueueOnCore_self (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c =
      ((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
        (queuedIdleThread c).priority := by
  rw [enqueueIdleThreadOnCore_scheduler]
  exact SchedulerState.setRunQueueOnCore_runQueueOnCore_self _ _ _

/-- WS-SM SM5.E.3/.4 (cross-core frame): enqueuing idle `c` leaves every *other*
core `c' ≠ c`'s run queue untouched — it never adds idle `c` to another core's
queue.  The operational half of `idleThread_core_locality`. -/
theorem enqueueIdleThreadOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (h : c ≠ c') :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c' =
      st.scheduler.runQueueOnCore c' := by
  rw [enqueueIdleThreadOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ h,
    SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]

/-- WS-SM SM5.E.3 (frame): the enqueue does not touch any core's active domain. -/
theorem enqueueIdleThreadOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler.activeDomainOnCore c' =
      st.scheduler.activeDomainOnCore c' := by
  rw [enqueueIdleThreadOnCore_scheduler]; simp

/-- WS-SM SM5.E.3 (frame): the enqueue does not touch any core's current slot. -/
theorem enqueueIdleThreadOnCore_currentOnCore (st : SystemState) (c c' : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler.currentOnCore c' =
      st.scheduler.currentOnCore c' := by
  rw [enqueueIdleThreadOnCore_scheduler]; simp

-- ============================================================================
-- §2  Membership, the object-store frames, and run-queue well-formedness
-- ============================================================================

/-- WS-SM SM5.E.3 (membership): after the enqueue, core `c`'s idle thread is a
member of core `c`'s run queue.  The substantive "the idle thread is genuinely
available as a fallback" content. -/
theorem enqueueIdleThreadOnCore_mem_runQueueOnCore_self (st : SystemState) (c : CoreId) :
    idleThreadId c ∈ ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c).toList := by
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self, RunQueue.mem_toList_iff_mem]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- WS-SM SM5.E.3 (idempotency): the run-queue membership effect of enqueuing the
idle thread is idempotent — after one enqueue the idle thread is already a member,
and `RunQueue.insert`'s internal `contains` guard makes a second enqueue add no
duplicate.  So a dispatch loop may call it repeatedly without growing the queue. -/
theorem enqueueIdleThreadOnCore_mem_idempotent (st : SystemState) (c : CoreId) :
    idleThreadId c ∈
      ((enqueueIdleThreadOnCore (enqueueIdleThreadOnCore st c) c).scheduler.runQueueOnCore c).toList :=
  enqueueIdleThreadOnCore_mem_runQueueOnCore_self (enqueueIdleThreadOnCore st c) c

/-- After the enqueue, core `c`'s idle slot holds the queued idle TCB, up to its
run-queue links (WS-ZA ZA4.5: the append writes them).  Requires the
object-store invariant so the insert lookup is exact. -/
theorem enqueueIdleThreadOnCore_objects_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    ((enqueueIdleThreadOnCore st c).objects[(idleThreadId c).toObjId]?).map
        KernelObject.withoutRunLinks =
      some (KernelObject.tcb (queuedIdleThread c)).withoutRunLinks := by
  rw [enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv,
    SystemState.withObjectStored_objects_self _ _ _ hInv]
  rfl

/-- The enqueue frames the object-store slot of any *distinct* `ObjId` up to its
run-queue links — its only other object-store writes are the unlink's and the
append's link writes on the idle thread's queue neighbours. -/
theorem enqueueIdleThreadOnCore_objects_ne (st : SystemState) (c : CoreId) (oid : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (h : (idleThreadId c).toObjId ≠ oid) :
    ((enqueueIdleThreadOnCore st c).objects[oid]?).map KernelObject.withoutRunLinks =
      (st.objects[oid]?).map KernelObject.withoutRunLinks := by
  rw [enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv,
    SystemState.withObjectStored_objects]
  have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => h (eq_of_beq heq)
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.getElem?_insert_ne st.objects (idleThreadId c).toObjId oid _ hNe hInv]

/-- WS-SM SM5.E.3 (resolution): after the enqueue, core `c`'s idle thread
resolves to the idle TCB, up to its run-queue links. -/
theorem enqueueIdleThreadOnCore_getTcb?_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    ∃ t, (enqueueIdleThreadOnCore st c).getTcb? (idleThreadId c) = some t ∧
      t.withoutRunLinks = (queuedIdleThread c).withoutRunLinks := by
  have hS : (st.withObjectStored (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c))).getTcb? (idleThreadId c) = some (queuedIdleThread c) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (SystemState.withObjectStored_objects_self _ _ _ hInv)
  have hA := (enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv).getTcb? (idleThreadId c)
  rw [hS] at hA
  exact TCB.exists_of_map_withoutRunLinks_eq hA

/-- The idle thread's record after the enqueue reads, on every field past the
run-queue links, as the queued idle TCB. -/
theorem enqueueIdleThreadOnCore_getTcb?_self_map {α : Type _} (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (f : TCB → α)
    (hf : ∀ u : TCB, f u.withoutRunLinks = f u := by intro; rfl) :
    ((enqueueIdleThreadOnCore st c).getTcb? (idleThreadId c)).map f =
      some (f (queuedIdleThread c)) := by
  obtain ⟨t, ht, e⟩ := enqueueIdleThreadOnCore_getTcb?_self st c hInv
  rw [ht]
  exact congrArg some (TCB.proj_eq_of_withoutRunLinks_eq f e hf)

/-- WS-SM SM5.E.3 (frame): the enqueue leaves every *other* thread's TCB
resolution unchanged up to its run-queue links. -/
theorem enqueueIdleThreadOnCore_getTcb?_ne (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c) :
    ((enqueueIdleThreadOnCore st c).getTcb? other).map TCB.withoutRunLinks =
      (st.getTcb? other).map TCB.withoutRunLinks := by
  rw [(enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv).getTcb? other]
  have hNeO : ¬ ((idleThreadId c).toObjId == other.toObjId) = true := fun he =>
    hNe (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
  simp only [SystemState.getTcb?, SystemState.withObjectStored_objects, RHTable_getElem?_eq_get?]
  rw [RHTable_get?_insert_ne st.objects (idleThreadId c).toObjId other.toObjId _ hNeO hInv]

/-- A thread other than idle that resolves after the enqueue resolved before,
to a TCB agreeing off its run-queue links. -/
theorem enqueueIdleThreadOnCore_getTcb?_ne_back (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c)
    {t : TCB} (h : (enqueueIdleThreadOnCore st c).getTcb? other = some t) :
    ∃ t', st.getTcb? other = some t' ∧ t.withoutRunLinks = t'.withoutRunLinks := by
  have hm := enqueueIdleThreadOnCore_getTcb?_ne st c other hInv hNe
  rw [h] at hm
  cases e : st.getTcb? other with
  | none => rw [e] at hm; cases hm
  | some t' => rw [e] at hm; exact ⟨t', rfl, Option.some.inj hm⟩

/-- ...and one that resolved before resolves after, agreeing off its links. -/
theorem enqueueIdleThreadOnCore_getTcb?_ne_fwd (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c)
    {t' : TCB} (h : st.getTcb? other = some t') :
    ∃ t, (enqueueIdleThreadOnCore st c).getTcb? other = some t ∧
      t.withoutRunLinks = t'.withoutRunLinks := by
  have hm := enqueueIdleThreadOnCore_getTcb?_ne st c other hInv hNe
  rw [h] at hm
  cases e : (enqueueIdleThreadOnCore st c).getTcb? other with
  | none => rw [e] at hm; cases hm
  | some t => rw [e] at hm; exact ⟨t, rfl, Option.some.inj hm⟩

/-- Another thread resolves after the enqueue exactly when it did before. -/
theorem enqueueIdleThreadOnCore_getTcb?_ne_isSome (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c) :
    ((enqueueIdleThreadOnCore st c).getTcb? other).isSome = (st.getTcb? other).isSome := by
  have := congrArg Option.isSome (enqueueIdleThreadOnCore_getTcb?_ne st c other hInv hNe)
  simpa using this

/-- The idle TCB as the enqueue leaves it on a queue that was empty: alone on
core `c`'s queue at the idle priority, with no neighbours (WS-ZA ZA4.5). -/
def idleThreadQueuedAlone (c : CoreId) : TCB :=
  { (queuedIdleThread c) with
      runCoreCode := c.val + 1, runPrio := (queuedIdleThread c).priority, runPrevCode := 0,
      runNextCode := 0, runBucketPrevCode := 0, runBucketNextCode := 0 }

/-- On a fresh idle slot and an empty queue there are no neighbours to relink:
the enqueue's object store is exactly the store of the idle TCB alone on its
queue (WS-ZA ZA4.5).  This is the boot's case. -/
theorem enqueueIdleThreadOnCore_objects_of_fresh (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hFresh : st.objects[(idleThreadId c).toObjId]? = none)
    (hTail : (st.scheduler.runQueueEndsOnCore c).tail = 0)
    (hBTail : (RunQueue.endsOf (st.scheduler.runQueueEndsOnCore c).buckets
      (queuedIdleThread c).priority).tail = 0) (x : SeLe4n.ObjId) :
    (enqueueIdleThreadOnCore st c).objects[x]? =
      (st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (idleThreadQueuedAlone c)))[x]? := by
  unfold enqueueIdleThreadOnCore
  have hL0 : st.runLinkOn c (idleThreadId c) = RunQueue.RunQueueLink.none := by
    unfold SystemState.runLinkOn SystemState.getTcb?
    rw [hFresh]
  have hS1o : (st.runRemoveOnCore c (idleThreadId c)).objects = st.objects := by
    rw [SystemState.runRemoveOnCore_objects, hL0]; rfl
  have hS1s : (st.runRemoveOnCore c (idleThreadId c)).scheduler.runQueueEndsOnCore c =
      st.scheduler.runQueueEndsOnCore c := by
    rw [SystemState.runRemoveOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueEndsOnCore,
      SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_self]
    unfold SystemState.runRemoveEnds; rw [hL0]; rfl
  generalize hS1 : st.runRemoveOnCore c (idleThreadId c) = S1 at hS1o hS1s
  have hInv1 : S1.objects.invExt := hS1o ▸ hInv
  have hS2o := SystemState.withObjectStored_objects S1 (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c))
  have hS2s := SystemState.withObjectStored_scheduler S1 (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c))
  have hS2t : (S1.withObjectStored (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c))).getTcb? (idleThreadId c) = some (queuedIdleThread c) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (SystemState.withObjectStored_objects_self _ _ _ hInv1)
  generalize S1.withObjectStored (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c)) = S2
    at hS2o hS2s hS2t
  have hL2 : S2.runLinkOn c (idleThreadId c) = RunQueue.RunQueueLink.none := by
    unfold SystemState.runLinkOn; rw [hS2t]; rfl
  rw [SystemState.runEnqueueOnCore_objects, hL2, if_neg (by decide)]
  unfold SystemState.runAppendLinks
  simp only [hS2s, hS1s, hTail, hBTail, SystemState.updateTcbAtCode, if_true]
  rw [SystemState.objects_mapTcbInPlace]
  by_cases hx : (idleThreadId c).toObjId = x
  · subst hx
    rw [if_pos (beq_self_eq_true _), hS2o, hS1o]
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_self _ _ _ hInv, RHTable.getElem?_insert_self _ _ _ hInv]
    rfl
  · have hNe : ¬(((idleThreadId c).toObjId == x) = true) := fun e => hx (eq_of_beq e)
    rw [if_neg hNe, hS2o, hS1o]
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne _ _ _ _ hNe hInv, RHTable.getElem?_insert_ne _ _ _ _ hNe hInv]

/-- The boot's form: core `c`'s queue still has the empty ends. -/
theorem enqueueIdleThreadOnCore_objects_of_empty (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hFresh : st.objects[(idleThreadId c).toObjId]? = none)
    (hEnds : st.scheduler.runQueueEndsOnCore c = RunQueueEnds.empty) (x : SeLe4n.ObjId) :
    (enqueueIdleThreadOnCore st c).objects[x]? =
      (st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (idleThreadQueuedAlone c)))[x]? :=
  enqueueIdleThreadOnCore_objects_of_fresh st c hInv hFresh (by rw [hEnds]; rfl)
    (by
      rw [hEnds]
      show ((RunQueue.empty.buckets.get? (queuedIdleThread c).priority).getD {}).tail = 0
      rw [show RunQueue.empty.buckets.get? (queuedIdleThread c).priority = none from
        RHTable_get?_empty 16 (by omega)]
      rfl) x

/-- The enqueue writes no other core's queue ends. -/
theorem enqueueIdleThreadOnCore_runQueueEndsOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueEndsOnCore c' =
      st.scheduler.runQueueEndsOnCore c' := by
  rw [enqueueIdleThreadOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueEndsOnCore,
    SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_ne _ _ _ _ h]

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves the object-store
RobinHood invariant — the unlink and append rewrite resident values, the store
is an `insert`. -/
theorem enqueueIdleThreadOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (enqueueIdleThreadOnCore st c).objects.invExt :=
  SystemState.runEnqueueOnCore_objects_invExt _ _ _ _
    (SystemState.withObjectStored_preserves_objects_invExt _ _ _
      (SystemState.runRemoveOnCore_objects_invExt _ _ _ hInv))

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves core `c`'s run-queue
well-formedness — the only run-queue mutation is the idle `insert`, which
preserves `RunQueue.wellFormed`. -/
theorem enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c).wellFormed := by
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self]
  exact RunQueue.insert_preserves_wellFormed _ (RunQueue.remove_preserves_wellFormed _ hwf _) _ _

/-- The enqueue adds at most one index entry: it stores one TCB, and the
run-queue link writes beside it leave the object index alone. -/
theorem enqueueIdleThreadOnCore_objectIndex_length_le (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).objectIndex.length ≤ st.objectIndex.length + 1 := by
  have h1 := SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer
    ((st.runRemoveOnCore c (idleThreadId c)).withObjectStored (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c))) c (idleThreadId c) (queuedIdleThread c).priority
  have h2 := SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c (idleThreadId c)
  have hLe := SystemState.withObjectStored_objectIndex_length_le
    (st.runRemoveOnCore c (idleThreadId c)) (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c))
  unfold SystemState.onlyObjectsSchedulerDiffer at h1 h2
  have e2 : (st.runRemoveOnCore c (idleThreadId c)).objectIndex = st.objectIndex := by rw [h2]
  unfold enqueueIdleThreadOnCore
  rw [h1]
  rw [e2] at hLe
  exact hLe

/-- The enqueue preserves `allTablesInvExtK`: the store's own preservation,
between two link writes that rewrite resident object values and nothing else. -/
theorem enqueueIdleThreadOnCore_preserves_allTablesInvExtK (st : SystemState) (c : CoreId)
    (hAll : st.allTablesInvExtK) : (enqueueIdleThreadOnCore st c).allTablesInvExtK := by
  have h1 := (SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c (idleThreadId c)).allTablesInvExtK
    (SystemState.runRemoveOnCore_objects_invExtK _ _ _ hAll.1) hAll
  have h2 := SystemState.withObjectStored_preserves_allTablesInvExtK _ (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c)) h1
  exact (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer _ _ _ _).allTablesInvExtK
    (SystemState.runEnqueueOnCore_objects_invExtK _ _ _ _ h2.1) h2

/-- The enqueue preserves the per-object CNode-slot invariant: the one key it
stores now holds a TCB, which is not a CNode, every other key is framed, and the
link writes touch TCBs alone. -/
theorem enqueueIdleThreadOnCore_preserves_perObjectSlotsInvariant (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hSlots : perObjectSlotsInvariant st) :
    perObjectSlotsInvariant (enqueueIdleThreadOnCore st c) := by
  intro oid cn hObj
  have hObj' := (enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv).get_of_not_tcb'
    (fun _ e => KernelObject.noConfusion e) hObj
  rw [SystemState.withObjectStored_objects] at hObj'
  simp only [RHTable_getElem?_eq_get?] at hObj'
  by_cases hEq : (idleThreadId c).toObjId = oid
  · subst hEq
    rw [RHTable.getElem?_insert_self st.objects _ _ hInv] at hObj'
    cases hObj'
  · have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => hEq (eq_of_beq heq)
    rw [RHTable.getElem?_insert_ne st.objects _ oid _ hNe hInv] at hObj'
    exact hSlots oid cn (by simpa only [RHTable_getElem?_eq_get?] using hObj')

/-- The enqueue preserves the per-object VSpace-mapping invariant, for the same
reason. -/
theorem enqueueIdleThreadOnCore_preserves_perObjectMappingsInvariant (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hMappings : perObjectMappingsInvariant st) :
    perObjectMappingsInvariant (enqueueIdleThreadOnCore st c) := by
  intro oid vs hObj
  have hObj' := (enqueueIdleThreadOnCore_objectsAgreeOffRunLinks st c hInv).get_of_not_tcb'
    (fun _ e => KernelObject.noConfusion e) hObj
  rw [SystemState.withObjectStored_objects] at hObj'
  simp only [RHTable_getElem?_eq_get?] at hObj'
  by_cases hEq : (idleThreadId c).toObjId = oid
  · subst hEq
    rw [RHTable.getElem?_insert_self st.objects _ _ hInv] at hObj'
    cases hObj'
  · have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => hEq (eq_of_beq heq)
    rw [RHTable.getElem?_insert_ne st.objects _ oid _ hNe hInv] at hObj'
    exact hMappings oid vs (by simpa only [RHTable_getElem?_eq_get?] using hObj')

/-- The enqueue preserves the lifecycle metadata's consistency with the object
store — the store's own theorem, between link writes that keep every object's
kind and leave the metadata alone. -/
theorem enqueueIdleThreadOnCore_preserves_objectTypeMetadataConsistent (st : SystemState)
    (c : CoreId) (hAll : st.allTablesInvExtK)
    (hC : SystemState.objectTypeMetadataConsistent st) :
    SystemState.objectTypeMetadataConsistent (enqueueIdleThreadOnCore st c) := by
  have hD1 := SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c (idleThreadId c)
  have hAll1 := hD1.allTablesInvExtK (SystemState.runRemoveOnCore_objects_invExtK _ _ _ hAll.1) hAll
  have hC1 := hD1.objectTypeMetadataConsistent
    (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c _) hC
  have hC2 := SystemState.withObjectStored_preserves_objectTypeMetadataConsistent _
    (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c))
    hAll1.1.1 hAll1.2.2.2.2.2.1.1 hC1
  exact (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer _ _ _ _).objectTypeMetadataConsistent
    (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _) hC2

end SeLe4n.Kernel
