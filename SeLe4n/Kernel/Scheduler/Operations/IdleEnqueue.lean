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
`capabilityRefs` and `asidTable`, the store maintains both.  Two bodies for one
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
  { st.withObjectStored (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c)) with
      scheduler := st.scheduler.setRunQueueOnCore c
        (((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
          (queuedIdleThread c).priority) }

/-- WS-SM SM5.E.3: the idle-enqueue's object-store write (definitional). -/
theorem enqueueIdleThreadOnCore_objects (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).objects =
      st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c)) := rfl

/-- WS-SM SM5.E.3: the idle-enqueue's scheduler write (definitional).  The
run-queue write is `remove`-then-`insert` so a *re-enqueue* of an already-resident
idle thread refreshes its priority bucket to `0` rather than leaving a stale
bucket (`RunQueue.insert` is an identity for existing members). -/
theorem enqueueIdleThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler =
      st.scheduler.setRunQueueOnCore c
        (((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
          (queuedIdleThread c).priority) := rfl

/-- The enqueue frames the machine state (definitional: the store writes the
object tables and the record update writes the scheduler; neither touches
`machine`). -/
theorem enqueueIdleThreadOnCore_machine (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).machine = st.machine := rfl

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
  rw [enqueueIdleThreadOnCore_scheduler]
  exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ h

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

/-- After the enqueue, core `c`'s idle slot holds the queued idle TCB.  Requires
the object-store invariant so the insert lookup is exact. -/
theorem enqueueIdleThreadOnCore_objects_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (enqueueIdleThreadOnCore st c).objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (queuedIdleThread c)) := by
  rw [enqueueIdleThreadOnCore_objects]
  exact RHTable.getElem?_insert_self st.objects (idleThreadId c).toObjId _ hInv

/-- The enqueue frames the object-store slot of any *distinct* `ObjId` — its
only object-store write is at the idle thread's key. -/
theorem enqueueIdleThreadOnCore_objects_ne (st : SystemState) (c : CoreId) (oid : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (h : (idleThreadId c).toObjId ≠ oid) :
    (enqueueIdleThreadOnCore st c).objects[oid]? = st.objects[oid]? := by
  rw [enqueueIdleThreadOnCore_objects]
  have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => h (eq_of_beq heq)
  exact RHTable.getElem?_insert_ne st.objects (idleThreadId c).toObjId oid _ hNe hInv

/-- WS-SM SM5.E.3 (resolution): after the enqueue, core `c`'s idle thread
resolves to the idle TCB in the object store. -/
theorem enqueueIdleThreadOnCore_getTcb?_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (enqueueIdleThreadOnCore st c).getTcb? (idleThreadId c) = some (queuedIdleThread c) :=
  (SystemState.getTcb?_eq_some_iff _ _ _).mpr (enqueueIdleThreadOnCore_objects_self st c hInv)

/-- WS-SM SM5.E.3 (frame): the enqueue leaves every *other* thread's TCB
resolution unchanged — its only object-store write is at the idle thread's key.
AK7-clean (routes through the typed `getTcb?` accessor + the `.get?`-method form
of `RHTable.getElem?_insert_ne`). -/
theorem enqueueIdleThreadOnCore_getTcb?_ne (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c) :
    (enqueueIdleThreadOnCore st c).getTcb? other = st.getTcb? other := by
  have hNeO : ¬ ((idleThreadId c).toObjId == other.toObjId) = true := fun he =>
    hNe (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
  simp only [SystemState.getTcb?, enqueueIdleThreadOnCore_objects, RHTable_getElem?_eq_get?]
  rw [RHTable_get?_insert_ne st.objects (idleThreadId c).toObjId other.toObjId _ hNeO hInv]

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves the object-store
RobinHood invariant — its only object-store write is an `insert`, which
preserves `invExt`. -/
theorem enqueueIdleThreadOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (enqueueIdleThreadOnCore st c).objects.invExt := by
  rw [enqueueIdleThreadOnCore_objects]
  exact RHTable_insert_preserves_invExt st.objects _ _ hInv

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves core `c`'s run-queue
well-formedness — the only run-queue mutation is the idle `insert`, which
preserves `RunQueue.wellFormed`. -/
theorem enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c).wellFormed := by
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self]
  exact RunQueue.insert_preserves_wellFormed _ (RunQueue.remove_preserves_wellFormed _ hwf _) _ _

-- ============================================================================
-- §3  The `IntermediateState` witnesses — what the boot carries through the
--     enqueue, stated once, of the operation the boot runs
-- ============================================================================

/-- The enqueue adds at most one index entry: it stores one TCB, and the
run-queue write beside it leaves the object index alone. -/
theorem enqueueIdleThreadOnCore_objectIndex_length_le (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).objectIndex.length ≤ st.objectIndex.length + 1 :=
  SystemState.withObjectStored_objectIndex_length_le st (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c))

/-- The enqueue preserves `allTablesInvExtK`.  Fourteen of the seventeen
conjuncts are the store's (`withObjectStored_preserves_allTablesInvExtK`); the
other three are the **boot core's run-queue tables** (`byPriority`,
`threadPriority`, `membership.table`), which the run-queue write may replace —
and `RunQueue` is a structure that *carries* those three proofs as fields, so
`remove` and `insert` hand the new queue back with its invariants already
discharged and the conjuncts are field projections on whatever queue the boot
core ends up with. -/
theorem enqueueIdleThreadOnCore_preserves_allTablesInvExtK (st : SystemState) (c : CoreId)
    (hAll : st.allTablesInvExtK) : (enqueueIdleThreadOnCore st c).allTablesInvExtK := by
  have h := SystemState.withObjectStored_preserves_allTablesInvExtK st
    (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c)) hAll
  unfold SystemState.allTablesInvExtK at h ⊢
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · exact RunQueue.byPrio_invExtK _
  · exact RunQueue.threadPrio_invExtK _
  · exact RunQueue.mem_invExtK _

/-- The enqueue preserves the per-object CNode-slot invariant: the one key it
writes now holds a TCB, which is not a CNode, and every other key is framed. -/
theorem enqueueIdleThreadOnCore_preserves_perObjectSlotsInvariant (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hSlots : perObjectSlotsInvariant st) :
    perObjectSlotsInvariant (enqueueIdleThreadOnCore st c) := by
  intro oid cn hObj
  by_cases hEq : (idleThreadId c).toObjId = oid
  · subst hEq
    rw [enqueueIdleThreadOnCore_objects_self st c hInv] at hObj
    cases hObj
  · rw [enqueueIdleThreadOnCore_objects_ne st c oid hInv hEq] at hObj
    exact hSlots oid cn hObj

/-- The enqueue preserves the per-object VSpace-mapping invariant: the one key
it writes now holds a TCB, which is not a VSpace root, and every other key is
framed. -/
theorem enqueueIdleThreadOnCore_preserves_perObjectMappingsInvariant (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hMappings : perObjectMappingsInvariant st) :
    perObjectMappingsInvariant (enqueueIdleThreadOnCore st c) := by
  intro oid vs hObj
  by_cases hEq : (idleThreadId c).toObjId = oid
  · subst hEq
    rw [enqueueIdleThreadOnCore_objects_self st c hInv] at hObj
    cases hObj
  · rw [enqueueIdleThreadOnCore_objects_ne st c oid hInv hEq] at hObj
    exact hMappings oid vs hObj

/-- The enqueue preserves the lifecycle metadata's consistency with the object
store — the store's own theorem, since the scheduler write beside it touches
neither the store nor the metadata. -/
theorem enqueueIdleThreadOnCore_preserves_lifecycleMetadataConsistent (st : SystemState)
    (c : CoreId) (hAll : st.allTablesInvExtK)
    (hC : SystemState.lifecycleMetadataConsistent st) :
    SystemState.lifecycleMetadataConsistent (enqueueIdleThreadOnCore st c) := by
  have h := SystemState.withObjectStored_preserves_lifecycleMetadataConsistent st
    (idleThreadId c).toObjId (KernelObject.tcb (queuedIdleThread c))
    hAll.1.1 hAll.2.2.2.2.2.1.1 hC
  exact ⟨h.1, h.2⟩

end SeLe4n.Kernel
