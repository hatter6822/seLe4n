-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Platform.Boot

/-!
# WS-SM SM5.E — Per-core idle threads

Per-core idle-thread theorems (plan §3.5 / §4.3 of
`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md`).  Each core has a dedicated
idle TCB — the lowest-priority thread it runs when nothing else is runnable —
bound to its own core and never migrating.

The idle-thread *definitions* (`idleThreadId`, `createIdleThread`) and the
*boot installer* (`installIdleThread`, `bootFromPlatformWithIdleThreads`) live
in `SeLe4n.Platform.Boot` (where they landed at WS-SM SM4.G, alongside the
`IntermediateState` / `Builder` machinery the install needs).  This module —
which can see both the idle definitions *and* the SM5.A `chooseThreadOnCore`
selection theorems — adds the scheduler-level idle properties that close SM5.E:

* **SM5.E.5** `idleThread_priority_zero` — the idle thread is priority `⟨0⟩`
  (the lowest), so a runnable user thread always outranks it; idle never
  starves a higher-priority thread.  Plus the companion field lemmas
  (`createIdleThread_domain_zero`, `createIdleThread_cpuAffinity`,
  `createIdleThread_tid`).

* **SM5.E.3 (run-queue form)** `enqueueIdleThreadOnCore` — the per-core
  primitive that makes core `c`'s idle thread *available in its run queue* (the
  SM4.G boot installer makes it *current*; for the selection to fall back to
  idle, idle must be a run-queue member, which `chooseThreadOnCore` reads).
  Its frame / membership / preservation lemmas mirror the SM5.C
  `enqueueRunnableOnCore` surface.

* **SM5.E.6** `chooseThreadOnCore_always_succeeds` — when core `c`'s idle thread
  is enqueued and in its active domain (the SM5.E discharge predicate
  `idleThreadEnqueuedOnCore`), `chooseThreadOnCore` returns `some` — it never
  spuriously idles a core that has at least the idle thread available.  This
  discharges the conditional SM5.A `chooseThreadOnCore_some_of_eligible` with
  the always-present idle candidate.  `enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds`
  demonstrates the discharge predicate is satisfiable (non-vacuity) by a real
  operation, on any well-formed boot-domain state.

* **SM5.E.4** `idleThread_core_locality` — core `c`'s idle thread never appears
  on another core `c' ≠ c`'s run queue.  The substantive form is *affinity*-
  based: idle `c` is bound to `cpuAffinity = some c` (SM5.E.2), so it is not
  admitted on `c'` (`affinityAdmitsCore`); the operational companion
  (`enqueueIdleThreadOnCore_runQueueOnCore_ne`) shows the enqueue is core-local.

This module is staged (`Platform.Staged`); SM5.I's per-core dispatch loop is the
first runtime exerciser (it wires `current = none` ⇒ run the per-core idle
thread).  Every declaration here is machine-checked, adding no trusted
dependency beyond Lean's foundational `propext` / `Quot.sound` /
`Classical.choice`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId allCores)
-- WS-SM SM5.E: `idleThreadId` + injectivity witnesses now live in
-- `SeLe4n.Kernel.Scheduler.IdleThread` (namespace `SeLe4n.Kernel`), so they
-- resolve unqualified here; only the idle TCB constructor still lives in `Boot`.
open SeLe4n.Platform.Boot (createIdleThread)

-- ============================================================================
-- §1  Idle-thread field lemmas (SM5.E.5 + companions)
-- ============================================================================

/-- WS-SM SM5.E.5 (plan §3.5, Theorem `idleThread_priority_zero`): the idle
thread is priority `⟨0⟩` — the lowest schedulable priority.  Consequence: a
runnable user thread (priority `> 0`, or even `0` with an earlier FIFO
position) is never displaced by idle; idle is only selected when no
higher-priority thread is eligible.  `rfl` from `createIdleThread`. -/
@[simp] theorem idleThread_priority_zero (c : CoreId) :
    (createIdleThread c).priority = ⟨0⟩ := rfl

/-- WS-SM SM5.E.5: the idle thread is in scheduling domain `⟨0⟩` (the boot
active domain).  So when core `c`'s active domain is the boot domain (the RPi5
v1.0.0 single-domain case, where `domainSchedule = []`), the idle thread is
in-domain and hence an eligible selection candidate. -/
@[simp] theorem createIdleThread_domain_zero (c : CoreId) :
    (createIdleThread c).domain = ⟨0⟩ := rfl

/-- WS-SM SM5.E.2 (plan §3.5): the idle thread for core `c` is pinned to core
`c` via `cpuAffinity = some c`.  This is the field that makes
`idleThread_core_locality` substantive — `affinityAdmitsCore (createIdleThread
c) c' = (c == c')`, so idle `c` is not admitted on any `c' ≠ c`. -/
@[simp] theorem createIdleThread_cpuAffinity (c : CoreId) :
    (createIdleThread c).cpuAffinity = some c := rfl

/-- WS-SM SM5.E.1: the idle thread's id is `idleThreadId c`. -/
@[simp] theorem createIdleThread_tid (c : CoreId) :
    (createIdleThread c).tid = idleThreadId c := rfl

-- ============================================================================
-- §2  `enqueueIdleThreadOnCore` — make core `c`'s idle thread run-queue-resident
-- ============================================================================

/-- WS-SM SM5.E.3 (run-queue form, plan §3.5): make core `c`'s idle thread
*available in its run queue*.

The SM4.G boot installer (`installIdleThread`) makes idle `c` the **current**
thread on core `c` (`current = some (idleThreadId c)`, run queue empty); the
production scheduler (`scheduleEffectiveOnCore`) then models a subsequently-idle
core as `current = none`.  For `chooseThreadOnCore` — which reads only the run
queue — to *fall back to idle*, the idle thread must be a run-queue *member*.
`enqueueIdleThreadOnCore` is the primitive that ensures this: it (a) creates /
refreshes the idle TCB in the object store at `(idleThreadId c).toObjId`, and
(b) `remove`s then re-`insert`s `idleThreadId c` into core `c`'s run queue at the
idle priority `⟨0⟩` (`= (createIdleThread c).priority`, which equals its effective
run-queue priority since idle carries no PIP boost).

The `remove`-then-`insert` (rather than a bare `insert`) is deliberate: a
*re-enqueue* of an already-resident idle thread must refresh its priority bucket
to `0`, but `RunQueue.insert` is an identity for existing members — a bare insert
would leave a stale `byPriority` bucket if idle were ever resident at a non-`0`
priority, so bucket-first selection could pick idle ahead of lower-bucket user
threads.  `remove`-then-`insert` makes the refresh sound for *every* prior state
(the membership set is unchanged — still `runQueue ∪ {idle}` — only idle's bucket
is canonicalised to `0`).

Footprint: WRITES the object-store slot `(idleThreadId c).toObjId` and core
`c`'s run-queue slot.  Every other object-store key and every other core's
scheduler slot is framed out (the lemmas below).  Mirrors the SM5.C
`enqueueRunnableOnCore` shape; the difference is that idle threads are created
here (they need not pre-exist), so there is no `getTcb?`-resolves precondition
and no fail-closed branch. -/
def enqueueIdleThreadOnCore (st : SystemState) (c : CoreId) : SystemState :=
  { st with
      objects := st.objects.insert (idleThreadId c).toObjId
        (KernelObject.tcb (createIdleThread c)),
      scheduler := st.scheduler.setRunQueueOnCore c
        (((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
          (createIdleThread c).priority) }

/-- WS-SM SM5.E.3: the idle-enqueue's object-store write (definitional). -/
theorem enqueueIdleThreadOnCore_objects (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).objects =
      st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (createIdleThread c)) := rfl

/-- WS-SM SM5.E.3: the idle-enqueue's scheduler write (definitional).  The
run-queue write is `remove`-then-`insert` so a *re-enqueue* of an already-resident
idle thread refreshes its priority bucket to `0` rather than leaving a stale
bucket (`RunQueue.insert` is an identity for existing members). -/
theorem enqueueIdleThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler =
      st.scheduler.setRunQueueOnCore c
        (((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
          (createIdleThread c).priority) := rfl

/-- WS-SM SM5.E.3: after the enqueue, core `c`'s run queue is the old one with
the idle thread inserted. -/
theorem enqueueIdleThreadOnCore_runQueueOnCore_self (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c =
      ((st.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert (idleThreadId c)
        (createIdleThread c).priority := by
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
-- §3  Membership, resolution, and invariant preservation
-- ============================================================================

/-- WS-SM SM5.E.3 (membership): after the enqueue, core `c`'s idle thread is a
member of core `c`'s run queue.  The substantive "the idle thread is genuinely
available as a fallback" content. -/
theorem enqueueIdleThreadOnCore_mem_runQueueOnCore_self (st : SystemState) (c : CoreId) :
    idleThreadId c ∈ ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c).toList := by
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self, RunQueue.mem_toList_iff_mem]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- WS-SM SM5.E.3 (resolution): after the enqueue, core `c`'s idle thread
resolves to the idle TCB in the object store.  Requires the object-store
invariant so the insert lookup is exact. -/
theorem enqueueIdleThreadOnCore_getTcb?_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (enqueueIdleThreadOnCore st c).getTcb? (idleThreadId c) = some (createIdleThread c) := by
  simp only [enqueueIdleThreadOnCore, SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact RHTable_get?_insert_self st.objects (idleThreadId c).toObjId _ hInv

/-- WS-SM SM5.E.3 (frame): the enqueue leaves every *other* thread's TCB
resolution unchanged — its only object-store write is at the idle thread's key.
AK7-clean (routes through the typed `getTcb?` accessor + the `.get?`-method form
of `RHTable.getElem?_insert_ne`). -/
theorem enqueueIdleThreadOnCore_getTcb?_ne (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c) :
    (enqueueIdleThreadOnCore st c).getTcb? other = st.getTcb? other := by
  have hNeO : ¬ ((idleThreadId c).toObjId == other.toObjId) = true := fun he =>
    hNe (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
  simp only [enqueueIdleThreadOnCore, SystemState.getTcb?, RHTable_getElem?_eq_get?]
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

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves the per-core
"every runnable thread resolves to a TCB" invariant.  The new run-queue member
set is the old one plus the idle thread; the idle thread resolves (it is freshly
inserted), and every old member's resolution is framed unchanged (it lives at a
distinct object-store key, or — for a pre-existing idle slot — is overwritten
with the idle TCB, which still resolves).  So enqueuing the idle thread can
never create a runnable-but-unresolvable entry. -/
theorem enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (enqueueIdleThreadOnCore st c) c := by
  intro tid htid
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self, RunQueue.mem_toList_iff_mem,
    RunQueue.mem_insert] at htid
  by_cases hEq : tid = idleThreadId c
  · subst hEq
    exact ⟨createIdleThread c, enqueueIdleThreadOnCore_getTcb?_self st c hInv⟩
  · -- `remove`-then-`insert`: a non-idle member came from the pre-remove queue.
    have hMemOld : tid ∈ st.scheduler.runQueueOnCore c :=
      ((RunQueue.mem_remove _ _ _).mp (htid.resolve_right hEq)).1
    obtain ⟨tcb, htcb⟩ := hRunnable tid ((RunQueue.mem_toList_iff_mem _ _).mpr hMemOld)
    exact ⟨tcb, by rw [enqueueIdleThreadOnCore_getTcb?_ne st c tid hInv hEq]; exact htcb⟩

-- ============================================================================
-- §3b  Per-core scheduler-invariant preservation (SM5.I consumption surface)
-- ============================================================================
--
-- The structural per-core invariants the SM5.I dispatch loop threads through an
-- idle enqueue.  `currentThreadValidOnCore` is preserved **unconditionally** (the
-- idle thread always resolves after the enqueue).  `queueCurrentConsistentOnCore`
-- and `currentThreadInActiveDomainOnCore` are preserved under the realistic
-- precondition that the idle thread is **not already the running thread** on core
-- `c` (`currentOnCore c ≠ some (idleThreadId c)`) — enqueuing a thread that is
-- currently running would put it both current *and* in the run queue, breaking
-- dequeue-on-dispatch.  This is the precondition SM5.E.3's consumers must honour;
-- it holds whenever idle is installed as a run-queue *fallback* (not as current).

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves core `c`'s
current-thread validity **unconditionally** — the idle thread always resolves to
a TCB after the enqueue (whether or not the current thread happens to be it), and
every other thread's resolution is framed.  Requires the object-store invariant
(for the insert-lookup exactness). -/
theorem enqueueIdleThreadOnCore_preserves_currentThreadValidOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hVal : currentThreadValidOnCore st c) :
    currentThreadValidOnCore (enqueueIdleThreadOnCore st c) c := by
  unfold currentThreadValidOnCore at *
  rw [enqueueIdleThreadOnCore_currentOnCore]
  cases hcur : st.scheduler.currentOnCore c with
  | none => trivial
  | some t =>
    rw [hcur] at hVal
    obtain ⟨tcb, htcb⟩ := hVal
    by_cases hEq : t = idleThreadId c
    · subst hEq
      exact ⟨createIdleThread c, enqueueIdleThreadOnCore_getTcb?_self st c hInv⟩
    · exact ⟨tcb, by rw [enqueueIdleThreadOnCore_getTcb?_ne st c t hInv hEq]; exact htcb⟩

/-- WS-SM SM5.E.3 (preservation, the soundness-critical one): the enqueue
preserves dequeue-on-dispatch consistency **provided the idle thread is not the
running thread** on core `c`.  Without that precondition the property genuinely
fails — enqueuing the *current* idle thread would make it both current and a
run-queue member.  This is the precondition the SM5.E.3 docstring records and
that SM5.I's dispatch loop honours (idle is enqueued as a fallback, never while
it is the running thread). -/
theorem enqueueIdleThreadOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (hNotCur : st.scheduler.currentOnCore c ≠ some (idleThreadId c))
    (hQC : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (enqueueIdleThreadOnCore st c).scheduler c := by
  unfold queueCurrentConsistentOnCore at *
  rw [enqueueIdleThreadOnCore_currentOnCore]
  cases hcur : st.scheduler.currentOnCore c with
  | none => trivial
  | some t =>
    rw [hcur] at hQC hNotCur
    simp only [enqueueIdleThreadOnCore_runQueueOnCore_self, RunQueue.mem_toList_iff_mem,
      RunQueue.mem_insert, not_or] at hQC ⊢
    -- `remove`-then-`insert`: the goal's non-idle disjunct is membership in the
    -- pre-remove queue, which `mem_remove` reduces to the original `t ∉ rq`.
    exact ⟨fun hmem => hQC ((RunQueue.mem_remove _ _ _).mp hmem).1,
           fun hEqIdle => hNotCur (congrArg some hEqIdle)⟩

/-- WS-SM SM5.E.3 (preservation): the enqueue preserves current-in-active-domain
under the same not-the-running-idle precondition — when `current ≠ idle`, the
current thread's TCB resolution (and core `c`'s active domain) are framed, so the
domain match is unchanged. -/
theorem enqueueIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c ≠ some (idleThreadId c))
    (hDom : currentThreadInActiveDomainOnCore st c) :
    currentThreadInActiveDomainOnCore (enqueueIdleThreadOnCore st c) c := by
  unfold currentThreadInActiveDomainOnCore at *
  rw [enqueueIdleThreadOnCore_currentOnCore, enqueueIdleThreadOnCore_activeDomainOnCore]
  cases hcur : st.scheduler.currentOnCore c with
  | none => trivial
  | some t =>
    rw [hcur] at hDom hNotCur
    have hNe : t ≠ idleThreadId c := fun heq => hNotCur (congrArg some heq)
    simp only [enqueueIdleThreadOnCore_getTcb?_ne st c t hInv hNe]
    exact hDom

/-- WS-SM SM5.E.3 (idempotency): the run-queue membership effect of enqueuing the
idle thread is idempotent — after one enqueue the idle thread is already a member,
and `RunQueue.insert`'s internal `contains` guard makes a second enqueue add no
duplicate.  So a dispatch loop may call it repeatedly without growing the queue. -/
theorem enqueueIdleThreadOnCore_mem_idempotent (st : SystemState) (c : CoreId) :
    idleThreadId c ∈
      ((enqueueIdleThreadOnCore (enqueueIdleThreadOnCore st c) c).scheduler.runQueueOnCore c).toList := by
  exact enqueueIdleThreadOnCore_mem_runQueueOnCore_self (enqueueIdleThreadOnCore st c) c

-- ============================================================================
-- §4  `chooseThreadOnCore_always_succeeds` (SM5.E.6)
-- ============================================================================

/-- WS-SM SM5.E.6 (plan §3.5.2): the SM5.E discharge predicate — core `c`'s
idle thread is *available as an in-domain run-queue candidate*.

Three conjuncts (the exact hypotheses `chooseThreadOnCore_some_of_eligible`
needs to commit to a `some` selection): (1) `idleThreadId c` is a member of core
`c`'s run queue; (2) it resolves to the idle TCB in the object store; (3) the
idle thread's domain (`⟨0⟩`) equals core `c`'s active domain.  Conjunct (3) is
exactly the RPi5 v1.0.0 single-domain condition (`activeDomainOnCore c = ⟨0⟩`,
which holds when `domainSchedule = []`); a multi-domain port would install one
idle thread per (core, domain) to keep idle in-domain in every domain — out of
v1.0.0 scope. -/
def idleThreadEnqueuedOnCore (st : SystemState) (c : CoreId) : Prop :=
  idleThreadId c ∈ (st.scheduler.runQueueOnCore c).toList ∧
  st.getTcb? (idleThreadId c) = some (createIdleThread c) ∧
  (createIdleThread c).domain = st.scheduler.activeDomainOnCore c

/-- WS-SM SM5.E.6 (non-vacuity, the constructive discharge): on any state whose
core `c` is in the boot active domain (`activeDomainOnCore c = ⟨0⟩`) and whose
object store is well-formed, `enqueueIdleThreadOnCore` *establishes*
`idleThreadEnqueuedOnCore`.  So the discharge predicate is genuinely satisfiable
by a real operation — `chooseThreadOnCore_always_succeeds` is not vacuous. -/
theorem enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt)
    (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    idleThreadEnqueuedOnCore (enqueueIdleThreadOnCore st c) c := by
  refine ⟨enqueueIdleThreadOnCore_mem_runQueueOnCore_self st c,
          enqueueIdleThreadOnCore_getTcb?_self st c hInv, ?_⟩
  rw [createIdleThread_domain_zero, enqueueIdleThreadOnCore_activeDomainOnCore, hDom]

/-- WS-SM SM5.E.6 (plan §3.5.2, Theorem `chooseThreadOnCore_always_succeeds`):
when core `c`'s idle thread is enqueued and in its active domain, the per-core
selection returns `some` — the scheduler never spuriously idles a core that has
at least its idle thread available.

This is the plan's "idle is always a fallback, so selection succeeds" result.
It discharges the conditional SM5.A `chooseThreadOnCore_some_of_eligible` by
supplying the **idle thread** as the always-present in-domain runnable
candidate.  The "always" is over user-thread availability: even with *no*
runnable user thread, idle is selected.  (The hypothesis `idleThreadEnqueuedOnCore`
— idle actually being a run-queue member — is the SM5.E discharge condition,
established constructively by `enqueueIdleThreadOnCore`.) -/
theorem chooseThreadOnCore_always_succeeds (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hIdle : idleThreadEnqueuedOnCore st c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  chooseThreadOnCore_some_of_eligible st c hwf hRunnable
    (idleThreadId c) (createIdleThread c) hIdle.1 hIdle.2.1 hIdle.2.2

/-- WS-SM SM5.E.6 (non-vacuity, end-to-end): for any well-formed boot-domain
state (object-store invariant, well-formed run queue, runnable-are-TCBs, active
domain `⟨0⟩`), enqueuing core `c`'s idle thread makes `chooseThreadOnCore`
succeed.  Composes the SM5.E.3 preservation lemmas with the keystone — the
constructive witness that `chooseThreadOnCore_always_succeeds` is satisfiable
(e.g. on the default state, or any boot-derived state). -/
theorem enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    ∃ tid, chooseThreadOnCore (enqueueIdleThreadOnCore st c) c = .ok (some tid) :=
  chooseThreadOnCore_always_succeeds (enqueueIdleThreadOnCore st c) c
    (enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed st c hwf)
    (enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore st c hInv hRunnable)
    (enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore st c hInv hDom)

-- ============================================================================
-- §5  `idleThread_core_locality` (SM5.E.4)
-- ============================================================================

/-- WS-SM SM5.E.4: core `c`'s run queue is *affinity-consistent* — every thread
it holds resolves to a TCB admitted on core `c` (`affinityAdmitsCore`).  This is
the run-queue↔affinity coherence that per-core scheduling under affinity-bound
threads maintains (a thread is enqueued only on a core it is admitted on); the
full per-core invariant lands at SM5.H/SM5.I.  `idleThread_core_locality`
consumes it to rule core `c`'s idle thread out of any *other* core's queue. -/
def runQueueAffinityConsistentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
    st.getTcb? tid = some tcb → affinityAdmitsCore tcb c = true

/-- WS-SM SM5.E.4 (plan §3.5, Theorem `idleThread_core_locality`): core `c`'s
idle thread never appears on a *different* core `c' ≠ c`'s run queue.

The proof is the substantive content of the SM5.E.2 `cpuAffinity := some c`
binding: were idle `c` on core `c'`'s affinity-consistent queue, it would be
admitted on `c'` (`hAff`); but idle `c` is pinned to `some c`
(`createIdleThread_cpuAffinity`), so `affinityAdmitsCore (createIdleThread c) c'
= (c == c')`, forcing `c = c'` — contradicting `c ≠ c'`.

The hypothesis `hIdleTcb` (core `c`'s idle slot holds the idle TCB, so we know
its affinity) holds wherever idle threads are installed (after
`enqueueIdleThreadOnCore c` / `bootFromPlatformWithIdleThreads`). -/
theorem idleThread_core_locality (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hIdleTcb : st.getTcb? (idleThreadId c) = some (createIdleThread c))
    (hAff : runQueueAffinityConsistentOnCore st c') :
    idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList := by
  intro hMem
  have hAdmit : affinityAdmitsCore (createIdleThread c) c' = true :=
    hAff (idleThreadId c) hMem (createIdleThread c) hIdleTcb
  rw [affinityAdmitsCore_some (createIdleThread c) c' c (createIdleThread_cpuAffinity c)] at hAdmit
  exact h (beq_iff_eq.mp hAdmit)

/-- WS-SM SM5.E.4 (operational companion): enqueuing core `c`'s idle thread onto
core `c` does not leak it onto a *different* core `c' ≠ c`'s run queue — if it
was absent from `c'`'s queue before, it stays absent.  The frame-based half of
locality (unconditional; does not need affinity consistency). -/
theorem idleThread_core_locality_of_enqueue (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hAbsent : idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList) :
    idleThreadId c ∉ ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c').toList := by
  rw [enqueueIdleThreadOnCore_runQueueOnCore_ne st c c' h]
  exact hAbsent

/-- WS-SM SM5.E.4 (affinity-consistency preservation, connecting the locality
hypothesis to a maintained property): enqueuing core `c`'s idle thread preserves
`runQueueAffinityConsistentOnCore` on core `c` — the new member (idle,
`cpuAffinity = some c`) is admitted on `c`
(`affinityAdmitsCore (createIdleThread c) c = (c == c) = true`), and every old
member's resolution + affinity is framed.  So the affinity-consistency that
`idleThread_core_locality` consumes on a *different* core is *established* on the
enqueue's own core, not merely assumed — connecting the locality hypothesis to a
reachable state.  (Cross-core preservation additionally requires
`idleThread_core_locality`'s own conclusion — idle `c ∉` core `c'`'s queue — so
the natural carrier is the per-core fold, not a standalone `c' ≠ c` lemma.) -/
theorem enqueueIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self
    (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hAff : runQueueAffinityConsistentOnCore st c) :
    runQueueAffinityConsistentOnCore (enqueueIdleThreadOnCore st c) c := by
  intro tid htid tcb htcb
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self, RunQueue.mem_toList_iff_mem,
    RunQueue.mem_insert] at htid
  by_cases hEq : tid = idleThreadId c
  · subst hEq
    rw [enqueueIdleThreadOnCore_getTcb?_self st c hInv] at htcb
    cases htcb
    simp [affinityAdmitsCore, createIdleThread_cpuAffinity]
  · have hMemOld : tid ∈ st.scheduler.runQueueOnCore c :=
      ((RunQueue.mem_remove _ _ _).mp (htid.resolve_right hEq)).1
    rw [enqueueIdleThreadOnCore_getTcb?_ne st c tid hInv hEq] at htcb
    exact hAff tid ((RunQueue.mem_toList_iff_mem _ _).mpr hMemOld) tcb htcb

/-- WS-SM SM5.E.4 (`∀ c` aggregate, plan §3.5 form): core `c`'s idle thread is
absent from *every other* core's run queue, simultaneously — the SMP locality
statement.  Each core's queue is affinity-consistent (`hAff`), and each core's
idle slot holds its idle TCB (`hIdle`). -/
theorem idleThread_core_locality_forall (st : SystemState)
    (hIdle : ∀ c, st.getTcb? (idleThreadId c) = some (createIdleThread c))
    (hAff : ∀ c, runQueueAffinityConsistentOnCore st c) :
    ∀ c c', c ≠ c' → idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList :=
  fun c c' h => idleThread_core_locality st c c' h (hIdle c) (hAff c')

-- ============================================================================
-- §6  Lock-set footprint (`enqueueIdleThreadOnCoreLockSet`, SM5.A–D parity)
-- ============================================================================

/-- WS-SM SM5.E.3 (plan §4.4): the cross-domain lock-set footprint of
`enqueueIdleThreadOnCore` — it WRITES the object store (the idle TCB insert) and
core `c`'s run queue (the idle insert), so both are **write** locks over SM5.A's
unified `SchedLockId` (object-store table lock before run-queue lock, the §4.4
ascending order).  Mirrors SM5.C's `wakeThreadLockSet`. -/
def enqueueIdleThreadOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨c⟩, .write) ]

@[simp] theorem enqueueIdleThreadOnCoreLockSet_length (c : CoreId) :
    (enqueueIdleThreadOnCoreLockSet c).length = 2 := rfl

/-- WS-SM SM5.E.3: every lock in the idle-enqueue footprint is **write** mode. -/
theorem enqueueIdleThreadOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ enqueueIdleThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [enqueueIdleThreadOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- WS-SM SM5.E.3: the object-store write lock is in the idle-enqueue footprint
(it guards the idle TCB insert). -/
theorem enqueueIdleThreadOnCoreLockSet_contains_objStore_write (c : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ enqueueIdleThreadOnCoreLockSet c := by
  simp [enqueueIdleThreadOnCoreLockSet]

/-- WS-SM SM5.E.3: core `c`'s run-queue write lock is in the idle-enqueue
footprint (it guards the idle insert). -/
theorem enqueueIdleThreadOnCoreLockSet_contains_runQueue_write (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ enqueueIdleThreadOnCoreLockSet c := by
  simp [enqueueIdleThreadOnCoreLockSet]

/-- WS-SM SM5.E.3 (plan §4.4): the object-store lock is acquired *before* the
run-queue lock — the cross-domain ascending order. -/
theorem enqueueIdleThreadOnCoreLockSet_object_before_runQueue (c : CoreId) :
    SchedLockId.object schedObjStoreLockId
      < SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
  SchedLockId.object_lt_runQueue _ _

/-- WS-SM SM5.E.3: the idle-enqueue footprint's projected keys are
duplicate-free. -/
theorem enqueueIdleThreadOnCoreLockSet_keys_nodup (c : CoreId) :
    ((enqueueIdleThreadOnCoreLockSet c).map (·.1)).Nodup := by
  simp [enqueueIdleThreadOnCoreLockSet]

/-- WS-SM SM5.E.3 (plan §4.4): the footprint's keys form a `SchedLockId`-ascending
acquisition sequence (`Pairwise (· ≤ ·)`), so the canonical `withLockSet`
acquisition is the list itself — the idle-enqueue's contribution to the SM3.D
deadlock-freedom ladder. -/
theorem enqueueIdleThreadOnCoreLockSet_pairwise_le (c : CoreId) :
    ((enqueueIdleThreadOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  have hle : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
    (SchedLockId.object_lt_runQueue _ _).1
  simp only [enqueueIdleThreadOnCoreLockSet, List.map_cons, List.map_nil]
  exact List.Pairwise.cons
    (fun a ha => by rcases List.mem_singleton.mp ha with rfl; exact hle)
    (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil)

-- ============================================================================
-- §7  No-starvation (idle never displaces a higher-priority thread)
-- ============================================================================

/-- WS-SM SM5.E.5 (no-starvation, the general theorem behind `idleThread_priority_zero`):
the idle thread is selected only when it is **not outranked** in core `c`'s
maximum-priority bucket — i.e. no in-domain runnable thread in the top bucket is a
better candidate (`isBetterCandidate`) than idle.  Since idle is priority `⟨0⟩`,
this means a runnable in-domain thread of higher priority is always preferred:
idle never starves a higher-priority thread.  An instantiation of the SM5.A
selection-optimality theorem `chooseThreadOnCore_selects_highest` with the idle
thread as the selected candidate. -/
theorem idleThread_no_starvation (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hr : runnableThreadsAreTCBsOnCore st c)
    (hSel : chooseThreadOnCore st c = .ok (some (idleThreadId c)))
    (hIdleTcb : st.getTcb? (idleThreadId c) = some (createIdleThread c)) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket, ∀ tcb : TCB,
      st.getTcb? t = some tcb → tcb.domain = st.scheduler.activeDomainOnCore c →
        isBetterCandidate (createIdleThread c).priority (createIdleThread c).deadline
          tcb.priority tcb.deadline = false :=
  chooseThreadOnCore_selects_highest st c (idleThreadId c) (createIdleThread c) hwf hr hSel hIdleTcb

-- ============================================================================
-- §8  Decidable companion + cross-core selection independence
-- ============================================================================

/-- WS-SM SM5.E.6 (decidable companion to `idleThreadEnqueuedOnCore`): a `Bool`
predicate testing whether core `c`'s idle thread is an *available in-domain
candidate* — it is a run-queue member, it resolves to a TCB, and that TCB's
domain matches core `c`'s active domain.  Unlike `idleThreadEnqueuedOnCore` (whose
`getTcb? = some (createIdleThread c)` conjunct is undecidable because `TCB` has no
`DecidableEq`), this checks only the *domain* of the resolved idle TCB, so it is
decidable and concrete states can `decide` it.  It is the form the
selection-success theorem actually needs (the selected-thread identity does not
require pinning the full idle TCB). -/
def idleAvailableOnCoreB (st : SystemState) (c : CoreId) : Bool :=
  (st.scheduler.runQueueOnCore c).contains (idleThreadId c) &&
  (match st.getTcb? (idleThreadId c) with
   | some tcb => tcb.domain == st.scheduler.activeDomainOnCore c
   | none => false)

/-- WS-SM SM5.E.6 (the decidable always-succeeds): when the decidable
`idleAvailableOnCoreB` holds (idle is an in-domain run-queue candidate), the
per-core selection returns `some`.  Discharges `chooseThreadOnCore_some_of_eligible`
with the *resolved* idle TCB (whatever it is) rather than `createIdleThread c`, so
it needs no undecidable full-TCB equality. -/
theorem chooseThreadOnCore_always_succeeds_of_idleAvailableB (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hB : idleAvailableOnCoreB st c = true) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) := by
  unfold idleAvailableOnCoreB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨hMemB, hDomB⟩ := hB
  have hMem : idleThreadId c ∈ (st.scheduler.runQueueOnCore c).toList :=
    (RunQueue.mem_toList_iff_mem _ _).mpr (by rwa [RunQueue.mem_iff_contains])
  cases hres : st.getTcb? (idleThreadId c) with
  | none => rw [hres] at hDomB; exact absurd hDomB (by simp)
  | some idleTcb =>
      rw [hres] at hDomB
      exact chooseThreadOnCore_some_of_eligible st c hwf hRunnable
        (idleThreadId c) idleTcb hMem hres (by simpa using hDomB)

/-- WS-SM SM5.E.6: the `Prop` discharge predicate `idleThreadEnqueuedOnCore`
implies its decidable companion `idleAvailableOnCoreB` — so any state satisfying
the (stronger, exact-TCB) `Prop` form can be `decide`d through the `Bool`
companion. -/
theorem idleThreadEnqueuedOnCore_idleAvailableOnCoreB (st : SystemState) (c : CoreId)
    (h : idleThreadEnqueuedOnCore st c) : idleAvailableOnCoreB st c = true := by
  obtain ⟨hMem, hTcb, hDom⟩ := h
  unfold idleAvailableOnCoreB
  rw [Bool.and_eq_true]
  refine ⟨by rw [← RunQueue.mem_iff_contains]; exact (RunQueue.mem_toList_iff_mem _ _).mp hMem, ?_⟩
  rw [hTcb]
  exact beq_iff_eq.mpr hDom

/-- WS-SM SM5.E (cross-core selection-frame, honest scope): enqueuing core `c`'s
idle thread leaves a *different* core `c'`'s run queue and active domain — the
two per-core inputs to `chooseThreadOnCore c'` — **unchanged**.  The remaining
input is the shared object store, into which the enqueue writes core `c`'s idle
TCB; by `idleThread_core_locality` that key is never a member of core `c'`'s run
queue, so the write is invisible to `c'`'s selection.  Promoting this to a full
selection *equality* (`chooseThreadOnCore (enqueue …) c' = chooseThreadOnCore … c'`)
needs a `chooseBestInBucket` object-lookup congruence restricted to the run-queue
members (chooseThreadOnCore reads the global object store); that finer frame
lemma is the SM5.A selection layer's to provide and is tracked for SM5.I. -/
theorem enqueueIdleThreadOnCore_selection_inputs_framed
    (st : SystemState) (c c' : CoreId) (h : c ≠ c') :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c' ∧
    (enqueueIdleThreadOnCore st c).scheduler.activeDomainOnCore c'
        = st.scheduler.activeDomainOnCore c' :=
  ⟨enqueueIdleThreadOnCore_runQueueOnCore_ne st c c' h,
   enqueueIdleThreadOnCore_activeDomainOnCore st c c'⟩

end SeLe4n.Kernel
