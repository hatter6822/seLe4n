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
open SeLe4n.Platform.Boot (idleThreadId createIdleThread idleThreadIdBase idleThreadId_ne
  idleThreadId_toObjId_ne)

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
(b) inserts `idleThreadId c` into core `c`'s run queue at the idle priority
`⟨0⟩` (`= (createIdleThread c).priority`, which equals its effective run-queue
priority since idle carries no PIP boost).

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
        ((st.scheduler.runQueueOnCore c).insert (idleThreadId c)
          (createIdleThread c).priority) }

/-- WS-SM SM5.E.3: the idle-enqueue's object-store write (definitional). -/
theorem enqueueIdleThreadOnCore_objects (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).objects =
      st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (createIdleThread c)) := rfl

/-- WS-SM SM5.E.3: the idle-enqueue's scheduler write (definitional). -/
theorem enqueueIdleThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler =
      st.scheduler.setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insert (idleThreadId c)
          (createIdleThread c).priority) := rfl

/-- WS-SM SM5.E.3: after the enqueue, core `c`'s run queue is the old one with
the idle thread inserted. -/
theorem enqueueIdleThreadOnCore_runQueueOnCore_self (st : SystemState) (c : CoreId) :
    (enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c =
      (st.scheduler.runQueueOnCore c).insert (idleThreadId c) (createIdleThread c).priority := by
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
  exact RunQueue.insert_preserves_wellFormed _ hwf _ _

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
  · have hMemOld : tid ∈ st.scheduler.runQueueOnCore c := htid.resolve_right hEq
    obtain ⟨tcb, htcb⟩ := hRunnable tid ((RunQueue.mem_toList_iff_mem _ _).mpr hMemOld)
    exact ⟨tcb, by rw [enqueueIdleThreadOnCore_getTcb?_ne st c tid hInv hEq]; exact htcb⟩

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

end SeLe4n.Kernel
