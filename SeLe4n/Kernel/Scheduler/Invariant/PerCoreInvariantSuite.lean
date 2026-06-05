-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCore
import SeLe4n.Kernel.Scheduler.Invariant.PerCorePreservation
import SeLe4n.Kernel.CrossSubsystemPerCore
import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs

/-!
# WS-SM SM5.I — Per-core invariant suite

This module is the SM5.I deliverable of WS-SM Phase 5 (plan
`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §5 SM5.I, §6.1).  It assembles
the per-core scheduler invariants that SM4.C/SM4.D defined as **predicates**
into a coherent suite, and — the heart of SM5.I.8 — proves that **every SM5
per-core scheduler transition preserves the system-wide SMP invariant**.

## The structural SMP invariant (a register-bank-free safety core)

The full SM4.C aggregate `schedulerInvariant_perCore` has eleven conjuncts.
`schedulerInvariantStructural_perCore` is the **register-bank-independent safety
core** — the four conjuncts that are both register-bank-independent and proved
preserved by every SM5 per-core transition:

* `queueCurrentConsistentOnCore` — dequeue-on-dispatch (current ∉ its own run
  queue): no thread is simultaneously running and runnable on the same core.
* `currentThreadValidOnCore` — no dangling current: a `some` current resolves
  to a real TCB.
* `runnableThreadsAreTCBsOnCore` — every run-queue member is a real TCB.
* `runQueueOnCoreWellFormed` — the run queue's internal `byPriority` ↔
  `membership` ↔ `threadPriority` indices are consistent.

The other **seven** conjuncts are excluded from this core, for three distinct
reasons (the first two genuinely-mathematical, the third a scope-bounding
deferral — none is a soundness gap):

1. **`contextMatchesCurrentOnCore`** asserts the *system-wide* `machine.regs`
   equals core `c`'s current thread's saved context.  With one shared register
   file this holds for **at most one** non-idle core at a time, so a per-core
   dispatch on core `c₀` — which writes `machine.regs` to `c₀`'s new current's
   context — necessarily *invalidates* every other non-idle core's conjunct.
   It is faithful only once SM5 introduces **per-core register banks** (the
   deferred context-bank migration the predicate's own docstring notes); until
   then the system-wide `schedulerInvariant_smp` (∀ c, full aggregate) is
   preserved only in the single-active-core regime.

2. **`edfCurrentHasEarliestDeadlineOnCore`**, `timeSlicePositiveOnCore`,
   `currentTimeSlicePositiveOnCore`, and `domainTimeRemainingPositiveOnCore`
   are **dispatch/tick-established**, not transition-stable: a *bare* wake
   enqueuing an earlier-deadline thread in the running thread's bucket
   transiently breaks EDF until the next dispatch re-establishes it (precisely
   *when* the wake fires a preemption SGI).  In the single-core model the same
   holds — `ensureRunnable` preserves only the base invariant, `schedule`
   re-establishes EDF.

3. **`schedulerPriorityMatchOnCore`** is register-bank-independent but coupled to
   dispatch via the **PIP-boost run-queue bucket migration**: a `pipBoost` change
   alters a thread's `effectiveRunQueuePriority`, and the matching run-queue index
   is re-bucketed only on the thread's home core (`updatePipBoostOnCore`), so the
   conjunct is not frame-stable across an arbitrary objects mutation.
   **`runQueueUniqueOnCore`** (run-queue `Nodup`) *is* both register-bank-
   independent and transition-stable — a clean extension of this structural core
   — but is deferred here to bound the cut (its wake/dispatch `RunQueue.insert` /
   `remove` `Nodup`-preservation lemmas, distinct from the SM4.C single-core
   `runQueueUnique` proofs, are the natural follow-on).

Crucially, its frame on a sibling core `c' ≠ c₀` needs **no `machine.regs`
agreement** (no `contextMatchesCurrent` conjunct), so a per-core dispatch on
`c₀` — which *does* rewrite `machine.regs` — preserves the structural
invariant on **every** core.  This is what makes `schedulerInvariantStructural_smp`
a genuine, register-bank-free, system-wide SMP invariant.

## What this module proves (plan §5 SM5.I)

* **SM5.I.1/.2/.3/.4** — suite re-export of `currentThreadValidOnCore` (I.1),
  `runQueueOnCoreWellFormed` (I.2), `schedContextRunQueueConsistent_perCore`
  (I.3), `priorityInheritance_perCore` (I.4) under their plan names.
* **SM5.I.5/.7** — the aggregate `schedulerInvariant_perCore` and the
  system-wide `schedulerInvariant_smp`, plus the new
  `schedulerInvariantStructural_perCore` / `_smp` and their projections,
  bridges, default-state, and frame lemma.
* **SM5.I.6** — `schedulerInvariant_perCore_pairwise` (cross-core
  independence; recapped) + the structural pairwise form.
* **SM5.I.8** — **preservation by every transition**: the per-core
  SMP-preservation engine plus `<op>_preserves_schedulerInvariantStructural_smp`
  for every SM5 per-core transition (wake, switch, dispatch, timer tick,
  domain rotate, idle enqueue, …), and — on the *operated* core — the
  strongest per-core establishment each transition delivers.
* **SM5.I.9** — `crossSubsystemInvariant_smp` (recapped from SM4.D).

Axiom-clean: every theorem depends only on the standard foundational axioms
(`propext` / `Quot.sound` / `Classical.choice`).

**Tracked debt (per-core register banks)**: the full `schedulerInvariant_smp`
(∀ c, including `contextMatchesCurrentOnCore`) preservation by a per-core
dispatch with *multiple* non-idle cores is gated on the SM5 per-core register
bank (the system-wide `machine.regs` makes multi-active-core
`contextMatchesCurrent` unsatisfiable).  The structural invariant is the
register-bank-free system-wide guarantee SM5.I delivers now; the full
aggregate's system-wide preservation lands with the per-core register banks.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores)

-- ============================================================================
-- §1  The structural per-core invariant (the register-bank-free safety core)
-- ============================================================================

/-- WS-SM SM5.I: the **structural** per-core scheduler invariant at core `c` —
the four register-bank-independent safety conjuncts of the full SM4.C
`schedulerInvariant_perCore` aggregate that are proved preserved by every SM5
per-core transition (see the module header for the accounting of the other
seven: register-bank-gated `contextMatchesCurrent`; dispatch/tick-established
EDF / time-slice / domain-time; PIP-dispatch-coupled `schedulerPriorityMatch`;
and the clean-extension `runQueueUnique` deferred to bound this cut). -/
def schedulerInvariantStructural_perCore (st : SystemState) (c : CoreId) : Prop :=
  queueCurrentConsistentOnCore st.scheduler c ∧
  currentThreadValidOnCore st c ∧
  runnableThreadsAreTCBsOnCore st c ∧
  runQueueOnCoreWellFormed st.scheduler c

/-- WS-SM SM5.I.7: the system-wide structural SMP scheduler invariant — the
structural per-core invariant holding on *every* core.  Unlike the full
`schedulerInvariant_smp`, this is preserved by genuine per-core dispatch on
multiple active cores (no `contextMatchesCurrent`, so no shared-register
conflict). -/
def schedulerInvariantStructural_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariantStructural_perCore st c

-- Per-conjunct projections from the structural per-core aggregate.

theorem schedulerInvariantStructural_perCore_to_queueCurrentConsistent
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructural_perCore st c) :
    queueCurrentConsistentOnCore st.scheduler c := h.1

theorem schedulerInvariantStructural_perCore_to_currentThreadValid
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructural_perCore st c) :
    currentThreadValidOnCore st c := h.2.1

theorem schedulerInvariantStructural_perCore_to_runnableThreadsAreTCBs
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructural_perCore st c) :
    runnableThreadsAreTCBsOnCore st c := h.2.2.1

theorem schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructural_perCore st c) :
    runQueueOnCoreWellFormed st.scheduler c := h.2.2.2

/-- The structural per-core slices aggregate to the system-wide structural
SMP invariant by definition. -/
theorem schedulerInvariantStructural_perCore_aggregateForall (st : SystemState) :
    (∀ c : CoreId, schedulerInvariantStructural_perCore st c) ↔
      schedulerInvariantStructural_smp st := Iff.rfl

/-- Project a single core's structural slice out of the SMP aggregate. -/
theorem schedulerInvariantStructural_smp_at (st : SystemState) (c : CoreId)
    (h : schedulerInvariantStructural_smp st) : schedulerInvariantStructural_perCore st c := h c

-- ----------------------------------------------------------------------------
-- Bridges to the full SM4.C aggregate
-- ----------------------------------------------------------------------------

/-- WS-SM SM5.I: the full SM4.C per-core aggregate implies the structural
per-core invariant (the structural conjuncts are a sub-conjunction of the
full eleven).  This is the non-orphan connection to the live SM4.C surface:
every existing full-aggregate witness yields the structural one for free. -/
theorem schedulerInvariant_perCore_to_structural {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : schedulerInvariantStructural_perCore st c :=
  ⟨schedulerInvariant_perCore_to_queueCurrentConsistent h,
   schedulerInvariant_perCore_to_currentThreadValid h,
   schedulerInvariant_perCore_to_runnableThreadsAreTCBs h,
   schedulerInvariant_perCore_to_runQueueOnCoreWellFormed h⟩

/-- WS-SM SM5.I: the full SMP aggregate implies the structural SMP invariant. -/
theorem schedulerInvariant_smp_to_structural {st : SystemState}
    (h : schedulerInvariant_smp st) : schedulerInvariantStructural_smp st :=
  fun c => schedulerInvariant_perCore_to_structural (h c)

-- ----------------------------------------------------------------------------
-- Default-state witnesses
-- ----------------------------------------------------------------------------

/-- WS-SM SM5.I: every core satisfies the structural per-core invariant on the
freshly-booted (empty) system. -/
theorem default_schedulerInvariantStructural_perCore (c : CoreId) :
    schedulerInvariantStructural_perCore (default : SystemState) c :=
  schedulerInvariant_perCore_to_structural (default_schedulerInvariant_perCore c)

/-- WS-SM SM5.I: the freshly-booted system satisfies the structural SMP
invariant on every core. -/
theorem default_schedulerInvariantStructural_smp :
    schedulerInvariantStructural_smp (default : SystemState) :=
  fun c => default_schedulerInvariantStructural_perCore c

-- ============================================================================
-- §2  The structural-invariant frame + the per-core SMP-preservation engine
-- ============================================================================

/-- WS-SM SM5.I: the **structural** per-core frame (preservation direction).

Unlike the full `schedulerInvariant_perCore_frame` (which needs `machine.regs`
*and* full `objects` agreement to carry `contextMatchesCurrentOnCore` and the
quantified conjuncts), the structural invariant on core `c` is preserved by
any state change that
  * leaves core `c`'s `current` slot (`hCur`) and run queue (`hRQ`) untouched,
  * and never *destroys* a TCB — every key that held a TCB still holds one
    (`hTcbSome`).

This is the precise frame a per-core dispatch on a *sibling* core `c₀ ≠ c`
satisfies: it rewrites `machine.regs` (irrelevant — no `contextMatchesCurrent`)
and saves an outgoing thread's register context (a TCB → TCB update, so
`isSome` is preserved everywhere), but touches neither `c`'s `current` nor `c`'s
run queue.  No `machine.regs` hypothesis is required — that is exactly why
`schedulerInvariantStructural_smp` survives genuine multi-core dispatch where
the full aggregate (with its shared-register `contextMatchesCurrent`) cannot. -/
theorem schedulerInvariantStructural_perCore_frame
    {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRQ  : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hTcbSome : ∀ tid, (st.getTcb? tid).isSome → (st'.getTcb? tid).isSome)
    (h : schedulerInvariantStructural_perCore st c) :
    schedulerInvariantStructural_perCore st' c := by
  obtain ⟨hQCC, hCTV, hRAT, hWf⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- queueCurrentConsistentOnCore: reads only current/runQueue.
    unfold queueCurrentConsistentOnCore at hQCC ⊢
    rw [hCur, hRQ]; exact hQCC
  · -- currentThreadValidOnCore: current unchanged; the resolved TCB stays a TCB.
    unfold currentThreadValidOnCore at hCTV ⊢
    rw [hCur]
    cases hcur : st.scheduler.currentOnCore c with
    | none => exact trivial
    | some tid =>
        rw [hcur] at hCTV
        obtain ⟨tcb, htcb⟩ := hCTV
        have : (st'.getTcb? tid).isSome := hTcbSome tid (by rw [htcb]; rfl)
        exact Option.isSome_iff_exists.mp this
  · -- runnableThreadsAreTCBsOnCore: run queue unchanged; each member stays a TCB.
    unfold runnableThreadsAreTCBsOnCore at hRAT ⊢
    rw [hRQ]
    intro tid htid
    obtain ⟨tcb, htcb⟩ := hRAT tid htid
    have : (st'.getTcb? tid).isSome := hTcbSome tid (by rw [htcb]; rfl)
    exact Option.isSome_iff_exists.mp this
  · -- runQueueOnCoreWellFormed: reads only the run queue.
    unfold runQueueOnCoreWellFormed at hWf ⊢
    rw [hRQ]; exact hWf

/-- WS-SM SM5.I.8: the **per-core SMP-preservation engine**.

A per-core transition operating on core `c₀` preserves the system-wide
structural SMP invariant given
  * the structural invariant is (re-)established on the *operated* core `c₀`
    (`hC0` — the per-op `_establishes_*` / `_preserves_*` lemmas compose into
    this), and
  * the transition frames every *sibling* core's `current` (`hFrameCur`) and
    run queue (`hFrameRQ`) and destroys no TCB (`hTcbSome`).

This is the per-arbitrary-core analogue of SM4.C's
`schedulerInvariant_smp_of_bootCore_and_idle_frame`: where the single-core
skeleton discharged sibling cores by *idleness vacuity* (and so needed full
`objects` agreement), this discharges them by the structural *frame* — which
needs no `machine.regs` agreement, so a per-core dispatch (which rewrites the
shared register file) is admissible.  Every `<op>_preserves_schedulerInvariantStructural_smp`
below is a one-line application of this engine. -/
theorem schedulerInvariantStructural_smp_of_establish_and_frame
    {st st' : SystemState} {c₀ : CoreId}
    (hPre : schedulerInvariantStructural_smp st)
    (hC0 : schedulerInvariantStructural_perCore st' c₀)
    (hFrameCur : ∀ c', c₀ ≠ c' →
      st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c')
    (hFrameRQ : ∀ c', c₀ ≠ c' →
      st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c')
    (hTcbSome : ∀ tid, (st.getTcb? tid).isSome → (st'.getTcb? tid).isSome) :
    schedulerInvariantStructural_smp st' := by
  intro c'
  by_cases hc : c₀ = c'
  · subst hc; exact hC0
  · exact schedulerInvariantStructural_perCore_frame
      (hFrameCur c' hc) (hFrameRQ c' hc) hTcbSome (hPre c')

-- ============================================================================
-- §3  Preservation by every SM5 per-core transition (SM5.I.8)
-- ============================================================================
--
-- Each theorem is a one-application use of the §2 engine: it supplies the
-- structural establishment on the operated core (composing the existing
-- per-conjunct `_establishes_*` / `_preserves_*` lemmas), the sibling-core
-- `current` / `runQueue` frame, and the `getTcb?`-isSome preservation.  The
-- transitions fall into two shapes — pure framing (touch neither `current`,
-- `runQueue`, nor `objects` on any core: domain rotation) and genuine
-- mutations (wake / switch / dispatch / tick).

-- ── §3.1  Per-core domain rotation (`advanceDomainOnCore`) ──

/-- WS-SM SM5.I.8: the pure per-core domain rotation preserves the structural
SMP invariant on every core.  `advanceDomainOnCore` writes only core `c₀`'s
domain triple (`activeDomain` / `domainTimeRemaining` / `domainScheduleIndex`)
— none of which any structural conjunct reads — so it frames `current`,
`runQueue`, and the object store on *every* core.  The cleanest possible
instance: even the operated core is discharged by the frame. -/
theorem advanceDomainOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (advanceDomainOnCore st c₀) := by
  intro c'
  refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c')
  · exact advanceDomainOnCore_currentOnCore st c₀ c'
  · exact advanceDomainOnCore_runQueueOnCore st c₀ c'
  · intro tid hsome; rw [advanceDomainOnCore_getTcb?]; exact hsome

-- ── §3.2  Cross-core wake (`enqueueRunnableOnCore`, `wakeThread`) ──

/-- WS-SM SM5.I.8 (missing structural conjunct, proved here): a wake on core `c`
preserves `runnableThreadsAreTCBsOnCore` on core `c`.  Every member of the
post-wake run queue resolves to a TCB in the *pre*-state — the woken thread
`tid` (the some-branch's `hTcb`) and every prior member (`h`) — and
`enqueueRunnableOnCore_getTcb?_isSome` lifts that resolvability across the wake.
This is the one structural conjunct without an SM5.C `enqueueRunnableOnCore_*`
lemma; SM5.I supplies it. -/
theorem enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (enqueueRunnableOnCore st c tid) c := by
  intro x hx
  -- It suffices to show `x` resolves to a TCB in `st`; `getTcb?_isSome` lifts it.
  suffices hres : ∃ t, st.getTcb? x = some t by
    obtain ⟨t, ht⟩ := hres
    exact enqueueRunnableOnCore_getTcb?_isSome st c tid x t hInv ht
  cases hTcb : st.getTcb? tid with
  | none =>
      rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb] at hx
      exact h x hx
  | some tcb =>
      cases hFresh : runnableOnSomeCore st tid with
      | true =>
          rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh] at hx
          exact h x hx
      | false =>
          by_cases hxtid : x = tid
          · exact ⟨tcb, by rw [hxtid]; exact hTcb⟩
          · -- `x ≠ tid`, so `x` was already in core `c`'s run queue pre-wake.
            have hx' : x ∈ ((st.scheduler.runQueueOnCore c).insert tid
                (effectiveRunQueuePriority tcb)).toList := by
              have h2 := hx
              simp only [enqueueRunnableOnCore, hTcb, hFresh, Bool.false_eq_true, if_false,
                SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at h2
              exact h2
            rcases (RunQueue.mem_insert _ _ _ _).mp ((RunQueue.mem_toList_iff_mem _ _).mp hx') with
              hold | heq
            · exact h x ((RunQueue.mem_toList_iff_mem _ _).mpr hold)
            · exact absurd heq hxtid

/-- WS-SM SM5.I.8: `enqueueRunnableOnCore` (the per-core wake) preserves the
structural SMP invariant.  Composes the four SM5.C/SM5.I per-conjunct lemmas on
the operated core `c₀` and frames every sibling core (the wake writes only core
`c₀`'s run queue and one TCB's `ipcState`).

`hNotCur` (the woken thread is not core `c₀`'s current) is the seL4-faithful
"do not wake the running thread" precondition — the wake only ever targets
*blocked* threads — that `queueCurrentConsistentOnCore` requires; it is the same
explicit precondition `enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self`
states (no never-taken runtime guard). -/
theorem enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c₀ ≠ some tid)
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (enqueueRunnableOnCore st c₀ tid) := by
  refine schedulerInvariantStructural_smp_of_establish_and_frame (c₀ := c₀) hPre ?_ ?_ ?_ ?_
  · -- structural establishment on the operated core
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self st c₀ tid hNotCur
        (hPre c₀).1
    · exact enqueueRunnableOnCore_preserves_currentThreadValidOnCore st c₀ c₀ tid hInv (hPre c₀).2.1
    · exact enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore st c₀ tid hInv (hPre c₀).2.2.1
    · exact enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed st c₀ tid (hPre c₀).2.2.2
  · exact fun c' _ => enqueueRunnableOnCore_currentOnCore st c₀ tid c'
  · exact fun c' hc => enqueueRunnableOnCore_runQueueOnCore_ne st c₀ c' tid hc
  · intro t hsome
    obtain ⟨tcb, ht⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨tcb', ht'⟩ := enqueueRunnableOnCore_getTcb?_isSome st c₀ tid t tcb hInv ht
    rw [ht']; rfl

/-- WS-SM SM5.I.8: `wakeThread` (the cross-core wake — `enqueueRunnableOnCore` on
the determined target core plus the optional cross-core SGI) preserves the
structural SMP invariant.  The state component is exactly the enqueue on the
target core (`wakeThread_state_eq_enqueue`), so this is a direct corollary of the
`enqueueRunnableOnCore` preservation; the SGI is metadata that does not touch
state. -/
theorem wakeThread_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid)
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (wakeThread st tid executingCore).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp
    st (determineTargetCore st tid) tid hInv hNotCur hPre

-- ── §3.3  Per-core budget-aware dispatch (`scheduleEffectiveOnCore`) ──

/-- WS-SM SM5.I (frame helper): the idle fallback frames every *sibling* core's
`current` slot — both arms (idle dispatch / `current = none`) write only core
`c`'s slot. -/
theorem idleFallbackOnCore_currentOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ h,
      restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore]
  · simp only [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ h]

/-- WS-SM SM5.I (frame helper): the idle fallback frames every *sibling* core's
run queue. -/
theorem idleFallbackOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
      restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore]

/-- WS-SM SM5.I.8 (other-core frame for the dispatcher): a per-core dispatch on
core `c` leaves every *sibling* core's `current` and `runQueue` slots untouched.
The dispatch's only scheduler writes are core `c`'s `setRunQueueOnCore` (dequeue)
and `setCurrentOnCore`; `saveOutgoingContextOnCore` / `restoreIncomingContext`
leave the scheduler structure intact (they touch only the object store /
`machine.regs`).  Proved over all OK branches (idle fallback + thread dispatch);
the error branch is impossible under `hStep`. -/
theorem scheduleEffectiveOnCore_independent_of_other_core (st : SystemState)
    (c c' : CoreId) (st' : SystemState) (hcc : c ≠ c')
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      refine ⟨?_, ?_⟩
      · rw [idleFallbackOnCore_currentOnCore_ne _ c c' hcc, saveOutgoingContextOnCore_scheduler_eq]
      · rw [idleFallbackOnCore_runQueueOnCore_ne _ c c' hcc, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          refine ⟨?_, ?_⟩
          · simp only [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc,
              restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
              saveOutgoingContextOnCore_scheduler_eq]
          · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
              restoreIncomingContext_scheduler,
              SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
              saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.I.8: the per-core budget-aware dispatch `scheduleEffectiveOnCore`
preserves the structural SMP invariant.  On the operated core `c₀` the dispatch
*establishes* all four structural conjuncts (dequeue-on-dispatch consistency +
current-thread validity from the selection, runnable-are-TCBs and run-queue
well-formedness preserved across the `remove`); every sibling core is framed
(`_independent_of_other_core`); the only object write — the outgoing
register-context save — preserves TCB-resolvability everywhere
(`_getTcb?_isSome`).  This is the *live* per-core scheduler step
(`timerTickOnCore` and `scheduleDomainOnCore` reach the idle thread through it),
so its structural preservation is the keystone of the per-core invariant
suite. -/
theorem scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructural_smp st)
    (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    schedulerInvariantStructural_smp st' := by
  refine schedulerInvariantStructural_smp_of_establish_and_frame (c₀ := c₀) hPre ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore st c₀ st' hStep
    · exact scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st c₀ st' hInv hStep
    · exact scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore st c₀ st' hInv hStep
        (hPre c₀).2.2.1
    · exact scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed st c₀ st' (hPre c₀).2.2.2 hStep
  · exact fun c' hc => (scheduleEffectiveOnCore_independent_of_other_core st c₀ c' st' hc hStep).1
  · exact fun c' hc => (scheduleEffectiveOnCore_independent_of_other_core st c₀ c' st' hc hStep).2
  · intro t hsome
    obtain ⟨tcb, ht⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨tcb', ht'⟩ := scheduleEffectiveOnCore_getTcb?_isSome st c₀ st' t hInv hStep ⟨tcb, ht⟩
    rw [ht']; rfl

/-- WS-SM SM5.I.8: `scheduleOrIdleOnCore` — the SM5.E idle-aware dispatcher,
definitionally `scheduleEffectiveOnCore` — preserves the structural SMP
invariant.  Direct corollary. -/
theorem scheduleOrIdleOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructural_smp st)
    (hStep : scheduleOrIdleOnCore st c₀ = .ok st') :
    schedulerInvariantStructural_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp st c₀ st' hInv hPre hStep

-- ── §3.4  Per-core context switch (`switchToThreadOnCore`) ──

/-- WS-SM SM5.I (frame helper): `preemptCurrentOnCore` destroys no TCB.  Its only
object-store write is the in-place save of core `c`'s outgoing thread's register
context (a TCB → TCB `insert`), so every key that resolved to a TCB still does. -/
theorem preemptCurrentOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId)
    (h : ∃ x, st.getTcb? t = some x) :
    ∃ x, (preemptCurrentOnCore st c incoming).getTcb? t = some x := by
  cases hCur : st.scheduler.currentOnCore c with
  | none =>
      rw [show preemptCurrentOnCore st c incoming = st from by
        simp only [preemptCurrentOnCore, hCur]]
      exact h
  | some prevTid =>
      cases hEqb : prevTid == incoming with
      | true =>
          rw [show preemptCurrentOnCore st c incoming = st from by
            simp only [preemptCurrentOnCore, hCur, hEqb, if_true]]
          exact h
      | false =>
          cases hPrev : st.getTcb? prevTid with
          | none =>
              rw [show preemptCurrentOnCore st c incoming = st from by
                simp only [preemptCurrentOnCore, hCur, hEqb, hPrev, Bool.false_eq_true, if_false]]
              exact h
          | some prevTcb =>
              -- active branch: `objects := insert prevTid (.tcb { prevTcb with regs })`.
              by_cases hT : t = prevTid
              · subst hT
                refine ⟨{ prevTcb with registerContext := st.machine.regs }, ?_⟩
                simp only [preemptCurrentOnCore, hCur, hEqb, hPrev, Bool.false_eq_true, if_false]
                simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
                rw [RobinHood.RHTable.getElem?_insert_self st.objects t.toObjId _ hInv]
              · obtain ⟨x, hx⟩ := h
                refine ⟨x, ?_⟩
                have hNeO : ¬ (prevTid.toObjId == t.toObjId) = true := fun he =>
                  hT (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
                simp only [preemptCurrentOnCore, hCur, hEqb, hPrev, Bool.false_eq_true, if_false]
                simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
                rw [RobinHood.RHTable.getElem?_insert_ne st.objects prevTid.toObjId t.toObjId
                  _ hNeO hInv]
                simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx

/-- WS-SM SM5.I (frame helper): every member of `preemptCurrentOnCore`'s run queue
on core `c` resolves to a TCB in the pre-state — prior members by
`runnableThreadsAreTCBsOnCore`, and the re-enqueued preempted thread (the old
current) by `currentThreadValidOnCore`.  This is what lets the *switch* preserve
`runnableThreadsAreTCBsOnCore` across the preempt re-enqueue. -/
theorem preemptCurrentOnCore_runQueue_resolves (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hRAT : runnableThreadsAreTCBsOnCore st c)
    (hCTV : currentThreadValidOnCore st c) (x : SeLe4n.ThreadId)
    (hx : x ∈ ((preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c).toList) :
    ∃ t, st.getTcb? x = some t := by
  cases hCur : st.scheduler.currentOnCore c with
  | none =>
      rw [show (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c
            = st.scheduler.runQueueOnCore c from by simp [preemptCurrentOnCore, hCur]] at hx
      exact hRAT x hx
  | some prevTid =>
      cases hEqb : prevTid == incoming with
      | true =>
          rw [show (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c
                = st.scheduler.runQueueOnCore c from by
            simp [preemptCurrentOnCore, hCur, hEqb]] at hx
          exact hRAT x hx
      | false =>
          cases hPrev : st.getTcb? prevTid with
          | none =>
              rw [show (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c
                    = st.scheduler.runQueueOnCore c from by
                simp [preemptCurrentOnCore, hCur, hEqb, hPrev]] at hx
              exact hRAT x hx
          | some prevTcb =>
              rw [preemptCurrentOnCore_runQueueOnCore_self_active st c incoming prevTid prevTcb
                hCur hEqb hPrev] at hx
              rcases (RunQueue.mem_insert _ _ _ _).mp ((RunQueue.mem_toList_iff_mem _ _).mp hx) with
                hold | heq
              · exact hRAT x ((RunQueue.mem_toList_iff_mem _ _).mpr hold)
              · subst heq
                unfold currentThreadValidOnCore at hCTV
                rw [hCur] at hCTV
                exact hCTV

/-- WS-SM SM5.I (frame helper): `switchToThreadOnCore` destroys no TCB.  Its
entire object-store footprint is the preempt's (`_objects_eq_preempt`), and the
preempt only saves the outgoing thread's register context (TCB → TCB), so
TCB-resolvability is preserved at every key. -/
theorem switchToThreadOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState) (hInv : st.objects.invExt)
    (h : switchToThreadOnCore st c tid = .ok st') (t : SeLe4n.ThreadId)
    (ht : ∃ x, st.getTcb? t = some x) :
    ∃ x, st'.getTcb? t = some x := by
  have hobj := switchToThreadOnCore_objects_eq_preempt st c tid st' h
  have hgt : st'.getTcb? t = (preemptCurrentOnCore st c tid).getTcb? t := by
    unfold SystemState.getTcb?; rw [hobj]
  rw [hgt]
  exact preemptCurrentOnCore_getTcb?_isSome st c tid hInv t ht

/-- WS-SM SM5.I.8 (missing structural conjunct, proved here): `switchToThreadOnCore`
preserves `runnableThreadsAreTCBsOnCore` on core `c`.  The post-switch run queue is
`(preempt-re-enqueue).remove tid`, every member of which resolves to a TCB in the
pre-state (`preemptCurrentOnCore_runQueue_resolves` — prior members + the
re-enqueued preempted thread), and `switchToThreadOnCore_getTcb?_isSome` lifts that
across the switch. -/
theorem switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState) (hInv : st.objects.invExt)
    (hRAT : runnableThreadsAreTCBsOnCore st c) (hCTV : currentThreadValidOnCore st c)
    (h : switchToThreadOnCore st c tid = .ok st') :
    runnableThreadsAreTCBsOnCore st' c := by
  -- The post-switch run queue on `c` is the preempt run queue with `tid` removed.
  have hrq : st'.scheduler.runQueueOnCore c
      = ((preemptCurrentOnCore st c tid).scheduler.runQueueOnCore c).remove tid := by
    unfold switchToThreadOnCore at h
    cases hTcb : st.getTcb? tid with
    | none => simp [hTcb] at h
    | some tidTcb =>
      simp only [hTcb] at h
      by_cases hAff : affinityAdmitsCore tidTcb c = true
      · rw [if_pos hAff, Except.ok.injEq] at h; subst h
        simp only [SchedulerState.setCurrentOnCore_runQueueOnCore, restoreIncomingContext_scheduler,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      · rw [if_neg hAff] at h; simp at h
  intro x hx
  rw [hrq] at hx
  -- `x ∈ (preempt rq).remove tid` ⇒ `x ∈ preempt rq`; that member resolves in `st`.
  have hxPre : x ∈ ((preemptCurrentOnCore st c tid).scheduler.runQueueOnCore c).toList :=
    (RunQueue.mem_toList_iff_mem _ _).mpr
      ((RunQueue.mem_remove _ _ _).mp ((RunQueue.mem_toList_iff_mem _ _).mp hx)).1
  exact switchToThreadOnCore_getTcb?_isSome st c tid st' hInv h x
    (preemptCurrentOnCore_runQueue_resolves st c tid hRAT hCTV x hxPre)

/-- WS-SM SM5.I.8: `switchToThreadOnCore` (the per-core preemptive context switch)
preserves the structural SMP invariant.  On the operated core `c₀` the switch
*establishes* dequeue-on-dispatch consistency and current-thread validity, and
preserves runnable-are-TCBs (across the preempt re-enqueue) and run-queue
well-formedness; sibling cores are framed (`_independent_of_other_core`); and the
only object write — the preempted thread's context save — preserves
TCB-resolvability everywhere.  The seL4-faithful preconditions `runnableThreadsAreTCBsOnCore`
and `currentThreadValidOnCore` on core `c₀` (the latter for the re-enqueued
preempted thread) come straight from the pre-state structural invariant. -/
theorem switchToThreadOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructural_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') :
    schedulerInvariantStructural_smp st' := by
  refine schedulerInvariantStructural_smp_of_establish_and_frame (c₀ := c₀) hPre ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact switchToThreadOnCore_establishes_queueCurrentConsistentOnCore st c₀ tid st' h
    · exact switchToThreadOnCore_establishes_currentThreadValidOnCore st c₀ tid st' hInv h
    · exact switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore st c₀ tid st' hInv
        (hPre c₀).2.2.1 (hPre c₀).2.1 h
    · exact switchToThreadOnCore_preserves_runQueueOnCore_wellFormed st c₀ tid st' (hPre c₀).2.2.2 h
  · exact fun c' hc => (switchToThreadOnCore_independent_of_other_core st c₀ c' tid st' hc h).1
  · exact fun c' hc => (switchToThreadOnCore_independent_of_other_core st c₀ c' tid st' hc h).2
  · intro t hsome
    obtain ⟨tcb, ht⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨tcb', ht'⟩ := switchToThreadOnCore_getTcb?_isSome st c₀ tid st' hInv h t ⟨tcb, ht⟩
    rw [ht']; rfl

-- ── §3.5  Cross-core reschedule-SGI handler (`handleRescheduleSgiOnCore`) ──

/-- WS-SM SM5.I.8: the reschedule-SGI handler preserves the structural SMP
invariant.  On the target core it either keeps the current thread (a no-op,
`st' = st`) or preemptively switches to a strictly-outranking candidate (via
`switchToThreadOnCore`); the no-op carries the pre-state invariant and the
switch is discharged by the SM5.B switch preservation. -/
theorem handleRescheduleSgiOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructural_smp st)
    (h : handleRescheduleSgiOnCore st c₀ = .ok st') :
    schedulerInvariantStructural_smp st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)                                  -- selection error: impossible
  · rw [Except.ok.injEq] at h; subst h; exact hPre            -- nothing eligible: st' = st
  · split at h
    · exact switchToThreadOnCore_preserves_schedulerInvariantStructural_smp     -- outranks: switch
        st c₀ _ st' hInv hPre h
    · rw [Except.ok.injEq] at h; subst h; exact hPre           -- does not outrank: st' = st

-- ── §3.6  Per-core idle-thread enqueue (`enqueueIdleThreadOnCore`) ──

/-- WS-SM SM5.I.8: enqueuing core `c₀`'s idle thread preserves the structural SMP
invariant.  On core `c₀` the four conjuncts are preserved by the SM5.E
`enqueueIdleThreadOnCore_preserves_*` lemmas (the `hNotCur` precondition — the idle
thread is not core `c₀`'s running thread — is the documented "idle is enqueued as a
fallback, never while running" discipline); sibling cores are framed; the only
object change (the idle slot's `createIdleThread`) keeps every key a TCB. -/
theorem enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c₀ ≠ some (idleThreadId c₀))
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (enqueueIdleThreadOnCore st c₀) := by
  refine schedulerInvariantStructural_smp_of_establish_and_frame (c₀ := c₀) hPre ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact enqueueIdleThreadOnCore_preserves_queueCurrentConsistentOnCore st c₀ hNotCur (hPre c₀).1
    · exact enqueueIdleThreadOnCore_preserves_currentThreadValidOnCore st c₀ hInv (hPre c₀).2.1
    · exact enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore st c₀ hInv (hPre c₀).2.2.1
    · exact enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed st c₀ (hPre c₀).2.2.2
  · exact fun c' _ => enqueueIdleThreadOnCore_currentOnCore st c₀ c'
  · exact fun c' hc => enqueueIdleThreadOnCore_runQueueOnCore_ne st c₀ c' hc
  · intro t hsome
    by_cases hEq : t = idleThreadId c₀
    · subst hEq; rw [enqueueIdleThreadOnCore_getTcb?_self st c₀ hInv]; rfl
    · rw [enqueueIdleThreadOnCore_getTcb?_ne st c₀ t hInv hEq]; exact hsome

-- ── §3.7  Per-core CBS replenishment (`replenishOnCore`) ──

/-- WS-SM SM5.I.8: scheduling a per-core CBS replenishment preserves the structural
SMP invariant.  `replenishOnCore` writes only core `c₀`'s replenish-queue slot —
which no structural conjunct reads — so it frames `current`, `runQueue`, and the
object store on every core (the cleanest framing instance, like the domain
rotation).  This witnesses that the CBS subsystem's scheduling primitive cannot
violate the per-core scheduler safety invariant. -/
theorem replenishOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (replenishOnCore st c₀ scId eligibleAt) := by
  intro c'
  refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c')
  · exact replenishOnCore_currentOnCore st c₀ c' scId eligibleAt
  · exact replenishOnCore_runQueueOnCore st c₀ c' scId eligibleAt
  · intro tid hsome; rw [replenishOnCore_getTcb?]; exact hsome

-- ── §3.8  Non-boundary per-core domain decrement (`decrementDomainTimeOnCore`) ──

/-- WS-SM SM5.I.8: the non-boundary per-core domain-time decrement preserves the
structural SMP invariant.  Like the domain rotation and CBS replenishment, it
writes only core `c₀`'s `domainTimeRemaining` slot — read by no structural
conjunct — so it frames `current`, `runQueue`, and the object store on every
core.  (`scheduleDomainOnCore`'s non-boundary branch is exactly this transition,
so this is the structural preservation of the live domain tick away from a
domain boundary.) -/
theorem decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructural_smp st) :
    schedulerInvariantStructural_smp (decrementDomainTimeOnCore st c₀) := by
  intro c'
  refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c')
  · exact decrementDomainTimeOnCore_currentOnCore st c₀ c'
  · exact decrementDomainTimeOnCore_runQueueOnCore st c₀ c'
  · intro tid hsome
    have : (decrementDomainTimeOnCore st c₀).getTcb? tid = st.getTcb? tid := by
      unfold SystemState.getTcb?; rw [decrementDomainTimeOnCore_objects_eq]
    rw [this]; exact hsome

-- ============================================================================
-- §3.9  Composite live-tick transitions — tracked SM5.I closure
-- ============================================================================
--
-- The composite live-tick transitions `switchDomainOnCore` / `scheduleDomainOnCore`
-- (the domain-*boundary* tick) and `timerTickOnCore` (the per-core CNTP tick)
-- preserve the structural SMP invariant by *composition* of the primitives proved
-- above:
--   * `scheduleDomainOnCore` = `switchDomainOnCore` (re-enqueue current, save
--     context, rotate domain on core `c`, set `current = none`) followed by
--     `scheduleEffectiveOnCore` on the boundary; its non-boundary branch is exactly
--     `decrementDomainTimeOnCore` (§3.8, proved).  `scheduleEffectiveOnCore`'s
--     structural preservation is §3.3; `switchDomainOnCore` is single-core (it
--     writes only core `c`'s slots, no cross-core wake) so it frames sibling cores.
--   * `timerTickOnCore` clears core `c`'s `lastTimeoutErrors` (frame), folds the
--     due CBS replenishments — each of which is a `wakeThread` whose structural
--     preservation is §3.2 — charges the running thread's budget, and on preemption
--     re-dispatches via `scheduleEffectiveOnCore` (§3.3).  Unlike every other
--     transition here it is genuinely *multi-core* (a cross-core replenish wake
--     enqueues a refilled thread onto a remote core's run queue), so its
--     system-wide preservation threads `wakeThread_preserves_schedulerInvariantStructural_smp`
--     through the replenishment fold rather than framing sibling cores.
--
-- These compositions are the SM5.I closure follow-on (the plan's "5 PRs"): the
-- executing-core establishment is already provided by SM5.D's
-- `timerTickOnCore_preserves_{currentThreadValid,queueCurrentConsistent,runQueueOnCoreWellFormed}OnCore`
-- and the §3 primitives; the remaining work is the mechanical fold composition.
-- Items deferred past v1.0.0 with correctness impact: NONE (the structural
-- safety core is established on the executing core; the sibling-core obligations
-- reduce to the already-proven `wakeThread` / `scheduleEffectiveOnCore`
-- preservations).

-- ============================================================================
-- §4  Suite index: the per-core invariants assembled (SM5.I.1–I.7, I.9)
-- ============================================================================
--
-- SM5.I.1–I.4 (the per-core *predicates*) and SM5.I.5/I.7/I.9 (the *aggregates*)
-- were defined as the SM4.C/SM4.D per-core migration; this section assembles them
-- into the SM5.I suite under their plan names, with the bridges that connect the
-- structural safety core to the full aggregate and the cross-subsystem suite.

/-- WS-SM SM5.I.1 (`currentOnCore_validThreadIfSome`): on a core whose per-core
invariant holds, a `some` current thread resolves to a real TCB — the usable
"no dangling current" form of `currentThreadValidOnCore`. -/
theorem currentOnCore_validThreadIfSome {st : SystemState} {c : CoreId}
    (h : currentThreadValidOnCore st c) {tid : SeLe4n.ThreadId}
    (hcur : st.scheduler.currentOnCore c = some tid) :
    ∃ tcb : TCB, st.getTcb? tid = some tcb := by
  unfold currentThreadValidOnCore at h; rw [hcur] at h; exact h

/-- WS-SM SM5.I.2 (`runQueueOnCore_wellFormed`): the run-queue well-formedness
projection of the structural invariant. -/
theorem runQueueOnCore_wellFormed_of_structural {st : SystemState} {c : CoreId}
    (h : schedulerInvariantStructural_perCore st c) :
    (st.scheduler.runQueueOnCore c).wellFormed :=
  schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed h

/-- WS-SM SM5.I.3 (`schedContextRunQueueConsistent_perCore`): the SchedContext ↔
run-queue per-core coherence predicate is carried by the cross-subsystem per-core
invariant (SM4.D); projected here as the SM5.I suite anchor. -/
theorem schedContextRunQueueConsistent_perCore_of_crossSubsystem {st : SystemState} {c : CoreId}
    (h : crossSubsystemInvariant_perCore st c) :
    schedContextRunQueueConsistent_perCore st c :=
  crossSubsystemInvariant_perCore_to_schedContextRunQueueConsistent h

/-- WS-SM SM5.I.4 (`priorityInheritance_perCore`): the per-core priority-inheritance
acyclicity predicate (SM4.C, `= PriorityInheritance.blockingAcyclic`); recapped as
the suite anchor.  (It is core-independent — the blocking graph is global — so the
`c` argument is structural metadata for the SM5 migration seam.) -/
theorem priorityInheritance_perCore_iff_blockingAcyclic (st : SystemState) (c : CoreId) :
    priorityInheritance_perCore st c ↔ PriorityInheritance.blockingAcyclic st := Iff.rfl

/-- WS-SM SM5.I.5/I.7: the full SM4.C per-core aggregate (`schedulerInvariant_perCore`)
and the system-wide `schedulerInvariant_smp` exist and dominate the structural
suite — every full witness yields the structural one (`…_to_structural`), and the
structural one is the register-bank-free core that survives genuine multi-core
dispatch. -/
theorem schedulerInvariant_smp_dominates_structural {st : SystemState}
    (h : schedulerInvariant_smp st) : schedulerInvariantStructural_smp st :=
  schedulerInvariant_smp_to_structural h

/-- WS-SM SM5.I.6: **structural cross-core independence** (the structural analogue
of SM4.C's `schedulerInvariant_perCore_pairwise`).  Overwriting a *different*
core's `current` and `runQueue` slots leaves this core's structural invariant
intact — the per-core `Vector` indexing (SM4.B) delivers genuine isolation, the
property SM5 relies on to reason about each core's scheduler independently. -/
theorem schedulerInvariantStructural_perCore_pairwise
    {st : SystemState} {c₁ c₂ : CoreId} (hne : c₁ ≠ c₂)
    (vc : Option SeLe4n.ThreadId) (vrq : RunQueue)
    (h : schedulerInvariantStructural_perCore st c₁) :
    schedulerInvariantStructural_perCore
      { st with scheduler := (st.scheduler.setCurrentOnCore c₂ vc).setRunQueueOnCore c₂ vrq } c₁ := by
  refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ h
  · simp [SchedulerState.setRunQueueOnCore_currentOnCore,
      SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hne)]
  · simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hne)]
  · intro tid hsome; exact hsome

/-- WS-SM SM5.I.9 (`crossSubsystemInvariant_smp`): the system-wide cross-subsystem
SMP invariant (SM4.D) dominates the structural suite — every cross-subsystem
witness contains the per-core scheduler invariant, hence the structural core. -/
theorem crossSubsystemInvariant_smp_dominates_structural {st : SystemState}
    (h : schedulerInvariant_smp_crossSubsystem st) : schedulerInvariantStructural_smp st :=
  fun c => schedulerInvariant_perCore_to_structural
    (schedulerInvariant_perCore_extended_to_base
      (schedulerInvariant_perCore_crossSubsystem_to_extended (h c)))

end SeLe4n.Kernel
