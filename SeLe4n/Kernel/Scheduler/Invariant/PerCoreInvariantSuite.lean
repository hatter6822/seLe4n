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
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Preservation

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

**`contextMatchesCurrentOnCore` is no longer excluded** (SM4.B per-core register
banks).  SM4.B replaced the single shared `machine.regs` with a per-core register
bank `Vector RegisterFile numCores` (accessor `regsOnCore c`), and
`contextMatchesCurrentOnCore` now reads core `c`'s **own** bank.  A per-core
dispatch on `c₀` writes only `setRegsOnCore c₀`, framing every sibling bank, so
the conjunct holds on *every* core simultaneously.  §2b/§4 below define the
**register-bank-extended** invariant `schedulerInvariantStructuralReg_perCore` /
`_smp` (the four structural conjuncts **+** `contextMatchesCurrentOnCore`) and
prove it preserved system-wide by *every* SM5 per-core transition — the SM4.B
payoff: the contextMatches conjunct that one shared register file could maintain
on at most one core is now a genuine ∀-core invariant.

The remaining **six** conjuncts are excluded from the structural core for two
distinct reasons (the first genuinely-mathematical, the second a scope-bounding
deferral — neither is a soundness gap):

1. **`edfCurrentHasEarliestDeadlineOnCore`**, `timeSlicePositiveOnCore`,
   `currentTimeSlicePositiveOnCore`, and `domainTimeRemainingPositiveOnCore`
   are **dispatch/tick-established**, not transition-stable: a *bare* wake
   enqueuing an earlier-deadline thread in the running thread's bucket
   transiently breaks EDF until the next dispatch re-establishes it (precisely
   *when* the wake fires a preemption SGI).  In the single-core model the same
   holds — `ensureRunnable` preserves only the base invariant, `schedule`
   re-establishes EDF.

2. **`schedulerPriorityMatchOnCore`** is register-bank-independent but coupled to
   dispatch via the **PIP-boost run-queue bucket migration**: a `pipBoost` change
   alters a thread's `effectiveRunQueuePriority`, and the matching run-queue index
   is re-bucketed only on the thread's home core (`updatePipBoostOnCore`), so the
   conjunct is not frame-stable across an arbitrary objects mutation.
   (**`runQueueUniqueOnCore`** — run-queue `Nodup` — *is* both register-bank-
   independent and transition-stable, and is included in the further-extended
   `schedulerInvariantStructuralRegNodup` invariant below.)

The base `schedulerInvariantStructural_perCore` frame on a sibling core
`c' ≠ c₀` needs **no register-bank agreement** (it carries none of the
register-reading conjuncts), so a per-core dispatch on `c₀` — which *does*
rewrite core `c₀`'s bank — trivially preserves it on **every** core.  The
register-bank-extended frame (§2b) additionally carries per-core `regsOnCore c'`
agreement (which the per-core banks deliver for free on a sibling), so
`schedulerInvariantStructuralReg_smp` is likewise a genuine system-wide SMP
invariant.

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
  (and the register-bank-extended `…StructuralReg_smp` and the
  Nodup-extended `…StructuralRegNodup_smp`) for every SM5 per-core transition
  (wake, switch, dispatch, timer tick, domain rotate, idle enqueue, …), and — on
  the *operated* core — the strongest per-core establishment each transition
  delivers (including, for the two dispatch transitions, the
  `contextMatchesCurrentOnCore` *establishment* the per-core register banks
  unlock).
* **SM5.I.9** — `crossSubsystemInvariant_smp` (recapped from SM4.D).
* **§2b/§4 (SM4.B register-bank payoff)** — the register-bank-extended
  invariant `schedulerInvariantStructuralReg_perCore` / `_smp` (the four
  structural conjuncts + `contextMatchesCurrentOnCore`) and its system-wide
  preservation by every SM5 per-core transition.  §4.4 further extends it with
  the run-queue `Nodup` conjunct (`…StructuralRegNodup`).

Axiom-clean: every theorem depends only on the standard foundational axioms
(`propext` / `Quot.sound` / `Classical.choice`).

**Per-core register banks (SM4.B) — LANDED.**  The system-wide
`schedulerInvariant_smp` (∀ c, including `contextMatchesCurrentOnCore`)
preservation by a per-core dispatch with *multiple* non-idle cores was
previously gated on the single shared `machine.regs` (which made multi-active-
core `contextMatchesCurrent` unsatisfiable).  SM4.B's per-core register banks
(`MachineState.coreRegs : Vector RegisterFile numCores`) close that gap: the
register-bank-extended `schedulerInvariantStructuralReg_smp` carries the
`contextMatchesCurrentOnCore` conjunct on *every* core and is preserved
system-wide by every transition (§4).  The only `registerContext` write any
transition makes — the outgoing-thread save — is `==`-idempotent on a thread
(pathologically) current on a sibling core, discharged by that sibling's
pre-state `contextMatchesCurrent` and the `RegisterFile` partial equivalence
(`RegisterFile.beq_symm` / `beq_trans`).  The remaining six full-aggregate
conjuncts (EDF / two time-slice / domain-time — dispatch/tick-established;
`schedulerPriorityMatch` — PIP-bucket-coupled) are excluded for reasons
*unrelated* to register banks.
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
-- §2b  The register-bank-extended structural invariant (the SM4.B per-core
--      register-bank payoff: `contextMatchesCurrentOnCore` becomes system-wide)
-- ============================================================================
--
-- SM4.B replaced the single shared `machine.regs` with a per-core register bank
-- `Vector RegisterFile numCores` (accessor `regsOnCore c` / `setRegsOnCore c`).
-- `contextMatchesCurrentOnCore` now reads core `c`'s *own* bank, so a per-core
-- dispatch on core `c₀` — which writes only `setRegsOnCore c₀` — leaves every
-- sibling core's `contextMatchesCurrent` untouched.  This is exactly the
-- conjunct the old module header flagged as register-bank-gated; with the banks
-- it is a genuine system-wide invariant, proved preserved by every transition.

/-- WS-SM SM5.I (register-bank payoff): `contextMatchesCurrentOnCore` is preserved
on core `c` when (a) core `c`'s `current` slot is unchanged, (b) core `c`'s
register bank is unchanged, and (c) the current thread's saved `registerContext`
is `==`-preserved.  `currentThreadValidOnCore st c` rules out the (vacuous)
non-TCB-current case where a fresh TCB could appear under the current pointer.
The `==`-preservation (rather than `=`) is what lets the dispatch sibling frame
discharge the pathological "current on two cores" case via the
`RegisterFile` partial-equivalence (`beq_trans`). -/
theorem contextMatchesCurrentOnCore_frame_at
    {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRegs : st'.machine.regsOnCore c = st.machine.regsOnCore c)
    (hRC : ∀ tid tcb, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some tcb →
       ∃ tcb', st'.getTcb? tid = some tcb' ∧ (tcb.registerContext == tcb'.registerContext) = true)
    (hValid : currentThreadValidOnCore st c)
    (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore st' c := by
  unfold contextMatchesCurrentOnCore at h ⊢
  rw [hCur]
  cases hcur : st.scheduler.currentOnCore c with
  | none => exact trivial
  | some tid =>
      have hvalid' := hValid
      unfold currentThreadValidOnCore at hvalid'
      simp only [hcur] at hvalid'
      obtain ⟨tcb, htcb⟩ := hvalid'
      simp only [hcur, htcb] at h
      obtain ⟨tcb', htcb', hrc⟩ := hRC tid tcb hcur htcb
      simp only [htcb', hRegs]
      -- h : (regsOnCore c == tcb.registerContext) = true;
      -- hrc : (tcb.registerContext == tcb'.registerContext) = true
      exact RegisterFile.beq_trans h hrc

/-- WS-SM SM5.I: the **register-bank-extended** structural per-core invariant —
the four register-bank-independent safety conjuncts plus
`contextMatchesCurrentOnCore` (sound system-wide now that SM4.B gives per-core
register banks).  This is the maximal *register-bank-sound* per-core scheduler
invariant (the remaining six conjuncts — EDF / the two time-slice conjuncts /
domain-time, which are dispatch/tick-established; `schedulerPriorityMatch`, which
is PIP-bucket-coupled; and `runQueueUnique` — are excluded for reasons unrelated
to register banks). -/
def schedulerInvariantStructuralReg_perCore (st : SystemState) (c : CoreId) : Prop :=
  schedulerInvariantStructural_perCore st c ∧ contextMatchesCurrentOnCore st c

/-- WS-SM SM5.I: the system-wide register-bank-extended structural SMP invariant —
the extended per-core invariant on *every* core.  Unlike the pre-SM4.B situation,
this **is** preserved by genuine multi-core dispatch: a dispatch on `c₀` writes
`setRegsOnCore c₀`, framing every sibling's bank, so no shared-register conflict
arises. -/
def schedulerInvariantStructuralReg_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariantStructuralReg_perCore st c

theorem schedulerInvariantStructuralReg_perCore_to_structural
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructuralReg_perCore st c) :
    schedulerInvariantStructural_perCore st c := h.1

theorem schedulerInvariantStructuralReg_perCore_to_contextMatches
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructuralReg_perCore st c) :
    contextMatchesCurrentOnCore st c := h.2

theorem schedulerInvariantStructuralReg_smp_to_structural {st : SystemState}
    (h : schedulerInvariantStructuralReg_smp st) : schedulerInvariantStructural_smp st :=
  fun c => (h c).1

/-- The full SM4.C per-core aggregate implies the register-bank-extended structural
invariant (its `contextMatchesCurrent` conjunct is the 5th here). -/
theorem schedulerInvariant_perCore_to_structuralReg {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : schedulerInvariantStructuralReg_perCore st c :=
  ⟨schedulerInvariant_perCore_to_structural h,
   schedulerInvariant_perCore_to_contextMatchesCurrent h⟩

theorem schedulerInvariant_smp_to_structuralReg {st : SystemState}
    (h : schedulerInvariant_smp st) : schedulerInvariantStructuralReg_smp st :=
  fun c => schedulerInvariant_perCore_to_structuralReg (h c)

/-- WS-SM SM5.I: the freshly-booted system satisfies the register-bank-extended
structural SMP invariant on every core. -/
theorem default_schedulerInvariantStructuralReg_smp :
    schedulerInvariantStructuralReg_smp (default : SystemState) :=
  fun c => schedulerInvariant_perCore_to_structuralReg (default_schedulerInvariant_perCore c)

/-- WS-SM SM5.I: lift a base structural SMP preservation plus a system-wide
`contextMatchesCurrentOnCore` proof into the extended invariant.  Every
`<op>_preserves_schedulerInvariantStructuralReg_smp` below is this combinator
applied to the (already-proved) base structural preservation and the per-op
`contextMatches` establishment/frame. -/
theorem schedulerInvariantStructuralReg_smp_of_base_and_ctx {st' : SystemState}
    (hBase : schedulerInvariantStructural_smp st')
    (hCtx : ∀ c, contextMatchesCurrentOnCore st' c) :
    schedulerInvariantStructuralReg_smp st' :=
  fun c => ⟨hBase c, hCtx c⟩

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
      restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore]
  · simp only [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ h]

/-- WS-SM SM5.I (frame helper): the idle fallback frames every *sibling* core's
run queue. -/
theorem idleFallbackOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
      restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
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
              restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
              saveOutgoingContextOnCore_scheduler_eq]
          · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
              restoreIncomingContextOnCore_scheduler,
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
                refine ⟨{ prevTcb with registerContext := st.machine.regsOnCore c }, ?_⟩
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
        simp only [SchedulerState.setCurrentOnCore_runQueueOnCore, restoreIncomingContextOnCore_scheduler,
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

/-- WS-SM SM5.I.6 (cross-core independence, **biconditional**): overwriting a
*different* core `c₂`'s `current` and `runQueue` slots leaves core `c₁`'s
structural invariant **unchanged in both directions** — the modification is
scheduler-only on `c₂`'s slots (so `c₁`'s `current` / `runQueue` and the whole
object store are untouched), hence the property is equivalent on the two states.
The forward direction strengthens the one-directional `_pairwise` per the
implement-the-improvement rule: genuine per-core isolation is an `↔`, not just a
one-way frame. -/
theorem schedulerInvariantStructural_perCore_pairwise_iff
    {st : SystemState} {c₁ c₂ : CoreId} (hne : c₁ ≠ c₂)
    (vc : Option SeLe4n.ThreadId) (vrq : RunQueue) :
    schedulerInvariantStructural_perCore
      { st with scheduler := (st.scheduler.setCurrentOnCore c₂ vc).setRunQueueOnCore c₂ vrq } c₁
    ↔ schedulerInvariantStructural_perCore st c₁ := by
  refine ⟨fun h => ?_, schedulerInvariantStructural_perCore_pairwise hne vc vrq⟩
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

-- ============================================================================
-- §4  Register-bank-extended preservation (SM5.I.8, the SM4.B payoff)
-- ============================================================================
--
-- Each `<op>_preserves_schedulerInvariantStructuralReg_smp` lifts the (already
-- proved) base structural preservation with a system-wide
-- `contextMatchesCurrentOnCore` proof: on the operated core via the new
-- establishment lemmas (dispatch) or a register-bank frame (non-dispatch), and on
-- every sibling core via the register-bank frame.  The crux is that a dispatch on
-- `c₀` writes `setRegsOnCore c₀` (framing sibling banks) and saves only `c₀`'s
-- outgoing thread's register context — so the sole `registerContext` write is
-- `==`-idempotent on any thread (pathologically) current on a sibling, by that
-- sibling's pre-state `contextMatchesCurrent` (`RegisterFile.beq_*`).

-- ── §4.1  Dispatch register-bank sibling frames ──

/-- WS-SM SM5.I (register-bank sibling frame): the idle fallback on core `c` leaves
every *sibling* core's register bank untouched — both arms write at most core
`c`'s bank (`dispatchIdle`'s restore) or nothing (`current = none`). -/
theorem idleFallbackOnCore_machine_regsOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold idleFallbackOnCore
  split
  · show (restoreIncomingContextOnCore _ c (idleThreadId c)).machine.regsOnCore c' = _
    exact restoreIncomingContextOnCore_regsOnCore_ne _ c c' (idleThreadId c) h
  · rfl

/-- WS-SM SM5.I (register-bank sibling frame): a per-core dispatch on core `c₀`
leaves every *sibling* core's register bank untouched — the only machine write is
the restore's `setRegsOnCore c₀`. -/
theorem scheduleEffectiveOnCore_machine_regsOnCore_ne (st : SystemState) (c₀ c' : CoreId)
    (st' : SystemState) (hcc : c₀ ≠ c') (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    st'.machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c₀ with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_machine_regsOnCore_ne _ c₀ c' hcc, saveOutgoingContextOnCore_machine]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          show (restoreIncomingContextOnCore _ c₀ tid).machine.regsOnCore c' = _
          rw [restoreIncomingContextOnCore_regsOnCore_ne _ c₀ c' tid hcc]
          show (saveOutgoingContextOnCore st c₀).machine.regsOnCore c' = _
          rw [saveOutgoingContextOnCore_machine]
        · simp at hStep

/-- WS-SM SM5.I (register-bank sibling frame): a per-core dispatch on core `c₀`
either leaves any thread's saved register context unchanged, or — when that thread
is `c₀`'s outgoing current — sets it to `machine.regsOnCore c₀` (the only
`registerContext` write, via `saveOutgoingContextOnCore`). -/
theorem scheduleEffectiveOnCore_getTcb?_regContext (st : SystemState) (c₀ : CoreId)
    (st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c₀ = .ok st') (ht : st.getTcb? tid = some tcb) :
    ∃ tcb', st'.getTcb? tid = some tcb' ∧
      (tcb'.registerContext = tcb.registerContext ∨
        (st.scheduler.currentOnCore c₀ = some tid ∧
          tcb'.registerContext = st.machine.regsOnCore c₀)) := by
  have hobj : st'.objects = (saveOutgoingContextOnCore st c₀).objects :=
    scheduleEffectiveOnCore_objects_eq st c₀ st' hStep
  have hgt : st'.getTcb? tid = (saveOutgoingContextOnCore st c₀).getTcb? tid := by
    simp only [SystemState.getTcb?, hobj]
  rw [hgt]
  exact saveOutgoingContextOnCore_getTcb?_regContext st c₀ tid tcb hInv ht

/-- WS-SM SM5.I (register-bank payoff): a per-core dispatch on `c₀` preserves
`contextMatchesCurrentOnCore` on every **sibling** core `c'`.  The bank is framed
(`_machine_regsOnCore_ne`); the only `registerContext` write is `==`-idempotent on
`c'`'s current thread — either it does not touch it, or that thread is also `c₀`'s
outgoing current and the saved value equals its old context by the pre-state
`contextMatchesCurrent` on `c₀` (`RegisterFile.beq_symm`). -/
theorem scheduleEffectiveOnCore_preserves_contextMatchesCurrentOnCore_sibling
    (st : SystemState) (c₀ c' : CoreId) (st' : SystemState) (hcc : c₀ ≠ c')
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    contextMatchesCurrentOnCore st' c' := by
  refine contextMatchesCurrentOnCore_frame_at
    (scheduleEffectiveOnCore_independent_of_other_core st c₀ c' st' hcc hStep).1
    (scheduleEffectiveOnCore_machine_regsOnCore_ne st c₀ c' st' hcc hStep)
    ?_ (hPre c').1.2.1 (hPre c').2
  intro tid tcb hcurc' htcb
  obtain ⟨tcb', ht', hdisj⟩ :=
    scheduleEffectiveOnCore_getTcb?_regContext st c₀ st' tid tcb hInv hStep htcb
  refine ⟨tcb', ht', ?_⟩
  cases hdisj with
  | inl heq => rw [heq]; exact RegisterFile.beq_self _
  | inr hr =>
      obtain ⟨hcurc0, hrc⟩ := hr
      have hcm0 := (hPre c₀).2
      unfold contextMatchesCurrentOnCore at hcm0
      simp only [hcurc0, htcb] at hcm0
      rw [hrc]
      exact RegisterFile.beq_symm hcm0

/-- WS-SM SM5.I.8 (register-bank payoff): the per-core budget-aware dispatch
`scheduleEffectiveOnCore` preserves the **register-bank-extended** structural SMP
invariant.  Lifts the base structural preservation with the system-wide
`contextMatchesCurrentOnCore`: established on the operated core
(`scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore`), framed on
every sibling (`…_sibling`). -/
theorem scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralReg_smp st' := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp st c₀ st' hInv
      (fun c => (hPre c).1) hStep) ?_
  intro c'
  by_cases hc : c₀ = c'
  · subst hc
    exact scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore st c₀ st' hInv hStep
  · exact scheduleEffectiveOnCore_preserves_contextMatchesCurrentOnCore_sibling
      st c₀ c' st' hc hInv hPre hStep

/-- WS-SM SM5.I.8: `scheduleOrIdleOnCore` (definitionally `scheduleEffectiveOnCore`)
preserves the register-bank-extended structural SMP invariant. -/
theorem scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (hStep : scheduleOrIdleOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralReg_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ st' hInv hPre hStep

-- ── §4.2  Switch register-bank preservation ──

/-- WS-SM SM5.I (register-bank sibling frame): the switch's `getTcb?` register-
context characterisation (via `switchToThreadOnCore_objects_eq_preempt` and the
preempt's `registerContext` write). -/
theorem switchToThreadOnCore_getTcb?_regContext (st : SystemState) (c₀ : CoreId)
    (tid t : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    (h : switchToThreadOnCore st c₀ tid = .ok st') (ht : st.getTcb? t = some tcb) :
    ∃ tcb', st'.getTcb? t = some tcb' ∧
      (tcb'.registerContext = tcb.registerContext ∨
        (st.scheduler.currentOnCore c₀ = some t ∧
          tcb'.registerContext = st.machine.regsOnCore c₀)) := by
  have hobj := switchToThreadOnCore_objects_eq_preempt st c₀ tid st' h
  have hgt : st'.getTcb? t = (preemptCurrentOnCore st c₀ tid).getTcb? t := by
    unfold SystemState.getTcb?; rw [hobj]
  rw [hgt]
  exact preemptCurrentOnCore_getTcb?_regContext st c₀ tid t tcb hInv ht

/-- WS-SM SM5.I (register-bank payoff): the per-core switch on `c₀` preserves
`contextMatchesCurrentOnCore` on every sibling core (same idempotent-save argument
as the dispatch). -/
theorem switchToThreadOnCore_preserves_contextMatchesCurrentOnCore_sibling
    (st : SystemState) (c₀ c' : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hcc : c₀ ≠ c') (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') :
    contextMatchesCurrentOnCore st' c' := by
  refine contextMatchesCurrentOnCore_frame_at
    (switchToThreadOnCore_independent_of_other_core st c₀ c' tid st' hcc h).1
    (switchToThreadOnCore_machine_regsOnCore_ne st c₀ c' tid st' hcc h)
    ?_ (hPre c').1.2.1 (hPre c').2
  intro t tcb hcurc' htcb
  obtain ⟨tcb', ht', hdisj⟩ :=
    switchToThreadOnCore_getTcb?_regContext st c₀ tid t tcb st' hInv h htcb
  refine ⟨tcb', ht', ?_⟩
  cases hdisj with
  | inl heq => rw [heq]; exact RegisterFile.beq_self _
  | inr hr =>
      obtain ⟨hcurc0, hrc⟩ := hr
      have hcm0 := (hPre c₀).2
      unfold contextMatchesCurrentOnCore at hcm0
      simp only [hcurc0, htcb] at hcm0
      rw [hrc]
      exact RegisterFile.beq_symm hcm0

/-- WS-SM SM5.I.8 (register-bank payoff): the per-core preemptive switch
`switchToThreadOnCore` preserves the register-bank-extended structural SMP
invariant — established on the operated core
(`switchToThreadOnCore_establishes_contextMatchesCurrentOnCore`), framed on every
sibling. -/
theorem switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') :
    schedulerInvariantStructuralReg_smp st' := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (switchToThreadOnCore_preserves_schedulerInvariantStructural_smp st c₀ tid st' hInv
      (fun c => (hPre c).1) h) ?_
  intro c'
  by_cases hc : c₀ = c'
  · subst hc
    exact switchToThreadOnCore_establishes_contextMatchesCurrentOnCore st c₀ tid st' hInv h
  · exact switchToThreadOnCore_preserves_contextMatchesCurrentOnCore_sibling
      st c₀ c' tid st' hc hInv hPre h

/-- WS-SM SM5.I.8 (register-bank payoff): the reschedule-SGI handler preserves the
register-bank-extended structural SMP invariant — switch (the SM5.B Reg
preservation) or no-op (`st' = st`, carries the pre-state invariant). -/
theorem handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralReg_smp st)
    (h : handleRescheduleSgiOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralReg_smp st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact hPre
  · split at h
    · exact switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp
        st c₀ _ st' hInv hPre h
    · rw [Except.ok.injEq] at h; subst h; exact hPre

-- ── §4.3  Non-dispatch register-bank preservation (machine-neutral ops) ──

/-- WS-SM SM5.I (register-bank payoff, machine-neutral): `contextMatchesCurrentOnCore`
is preserved on core `c` by any transition that leaves the *whole* machine
(`hMach` — hence every register bank) and the current slot (`hCur`) unchanged and
preserves the current thread's `registerContext` (`hRC`, given pointwise as an
equality).  Covers every non-dispatch per-core transition (domain rotation, wake,
CBS replenishment, domain-time decrement). -/
theorem contextMatchesCurrentOnCore_of_machine_eq_and_regContext
    {st st' : SystemState} {c : CoreId}
    (hMach : st'.machine = st.machine)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRC : ∀ tid tcb, st.getTcb? tid = some tcb →
       ∃ tcb', st'.getTcb? tid = some tcb' ∧ tcb'.registerContext = tcb.registerContext)
    (hValid : currentThreadValidOnCore st c)
    (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore st' c := by
  refine contextMatchesCurrentOnCore_frame_at hCur (by rw [hMach]) ?_ hValid h
  intro tid tcb _ htcb
  obtain ⟨tcb', ht', hrc⟩ := hRC tid tcb htcb
  exact ⟨tcb', ht', by rw [hrc]; exact RegisterFile.beq_self _⟩

/-- WS-SM SM5.I (register-bank frame): `enqueueRunnableOnCore` preserves every
thread's saved `registerContext` (its only object write sets the woken thread's
`ipcState`, never its registers). -/
theorem enqueueRunnableOnCore_getTcb?_regContext (st : SystemState) (c : CoreId)
    (tid other : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (ht : st.getTcb? other = some tcb) :
    ∃ tcb', (enqueueRunnableOnCore st c tid).getTcb? other = some tcb' ∧
      tcb'.registerContext = tcb.registerContext := by
  by_cases hot : other = tid
  · subst hot
    cases hFresh : runnableOnSomeCore st other with
    | true =>
        refine ⟨tcb, ?_, rfl⟩
        rw [enqueueRunnableOnCore_eq_self_of_runnable st c other hFresh]; exact ht
    | false =>
        exact ⟨{ tcb with ipcState := .ready },
          enqueueRunnableOnCore_makes_ready st c other tcb ht hInv hFresh, rfl⟩
  · exact ⟨tcb, by rw [enqueueRunnableOnCore_getTcb?_ne st c tid other hInv hot]; exact ht, rfl⟩

/-- WS-SM SM5.I.8 (register-bank payoff): the pure per-core domain rotation
preserves the register-bank-extended structural SMP invariant — it touches no
register bank and no `registerContext`. -/
theorem advanceDomainOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (advanceDomainOnCore st c₀) := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (advanceDomainOnCore_preserves_schedulerInvariantStructural_smp st c₀ (fun c => (hPre c).1)) ?_
  intro c'
  refine contextMatchesCurrentOnCore_of_machine_eq_and_regContext
    (show (advanceDomainOnCore st c₀).machine = st.machine by
      unfold advanceDomainOnCore; split <;> rfl)
    (advanceDomainOnCore_currentOnCore st c₀ c') ?_ (hPre c').1.2.1 (hPre c').2
  intro tid tcb ht; exact ⟨tcb, by rw [advanceDomainOnCore_getTcb?]; exact ht, rfl⟩

/-- WS-SM SM5.I.8 (register-bank payoff): the per-core wake `enqueueRunnableOnCore`
preserves the register-bank-extended structural SMP invariant — machine-neutral,
and its only object write preserves every thread's `registerContext`. -/
theorem enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c₀ ≠ some tid)
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (enqueueRunnableOnCore st c₀ tid) := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp st c₀ tid hInv hNotCur
      (fun c => (hPre c).1)) ?_
  intro c'
  refine contextMatchesCurrentOnCore_of_machine_eq_and_regContext
    (enqueueRunnableOnCore_machine_eq st c₀ tid)
    (enqueueRunnableOnCore_currentOnCore st c₀ tid c') ?_ (hPre c').1.2.1 (hPre c').2
  intro t tcb ht; exact enqueueRunnableOnCore_getTcb?_regContext st c₀ tid t tcb hInv ht

/-- WS-SM SM5.I.8 (register-bank payoff): the cross-core wake `wakeThread`
preserves the register-bank-extended structural SMP invariant.  Direct corollary
of the `enqueueRunnableOnCore` register-bank preservation (the state component is
exactly the enqueue on the target core). -/
theorem wakeThread_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid)
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (wakeThread st tid executingCore).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp
    st (determineTargetCore st tid) tid hInv hNotCur hPre

/-- WS-SM SM5.I.8 (register-bank payoff): scheduling a per-core CBS replenishment
preserves the register-bank-extended structural SMP invariant — machine-neutral,
object-store-neutral. -/
theorem replenishOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (replenishOnCore st c₀ scId eligibleAt) := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (replenishOnCore_preserves_schedulerInvariantStructural_smp st c₀ scId eligibleAt
      (fun c => (hPre c).1)) ?_
  intro c'
  refine contextMatchesCurrentOnCore_of_machine_eq_and_regContext
    (replenishOnCore_machine st c₀ scId eligibleAt)
    (replenishOnCore_currentOnCore st c₀ c' scId eligibleAt) ?_ (hPre c').1.2.1 (hPre c').2
  intro tid tcb ht; exact ⟨tcb, by rw [replenishOnCore_getTcb?]; exact ht, rfl⟩

/-- WS-SM SM5.I.8 (register-bank payoff): the non-boundary per-core domain-time
decrement preserves the register-bank-extended structural SMP invariant —
machine-neutral, object-store-neutral. -/
theorem decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (decrementDomainTimeOnCore st c₀) := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp st c₀
      (fun c => (hPre c).1)) ?_
  intro c'
  refine contextMatchesCurrentOnCore_of_machine_eq_and_regContext
    (decrementDomainTimeOnCore_machine_eq st c₀)
    (decrementDomainTimeOnCore_currentOnCore st c₀ c') ?_ (hPre c').1.2.1 (hPre c').2
  intro tid tcb ht
  exact ⟨tcb, by rw [show (decrementDomainTimeOnCore st c₀).getTcb? tid = st.getTcb? tid from by
    unfold SystemState.getTcb?; rw [decrementDomainTimeOnCore_objects_eq]]; exact ht, rfl⟩

/-- WS-SM SM5.I.8 (register-bank payoff): making core `c₀`'s idle thread available
preserves the register-bank-extended structural SMP invariant.  The enqueue
overwrites the idle TCB (`createIdleThread c₀`, register context `default`), so —
unlike the other non-dispatch transitions — `contextMatches` is preserved only
when the idle thread is **not current on any core** (`hNotCurAny`).  This is the
seL4-faithful "make idle available while it is not running" precondition (idle is
core-`c₀`-pinned, so it can only be current on `c₀`; the `∀ c'` form states the
invariant the dispatch maintains without appealing to affinity placement). -/
theorem enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralReg_smp
    (st : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt)
    (hNotCurAny : ∀ c', st.scheduler.currentOnCore c' ≠ some (idleThreadId c₀))
    (hPre : schedulerInvariantStructuralReg_smp st) :
    schedulerInvariantStructuralReg_smp (enqueueIdleThreadOnCore st c₀) := by
  refine schedulerInvariantStructuralReg_smp_of_base_and_ctx
    (enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp st c₀ hInv
      (hNotCurAny c₀) (fun c => (hPre c).1)) ?_
  intro c'
  refine contextMatchesCurrentOnCore_frame_at
    (enqueueIdleThreadOnCore_currentOnCore st c₀ c')
    rfl ?_ (hPre c').1.2.1 (hPre c').2
  intro tid tcb hcur htcb
  -- `tid = current c' ≠ idleThreadId c₀`, so the enqueue's only object write frames it.
  have hne : tid ≠ idleThreadId c₀ := by
    intro he; subst he; exact hNotCurAny c' hcur
  refine ⟨tcb, ?_, RegisterFile.beq_self _⟩
  rw [enqueueIdleThreadOnCore_getTcb?_ne st c₀ tid hInv hne]; exact htcb

-- ============================================================================
-- §4.4  The Nodup-extended structural invariant (`runQueueUniqueOnCore` 6th conjunct)
-- ============================================================================
--
-- `runQueueUniqueOnCore` (run-queue `toList.Nodup`) is both register-bank-
-- independent and transition-stable.  The `RunQueue` API maintains it
-- structurally (`insert` guards on `contains`, `remove` filters), so every SM5
-- per-core transition preserves it — mirroring the `runQueueOnCoreWellFormed`
-- preservation with `RunQueue.{insert,remove}_preserves_toList_nodup`.

/-- WS-SM SM5.I: the idle fallback preserves core `c`'s run-queue `Nodup` (idle arm
`remove`s, `none` arm frames).  Mirror of `idleFallbackOnCore_preserves_runQueueOnCoreWellFormed`. -/
theorem idleFallbackOnCore_preserves_runQueueUniqueOnCore_self (st : SystemState) (c : CoreId)
    (hN : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((idleFallbackOnCore st c).scheduler.runQueueOnCore c).toList.Nodup := by
  unfold idleFallbackOnCore
  split
  · rw [dispatchIdleOnCore_runQueueOnCore]
    exact RunQueue.remove_preserves_toList_nodup _ _ hN
  · simpa [SchedulerState.setCurrentOnCore_runQueueOnCore] using hN

/-- WS-SM SM5.I: the preempt preserves core `c`'s run-queue `Nodup` (the re-enqueue
is a `RunQueue.insert`).  Mirror of `preemptCurrentOnCore_preserves_runQueueOnCore_wellFormed`. -/
theorem preemptCurrentOnCore_preserves_runQueueUniqueOnCore_self (st : SystemState)
    (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hN : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c).toList.Nodup := by
  unfold preemptCurrentOnCore
  split
  · exact hN
  · split
    · exact hN
    · split
      · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.insert_preserves_toList_nodup _ _ _ hN
      · exact hN

/-- WS-SM SM5.I: the register-bank-and-Nodup-extended structural per-core
invariant — the five `…Reg` conjuncts plus `runQueueUniqueOnCore`. -/
def schedulerInvariantStructuralRegNodup_perCore (st : SystemState) (c : CoreId) : Prop :=
  schedulerInvariantStructuralReg_perCore st c ∧ runQueueUniqueOnCore st.scheduler c

/-- WS-SM SM5.I: the system-wide Nodup-extended structural SMP invariant. -/
def schedulerInvariantStructuralRegNodup_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariantStructuralRegNodup_perCore st c

theorem schedulerInvariantStructuralRegNodup_perCore_to_reg
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructuralRegNodup_perCore st c) :
    schedulerInvariantStructuralReg_perCore st c := h.1

theorem schedulerInvariantStructuralRegNodup_perCore_to_runQueueUnique
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructuralRegNodup_perCore st c) :
    runQueueUniqueOnCore st.scheduler c := h.2

theorem schedulerInvariantStructuralRegNodup_smp_to_reg {st : SystemState}
    (h : schedulerInvariantStructuralRegNodup_smp st) : schedulerInvariantStructuralReg_smp st :=
  fun c => (h c).1

/-- The full SM4.C per-core aggregate implies the Nodup-extended structural
invariant (its `runQueueUniqueOnCore` conjunct is the 6th here). -/
theorem schedulerInvariant_perCore_to_structuralRegNodup {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : schedulerInvariantStructuralRegNodup_perCore st c :=
  ⟨schedulerInvariant_perCore_to_structuralReg h, schedulerInvariant_perCore_to_runQueueUnique h⟩

theorem schedulerInvariant_smp_to_structuralRegNodup {st : SystemState}
    (h : schedulerInvariant_smp st) : schedulerInvariantStructuralRegNodup_smp st :=
  fun c => schedulerInvariant_perCore_to_structuralRegNodup (h c)

/-- WS-SM SM5.I: the freshly-booted system satisfies the Nodup-extended structural
SMP invariant on every core. -/
theorem default_schedulerInvariantStructuralRegNodup_smp :
    schedulerInvariantStructuralRegNodup_smp (default : SystemState) :=
  fun c => schedulerInvariant_perCore_to_structuralRegNodup (default_schedulerInvariant_perCore c)

/-- WS-SM SM5.I: lift a register-bank-extended SMP preservation plus a system-wide
`runQueueUniqueOnCore` proof into the Nodup-extended invariant. -/
theorem schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup {st' : SystemState}
    (hReg : schedulerInvariantStructuralReg_smp st')
    (hN : ∀ c, runQueueUniqueOnCore st'.scheduler c) :
    schedulerInvariantStructuralRegNodup_smp st' :=
  fun c => ⟨hReg c, hN c⟩

/-- WS-SM SM5.I: discharge system-wide `runQueueUniqueOnCore` from the operated
core's preservation and the sibling-core run-queue frame. -/
theorem runQueueUniqueOnCore_smp_of_operated_and_frame
    {st st' : SystemState} {c₀ : CoreId}
    (hPre : ∀ c, runQueueUniqueOnCore st.scheduler c)
    (hC0 : runQueueUniqueOnCore st'.scheduler c₀)
    (hFrame : ∀ c', c₀ ≠ c' →
      st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c') :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := by
  intro c
  by_cases hc : c₀ = c
  · subst hc; exact hC0
  · exact (runQueueUniqueOnCore_frame (hFrame c hc)).mpr (hPre c)

-- Per-transition Nodup-extended preservation.

theorem advanceDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (advanceDomainOnCore st c₀) := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (advanceDomainOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ (fun c => (hPre c).1)) ?_
  intro c
  exact (runQueueUniqueOnCore_frame (advanceDomainOnCore_runQueueOnCore st c₀ c)).mpr (hPre c).2

theorem replenishOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (replenishOnCore st c₀ scId eligibleAt) := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (replenishOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ scId eligibleAt
      (fun c => (hPre c).1)) ?_
  intro c
  exact (runQueueUniqueOnCore_frame (replenishOnCore_runQueueOnCore st c₀ c scId eligibleAt)).mpr (hPre c).2

theorem decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (decrementDomainTimeOnCore st c₀) := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀
      (fun c => (hPre c).1)) ?_
  intro c
  exact (runQueueUniqueOnCore_frame
    (decrementDomainTimeOnCore_runQueueOnCore st c₀ c)).mpr (hPre c).2

theorem enqueueRunnableOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c₀ ≠ some tid)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (enqueueRunnableOnCore st c₀ tid) := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ tid hInv hNotCur
      (fun c => (hPre c).1)) ?_
  refine runQueueUniqueOnCore_smp_of_operated_and_frame (c₀ := c₀) (fun c => (hPre c).2) ?_
    (fun c' hc => enqueueRunnableOnCore_runQueueOnCore_ne st c₀ c' tid hc)
  -- operated core: the wake is a `RunQueue.insert`.
  unfold runQueueUniqueOnCore
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]; exact (hPre c₀).2
  | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb]
      split
      · exact (hPre c₀).2
      · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.insert_preserves_toList_nodup _ _ _ (hPre c₀).2

theorem wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (wakeThread st tid executingCore).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    st (determineTargetCore st tid) tid hInv hNotCur hPre

theorem scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ st' hInv
      (fun c => (hPre c).1) hStep) ?_
  refine runQueueUniqueOnCore_smp_of_operated_and_frame (c₀ := c₀) (fun c => (hPre c).2) ?_
    (fun c' hc => (scheduleEffectiveOnCore_independent_of_other_core st c₀ c' st' hc hStep).2)
  -- operated core: dispatch dequeues (`remove`), idle case is the idle fallback.
  unfold runQueueUniqueOnCore
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c₀ with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      apply idleFallbackOnCore_preserves_runQueueUniqueOnCore_self
      rw [saveOutgoingContextOnCore_scheduler_eq]; exact (hPre c₀).2
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [saveOutgoingContextOnCore_scheduler_eq]
          exact RunQueue.remove_preserves_toList_nodup _ tid (hPre c₀).2
        · simp at hStep

theorem scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (hStep : scheduleOrIdleOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp st c₀ st' hInv hPre hStep

theorem switchToThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ tid st' hInv
      (fun c => (hPre c).1) h) ?_
  refine runQueueUniqueOnCore_smp_of_operated_and_frame (c₀ := c₀) (fun c => (hPre c).2) ?_
    (fun c' hc => (switchToThreadOnCore_independent_of_other_core st c₀ c' tid st' hc h).2)
  -- operated core: preempt re-enqueue (`insert`) then dequeue (`remove`).
  unfold runQueueUniqueOnCore
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c₀ = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
        restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact RunQueue.remove_preserves_toList_nodup _ tid
        (preemptCurrentOnCore_preserves_runQueueUniqueOnCore_self st c₀ tid (hPre c₀).2)
    · rw [if_neg hAff] at h; simp at h

theorem handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (h : handleRescheduleSgiOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact hPre
  · split at h
    · exact switchToThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
        st c₀ _ st' hInv hPre h
    · rw [Except.ok.injEq] at h; subst h; exact hPre

theorem enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt)
    (hNotCurAny : ∀ c', st.scheduler.currentOnCore c' ≠ some (idleThreadId c₀))
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (enqueueIdleThreadOnCore st c₀) := by
  refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
    (enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ hInv hNotCurAny
      (fun c => (hPre c).1)) ?_
  refine runQueueUniqueOnCore_smp_of_operated_and_frame (c₀ := c₀) (fun c => (hPre c).2) ?_
    (fun c' hc => enqueueIdleThreadOnCore_runQueueOnCore_ne st c₀ c' hc)
  -- operated core: the enqueue rebuckets idle (`remove` then `insert`).
  unfold runQueueUniqueOnCore
  rw [enqueueIdleThreadOnCore_runQueueOnCore_self]
  exact RunQueue.insert_preserves_toList_nodup _ _ _
    (RunQueue.remove_preserves_toList_nodup _ _ (hPre c₀).2)

-- ============================================================================
-- §8  Composite live-tick transition preservation (SM5.I.8 completion)
--
-- The 10 primitive per-core transitions above are proved to preserve the base
-- safety invariant (`schedulerInvariantStructuralRegNodup`).  This section adds
-- the THREE *composite* transitions the live `perCoreTimerTickEntry` driver
-- actually runs: `switchDomainOnCore`, `scheduleDomainOnCore` (domain-boundary
-- tick) and `timerTickOnCore` (per-core CNTP tick).  Without these, "preservation
-- by every transition" (SM5.I.8) literally excludes the transitions the running
-- kernel executes.
--
-- `switchDomainOnCore` / `scheduleDomainOnCore` are single-core (the engine
-- applies via sibling framing).  `timerTickOnCore` is genuinely multi-core (its
-- CBS replenish-wake can `wakeThread` onto a *remote* core), so it threads the
-- `wakeThread` preservation through the replenishment fold rather than framing
-- siblings (handled in §8.3).
-- ============================================================================

-- ── §8.1  `switchDomainOnCore` frame + characterisation helpers ──

/-- `switchDomainOnCore` on core `c` frames a sibling core `c'`'s run queue. -/
theorem switchDomainOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (st' : SystemState) (hc : c ≠ c') (h : switchDomainOnCore st c = .ok st') :
    st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      simp only [SchedulerState.setDomainScheduleIndexOnCore_runQueueOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_runQueueOnCore,
        SchedulerState.setActiveDomainOnCore_runQueueOnCore,
        SchedulerState.setCurrentOnCore_runQueueOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]

/-- `switchDomainOnCore` on core `c` frames a sibling core `c'`'s current thread. -/
theorem switchDomainOnCore_currentOnCore_ne (st : SystemState) (c c' : CoreId)
    (st' : SystemState) (hc : c ≠ c') (h : switchDomainOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      simp only [SchedulerState.setDomainScheduleIndexOnCore_currentOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_currentOnCore,
        SchedulerState.setActiveDomainOnCore_currentOnCore,
        SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hc,
        SchedulerState.setRunQueueOnCore_currentOnCore]

/-- `switchDomainOnCore` preserves TCB-resolvability of every thread (its only
object write is the outgoing-context save, which keeps the outgoing thread a
TCB). -/
theorem switchDomainOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt) (h : switchDomainOnCore st c = .ok st') :
    ∀ tid, (st.getTcb? tid).isSome → (st'.getTcb? tid).isSome := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; exact fun _ hh => hh
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      intro tid hSome
      have : ∃ t, (saveOutgoingContextOnCore st c).getTcb? tid = some t :=
        saveOutgoingContextOnCore_getTcb?_isSome st c tid hInv
          (Option.isSome_iff_exists.mp hSome)
      exact Option.isSome_iff_exists.mpr this

/-- The operated core is **idle** (no current thread) after `switchDomainOnCore`
on a non-empty domain schedule — it sets `current := none` before re-dispatch.
The current-dependent base conjuncts (`queueCurrentConsistent`,
`currentThreadValid`, `contextMatchesCurrent`) are thereby vacuous on `c`. -/
theorem switchDomainOnCore_operated_currentOnCore_none (st : SystemState) (c : CoreId)
    (st' : SystemState) (h : switchDomainOnCore st c = .ok st')
    (hSched : st.scheduler.domainSchedule ≠ []) :
    st'.scheduler.currentOnCore c = none :=
  switchDomainOnCore_sets_currentOnCore_none st c st' h hSched

/-- The operated core's run queue after `switchDomainOnCore` is well-formed,
duplicate-free, and all-TCB whenever the pre-state base safety invariant held on
`c`: the only change is re-enqueuing the (TCB) current thread, which `RunQueue.insert`
preserves; all members stay TCBs across the outgoing-context save. -/
theorem switchDomainOnCore_operated_runQueue_props (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt) (h : switchDomainOnCore st c = .ok st')
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hPre : schedulerInvariantStructuralRegNodup_perCore st c) :
    (st'.scheduler.runQueueOnCore c).wellFormed ∧
      (st'.scheduler.runQueueOnCore c).toList.Nodup ∧
      runnableThreadsAreTCBsOnCore st' c := by
  -- Pre-state base conjuncts on `c`.
  obtain ⟨⟨⟨_hQCC, _hCTV, hRAT, hWf⟩, _hCtx⟩, hNodup⟩ := hPre
  -- TCB preservation across the step (derived from the *original* `h` before it
  -- is consumed by the unfold/subst below).
  have hgoal : ∀ tid, (st.getTcb? tid).isSome = true → ∃ tcb, st'.getTcb? tid = some tcb :=
    fun tid hh =>
      Option.isSome_iff_exists.mp (switchDomainOnCore_getTcb?_isSome st c st' hInv h tid hh)
  -- Unfold once and reduce per-conjunct.
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => exact absurd hcase hSched
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, ?_, ?_⟩
      · -- wellFormed
        simp only [SchedulerState.setDomainScheduleIndexOnCore_runQueueOnCore,
          SchedulerState.setDomainTimeRemainingOnCore_runQueueOnCore,
          SchedulerState.setActiveDomainOnCore_runQueueOnCore,
          SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        split
        · exact hWf
        · split
          · exact RunQueue.insert_preserves_wellFormed _ hWf _ _
          · exact hWf
      · -- Nodup
        simp only [SchedulerState.setDomainScheduleIndexOnCore_runQueueOnCore,
          SchedulerState.setDomainTimeRemainingOnCore_runQueueOnCore,
          SchedulerState.setActiveDomainOnCore_runQueueOnCore,
          SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        split
        · exact hNodup
        · split
          · exact RunQueue.insert_preserves_toList_nodup _ _ _ hNodup
          · exact hNodup
      · -- runnableThreadsAreTCBs on the post state
        intro tid htid
        simp only [SchedulerState.setDomainScheduleIndexOnCore_runQueueOnCore,
          SchedulerState.setDomainTimeRemainingOnCore_runQueueOnCore,
          SchedulerState.setActiveDomainOnCore_runQueueOnCore,
          SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at htid
        cases hcur : st.scheduler.currentOnCore c with
        | none =>
            simp only [hcur] at htid
            obtain ⟨tcb, htcb⟩ := hRAT tid htid
            exact hgoal tid (by rw [htcb]; rfl)
        | some tid0 =>
            simp only [hcur] at htid
            cases htcb0 : st.getTcb? tid0 with
            | none =>
                simp only [htcb0] at htid
                obtain ⟨tcb, htcb⟩ := hRAT tid htid
                exact hgoal tid (by rw [htcb]; rfl)
            | some tcb0 =>
                simp only [htcb0] at htid
                rcases (RunQueue.mem_insert _ tid0 _ tid).mp
                    ((RunQueue.mem_toList_iff_mem _ tid).mp htid) with hold | heq
                · obtain ⟨tcb, htcb⟩ := hRAT tid ((RunQueue.mem_toList_iff_mem _ tid).mpr hold)
                  exact hgoal tid (by rw [htcb]; rfl)
                · subst heq
                  exact hgoal tid (by rw [htcb0]; rfl)

/-- `switchDomainOnCore` leaves the machine register banks unchanged (its only
object write is the outgoing-context save, which reads `regsOnCore c₀` and writes
a TCB; it never writes `machine.coreRegs`). -/
theorem switchDomainOnCore_machine_eq (st : SystemState) (c : CoreId)
    (st' : SystemState) (h : switchDomainOnCore st c = .ok st') :
    st'.machine = st.machine := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      exact saveOutgoingContextOnCore_machine st c

/-- `switchDomainOnCore`'s only `registerContext` write is the outgoing-context
save: a thread's saved context is left unchanged, or — when it is core `c₀`'s
outgoing current — set to `regsOnCore c₀`.  (Lifts `saveOutgoingContextOnCore_getTcb?_regContext`
through the scheduler-only record update.) -/
theorem switchDomainOnCore_getTcb?_regContext (st : SystemState) (c₀ : CoreId)
    (st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (h : switchDomainOnCore st c₀ = .ok st') (htcb : st.getTcb? tid = some tcb) :
    ∃ tcb', st'.getTcb? tid = some tcb' ∧
      (tcb'.registerContext = tcb.registerContext ∨
        (st.scheduler.currentOnCore c₀ = some tid ∧
          tcb'.registerContext = st.machine.regsOnCore c₀)) := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; exact ⟨tcb, htcb, Or.inl rfl⟩
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      exact saveOutgoingContextOnCore_getTcb?_regContext st c₀ tid tcb hInv htcb

/-- `switchDomainOnCore` on core `c₀` preserves `contextMatchesCurrentOnCore` on a
*sibling* core `c'`: its current pointer is framed, its register bank is
unchanged, and the only saved-context write `==`-matches via the operated core's
own `contextMatchesCurrent` (the pathological "current on two cores" case is
closed by `RegisterFile` partial-equivalence). -/
theorem switchDomainOnCore_preserves_contextMatchesCurrentOnCore_sibling
    (st : SystemState) (c₀ c' : CoreId) (st' : SystemState) (hc : c₀ ≠ c')
    (hInv : st.objects.invExt)
    (hValid : currentThreadValidOnCore st c')
    (hCtx0 : contextMatchesCurrentOnCore st c₀)
    (hCtx' : contextMatchesCurrentOnCore st c')
    (h : switchDomainOnCore st c₀ = .ok st') :
    contextMatchesCurrentOnCore st' c' := by
  refine contextMatchesCurrentOnCore_frame_at
    (switchDomainOnCore_currentOnCore_ne st c₀ c' st' hc h) ?_ ?_ hValid hCtx'
  · rw [switchDomainOnCore_machine_eq st c₀ st' h]
  · intro tid tcb hcur' htcb
    obtain ⟨tcb', htcb', hrc⟩ :=
      switchDomainOnCore_getTcb?_regContext st c₀ st' tid tcb hInv h htcb
    refine ⟨tcb', htcb', ?_⟩
    rcases hrc with hEq | ⟨hcur0, hEq⟩
    · rw [hEq]; exact RegisterFile.beq_self _
    · rw [hEq]
      simp only [contextMatchesCurrentOnCore, hcur0, htcb] at hCtx0
      exact RegisterFile.beq_symm hCtx0

/-- WS-SM SM5.I.8 (composite, single-core): the per-core **domain switch** — the
boundary half of the live domain tick — preserves the base safety invariant on
every core.  Single-domain mode (`domainSchedule = []`) is a no-op; otherwise the
operated core becomes idle (current `none`) with its current thread re-enqueued,
and every sibling is framed. -/
theorem switchDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (h : switchDomainOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' := by
  by_cases hDS : st.scheduler.domainSchedule = []
  · -- single-domain: `switchDomainOnCore` is the identity.
    have heq : st' = st := by
      unfold switchDomainOnCore at h
      rw [hDS] at h; simp only [Except.ok.injEq] at h; exact h.symm
    subst heq; exact hPre
  · -- rotate path.
    have hCurNone := switchDomainOnCore_sets_currentOnCore_none st c₀ st' h hDS
    obtain ⟨hWf', hNodup', hRAT'⟩ :=
      switchDomainOnCore_operated_runQueue_props st c₀ st' hInv h hDS (hPre c₀)
    have hFrameCur := fun c' (hc : c₀ ≠ c') =>
      switchDomainOnCore_currentOnCore_ne st c₀ c' st' hc h
    have hFrameRQ := fun c' (hc : c₀ ≠ c') =>
      switchDomainOnCore_runQueueOnCore_ne st c₀ c' st' hc h
    have hTcbSome := switchDomainOnCore_getTcb?_isSome st c₀ st' hInv h
    -- operated-core structural establishment (current = none).
    have hC0Struct : schedulerInvariantStructural_perCore st' c₀ := by
      refine ⟨?_, ?_, hRAT', hWf'⟩
      · simp only [queueCurrentConsistentOnCore, hCurNone]
      · simp only [currentThreadValidOnCore, hCurNone]
    have hBase : schedulerInvariantStructural_smp st' :=
      schedulerInvariantStructural_smp_of_establish_and_frame
        (fun c => (hPre c).1.1) hC0Struct hFrameCur hFrameRQ hTcbSome
    -- contextMatchesCurrent on every core.
    have hCtx : ∀ c', contextMatchesCurrentOnCore st' c' := by
      intro c'
      by_cases hc : c₀ = c'
      · subst hc; simp only [contextMatchesCurrentOnCore, hCurNone]
      · exact switchDomainOnCore_preserves_contextMatchesCurrentOnCore_sibling
          st c₀ c' st' hc hInv ((hPre c').1.1.2.1) ((hPre c₀).1.2) ((hPre c').1.2) h
    refine schedulerInvariantStructuralRegNodup_smp_of_reg_and_nodup
      (schedulerInvariantStructuralReg_smp_of_base_and_ctx hBase hCtx) ?_
    refine runQueueUniqueOnCore_smp_of_operated_and_frame (c₀ := c₀)
      (fun c => (hPre c).2) hNodup' (fun c' hc => hFrameRQ c' hc)

/-- WS-SM SM5.I.8 (composite, single-core): the per-core **domain tick** preserves
the base safety invariant on every core.  At a domain boundary it composes the
domain switch with the budget-aware re-dispatch (`scheduleEffectiveOnCore`); off a
boundary it is the pure domain-time decrement. -/
theorem scheduleDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (h : scheduleDomainOnCore st c₀ = .ok st') :
    schedulerInvariantStructuralRegNodup_smp st' := by
  unfold scheduleDomainOnCore at h
  split at h
  · -- domain boundary: switch then re-dispatch.
    cases hsw : switchDomainOnCore st c₀ with
    | error e => rw [hsw] at h; simp at h
    | ok stMid =>
        rw [hsw] at h
        have hMid := switchDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
          st c₀ stMid hInv hPre hsw
        have hMidInv := switchDomainOnCore_preserves_objects_invExt st c₀ stMid hInv hsw
        exact scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
          stMid c₀ st' hMidInv hMid h
  · -- non-boundary: pure domain-time decrement.
    simp only [Except.ok.injEq] at h; subst h
    exact decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralRegNodup_smp st c₀ hPre

-- ── §8.3  `timerTickOnCore` base preservation (the genuinely multi-core tick) ──
--
-- Unlike the domain composites, `timerTickOnCore`'s CBS replenishment fold can
-- `wakeThread` onto a *remote* core, so it threads the per-step `wakeThread`
-- preservation through the fold rather than framing siblings.  Phases:
--   (0) clear `lastTimeoutErrors` on `c`  — pure scheduler frame
--   (1) `processReplenishmentsDueOnCore` — fold of `refillSchedContext` + wakes
--   (2) `timerTickBudgetOnCore` (+ `scheduleEffectiveOnCore` on preempt)

/-- `refillSchedContext` leaves every thread's `getTcb?` unchanged — its only
write replaces a `.schedContext` at `scId`, which `getTcb?` never reads. -/
theorem refillSchedContext_getTcb?_eq (st : SystemState) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) :
    (refillSchedContext st scId now).getTcb? tid = st.getTcb? tid := by
  unfold refillSchedContext
  split
  · rename_i sc hsc
    exact getTcb?_insert_schedContext_eq st _ scId sc _ hInv
      (by rw [← RHTable_getElem?_eq_get?]; exact hsc) rfl tid
  · rfl

/-- WS-SM SM5.I.8 (tick phase 1 atom): `refillSchedContext` preserves the base
safety invariant on every core — it touches only a SchedContext, leaving the
scheduler, the register banks, and every `getTcb?` unchanged. -/
theorem refillSchedContext_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (refillSchedContext st scId now) := by
  have hsch := refillSchedContext_scheduler_eq st scId now
  have hmac := refillSchedContext_machine_eq st scId now
  have hgt := fun tid => refillSchedContext_getTcb?_eq st scId now hInv tid
  intro c
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c).1.1
    · rw [hsch]
    · rw [hsch]
    · intro tid hh; rw [hgt tid]; exact hh
  · refine contextMatchesCurrentOnCore_frame_at ?_ ?_ ?_ ((hPre c).1.1.2.1) ((hPre c).1.2)
    · rw [hsch]
    · rw [hmac]
    · intro tid tcb _hcur htcb
      exact ⟨tcb, by rw [hgt tid]; exact htcb, RegisterFile.beq_self _⟩
  · exact (runQueueUniqueOnCore_frame (by rw [hsch])).mpr (hPre c).2

/-- From a failed single-placement guard: a thread not running on *any* core is
not the current thread of *any* core (in particular its wake target). -/
theorem currentOnCore_ne_of_not_runningOnSomeCore {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runningOnSomeCore st tid = false) (c : CoreId) :
    st.scheduler.currentOnCore c ≠ some tid := by
  intro hc
  have hrun : runningOnSomeCore st tid = true := by
    unfold runningOnSomeCore
    rw [List.any_eq_true]
    exact ⟨c, List.mem_finRange c, by simp [hc]⟩
  rw [hrun] at h; exact absurd h (by simp)

/-- WS-SM SM5.I.8 (tick phase 1 step): one CBS replenishment step preserves the
base safety invariant — `refillSchedContext` preserves it (phase-1 atom) and the
optional cross-core `wakeThread` preserves it (the per-step single-placement
guard discharges `wakeThread`'s no-self-current precondition). -/
theorem processOneReplenishmentOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp
      (processOneReplenishmentOnCore st execCore scId now).1 := by
  have hRefillPre := refillSchedContext_preserves_schedulerInvariantStructuralRegNodup_smp
    st scId now hInv hPre
  have hRefillInv := refillSchedContext_preserves_objects_invExt st scId now hInv
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · exact hRefillPre
    · rename_i tid _hwt hr
      exact wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp
        (refillSchedContext st scId now) tid execCore hRefillInv
        (currentOnCore_ne_of_not_runningOnSomeCore (by simpa using hr) _) hRefillPre
  · exact hRefillPre

/-- WS-SM SM5.I.8 (tick phase 1 fold): the CBS replenishment fold preserves the
base safety invariant (and `objects.invExt`), by induction over the due list —
each step is `processOneReplenishmentOnCore`. -/
theorem foldl_processOneReplenishment_preserves (c : CoreId) (now : Nat)
    (dueIds : List SeLe4n.SchedContextId) :
    ∀ acc : SystemState × List (CoreId × Concurrency.SgiKind),
      acc.1.objects.invExt → schedulerInvariantStructuralRegNodup_smp acc.1 →
      ((dueIds.foldl (fun acc scId =>
          let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
          (s, acc.2 ++ sgi?.toList)) acc).1.objects.invExt ∧
        schedulerInvariantStructuralRegNodup_smp
          (dueIds.foldl (fun acc scId =>
            let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
            (s, acc.2 ++ sgi?.toList)) acc).1) := by
  induction dueIds with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons hd tl ih =>
      intro acc h1 h2
      refine ih _ ?_ ?_
      · exact processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now h1
      · exact processOneReplenishmentOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
          acc.1 c hd now h1 h2

/-- WS-SM SM5.I.8 (tick phase 1): `processReplenishmentsDueOnCore` preserves the
base safety invariant on every core. -/
theorem processReplenishmentsDueOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (processReplenishmentsDueOnCore st c now).1 := by
  simp only [processReplenishmentsDueOnCore]
  refine (foldl_processOneReplenishment_preserves c now _ _ ?_ ?_).2
  · exact hInv
  · intro c'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine schedulerInvariantStructural_perCore_frame ?_ ?_ (fun _ hh => hh) (hPre c').1.1
      · simp only [SchedulerState.setReplenishQueueOnCore_currentOnCore]
      · simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore]
    · refine contextMatchesCurrentOnCore_frame_at ?_ rfl
        (fun tid tcb _ htcb => ⟨tcb, htcb, RegisterFile.beq_self _⟩) ((hPre c').1.1.2.1) ((hPre c').1.2)
      · simp only [SchedulerState.setReplenishQueueOnCore_currentOnCore]
    · exact (runQueueUniqueOnCore_frame
        (by simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore])).mpr (hPre c').2

-- ── §8.3b  The IPC timeout-path base preservation (ensureRunnable / timeoutThread
--           / timeoutBlockedThreads), feeding the budget phase of the tick ──

/-- WS-SM SM5.I.8 (timeout atom): `ensureRunnable` preserves the base safety
invariant on every core, given the enqueued thread is not the boot core's current
thread (so the boot `queueCurrentConsistent` survives the insert).  `ensureRunnable`
writes only the boot run queue (objects unchanged), so siblings frame and boot
takes a `RunQueue.insert`. -/
theorem ensureRunnable_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore bootCoreId ≠ some tid)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (ensureRunnable st tid) := by
  unfold ensureRunnable
  split
  · exact hPre
  · split
    · rename_i tcb htcb
      intro c'
      by_cases hc : c' = bootCoreId
      · subst hc
        obtain ⟨⟨⟨hQCC, hCTV, hRAT, hWf⟩, hCtx⟩, hNod⟩ := hPre bootCoreId
        refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · -- queueCurrentConsistent on boot: current ∉ (oldRq.insert tid)
          simp only [queueCurrentConsistentOnCore,
            SchedulerState.setRunQueueOnCore_currentOnCore,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          simp only [queueCurrentConsistentOnCore] at hQCC
          cases hcur : st.scheduler.currentOnCore bootCoreId with
          | none => exact trivial
          | some t =>
              rw [hcur] at hQCC
              intro hmem
              rcases (RunQueue.mem_insert _ tid _ t).mp
                ((RunQueue.mem_toList_iff_mem _ t).mp hmem) with hold | heq
              · exact hQCC ((RunQueue.mem_toList_iff_mem _ t).mpr hold)
              · exact hNotCur (by rw [hcur, heq])
        · -- currentThreadValid: current + objects unchanged
          simp only [currentThreadValidOnCore, SchedulerState.setRunQueueOnCore_currentOnCore]
          exact hCTV
        · -- runnableThreadsAreTCBs: members are old TCBs ∪ {tid}, objects unchanged
          intro t hmem
          simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hmem
          rcases (RunQueue.mem_insert _ tid _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hmem) with hold | heq
          · exact hRAT t ((RunQueue.mem_toList_iff_mem _ t).mpr hold)
          · exact ⟨tcb, by rw [heq]; exact htcb⟩
        · -- runQueueWellFormed: insert preserves
          simp only [runQueueOnCoreWellFormed, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.insert_preserves_wellFormed _ hWf _ _
        · -- contextMatches: current + regs + objects unchanged
          refine contextMatchesCurrentOnCore_frame_at ?_ rfl
            (fun t tcb' _ ht => ⟨tcb', ht, RegisterFile.beq_self _⟩) hCTV hCtx
          simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
        · -- Nodup: insert preserves
          simp only [runQueueUniqueOnCore, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.insert_preserves_toList_nodup _ _ _ hNod
      · -- sibling c' ≠ boot: run queue + current framed, objects unchanged
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c').1.1
          · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
          · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc)]
          · exact fun _ hh => hh
        · refine contextMatchesCurrentOnCore_frame_at ?_ rfl
            (fun t tcb' _ ht => ⟨tcb', ht, RegisterFile.beq_self _⟩) ((hPre c').1.1.2.1) ((hPre c').1.2)
          · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
        · exact (runQueueUniqueOnCore_frame
            (by simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc)])).mpr
            (hPre c').2
    · exact hPre

/-- WS-SM SM5.I.8 (reusable object atom): inserting a TCB whose `registerContext`
equals the displaced TCB's at the same key preserves the base safety invariant.
The scheduler and register banks are untouched (objects-only write); `getTcb?`
stays resolvable everywhere and the current thread's saved context is unchanged,
so `contextMatchesCurrent` survives.  Used by `updatePipBoost` (pipBoost write)
and `timeoutThread` (`storeObject` of the unblocked TCB). -/
theorem objects_insert_tcb_sameReg_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb tcb' : TCB) (hInv : st.objects.invExt)
    (hOld : st.getTcb? tid = some tcb)
    (hReg : tcb'.registerContext = tcb.registerContext)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp
      { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } := by
  -- getTcb? at the inserted key, and the frame for every other key.
  have hself : ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).getTcb? tid = some tcb' := by
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
  have hne : ∀ x : SeLe4n.ThreadId, x ≠ tid → ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).getTcb? x = st.getTcb? x := by
    intro x hx
    have hNe : ¬ (tid.toObjId == x.toObjId) = true := fun h => hx (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq h)).symm
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
  have hSome : ∀ x : SeLe4n.ThreadId, (st.getTcb? x).isSome → (({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).getTcb? x).isSome := by
    intro x hx
    by_cases hEq : x = tid
    · subst hEq; rw [hself]; rfl
    · rw [hne x hEq]; exact hx
  intro c
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine schedulerInvariantStructural_perCore_frame ?_ ?_ hSome (hPre c).1.1
    · rfl
    · rfl
  · refine contextMatchesCurrentOnCore_frame_at ?_ ?_ ?_ ((hPre c).1.1.2.1) ((hPre c).1.2)
    · rfl
    · rfl
    · intro x txcb _hcur htcb
      by_cases hEq : x = tid
      · subst hEq
        rw [hOld] at htcb
        have hxt : txcb = tcb := (Option.some.injEq _ _).mp htcb.symm
        exact ⟨tcb', hself, by rw [hReg, hxt]; exact RegisterFile.beq_self _⟩
      · exact ⟨txcb, by rw [hne x hEq]; exact htcb, RegisterFile.beq_self _⟩
  · exact (runQueueUniqueOnCore_frame (rfl : ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)).mpr (hPre c).2

/-- WS-SM SM5.I.8 (reusable run-queue atom): replacing core `c₀`'s run queue with
a well-formed, duplicate-free, all-TCB queue that excludes `c₀`'s current thread
preserves the base safety invariant.  Objects/registers untouched; siblings frame.
Used by `updatePipBoost`'s priority-bucket migration. -/
theorem setRunQueueOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (c₀ : CoreId) (newRq : SeLe4n.Kernel.RunQueue)
    (hWf : newRq.wellFormed) (hNod : newRq.toList.Nodup)
    (hTcbs : ∀ t : SeLe4n.ThreadId, t ∈ newRq.toList → ∃ tcb, st.getTcb? t = some tcb)
    (hQCC : ∀ t : SeLe4n.ThreadId, st.scheduler.currentOnCore c₀ = some t → t ∉ newRq.toList)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp
      { st with scheduler := st.scheduler.setRunQueueOnCore c₀ newRq } := by
  intro c
  by_cases hc : c₀ = c
  · subst hc
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [queueCurrentConsistentOnCore, SchedulerState.setRunQueueOnCore_currentOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      cases hcur : st.scheduler.currentOnCore c₀ with
      | none => exact trivial
      | some t => exact hQCC t hcur
    · simp only [currentThreadValidOnCore, SchedulerState.setRunQueueOnCore_currentOnCore]
      exact (hPre c₀).1.1.2.1
    · intro tid htid
      simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at htid
      exact hTcbs tid htid
    · simp only [runQueueOnCoreWellFormed, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact hWf
    · refine contextMatchesCurrentOnCore_frame_at ?_ ?_ ?_ ((hPre c₀).1.1.2.1) ((hPre c₀).1.2)
      · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
      · rfl
      · exact fun x t _ ht => ⟨t, ht, RegisterFile.beq_self _⟩
    · simp only [runQueueUniqueOnCore, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact hNod
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine schedulerInvariantStructural_perCore_frame ?_ ?_ ?_ (hPre c).1.1
      · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
      · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]
      · exact fun _ hh => hh
    · refine contextMatchesCurrentOnCore_frame_at ?_ ?_ ?_ ((hPre c).1.1.2.1) ((hPre c).1.2)
      · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]
      · rfl
      · exact fun x t _ ht => ⟨t, ht, RegisterFile.beq_self _⟩
    · exact (runQueueUniqueOnCore_frame
        (by simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc])).mpr
        (hPre c).2

open SeLe4n.Kernel.PriorityInheritance in
/-- WS-SM SM5.I.8 (PIP atom): `updatePipBoost` preserves the base safety invariant
on every core.  Its only object write is the boosted thread's `pipBoost` (same
`registerContext` — atom 1); its only scheduler write is the boot-core priority
rebucket (`remove`+`insert`, membership-preserving — atom 2). -/
theorem updatePipBoost_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (updatePipBoost st tid) := by
  simp only [updatePipBoost]
  split
  · rename_i tcb heq
    have hOld : st.getTcb? tid = some tcb := by simp only [SystemState.getTcb?, heq]
    split
    · exact hPre
    · -- the boost changed: `st' = insert tid {tcb with pipBoost := newBoost}`.
      let tcb' : TCB := { tcb with pipBoost := computeMaxWaiterPriority st tid }
      have hst' : schedulerInvariantStructuralRegNodup_smp
          { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } :=
        objects_insert_tcb_sameReg_preserves_schedulerInvariantStructuralRegNodup_smp
          st tid tcb tcb' hInv hOld rfl hPre
      split
      · -- tid ∈ runQueue boot
        split
        · -- oldPrio ≠ newPrio: rebucket the boot run queue.
          rename_i hmemRq _hprio
          -- getTcb? facts for `st'` (the objects insert).
          have hself : ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).getTcb? tid = some tcb' := by
            simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
          have hne : ∀ x : SeLe4n.ThreadId, x ≠ tid → ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') } : SystemState).getTcb? x = st.getTcb? x := by
            intro x hx
            have hNe : ¬ (tid.toObjId == x.toObjId) = true := fun h => hx (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq h)).symm
            simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
          -- The rebucket: remove tid then re-insert at the new priority.
          refine setRunQueueOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
            { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } bootCoreId _ ?_ ?_ ?_ ?_ hst'
          · exact RunQueue.insert_preserves_wellFormed _
              (RunQueue.remove_preserves_wellFormed _ (hPre bootCoreId).1.1.2.2.2 tid) _ _
          · exact RunQueue.insert_preserves_toList_nodup _ _ _
              (RunQueue.remove_preserves_toList_nodup _ tid (hPre bootCoreId).2)
          · -- members are TCBs
            intro t ht
            rcases (RunQueue.mem_insert _ tid _ t).mp ((RunQueue.mem_toList_iff_mem _ t).mp ht) with hold | heqt
            · -- t ∈ (rq.remove tid): t ∈ rq ∧ t ≠ tid
              rw [RunQueue.mem_remove] at hold
              obtain ⟨hmem, hnetid⟩ := hold
              obtain ⟨tcbt, htcbt⟩ := (hPre bootCoreId).1.1.2.2.1 t
                ((RunQueue.mem_toList_iff_mem _ t).mpr hmem)
              exact ⟨tcbt, by rw [hne t hnetid]; exact htcbt⟩
            · exact ⟨tcb', by rw [heqt]; exact hself⟩
          · -- current ∉ rebucketed queue
            intro t hcur hmem
            have hcur0 : st.scheduler.currentOnCore bootCoreId = some t := hcur
            have hqcc := (hPre bootCoreId).1.1.1
            simp only [queueCurrentConsistentOnCore, hcur0] at hqcc
            rcases (RunQueue.mem_insert _ tid _ t).mp ((RunQueue.mem_toList_iff_mem _ t).mp hmem) with hold | heqt
            · rw [RunQueue.mem_remove] at hold
              exact hqcc ((RunQueue.mem_toList_iff_mem _ t).mpr hold.1)
            · subst heqt; exact absurd ((RunQueue.mem_toList_iff_mem _ t).mpr hmemRq) hqcc
        · exact hst'
      · exact hst'
  · exact hPre

open SeLe4n.Kernel.PriorityInheritance in
/-- WS-SM SM5.I.8 (PIP chain): `revertPriorityInheritance` preserves the base
safety invariant — a fuel-bounded chain of `updatePipBoost`, each step preserving
both the invariant (the atom above) and `objects.invExt`. -/
theorem revertPriorityInheritance_preserves_schedulerInvariantStructuralRegNodup_smp
    (fuel : Nat) : ∀ (st : SystemState) (tid : SeLe4n.ThreadId),
      st.objects.invExt → schedulerInvariantStructuralRegNodup_smp st →
      schedulerInvariantStructuralRegNodup_smp (revertPriorityInheritance st tid fuel) := by
  induction fuel with
  | zero => intro st tid _ hPre; simp only [revertPriorityInheritance]; exact hPre
  | succ fuel' ih =>
    intro st tid hInv hPre
    simp only [revertPriorityInheritance]
    have hst' := updatePipBoost_preserves_schedulerInvariantStructuralRegNodup_smp st tid hInv hPre
    have hInv' := updatePipBoost_preserves_objects_invExt st tid hInv
    split
    · exact ih (updatePipBoost st tid) _ hInv' hst'
    · exact hst'

/-- WS-SM SM5.I.8 (general object atom): any objects-only change that leaves the
scheduler and register banks fixed, keeps every `getTcb?` resolvable, and
preserves the current thread's saved `registerContext`, preserves the base safety
invariant.  Subsumes the TCB-insert atom; reused for `storeObject` and
`endpointQueueRemove`. -/
theorem objects_change_preserves_schedulerInvariantStructuralRegNodup_smp
    (st st' : SystemState)
    (hsch : st'.scheduler = st.scheduler)
    (hmac : st'.machine = st.machine)
    (hSome : ∀ x : SeLe4n.ThreadId, (st.getTcb? x).isSome → (st'.getTcb? x).isSome)
    (hReg : ∀ (x : SeLe4n.ThreadId) (txcb : TCB), st.getTcb? x = some txcb →
       ∃ tcb', st'.getTcb? x = some tcb' ∧ txcb.registerContext = tcb'.registerContext)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp st' := by
  intro c
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine schedulerInvariantStructural_perCore_frame ?_ ?_ hSome (hPre c).1.1
    · rw [hsch]
    · rw [hsch]
  · refine contextMatchesCurrentOnCore_frame_at ?_ ?_ ?_ ((hPre c).1.1.2.1) ((hPre c).1.2)
    · rw [hsch]
    · rw [hmac]
    · intro x txcb _hcur htcb
      obtain ⟨tcb', htcb', hr⟩ := hReg x txcb htcb
      exact ⟨tcb', htcb', by rw [hr]; exact RegisterFile.beq_self _⟩
  · exact (runQueueUniqueOnCore_frame (by rw [hsch])).mpr (hPre c).2

/-- WS-SM SM5.I.8 (timeout atom): `storeObject` of a TCB with the same
`registerContext` preserves the base safety invariant (objects insert + index /
lifecycle changes the invariant never reads; scheduler + machine fixed). -/
theorem storeObject_tcb_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb tcb' : TCB) (st2 : SystemState)
    (hInv : st.objects.invExt) (hOld : st.getTcb? tid = some tcb)
    (hReg : tcb'.registerContext = tcb.registerContext)
    (hStore : storeObject tid.toObjId (.tcb tcb') st = .ok ((), st2))
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp st2 := by
  have hobj : st2.objects = st.objects.insert tid.toObjId (.tcb tcb') := by
    have h := hStore; unfold storeObject at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  refine objects_change_preserves_schedulerInvariantStructuralRegNodup_smp st st2
    (storeObject_scheduler_eq st st2 _ _ hStore) (storeObject_machine_eq st st2 _ _ hStore)
    ?_ ?_ hPre
  · intro x hx
    by_cases hEq : x = tid
    · subst hEq
      simp only [SystemState.getTcb?, hobj, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_self st.objects x.toObjId _ hInv]; rfl
    · have hNe : ¬ (tid.toObjId == x.toObjId) = true := fun h =>
        hEq (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq h)).symm
      simp only [SystemState.getTcb?, hobj, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
      simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx
  · intro x txcb htcb
    by_cases hEq : x = tid
    · subst hEq
      rw [hOld] at htcb
      have hxt : txcb = tcb := (Option.some.injEq _ _).mp htcb.symm
      refine ⟨tcb', ?_, by rw [hReg, hxt]⟩
      simp only [SystemState.getTcb?, hobj, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_self st.objects x.toObjId _ hInv]
    · have hNe : ¬ (tid.toObjId == x.toObjId) = true := fun h =>
        hEq (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq h)).symm
      refine ⟨txcb, ?_, rfl⟩
      simp only [SystemState.getTcb?, hobj, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
      simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using htcb

/-- WS-SM SM5.I.8 (IPC dual-queue atom): a *conditional* TCB link-patch — insert
`.tcb (f o)` at `k` only when `k` already holds a TCB `o` — has a clean get?
characterisation: every slot is unchanged, except the patched TCB key whose value
becomes `.tcb (f o)`.  The patch is self-guarding (it never touches a non-TCB
slot), so it preserves `invExt` and the object kind everywhere.  This is the
building block for `endpointQueueRemove`'s ≤4 conditional inserts. -/
theorem condTcbPatch_get? (objs objs' : RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (hInv : objs.invExt) (k? : Option SeLe4n.ThreadId) (f : TCB → TCB)
    (hNew : objs' = (match k? with
      | none => objs
      | some k => match objs.get? k.toObjId with
        | some (.tcb o) => objs.insert k.toObjId (.tcb (f o))
        | _ => objs)) :
    objs'.invExt ∧ ∀ (a : SeLe4n.ObjId) (obj0 : KernelObject), objs.get? a = some obj0 →
      ∃ obj1, objs'.get? a = some obj1 ∧
        (obj1 = obj0 ∨ ∃ ot, obj0 = .tcb ot ∧ obj1 = .tcb (f ot)) := by
  cases k? with
  | none => subst hNew; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
  | some k =>
    cases hk : objs.get? k.toObjId with
    | none => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
    | some o =>
      cases o with
      | tcb ot =>
        simp only [hNew, hk]
        refine ⟨RobinHood.RHTable.insert_preserves_invExt objs k.toObjId (.tcb (f ot)) hInv, ?_⟩
        intro a obj0 ha
        rw [RHTable_getElem?_insert objs k.toObjId (.tcb (f ot)) hInv a]
        split
        · rename_i hak
          have hka : k.toObjId = a := eq_of_beq hak
          rw [← hka, hk] at ha
          have hobj0 : obj0 = .tcb ot := (Option.some.injEq _ _).mp ha.symm
          exact ⟨.tcb (f ot), rfl, Or.inr ⟨ot, hobj0, rfl⟩⟩
        · exact ⟨obj0, ha, Or.inl rfl⟩
      | endpoint _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
      | notification _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
      | cnode _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
      | vspaceRoot _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
      | untyped _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩
      | schedContext _ => simp only [hNew, hk]; exact ⟨hInv, fun a obj0 ha => ⟨obj0, ha, Or.inl rfl⟩⟩

-- ── §8.3c  endpointQueueRemove → timeoutThread → timeoutBlockedThreads
--           base-safety preservation (the IPC dequeue feeding the budget tick) ──

/-- WS-SM SM5.I.8 (bridge): `endpointQueueRemove`'s `registerContext`-preservation
lifted from the raw object store (`endpointQueueRemove_getTcb_upToReg`) to the
typed `getTcb?` accessor the base-safety invariant reads. -/
theorem endpointQueueRemove_getTcb?_upToReg
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st')
    (x : SeLe4n.ThreadId) (t : TCB) (hx : st.getTcb? x = some t) :
    ∃ t', st'.getTcb? x = some t' ∧ t.registerContext = t'.registerContext := by
  rw [SystemState.getTcb?_eq_some_iff] at hx
  obtain ⟨t', ht', hreg⟩ :=
    endpointQueueRemove_getTcb_upToReg endpointId isReceiveQ tid st st' hInv hStep x.toObjId t hx
  exact ⟨t', by rw [SystemState.getTcb?_eq_some_iff]; exact ht', hreg⟩

/-- WS-SM SM5.I.8 (timeout atom): `endpointQueueRemove` preserves the base safety
invariant.  It writes only the object store (scheduler + register banks framed by
`endpointQueueRemove_scheduler_eq` / `_machine`), and keeps every TCB resolvable
with an unchanged `registerContext` (`endpointQueueRemove_getTcb_upToReg`), so the
generic objects-change atom discharges it. -/
theorem endpointQueueRemove_preserves_schedulerInvariantStructuralRegNodup_smp
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st')
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp st' := by
  refine objects_change_preserves_schedulerInvariantStructuralRegNodup_smp st st'
    (endpointQueueRemove_scheduler_eq endpointId isReceiveQ tid st st' hStep)
    (endpointQueueRemove_machine endpointId isReceiveQ tid st st' hStep)
    ?_ ?_ hPre
  · intro x hx
    cases hgt : st.getTcb? x with
    | none => simp [hgt] at hx
    | some t =>
      obtain ⟨t', ht', _⟩ :=
        endpointQueueRemove_getTcb?_upToReg endpointId isReceiveQ tid st st' hInv hStep x t hgt
      simp [ht']
  · intro x txcb htcb
    exact endpointQueueRemove_getTcb?_upToReg endpointId isReceiveQ tid st st' hInv hStep x txcb htcb

/-- `ensureRunnable` leaves the object store untouched (it writes only the boot
run queue).  Thin local copy — the `Lifecycle.Suspend` original is outside this
module's import closure (mirrors `PerCoreTimerTick`'s `_local` copy). -/
private theorem ensureRunnable_objects_eq_local (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable; split
  · rfl
  · split <;> rfl

open SeLe4n.Kernel.PriorityInheritance in
/-- WS-SM SM5.I.8 (timeout atom): `timeoutThread` preserves the base safety
invariant.  It composes `endpointQueueRemove` (preserves — atom above), the
`storeObject` of the unblocked TCB (same `registerContext`; `ipcState` / state
fields change, which the base invariant never reads), `ensureRunnable` (re-enqueue
of the timed-out thread, which is not the boot core's current thread — `hNotCur`),
and the optional `revertPriorityInheritance` (PIP chain).  `hNotCur` propagates
unchanged across the object writes (neither `endpointQueueRemove` nor `storeObject`
touches the scheduler). -/
theorem timeoutThread_preserves_schedulerInvariantStructuralRegNodup_smp
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore bootCoreId ≠ some tid)
    (hStep : timeoutThread endpointId isReceiveQ tid st = .ok st')
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp st' := by
  unfold timeoutThread at hStep
  split at hStep
  · simp at hStep
  · rename_i st1 hEQR
    have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
    have hPre1 := endpointQueueRemove_preserves_schedulerInvariantStructuralRegNodup_smp
      _ _ _ _ _ hInv hEQR hPre
    have hSch1 := endpointQueueRemove_scheduler_eq _ _ _ _ _ hEQR
    split at hStep
    · simp at hStep
    · rename_i tcb hLook
      have hOld1 : st1.getTcb? tid = some tcb :=
        (SystemState.getTcb?_eq_some_iff st1 tid tcb).mpr (lookupTcb_some_objects st1 tid tcb hLook)
      simp only [] at hStep
      split at hStep
      · simp at hStep
      · rename_i st2 heq
        have hPre2 := by
          refine storeObject_tcb_preserves_schedulerInvariantStructuralRegNodup_smp
            st1 tid tcb _ st2 hInv1 hOld1 ?_ heq hPre1
          rfl
        have hInv2 := storeObject_preserves_objects_invExt st1 st2 tid.toObjId _ hInv1 heq
        have hSch2 := storeObject_scheduler_eq st1 st2 tid.toObjId _ heq
        have hNotCur2 : st2.scheduler.currentOnCore bootCoreId ≠ some tid := by
          rw [hSch2, hSch1]; exact hNotCur
        have hPre3 := ensureRunnable_preserves_schedulerInvariantStructuralRegNodup_smp
          st2 tid hInv2 hNotCur2 hPre2
        have hInv3 : (ensureRunnable st2 tid).objects.invExt := by
          rw [ensureRunnable_objects_eq_local]; exact hInv2
        split at hStep <;>
          · simp only [Except.ok.injEq] at hStep
            subst hStep
            first
              | exact revertPriorityInheritance_preserves_schedulerInvariantStructuralRegNodup_smp
                  _ _ _ hInv3 hPre3
              | exact hPre3

open SeLe4n.Kernel.PriorityInheritance in
/-- WS-SM SM5.I.8 (timeout atom): `timeoutThread` preserves the boot core's
current thread.  Every step leaves `currentOnCore bootCoreId` fixed
(`endpointQueueRemove` / `storeObject` don't touch the scheduler;
`ensureRunnable` and `revertPriorityInheritance` only rebucket the run queue).
This is the invariant the `timeoutBlockedThreads` fold maintains so each step's
timed-out thread stays distinct from the (unchanging) boot current. -/
theorem timeoutThread_currentOnCore_bootCore_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : timeoutThread endpointId isReceiveQ tid st = .ok st') :
    st'.scheduler.currentOnCore bootCoreId = st.scheduler.currentOnCore bootCoreId := by
  unfold timeoutThread at hStep
  split at hStep
  · simp at hStep
  · rename_i st1 hEQR
    have h1 := endpointQueueRemove_scheduler_eq _ _ _ _ _ hEQR
    split at hStep
    · simp at hStep
    · rename_i tcb hLook
      simp only [] at hStep
      split at hStep
      · simp at hStep
      · rename_i st2 heq
        have h2 := storeObject_scheduler_eq _ _ _ _ heq
        split at hStep <;>
          · simp only [Except.ok.injEq] at hStep
            subst hStep
            first
              | rw [revert_preserves_current, ensureRunnable_scheduler_current, h2, h1]
              | rw [ensureRunnable_scheduler_current, h2, h1]

/-- WS-SM SM5.I.8 (timeout atom): `timeoutBlockedThreads` preserves the base
safety invariant.  It folds `timeoutThread` over the SchedContext's blocked
threads; each step preserves the invariant (atom above) provided the timed-out
thread is not the boot core's current thread.  `hNotCur` (the boot current is
not among the SchedContext's indexed threads) supplies that for every step —
it holds because a blocked thread is never the running thread, discharged from
the IPC↔scheduler contract at the integration site. -/
theorem timeoutBlockedThreads_preserves_schedulerInvariantStructuralRegNodup_smp
    (st : SystemState) (scId : SeLe4n.SchedContextId) (hInv : st.objects.invExt)
    (hNotCur : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      t ∉ (st.scThreadIndex[scId]?.getD []))
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (timeoutBlockedThreads st scId).1 := by
  unfold timeoutBlockedThreads
  suffices H : ∀ (L : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError)),
      schedulerInvariantStructuralRegNodup_smp acc.1 →
      acc.1.objects.invExt →
      acc.1.scheduler.currentOnCore bootCoreId = st.scheduler.currentOnCore bootCoreId →
      (∀ t ∈ L, st.scheduler.currentOnCore bootCoreId ≠ some t) →
      schedulerInvariantStructuralRegNodup_smp
        (L.foldl (fun (acc : SystemState × List (SeLe4n.ThreadId × KernelError)) tid =>
          let (st', errs) := acc
          match st'.getTcb? tid with
          | some tcb =>
            match tcbBlockingInfo tcb with
            | some (epId, isReceiveQ) =>
              match timeoutThread epId isReceiveQ tid st' with
              | .ok st'' => (st'', errs)
              | .error e => (st', errs ++ [(tid, e)])
            | none => (st', errs)
          | none => (st', errs)) acc).1 by
    refine H (st.scThreadIndex[scId]?.getD []) (st, []) hPre hInv rfl ?_
    intro t ht hc
    exact hNotCur t hc ht
  intro L
  induction L with
  | nil => intro acc hP _ _ _; exact hP
  | cons hd tl ih =>
    intro acc hP hI hC hN
    rw [List.foldl_cons]
    obtain ⟨st', errs⟩ := acc
    simp only []
    split
    · rename_i tcb _
      rcases hbi : tcbBlockingInfo tcb with _ | ⟨epId, isReceiveQ⟩
      · exact ih _ hP hI hC (fun t ht => hN t (List.mem_cons_of_mem hd ht))
      · dsimp only
        split
        · rename_i st'' heqT
          apply ih
          · exact timeoutThread_preserves_schedulerInvariantStructuralRegNodup_smp
              epId isReceiveQ hd st' st'' hI
              (by rw [hC]; exact hN hd List.mem_cons_self) heqT hP
          · exact timeoutThread_preserves_objects_invExt epId isReceiveQ hd st' st'' hI heqT
          · rw [timeoutThread_currentOnCore_bootCore_eq epId isReceiveQ hd st' st'' heqT]
            exact hC
          · intro t ht; exact hN t (List.mem_cons_of_mem hd ht)
        · exact ih _ hP hI hC (fun t ht => hN t (List.mem_cons_of_mem hd ht))
    · exact ih _ hP hI hC (fun t ht => hN t (List.mem_cons_of_mem hd ht))

-- ════════════════════════════════════════════════════════════════════════════
-- §8.4  Budget-tick discharge — the qcc-free run-queue safety sub-bundle
-- ════════════════════════════════════════════════════════════════════════════
--
-- The capstone's `hBudget*` hypotheses are the three run-queue conjuncts (rat /
-- rqWf / Nodup) of the budget-tick result on core `c`.  `timerTickBudgetOnCore`'s
-- preempt paths RE-ENQUEUE the current thread — breaking `queueCurrentConsistent`
-- (current ∈ run queue) but NOT the three run-queue conjuncts (none read
-- `current`).  This section bundles exactly those three qcc-free conjuncts and
-- proves the budget tick — *including* the budget-exhausted `timeoutBlockedThreads`
-- path (the former SM5.F tracked gap) — preserves them UNCONDITIONALLY (no
-- `hNotCur`), so the capstone needs no budget hypotheses.

/-- WS-SM SM5.I.8: the qcc-free run-queue safety conjuncts on core `c` —
runnable-threads-are-TCBs, run-queue well-formedness, run-queue uniqueness.
These three conjuncts of the base structural invariant never read `current`, so
they survive the budget tick's current-thread re-enqueue (which breaks `qcc`). -/
def runQueueSafetyOnCore (st : SystemState) (c : CoreId) : Prop :=
  runnableThreadsAreTCBsOnCore st c ∧
  runQueueOnCoreWellFormed st.scheduler c ∧
  runQueueUniqueOnCore st.scheduler c

/-- Project the qcc-free run-queue safety bundle out of the full base invariant. -/
theorem schedulerInvariantStructuralRegNodup_perCore_to_runQueueSafety
    {st : SystemState} {c : CoreId} (h : schedulerInvariantStructuralRegNodup_perCore st c) :
    runQueueSafetyOnCore st c :=
  ⟨h.1.1.2.2.1, h.1.1.2.2.2, h.2⟩

/-- WS-SM SM5.I.8 (objects frame): an objects-only change that fixes the scheduler
and keeps every `getTcb?` resolvable preserves the qcc-free run-queue safety
bundle (run queue unchanged ⇒ wellFormed/Nodup; members still resolve ⇒ rat). -/
theorem objects_frame_preserves_runQueueSafetyOnCore (st st' : SystemState) (c : CoreId)
    (hsch : st'.scheduler = st.scheduler)
    (hSome : ∀ x : SeLe4n.ThreadId, (st.getTcb? x).isSome → (st'.getTcb? x).isSome)
    (h : runQueueSafetyOnCore st c) : runQueueSafetyOnCore st' c := by
  obtain ⟨hRat, hWf, hNd⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hsch] at ht
    obtain ⟨tcbt, htcbt⟩ := hRat t ht
    have hs : (st'.getTcb? t).isSome = true := hSome t (by simp [htcbt])
    cases h' : st'.getTcb? t with
    | none => rw [h'] at hs; exact absurd hs (by simp)
    | some tcb' => exact ⟨tcb', rfl⟩
  · show runQueueOnCoreWellFormed st'.scheduler c
    rw [hsch]; exact hWf
  · show runQueueUniqueOnCore st'.scheduler c
    rw [hsch]; exact hNd

/-- WS-SM SM5.I.8 (TCB-insert getTcb? frame): inserting a TCB at `tid` keeps every
`getTcb?` resolvable — `tid` resolves to the inserted TCB; every other key is
unchanged. -/
theorem getTcb?_isSome_insert_tcb (st : SystemState) (tid : SeLe4n.ThreadId) (v : TCB)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) (hx : (st.getTcb? x).isSome) :
    (({ st with objects := st.objects.insert tid.toObjId (.tcb v) } : SystemState).getTcb? x).isSome := by
  by_cases hxt : x = tid
  · rw [hxt]
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
      RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv, Option.isSome_some]
  · have hNe : ¬ (tid.toObjId == x.toObjId) = true :=
      fun hh => hxt (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq hh)).symm
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
    exact hx

/-- WS-SM SM5.I.8 (general run-queue frame): if core `c`'s run queue is unchanged
and every `getTcb?` stays resolvable, the qcc-free run-queue safety bundle on core
`c` is preserved.  The workhorse for the bootCoreId-pinned timeout sub-ops on a
`c ≠ bootCoreId` (the run queue on `c` is framed). -/
theorem runQueue_frame_preserves_runQueueSafetyOnCore (st st' : SystemState) (c : CoreId)
    (hrq : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hSome : ∀ x : SeLe4n.ThreadId, (st.getTcb? x).isSome → (st'.getTcb? x).isSome)
    (h : runQueueSafetyOnCore st c) : runQueueSafetyOnCore st' c := by
  obtain ⟨hRat, hWf, hNd⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hrq] at ht
    obtain ⟨tcbt, htcbt⟩ := hRat t ht
    have hs : (st'.getTcb? t).isSome = true := hSome t (by simp [htcbt])
    cases h' : st'.getTcb? t with
    | none => rw [h'] at hs; exact absurd hs (by simp)
    | some tcb' => exact ⟨tcb', rfl⟩
  · show runQueueOnCoreWellFormed st'.scheduler c
    simp only [runQueueOnCoreWellFormed, hrq]; exact hWf
  · show runQueueUniqueOnCore st'.scheduler c
    simp only [runQueueUniqueOnCore, hrq]; exact hNd

/-- `ensureRunnable` frames core `c`'s run queue when `c ≠ bootCoreId` (it writes
only the boot run queue). -/
theorem ensureRunnable_runQueueOnCore_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (hc : c ≠ bootCoreId) :
    (ensureRunnable st tid).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c := by
  unfold ensureRunnable
  split
  · rfl
  · split
    · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc)]
    · rfl

/-- WS-SM SM5.I.8: `ensureRunnable` preserves the qcc-free run-queue safety bundle
on core `c`.  Objects are untouched (`getTcb?` fixed); on `bootCoreId` the
re-enqueue is an `insert` (preserves wellFormed/Nodup; the inserted thread is a
TCB); on any other core the run queue is framed. -/
theorem ensureRunnable_preserves_runQueueSafetyOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (h : runQueueSafetyOnCore st c) :
    runQueueSafetyOnCore (ensureRunnable st tid) c := by
  by_cases hc : c = bootCoreId
  · subst hc
    unfold ensureRunnable
    split
    · exact h
    · split
      · rename_i tcb htcb
        obtain ⟨hRat, hWf, hNd⟩ := h
        refine ⟨?_, ?_, ?_⟩
        · intro t ht
          simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at ht
          rcases (RunQueue.mem_insert _ tid _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp ht) with hold | heq
          · exact hRat t ((RunQueue.mem_toList_iff_mem _ t).mpr hold)
          · exact ⟨tcb, by rw [heq]; exact htcb⟩
        · show runQueueOnCoreWellFormed _ bootCoreId
          simp only [runQueueOnCoreWellFormed, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.insert_preserves_wellFormed _ hWf _ _
        · show runQueueUniqueOnCore _ bootCoreId
          simp only [runQueueUniqueOnCore, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.insert_preserves_toList_nodup _ _ _ hNd
      · exact h
  · exact runQueue_frame_preserves_runQueueSafetyOnCore st _ c
      (ensureRunnable_runQueueOnCore_ne st tid c hc)
      (fun x hx => by rw [show (ensureRunnable st tid).getTcb? x = st.getTcb? x from by
        unfold SystemState.getTcb?; rw [ensureRunnable_objects_eq_local]]; exact hx) h

-- ── §8.3d  Prepared-phase discharge of the getTcb?-reading conjuncts
--           (`runnableThreadsAreTCBs`) — placed here for `refillSchedContext_getTcb?_eq`. ──

/-- `refillSchedContext` preserves runnable-threads-are-TCBs on every core (it
frames the scheduler and every `getTcb?`). -/
theorem refillSchedContext_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c') :
    runnableThreadsAreTCBsOnCore (refillSchedContext st scId now) c' := by
  intro t ht
  rw [refillSchedContext_scheduler_eq] at ht
  obtain ⟨tcbt, htcbt⟩ := h t ht
  exact ⟨tcbt, by rw [refillSchedContext_getTcb?_eq st scId now hInv]; exact htcbt⟩

/-- `processOneReplenishmentOnCore` preserves runnable-threads-are-TCBs on every
core `c'` (refill frames it; the wake preserves it). -/
theorem processOneReplenishmentOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c') :
    runnableThreadsAreTCBsOnCore (processOneReplenishmentOnCore st execCore scId now).1 c' := by
  have hRefInv : (refillSchedContext st scId now).objects.invExt :=
    refillSchedContext_preserves_objects_invExt st scId now hInv
  have hRef : runnableThreadsAreTCBsOnCore (refillSchedContext st scId now) c' :=
    refillSchedContext_preserves_runnableThreadsAreTCBsOnCore st scId now c' hInv h
  simp only [processOneReplenishmentOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next _hcond =>
      exact wakeThread_preserves_runnableThreadsAreTCBsOnCore (refillSchedContext st scId now)
        tid execCore c' hRefInv hRef
  next _heq => exact hRef

private theorem foldl_processOneReplenishment_preserves_runnableThreadsAreTCBs
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × Concurrency.SgiKind))
    (hInv : acc.1.objects.invExt) (h : runnableThreadsAreTCBsOnCore acc.1 c') :
    runnableThreadsAreTCBsOnCore
      (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1 c' := by
  induction dueIds generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)
        (processOneReplenishmentOnCore_preserves_runnableThreadsAreTCBsOnCore acc.1 c c' hd now hInv h)

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
runnable-threads-are-TCBs on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (processReplenishmentsDueOnCore st c now).1 c := by
  simp only [processReplenishmentsDueOnCore]
  apply foldl_processOneReplenishment_preserves_runnableThreadsAreTCBs
  · exact hInv
  · intro t ht
    simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore] at ht
    exact h t ht

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves
runnable-threads-are-TCBs — discharges the capstone's `hPrepRat`. -/
theorem timerTickOnCorePrepared_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (timerTickOnCorePrepared st c).1 c := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_runnableThreadsAreTCBsOnCore
  · exact hInv
  · intro t ht
    simp only [SchedulerState.setLastTimeoutErrorsOnCore_runQueueOnCore] at ht
    exact h t ht

-- ── §8.3e  Prepared-phase discharge — `contextMatchesCurrentOnCore` (register bank) ──

/-- A wake keeps any pre-state thread resolvable with an unchanged
`registerContext` (it changes only the woken thread's `ipcState`). -/
theorem enqueueRunnableOnCore_getTcb?_upToReg (st : SystemState) (c : CoreId)
    (tid x : SeLe4n.ThreadId) (t : TCB) (hInv : st.objects.invExt)
    (hres : st.getTcb? x = some t) :
    ∃ t', (enqueueRunnableOnCore st c tid).getTcb? x = some t' ∧
      t.registerContext = t'.registerContext := by
  cases hFresh : runnableOnSomeCore st tid with
  | true => rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]; exact ⟨t, hres, rfl⟩
  | false =>
    by_cases hEq : x = tid
    · subst hEq
      exact ⟨_, enqueueRunnableOnCore_makes_ready st c x t hres hInv hFresh, rfl⟩
    · rw [enqueueRunnableOnCore_getTcb?_ne st c tid x hInv hEq]; exact ⟨t, hres, rfl⟩

/-- A wake keeps a non-TCB slot non-resolvable (it cannot turn a non-TCB into a
TCB). -/
theorem enqueueRunnableOnCore_getTcb?_eq_none (st : SystemState) (c : CoreId)
    (tid x : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hres : st.getTcb? x = none) :
    (enqueueRunnableOnCore st c tid).getTcb? x = none := by
  cases hFresh : runnableOnSomeCore st tid with
  | true => rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]; exact hres
  | false =>
    by_cases hEq : x = tid
    · subst hEq; rw [enqueueRunnableOnCore_no_tcb_noop st c x hres]; exact hres
    · rw [enqueueRunnableOnCore_getTcb?_ne st c tid x hInv hEq]; exact hres

/-- WS-SM SM5.I.8 (preservation, SM4.C `contextMatchesCurrentOnCore`): a wake on
core `c` preserves the register-bank match on **every** core `c'` — it writes no
`current` slot and no register bank, and the current thread's `registerContext`
survives (the wake touches only `ipcState`). -/
theorem enqueueRunnableOnCore_preserves_contextMatchesCurrentOnCore_anyCore (st : SystemState)
    (c c' : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c') :
    contextMatchesCurrentOnCore (enqueueRunnableOnCore st c tid) c' := by
  unfold contextMatchesCurrentOnCore at h ⊢
  rw [enqueueRunnableOnCore_currentOnCore st c tid c', enqueueRunnableOnCore_machine_eq]
  cases hCur : st.scheduler.currentOnCore c' with
  | none => exact True.intro
  | some cur =>
    simp only [hCur] at h ⊢
    cases hCurTcb : st.getTcb? cur with
    | none => simp only [enqueueRunnableOnCore_getTcb?_eq_none st c tid cur hInv hCurTcb]
    | some curTcb =>
      simp only [hCurTcb] at h
      obtain ⟨t', ht', hreg⟩ :=
        enqueueRunnableOnCore_getTcb?_upToReg st c tid cur curTcb hInv hCurTcb
      rw [ht']
      show (st.machine.regsOnCore c' == t'.registerContext) = true
      rw [← hreg]; exact h

/-- WS-SM SM5.I.8: a wake preserves the register-bank match on every core `c'`. -/
theorem wakeThread_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore c' : CoreId) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c') :
    contextMatchesCurrentOnCore (wakeThread st tid executingCore).1 c' := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_contextMatchesCurrentOnCore_anyCore st
    (determineTargetCore st tid) c' tid hInv h

/-- `refillSchedContext` preserves the register-bank match (it frames the
scheduler, the machine, and every `getTcb?`). -/
theorem refillSchedContext_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c') :
    contextMatchesCurrentOnCore (refillSchedContext st scId now) c' := by
  unfold contextMatchesCurrentOnCore at h ⊢
  rw [refillSchedContext_scheduler_eq, refillSchedContext_machine_eq]
  cases hCur : st.scheduler.currentOnCore c' with
  | none => exact True.intro
  | some cur =>
    simp only [hCur] at h ⊢
    rw [refillSchedContext_getTcb?_eq st scId now hInv cur]; exact h

/-- `processOneReplenishmentOnCore` preserves the register-bank match on every
core `c'`. -/
theorem processOneReplenishmentOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c') :
    contextMatchesCurrentOnCore (processOneReplenishmentOnCore st execCore scId now).1 c' := by
  have hRefInv : (refillSchedContext st scId now).objects.invExt :=
    refillSchedContext_preserves_objects_invExt st scId now hInv
  have hRef : contextMatchesCurrentOnCore (refillSchedContext st scId now) c' :=
    refillSchedContext_preserves_contextMatchesCurrentOnCore st scId now c' hInv h
  simp only [processOneReplenishmentOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next _hcond =>
      exact wakeThread_preserves_contextMatchesCurrentOnCore (refillSchedContext st scId now)
        tid execCore c' hRefInv hRef
  next _heq => exact hRef

private theorem foldl_processOneReplenishment_preserves_contextMatchesCurrentOnCore
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × Concurrency.SgiKind))
    (hInv : acc.1.objects.invExt) (h : contextMatchesCurrentOnCore acc.1 c') :
    contextMatchesCurrentOnCore
      (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1 c' := by
  induction dueIds generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)
        (processOneReplenishmentOnCore_preserves_contextMatchesCurrentOnCore acc.1 c c' hd now hInv h)

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
the register-bank match on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (processReplenishmentsDueOnCore st c now).1 c := by
  simp only [processReplenishmentsDueOnCore]
  apply foldl_processOneReplenishment_preserves_contextMatchesCurrentOnCore
  · exact hInv
  · simpa only [contextMatchesCurrentOnCore, SchedulerState.setReplenishQueueOnCore_currentOnCore]
      using h

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves the
register-bank match — discharges the capstone's `hPrepCtx`. -/
theorem timerTickOnCorePrepared_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (timerTickOnCorePrepared st c).1 c := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_contextMatchesCurrentOnCore
  · exact hInv
  · simpa only [contextMatchesCurrentOnCore, SchedulerState.setLastTimeoutErrorsOnCore_currentOnCore]
      using h

/-- WS-SM SM5.I.8 (capstone): the per-core timer tick preserves the full
register-bank+Nodup base safety invariant on the operated core `c`, composing the
six per-conjunct `timerTickOnCore_preserves_*` lemmas.  `currentThreadValid` is
unconditional; the other five are supplied their `prepared`-state conjunct
(`hPrep*`) — the prepared (cross-core replenishment-wake) discharge is the SM5
cross-core follow-on — and `wellFormed` / `runnableTCBs` / `Nodup` additionally
take their budget-tick preservation (`hBudget*`), discharged on every clean path by
the `timerTickBudgetOnCore_notPreempted_preserves_*` lemmas; the budget-exhausted
`timeoutBlockedThreads` path is the SM5.F per-core-PIP tracked gap. -/
theorem timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (sgis : List (CoreId × Concurrency.SgiKind))
    (hInv : st.objects.invExt)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hPrepQcc : queueCurrentConsistentOnCore (timerTickOnCorePrepared st c).1.scheduler c)
    (hPrepRat : runnableThreadsAreTCBsOnCore (timerTickOnCorePrepared st c).1 c)
    (hPrepCtx : contextMatchesCurrentOnCore (timerTickOnCorePrepared st c).1 c)
    (hPrepNd : ((timerTickOnCorePrepared st c).1.scheduler.runQueueOnCore c).toList.Nodup)
    (hBudgetRqWf : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       (st3.scheduler.runQueueOnCore c).wellFormed)
    (hBudgetRat : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       runnableThreadsAreTCBsOnCore st3 c)
    (hBudgetNd : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       (st3.scheduler.runQueueOnCore c).toList.Nodup)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    schedulerInvariantStructuralRegNodup_perCore st' c := by
  have hPrepInv := timerTickOnCorePrepared_objects_invExt st c hInv
  exact ⟨⟨⟨timerTickOnCore_preserves_queueCurrentConsistentOnCore st c st' sgis hPrepQcc hStep,
            timerTickOnCore_preserves_currentThreadValidOnCore st c st' sgis hInv hStep,
            timerTickOnCore_preserves_runnableThreadsAreTCBsOnCore st c st' sgis
              hPrepInv hPrepRat hBudgetRat hStep,
            timerTickOnCore_preserves_runQueueOnCoreWellFormed st c st' sgis hwf hBudgetRqWf hStep⟩,
           timerTickOnCore_preserves_contextMatchesCurrentOnCore st c st' sgis
             hPrepInv hPrepCtx hStep⟩,
          timerTickOnCore_preserves_runQueueUniqueOnCore st c st' sgis hPrepNd hBudgetNd hStep⟩

/-- WS-SM SM5.I.8 (capstone, clean form): the per-core timer tick preserves the
full register-bank+Nodup base safety invariant, taking the **bundled pre-state**
invariant `schedulerInvariantStructuralRegNodup_perCore st c` (instead of the four
loose `hPrep*` obligations) and discharging the four prepared-phase obligations
automatically via the prepared-discharge cascade (qcc / Nodup / rat / ctx —
`timerTickOnCorePrepared_preserves_*`).

The three `hBudget*` budget-tick hypotheses remain parameterized — discharged on
every clean (not-preempted) path by the `timerTickBudgetOnCore_notPreempted_preserves_*`
lemmas; the budget-exhausted `timeoutBlockedThreads` re-enqueue path (through the
bootCoreId-pinned `ensureRunnable` / `revertPriorityInheritance`) is the SM5.F
per-core-PIP-migration tracked gap. -/
theorem timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore_of_pre
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (sgis : List (CoreId × Concurrency.SgiKind))
    (hInv : st.objects.invExt)
    (hPre : schedulerInvariantStructuralRegNodup_perCore st c)
    (hBudgetRqWf : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       (st3.scheduler.runQueueOnCore c).wellFormed)
    (hBudgetRat : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       runnableThreadsAreTCBsOnCore st3 c)
    (hBudgetNd : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       (st3.scheduler.runQueueOnCore c).toList.Nodup)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    schedulerInvariantStructuralRegNodup_perCore st' c := by
  obtain ⟨⟨⟨hQcc, _hCtv, hRat, hRqwf⟩, hCtx⟩, hNd⟩ := hPre
  exact timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore
    st c st' sgis hInv hRqwf
    (timerTickOnCorePrepared_preserves_queueCurrentConsistentOnCore st c hQcc)
    (timerTickOnCorePrepared_preserves_runnableThreadsAreTCBsOnCore st c hInv hRat)
    (timerTickOnCorePrepared_preserves_contextMatchesCurrentOnCore st c hInv hCtx)
    (timerTickOnCorePrepared_preserves_runQueueUnique st c hNd)
    hBudgetRqWf hBudgetRat hBudgetNd hStep

end SeLe4n.Kernel
