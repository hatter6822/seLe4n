-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.SchedContext.Invariant

/-!
# Scheduler Invariant Definitions

This module contains invariant definitions for the scheduler subsystem: queue
uniqueness, current-thread validity, and queue/current consistency.

## AN5-C: Invariant hierarchy

The scheduler invariant surface is layered from smallest to largest. A
proof author should consume the narrowest predicate that discharges the
obligation at hand; downstream composition theorems lift each to the
full bundle.

1. **Base invariants** (per-field correctness):
   * `queueCurrentConsistent` / `schedulerWellFormed` — dequeue-on-dispatch
     (seL4 semantics): the current thread is not in the runnable queue.
   * `runQueueUnique` — `Nodup` on the flat runnable list.
   * `currentThreadValid` — the current thread (if any) resolves to a
     TCB in the object store.

2. **Structural invariants**:
   * `currentThreadInActiveDomain` — active-domain correctness.
   * `timeSlicePositive` / `currentTimeSlicePositive` — time-slice
     positivity for runnable threads and the current thread.
   * `configTimeSlicePositive` — deployment-level positivity of
     `configDefaultTimeSlice` (prevents zero-quantum boot misconfiguration).
   * `replenishmentPipelineOrder` (AN5-B / SCH-M03) — post-pipeline
     witness: every `replenishQueue` entry has `eligibleAt > machine.timer`.

3. **Base bundle**:
   * `schedulerInvariantBundle` = (queueCurrentConsistent ∧ runQueueUnique
     ∧ currentThreadValid). Used by cross-subsystem composition surfaces
     where a minimal scheduler witness is required.

4. **Full bundle**:
   * `schedulerInvariantBundleFull` — adds time-slice, domain, EDF,
     context-matches, and priority-match conjuncts. Consumed by top-level
     liveness/WCRT theorems. Full preservation proofs for the primary
     transitions (`schedule`, `handleYield`, `timerTick`, `switchDomain`,
     `scheduleDomain`) live in `Operations/Preservation.lean`.

5. **Cross-subsystem composition**:
   * `crossSubsystemInvariant` (in `SeLe4n/Kernel/CrossSubsystem.lean`)
     bundles the scheduler invariant with IPC / Capability / Lifecycle /
     Architecture invariants. Per-operation preservation theorems in the
     scheduler module discharge the scheduler conjunct.

## Proof scope qualification (F-16)

**Structural theorems** (high assurance):
- `schedulerWellFormed_iff_queueCurrentConsistent`
- `queueCurrentConsistent_when_no_current`

Scheduler *preservation* theorems (e.g. `chooseThread_preserves_*`,
`schedule_preserves_*`, `handleYield_preserves_*`) live in the IPC and Capability
invariant modules where they compose with cross-subsystem bundles. This module
provides only the invariant definitions and basic structural lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- WS-H12b/H-04: Dequeue-on-dispatch queue/current consistency.

seL4 semantics: the running thread is **removed** from the ready queue at
dispatch time and re-enqueued only on preemption, yield, or blocking.
When `current = some tid`, `tid` must **not** appear in the runnable queue.

This inverts the pre-H12b "strict" policy (`tid ∈ runnable`) to match seL4's
`switchToThread` which calls `tcbSchedDequeue` before setting `ksCurThread`. -/
def queueCurrentConsistent (s : SchedulerState) : Prop :=
  match s.currentOnCore bootCoreId with
  | none => True
  | some tid => tid ∉ s.runnable

/-- Minimal scheduling well-formedness condition.

Alias for `queueCurrentConsistent` (dequeue-on-dispatch semantics since WS-H12b). -/
abbrev schedulerWellFormed (s : SchedulerState) : Prop :=
  queueCurrentConsistent s

/-- Scheduler invariant component #1 (M1 bundle v1): runnable queue has no duplicate TIDs. -/
def runQueueUnique (s : SchedulerState) : Prop :=
  s.runnable.Nodup

/-- Scheduler invariant component #2 (M1 bundle v1): the selected current thread, if any,
resolves to a TCB in the object store. -/
def currentThreadValid (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid => ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- M-05/WS-E6: The currently scheduled thread (if any) belongs to the
active scheduling domain. This is the basic temporal partitioning guarantee:
the scheduler only runs threads in the current domain. -/
def currentThreadInActiveDomain (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.domain = (st.scheduler.activeDomainOnCore bootCoreId)
      | _ => True

/-- Scheduler Invariant Bundle v1 entrypoint used by composed IPC/architecture bundles.

The base triad used by cross-subsystem composition surfaces. -/
def schedulerInvariantBundle (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧ runQueueUnique st.scheduler ∧ currentThreadValid st

theorem schedulerWellFormed_iff_queueCurrentConsistent (s : SchedulerState) :
    schedulerWellFormed s ↔ queueCurrentConsistent s := by
  simp [schedulerWellFormed, queueCurrentConsistent]

-- ============================================================================
-- AI3-D (L-10): configDefaultTimeSlice positivity invariant
-- ============================================================================

/-- AI3-D (L-10): The configurable default time-slice quantum is always positive.
Preservation theorems in Preservation.lean carry an external hypothesis
`hConfigTS : st.scheduler.configDefaultTimeSlice > 0`. This predicate makes
the requirement first-class so it can be composed with the invariant bundle
or verified at boot. The default value (5) satisfies this by construction.

Zero time slice would cause immediate timer expiry on every scheduling round,
preventing any thread from executing. Guard ensures positivity; default 5
matches seL4 convention. -/
def configTimeSlicePositive (st : SystemState) : Prop :=
  st.scheduler.configDefaultTimeSlice > 0

/-- AI3-D: Default state has `configDefaultTimeSlice = 5`, which is positive. -/
theorem default_configTimeSlicePositive :
    configTimeSlicePositive (default : SystemState) := by
  simp [configTimeSlicePositive]
  decide

-- ============================================================================
-- AN5-B (SCH-M03): Replenishment pipeline ordering invariant
-- ============================================================================

/-- AN5-B (SCH-M03): Replenishment pipeline ordering invariant.

`timerTickWithBudget` performs its replenishment pipeline in a fixed
three-step order:

1. **Pop due entries** (`popDueReplenishments`): extract every entry
   whose `eligibleAt ≤ now` from the sorted `replenishQueue`.
2. **Refill SchedContexts** (`refillSchedContext` × k): for each popped
   entry, run `processReplenishments` + `cbsUpdateDeadline` on the
   owning SchedContext.
3. **Process current thread's budget** (`timerTickBudget`): decrement
   the current thread's CBS budget, possibly re-enqueueing on
   exhaustion.

## Semantic scope (IMPORTANT)

This predicate is a **post-condition of step 1** relative to
`st.machine.timer` at the moment the pipeline was invoked. Concretely,
`replenishmentPipelineOrder st` asserts that every remaining entry has
`eligibleAt > st.machine.timer`.

The predicate is **NOT a free-standing state invariant preserved by
arbitrary operations**. In particular, it is NOT preserved by a bare
`tick` of the machine timer: after `machine.timer := timer + 1`, an
entry whose `eligibleAt = timer + 1` that satisfied `> timer` pre-tick
now satisfies only `= post-tick timer`, which falsifies the strict
`>` condition.

The invariant is instead **re-established on every pipeline entry** by
the pop-due sweep (step 1). The sorted-queue post-state witness
`popDueReplenishments_remaining_gt_now` in
`Scheduler/Operations/Preservation.lean` discharges the invariant
immediately after step 1 completes. Callers that need the invariant
held at an arbitrary moment should invoke `processReplenishmentsDue`
at that moment and then assert the invariant via the sorted-queue
witness — see `timerTickWithBudget` in
`Scheduler/Operations/Core.lean` for the canonical call pattern
(`now := st.machine.timer` then `processReplenishmentsDue st now`
then dispatch to `timerTickBudget`).

A future refactor that reorders the pipeline (e.g. swaps steps 1 and 3)
would leave due-but-unprocessed entries in the queue, falsifying this
invariant at the expected post-state. -/
def replenishmentPipelineOrder (st : SystemState) : Prop :=
  ∀ (pair : SchedContextId × Nat),
    pair ∈ (st.scheduler.replenishQueueOnCore bootCoreId).entries → pair.2 > st.machine.timer

/-- AN5-B (SCH-M03): The default state has an empty `replenishQueue` so
`replenishmentPipelineOrder` holds vacuously. -/
theorem default_replenishmentPipelineOrder :
    replenishmentPipelineOrder (default : SystemState) := by
  intro pair hMem
  -- Default ReplenishQueue has empty entries list
  have : ((default : SystemState).scheduler.replenishQueueOnCore bootCoreId).entries = [] := by
    rfl
  rw [this] at hMem
  exact absurd hMem (by simp)

/-- AN5-B (SCH-M03): If the `replenishQueue` is empty, the pipeline-order
invariant holds vacuously. -/
theorem replenishmentPipelineOrder_of_empty
    (st : SystemState)
    (hEmpty : (st.scheduler.replenishQueueOnCore bootCoreId).entries = []) :
    replenishmentPipelineOrder st := by
  intro pair hMem
  rw [hEmpty] at hMem
  exact absurd hMem (by simp)

-- ============================================================================
-- M-04/WS-E6: Time-slice positivity invariant
-- ============================================================================

/-- M-04/WS-E6: All runnable threads have a positive time-slice remaining.
This ensures `timerTick` can always decrement without underflow, and that
preemption only occurs when a thread has exhausted its quantum. -/
def timeSlicePositive (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runnable →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.timeSlice > 0
    | _ => True

/-- WS-H12b: The current thread (if any) has a positive time-slice remaining.

Under dequeue-on-dispatch semantics, the current thread is removed from the
run queue at dispatch time, so `timeSlicePositive` (which quantifies over
runnable threads) no longer covers it. This companion predicate closes the gap
and is included in `schedulerInvariantBundleFull`. -/
def currentTimeSlicePositive (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.timeSlice > 0
    | _ => True

-- ============================================================================
-- AI3-A: Effective RunQueue priority computation (must precede EDF)
-- ============================================================================

-- **The reading itself lives in the model** (`TCB.boostedPriority`,
-- `Model/Object/Types.lean`).  This module used to define it, the IPC surface
-- carried a second body because importing this one would close an import cycle,
-- and a `rfl` theorem pinned the two together.  The shared answer belongs
-- upstream of both, where the cycle objection never applied -- so both bodies
-- and the pin are gone, and every site calls the accessor.  What stays here is
-- the specialisation the scheduler's proofs consume.

/-- AI3-A: For threads without PIP boost, effective priority equals base
TCB priority. -/
theorem boostedPriority_no_pip (tcb : TCB)
    (hNoPip : tcb.pipBoost = none) :
    tcb.boostedPriority = tcb.priority := by
  simp [TCB.boostedPriority, hNoPip]

/-- AK2-B (S-H04) helper: the bucket a thread is keyed by.

**WS-RR (`v0.35.133`): this was the THIRD copy of the priority resolver, and
the one-home collapse retires its body.**  It mirrored
`resolveEffectivePrioDeadline`'s classification here because `Invariant.lean`
sits below `Selection.lean` and cannot call it — a second implementation kept
in step by `effectiveBucketPriority_eq_resolveEffective`, which is the shape
this project spends its length retiring and which it kept only because the base
had two homes to choose between.

With `TCB.priority` the only home there is nothing to classify: the bucket is
`TCB.boostedPriority` at every binding, the import-cycle objection has no
subject, and the pin against `resolveEffectivePrioDeadline` becomes the
statement that both are that accessor.  The name is kept because the run-queue
invariants are stated over it and it says *which* question is being asked; what
is gone is the second answer. -/
def effectiveBucketPriority (_st : SystemState) (tcb : TCB) : SeLe4n.Priority :=
  tcb.boostedPriority

/-- The collapse, stated: the bucket is the thread's own boosted priority,
whatever the binding and whatever the store holds.  Every arm-specific reading
this helper used to need is this theorem. -/
@[simp] theorem effectiveBucketPriority_eq (st : SystemState) (tcb : TCB) :
    effectiveBucketPriority st tcb = tcb.boostedPriority := rfl

/-- **The bucket is insensitive to the store, so the frame is a congruence.**

`effectiveBucketPriority` reads the TCB and nothing else, so "preserved
whenever the thread's SchedContext lookup agrees" is a statement with a dead
hypothesis: the conclusion holds for *any* two states.  Stated at the strength
the accessor has. -/
theorem effectiveBucketPriority_congr (st st' : SystemState) (tcb : TCB) :
    effectiveBucketPriority st' tcb = effectiveBucketPriority st tcb := rfl

-- **Six theorems stood here and are DELETED at `v0.35.134`** -- the sweep
-- `v0.35.133` owed its own sibling family and did not run.
--
-- That cut collapsed this accessor's body to `TCB.boostedPriority` and deleted
-- `resolveEffectivePrioDeadline`'s three arm-specific readings for the stated
-- reason that *every arm-specific reading the resolver used to need is the
-- unconditional theorem*.  The identical family over **this** accessor was left
-- standing one file over, with hypotheses the collapse had made dead:
--
--   * `effectiveBucketPriority_of_unbound`, `_of_bound_sc_missing`,
--     `_of_donated` -- each `effectiveBucketPriority_eq` under a binding
--     hypothesis nothing reads.  A name like `_of_bound_sc_missing` kept past
--     its hypothesis does not merely repeat the unconditional lemma, it
--     *teaches a false dependency*: a reader concludes the bucket still turns
--     on whether a SchedContext resolves.
--   * `effectiveBucketPriority_lookup_non_sc` -- a lemma about the expression
--     `match … | some (.schedContext sc) => sc.priority | _ => tcb.priority`,
--     which this accessor no longer contains and which occurs nowhere else.  A
--     theorem whose subject is gone is the tautological pin this project
--     retires: it reads in a report exactly like a check that decides
--     something.
--   * `effectiveBucketPriority_frame` and `_frame_weak` -- replaced by the
--     unconditional `effectiveBucketPriority_congr` above, which is strictly
--     stronger; `_frame_weak`'s one consumer
--     (`Scheduler/Operations/Preservation.lean`) cites the congruence.
--
-- All six were `rfl`, five had no consumer at all, and three carried
-- `unused variable` warnings that said so.  Tier 3 negatives refuse each name.


-- ============================================================================
-- M-03/WS-E6: EDF scheduling invariant
-- ============================================================================

/-- M-03/WS-E6/WS-H6: The currently scheduled thread has the earliest deadline
among all runnable threads **in the same scheduling domain** at the same
priority level. This captures the domain-partitioned EDF policy: within equal
effective priority, equal base priority and equal domain, the thread with the
most urgent deadline is selected.

**WS-H6 fix:** The original definition quantified over all runnable threads
regardless of domain, which was unprovable for a domain-aware scheduler that
only selects among same-domain candidates. Adding the domain constraint
aligns the invariant with `chooseBestRunnableInDomain` semantics.

**AI3-A:** Added `TCB.boostedPriority` guard. The RunQueue buckets
threads by effective priority, so deadline ordering is only meaningful among
threads in the same effective priority bucket. Threads at a lower effective
priority are not considered during bucket-based selection and thus fall
outside the EDF comparison scope. -/
def edfCurrentHasEarliestDeadline (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some curTid =>
      match st.objects[curTid.toObjId]? with
      | some (.tcb curTcb) =>
          ∀ tid, tid ∈ st.scheduler.runnable →
            match st.objects[tid.toObjId]? with
            | some (.tcb tcb) =>
                tcb.domain = curTcb.domain →
                tcb.boostedPriority = curTcb.boostedPriority →
                tcb.priority = curTcb.priority →
                curTcb.deadline.toNat = 0 ∨
                (tcb.deadline.toNat = 0 ∨ curTcb.deadline.toNat ≤ tcb.deadline.toNat)
            | _ => True
      | _ => True

-- ============================================================================
-- WS-H12c/H-03: Per-TCB register context invariant
-- ============================================================================

/-- WS-H12c/H-03: When a thread is current, the machine's register file
matches that thread's saved register context. This is established atomically
by the inline context restore step in `schedule`.

When `current = none` (idle), the invariant is vacuously satisfied.
When the current thread's object is not a TCB (impossible under
`currentThreadValid`), the invariant is vacuously satisfied.

**X5-D (M-5): Idle-state design rationale.** `contextMatchesCurrent` is
vacuously true when `current = none` by design. During domain switching
(`switchDomain`), the kernel enters an idle state where no thread is dispatched
and `current` is set to `none`. The invariant is re-established by the
`schedule` transition, which atomically loads the selected thread's saved
context into the register file (Core.lean inline context restore). This design
avoids the need for an "idle context" concept and simplifies proof obligations:
every preservation theorem for operations that set `current := none` trivially
satisfies this predicate. The invariant's strength lies in the `some tid` branch,
where it guarantees register-TCB synchronization for the dispatched thread.
Under `currentThreadValid`, the "not a TCB" branch is unreachable, making the
match on `st.objects[tid.toObjId]?` effectively a two-case analysis. -/
def contextMatchesCurrent (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => (st.machine.regs == tcb.registerContext) = true
      | _ => True
  | none => True

/-- AG7-D bridge: propositional RegisterFile equality implies BEq contextMatchesCurrent.
    Used by scheduler operations that establish `machine.regs = tcb.registerContext`
    via definitional equality (e.g., inline context restore in `schedule`). -/
theorem contextMatchesCurrent_of_regs_eq {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB}
    (hCurr : (st.scheduler.currentOnCore bootCoreId) = some tid)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hRegs : st.machine.regs = tcb.registerContext) :
    contextMatchesCurrent st := by
  simp [contextMatchesCurrent, hCurr, hObj, hRegs, RegisterFile.beq_self]

-- ============================================================================
-- WS-H6: Full scheduler invariant bundle
-- ============================================================================

-- Full Scheduler Invariant Bundle — extends the structural triad with
-- `timeSlicePositive`, `currentTimeSlicePositive`,
-- `edfCurrentHasEarliestDeadline`, `contextMatchesCurrent`, and
-- `runnableThreadsAreTCBs` (WS-F6/D3 6-tuple extension).

-- ============================================================================
-- WS-F6/D3: Runnable threads type-safety invariant
-- ============================================================================

/-- WS-F6/D3/MED-06: Every thread ID in the scheduler's runnable queue
corresponds to a valid TCB in the object store.

This is a type-safety backstop for the scheduler: without it, a lifecycle
`retypeObject` that overwrites a TCB with a non-TCB object while leaving the
thread ID in the run queue could cause `chooseThread` to read TCB fields from
a non-TCB object. `currentThreadValid` only covers the *current* thread;
this predicate covers *all* runnable threads. -/
def runnableThreadsAreTCBs (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runnable →
    ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- WS-F6/D3: Default state has empty run queue, so the predicate is vacuously true. -/
theorem default_runnableThreadsAreTCBs :
    runnableThreadsAreTCBs (default : SystemState) := by
  intro tid hMem
  have : (default : SystemState).scheduler.runnable = [] := by decide
  rw [this] at hMem; simp at hMem


-- ============================================================================
-- WS-H6: RunQueue priority-match predicate
-- ============================================================================

/-- WS-H6/AI3-A: The RunQueue's recorded `threadPriority` mapping matches the
effective priority for every run-queue member.

AI3-A (M-04) → AK2-B (S-H04): Updated from `TCB.boostedPriority` (TCB
base + PIP, SC-unaware) to `effectiveBucketPriority` — a fully SC-aware resolver
that agrees with `resolveEffectivePrioDeadline` used by selection. This
FUSES the prior pair `schedulerPriorityMatch` + `effectiveParamsMatchRunQueue`
(audit S-H04 joint over-constraint). Selection and insertion now agree on the
same priority across all thread states (unbound, bound, PIP-boosted, donated).

The prior bifurcation was inconsistent for any SC-bound thread with
`sc.priority ≠ tcb.priority` (impossible to jointly satisfy) and for any
PIP-boosted bound thread (`effectiveParamsMatchRunQueue` ignored PIP boost).

Together with `RunQueue.wellFormed`, this enables the bucket-first scheduling
proof: if a thread has the same effective priority as the selected candidate,
it must reside in the same priority bucket. -/
def schedulerPriorityMatch (st : SystemState) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore bootCoreId) →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        (st.scheduler.runQueueOnCore bootCoreId).threadPriority[tid]? = some (tcb.boostedPriority)
    | _ => True

/-- V5-H (M-HW-7): The scheduler's `domainTimeRemaining` is always positive (> 0).

This invariant ensures that `scheduleDomain`'s decrement operation
(`domainTimeRemaining - 1`) never underflows to `Nat.zero` in the
non-expiry branch. It is established at initialization (default value 5)
and maintained by:
- `scheduleDomain`: on expiry, `switchDomain` sets `domainTimeRemaining` to
  the next domain entry's `length` field (which must be positive per
  `DomainScheduleEntry` well-formedness); on non-expiry, decrements by 1
  (result ≥ 1 since pre-condition was > 1).
- `timerTick`: does not modify `domainTimeRemaining`.
- `schedule`: does not modify `domainTimeRemaining`.
- `handleYield`: does not modify `domainTimeRemaining`. -/
def domainTimeRemainingPositive (st : SystemState) : Prop :=
  (st.scheduler.domainTimeRemainingOnCore bootCoreId) > 0

/-- X2-A/H-2: All entries in the domain schedule table have positive length.
This validates that `switchDomain` will never set `domainTimeRemaining` to 0
when advancing to the next schedule entry. The domain schedule is set once
at boot and is immutable at runtime, so this predicate is trivially preserved
by all scheduler operations (frame lemma — `domainSchedule` unchanged). -/
def domainScheduleEntriesPositive (st : SystemState) : Prop :=
  ∀ e, e ∈ st.scheduler.domainSchedule → e.length > 0

/-- X2-A: Default state has empty domain schedule, so the predicate is vacuously true. -/
theorem default_domainScheduleEntriesPositive :
    domainScheduleEntriesPositive (default : SystemState) := by
  intro e hMem
  have : (default : SystemState).scheduler.domainSchedule = [] := by decide
  rw [this] at hMem; simp at hMem

/-- R6-D/L-12/V5-H/X2-A: Extended full scheduler invariant bundle.
    9-tuple: base triad + timeSlice + EDF + context + runnableAreTCBs +
    priorityMatch + domainTimeRemainingPositive + domainScheduleEntriesPositive.
    `schedulerPriorityMatch` ensures the RunQueue's priority index stays in sync
    with the authoritative TCB priority in the object store.
    `domainTimeRemainingPositive` (V5-H) ensures domain time remaining > 0.
    `domainScheduleEntriesPositive` (X2-A/H-2) ensures all domain schedule entries
    have positive length, closing the `hEntriesPos` precondition gap in
    `switchDomain_preserves_domainTimeRemainingPositive`. -/
def schedulerInvariantBundleFull (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ timeSlicePositive st ∧
  currentTimeSlicePositive st ∧ edfCurrentHasEarliestDeadline st ∧
  contextMatchesCurrent st ∧ runnableThreadsAreTCBs st ∧
  schedulerPriorityMatch st ∧ domainTimeRemainingPositive st ∧
  domainScheduleEntriesPositive st

/-- Project the structural triad from the full bundle. -/
theorem schedulerInvariantBundleFull_to_base {st : SystemState}
    (h : schedulerInvariantBundleFull st) : schedulerInvariantBundle st :=
  h.1

/-- WS-H12e: Project `contextMatchesCurrent` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_contextMatchesCurrent {st : SystemState}
    (h : schedulerInvariantBundleFull st) : contextMatchesCurrent st :=
  h.2.2.2.2.1

/-- R6-D: Project `schedulerPriorityMatch` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_priorityMatch {st : SystemState}
    (h : schedulerInvariantBundleFull st) : schedulerPriorityMatch st :=
  h.2.2.2.2.2.2.1

/-- V5-H: Project `domainTimeRemainingPositive` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_domainTimeRemainingPositive {st : SystemState}
    (h : schedulerInvariantBundleFull st) : domainTimeRemainingPositive st :=
  h.2.2.2.2.2.2.2.1

/-- X2-A: Project `domainScheduleEntriesPositive` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_domainScheduleEntriesPositive {st : SystemState}
    (h : schedulerInvariantBundleFull st) : domainScheduleEntriesPositive st :=
  h.2.2.2.2.2.2.2.2

/-- R6-D: schedulerPriorityMatch is preserved when both runQueue and objects
are unchanged. -/
theorem schedulerPriorityMatch_of_runQueue_objects_eq
    (st st' : SystemState)
    (hInv : schedulerPriorityMatch st)
    (hRQEq : (st'.scheduler.runQueueOnCore bootCoreId) = (st.scheduler.runQueueOnCore bootCoreId))
    (hObjEq : st'.objects = st.objects) :
    schedulerPriorityMatch st' := by
  intro tid hMem; rw [hRQEq] at hMem; rw [hRQEq, hObjEq]; exact hInv tid hMem

/-- R6-D/AI3-A: schedulerPriorityMatch after inserting the current thread at
its effective priority. The inserted priority must equal
`curTcb.boostedPriority` for the invariant to hold. -/
theorem schedulerPriorityMatch_insert
    (st : SystemState) (curTid : ThreadId) (curTcb : TCB)
    (hPM : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hCur : (st.scheduler.currentOnCore bootCoreId) = some curTid)
    (hObj : st.objects[curTid.toObjId]? = some (.tcb curTcb)) :
    ∀ tid, tid ∈ (st.scheduler.runQueueOnCore bootCoreId).insert curTid (curTcb.boostedPriority) →
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        ((st.scheduler.runQueueOnCore bootCoreId).insert curTid (curTcb.boostedPriority)).threadPriority[tid]?
          = some (tcb.boostedPriority)
      | _ => True := by
  intro tid hMem
  have hNotMem : curTid ∉ (st.scheduler.runQueueOnCore bootCoreId) := by
    simp [queueCurrentConsistent, hCur] at hQCC
    intro h; exact hQCC ((RunQueue.mem_toList_iff_mem _ _).2 h)
  have hContF : (st.scheduler.runQueueOnCore bootCoreId).contains curTid = false := by
    cases h : (st.scheduler.runQueueOnCore bootCoreId).contains curTid; rfl; exact absurd h hNotMem
  rw [RunQueue.mem_insert] at hMem
  rw [RunQueue.insert_threadPriority]; simp only [hContF, Bool.false_eq_true, ↓reduceIte]
  cases hMem with
  | inl hOld =>
    have hNeq : curTid ≠ tid := fun h => hNotMem (h ▸ hOld)
    have hBEq : (curTid == tid) = false := by
      cases h : (curTid == tid) <;> simp_all
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert (st.scheduler.runQueueOnCore bootCoreId).threadPriority _ _ (st.scheduler.runQueueOnCore bootCoreId).threadPrio_invExtK.1]
    simp only [hBEq, Bool.false_eq_true, ↓reduceIte]
    have := hPM tid hOld
    simp only [RHTable_getElem?_eq_get?] at this; exact this
  | inr hEq =>
    subst hEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert (st.scheduler.runQueueOnCore bootCoreId).threadPriority _ _ (st.scheduler.runQueueOnCore bootCoreId).threadPrio_invExtK.1]
    simp only [beq_self_eq_true, ↓reduceIte]
    simp only [RHTable_getElem?_eq_get?] at hObj; rw [hObj]

-- ============================================================================
-- Z4-K: budgetPositive invariant
-- ============================================================================

/-- Z4-K: Every SchedContext-bound runnable thread has positive budget remaining.

For unbound threads, this is vacuously true (they use the `timeSlice` mechanism).
For bound threads, the SchedContext must have `budgetRemaining > 0` to be in
the run queue. This is the CBS analog of `timeSlicePositive`. -/
def budgetPositive (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runnable →
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.getSchedContext? scId with
        | some sc => sc.budgetRemaining.val > 0
        | none => True
    | none => True

/-- Z4-K: Default state has empty run queue — vacuously true. -/
theorem default_budgetPositive :
    budgetPositive (default : SystemState) := by
  intro tid hMem
  have : (default : SystemState).scheduler.runnable = [] := by decide
  rw [this] at hMem; simp at hMem

-- ============================================================================
-- Z4-L: currentBudgetPositive invariant
-- ============================================================================

/-- Z4-L: The current thread (if SchedContext-bound) has positive budget.

Under dequeue-on-dispatch, `budgetPositive` does not cover the current thread.
This companion predicate closes the gap. -/
def currentBudgetPositive (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid =>
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.getSchedContext? scId with
        | some sc => sc.budgetRemaining.val > 0
        | none => True
    | none => True

/-- Z4-L: Default state has no current thread — vacuously true. -/
theorem default_currentBudgetPositive :
    currentBudgetPositive (default : SystemState) := by
  have h : (default : SystemState).scheduler.currentOnCore bootCoreId = none :=
    (default_state_perCoreInitialized bootCoreId).1
  simp [currentBudgetPositive, h]

-- ============================================================================
-- Z4-M: schedContextsWellFormed invariant
-- ============================================================================

/-- Z4-M: Every SchedContext object in the store satisfies `schedContextWellFormed`.

System-wide per-object well-formedness for all SchedContext objects. -/
def schedContextsWellFormed (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
    st.objects[oid]? = some (.schedContext sc) →
    schedContextWellFormed sc

/-- Z4-M: Default state has no SchedContext objects — vacuously true.
The default object store is empty (`RHTable.empty 16`), so all lookups
return `none`. -/
theorem default_schedContextsWellFormed :
    schedContextsWellFormed (default : SystemState) := by
  intro oid sc hObj
  have hNone : (default : SystemState).objects.get? oid = none :=
    RobinHood.RHTable.getElem?_empty 16 (by omega) oid
  simp [GetElem?.getElem?] at hObj
  rw [hNone] at hObj
  exact absurd hObj (by simp)

-- ============================================================================
-- Z4-N: replenishQueueValid invariant
-- ============================================================================

/-- Z4-N: The system replenish queue is sorted and every entry references an
active SchedContext. Connects Z3's queue invariants to system state. -/
def replenishQueueValid (st : SystemState) : Prop :=
  replenishQueueSorted (st.scheduler.replenishQueueOnCore bootCoreId) ∧
  replenishQueueSizeConsistent (st.scheduler.replenishQueueOnCore bootCoreId)

/-- Z4-N: Default state has empty replenish queue — trivially valid. -/
theorem default_replenishQueueValid :
    replenishQueueValid (default : SystemState) := by
  constructor
  · exact empty_sorted
  · exact empty_sizeConsistent

-- ============================================================================
-- Z4-O: schedContextBindingConsistent invariant
-- ============================================================================

/-- Z4-O: Bidirectional consistency between TCB and SchedContext binding.

For every TCB with `schedContextBinding = .bound scId`, the SchedContext
object exists and `sc.boundThread = some tid`. Conversely, for every
SchedContext with `boundThread = some tid`, the TCB has a matching binding. -/
def schedContextBindingConsistent (st : SystemState) : Prop :=
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    ∀ scId, tcb.schedContextBinding = .bound scId →
      ∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
        sc.boundThread = some tid) ∧
  (∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∀ tid, sc.boundThread = some tid →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        (tcb.schedContextBinding = .bound scId ∨
         ∃ owner, tcb.schedContextBinding = .donated scId owner))

/-- **`v0.35.183` (WS-RR RR8.12, register row 63): the two projections Z4-O
reads, and the only two.**

`schedContextBindingConsistent` is a reciprocity between a thread's
`schedContextBinding` and a scheduling context's `boundThread`; it reads no other
field of either record and no key outside the two it quantifies over.  So a step
that fixes those two projections **pointwise** carries it whole, whatever else it
rewrites — which is what every step of the destroy path but three does (queue
links, `ipcState`, endpoints, notifications, `SchedContext.donationOrigin`, CDT
edges, the service registry, the scheduler).

Stated as a transfer over the projections rather than as a named `sameBindingGraph`
relation with `refl` / `trans`, because each step's own frame already *is* an
`Option.map` equality at an arbitrary key and `Eq.trans` chains them: a relation
would be a second name for what the frames already say.  This mirrors
`replenishQueueAffinityConsistentOnCore_transfer`, the shape the SM5.H invariant
uses for the same reason.

Register row 63 records that *no* `preserves_schedContextBindingConsistent`
theorem existed anywhere in this tree, so every consumer of the invariant had to
take it as a hypothesis; this is the one owner the destroy path's eight steps are
proved through. -/
theorem schedContextBindingConsistent_transfer {st st' : SystemState}
    (hTcb : ∀ tid : SeLe4n.ThreadId, (st'.getTcb? tid).map (·.schedContextBinding)
      = (st.getTcb? tid).map (·.schedContextBinding))
    (hSc : ∀ scId : SeLe4n.SchedContextId, (st'.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread))
    (h : schedContextBindingConsistent st) :
    schedContextBindingConsistent st' := by
  constructor
  · intro tid tcb' hObj' scId hBound'
    -- The thread's binding is the pre-state's, so Z4-O's forward clause applies
    -- there and its witness is transported back by the context projection.
    have hT : (st.getTcb? tid).map (·.schedContextBinding) = some (.bound scId) := by
      rw [← hTcb tid, (SystemState.getTcb?_eq_some_iff st' tid tcb').mpr hObj']
      simp [hBound']
    cases hTPre : st.getTcb? tid with
    | none => rw [hTPre] at hT; exact absurd hT (by simp)
    | some tcb =>
      rw [hTPre] at hT
      have hBound : tcb.schedContextBinding = .bound scId := by
        simpa using hT
      obtain ⟨sc, hScObj, hBT⟩ := h.1 tid tcb
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hTPre) scId hBound
      have hS : (st'.getSchedContext? scId).map (·.boundThread) = some (some tid) := by
        rw [hSc scId, (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hScObj]
        simp [hBT]
      cases hSPost : st'.getSchedContext? scId with
      | none => rw [hSPost] at hS; exact absurd hS (by simp)
      | some sc' =>
        rw [hSPost] at hS
        exact ⟨sc', (SystemState.getSchedContext?_eq_some_iff st' scId sc').mp hSPost,
          by simpa using hS⟩
  · intro scId sc' hObj' tid hBound'
    have hS : (st.getSchedContext? scId).map (·.boundThread) = some (some tid) := by
      rw [← hSc scId, (SystemState.getSchedContext?_eq_some_iff st' scId sc').mpr hObj']
      simp [hBound']
    cases hSPre : st.getSchedContext? scId with
    | none => rw [hSPre] at hS; exact absurd hS (by simp)
    | some sc =>
      rw [hSPre] at hS
      obtain ⟨tcb, hTObj, hBind⟩ := h.2 scId sc
        ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSPre) tid (by simpa using hS)
      have hT : (st'.getTcb? tid).map (·.schedContextBinding)
          = some tcb.schedContextBinding := by
        rw [hTcb tid, (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTObj]
        simp
      cases hTPost : st'.getTcb? tid with
      | none => rw [hTPost] at hT; exact absurd hT (by simp)
      | some tcb' =>
        rw [hTPost] at hT
        have hEq : tcb'.schedContextBinding = tcb.schedContextBinding := by simpa using hT
        refine ⟨tcb', (SystemState.getTcb?_eq_some_iff st' tid tcb').mp hTPost, ?_⟩
        rw [hEq]; exact hBind

/-- **`v0.35.183`**: a step that writes no object at all carries Z4-O. -/
theorem schedContextBindingConsistent_of_objects_eq {st st' : SystemState}
    (hObj : st'.objects = st.objects) (h : schedContextBindingConsistent st) :
    schedContextBindingConsistent st' :=
  schedContextBindingConsistent_transfer
    (fun tid => by rw [SystemState.getTcb?_frame hObj tid])
    (fun scId => by rw [SystemState.getSchedContext?_frame hObj scId]) h

/-- Z4-O: Default state has no objects — vacuously true. -/
theorem default_schedContextBindingConsistent :
    schedContextBindingConsistent (default : SystemState) := by
  constructor
  · intro tid tcb hObj
    have hNone : (default : SystemState).objects.get? tid.toObjId = none :=
      RobinHood.RHTable.getElem?_empty 16 (by omega) tid.toObjId
    simp [GetElem?.getElem?] at hObj
    rw [hNone] at hObj; exact absurd hObj (by simp)
  · intro scId sc hObj
    have hNone : (default : SystemState).objects.get? scId.toObjId = none :=
      RobinHood.RHTable.getElem?_empty 16 (by omega) scId.toObjId
    simp [GetElem?.getElem?] at hObj
    rw [hNone] at hObj; exact absurd hObj (by simp)

-- ============================================================================
-- Z4-P: effectiveParamsMatchRunQueue invariant
-- ============================================================================

/-- Z4-P: for every run-queue member, the RunQueue's cached `threadPriority`
entry is that thread's **base** priority.

WS-RR (`v0.35.133`): this used to be a three-armed case analysis on the binding,
whose `.bound` arm demanded the recorded bucket equal the RESERVATION's
`priority` — the SchedContext-aware reading its Z4-P docstring described.  With
`TCB.priority` the base's one home that arm says what the other two say, so the
binding analysis is gone and with it the raw SchedContext read it needed.

Two things the collapse changed, and neither is cosmetic.  The `.bound` arm's
inner `match` had a `| _ => True` fallback, so a bound thread whose reservation
did **not** resolve was silently excused from the bucket claim: a default arm is
a decision, and that one excused a case nobody chose to excuse.  And under two
homes this predicate and `schedulerPriorityMatch` were jointly unsatisfiable for
any bound thread whose mirror had drifted (`sc.priority ≠ tcb.priority`) — the
S-H04 over-constraint the fusion docstring above records — so the collapse is
what makes the pair satisfiable rather than merely tidier.

It stays the PIP-unaware sibling of `schedulerPriorityMatch`, which reads
`TCB.boostedPriority`; the two agree exactly on an unboosted thread. -/
def effectiveParamsMatchRunQueue (st : SystemState) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore bootCoreId) →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      (st.scheduler.runQueueOnCore bootCoreId).threadPriority[tid]? = some tcb.priority
    | _ => True

/-- Z4-P: Default state has empty run queue — vacuously true. -/
theorem default_effectiveParamsMatchRunQueue :
    effectiveParamsMatchRunQueue (default : SystemState) := by
  intro tid hMem
  have hEmpty : ((default : SystemState).scheduler.runQueueOnCore bootCoreId).membership.contains tid = false :=
    RobinHood.RHSet.contains_empty tid
  simp [Membership.mem, RunQueue.contains] at hMem
  simp [hEmpty] at hMem

-- ============================================================================
-- AE3-A/U-11: boundThreadDomainConsistent invariant
-- ============================================================================

/-- AE3-A/U-11: For every thread bound to a SchedContext, the thread's domain
must match the SchedContext's domain.  Established by the domain check in
`schedContextBind` (AE3-A2), which refuses a cross-domain bind outright, and
maintained by `schedContextConfigureBoundPropagate`, which moves both homes
under `schedContextConfigurePropagates`.

**WS-RR (`v0.35.136`): it is NOT an invariant, and the enumeration that stood
here said otherwise.**  *"Preserved by all binding-modifying operations
(unbind/cancelDonation clear `.bound`; donation uses `.donated` not `.bound`)"*
was written before the donation **pop** existed, and `returnDonatedSchedContext`
is a binding-modifying operation that installs `.bound` — writing neither
`TCB.domain` nor `SchedContext.domain`.  So the agreement survives a loan only
while nothing moves either home during it, and `schedContextConfigure` on a
**donated** reservation moves one: its propagation is gated on the donee's
`ownScId?`, which is `none`, so `sc.domain` changes alone and the pop then
rebinds the origin under it.  `tests/PriorityManagementSuite.lean`'s
WS-RR-PRIO-09 drives exactly that, through two live operations, with
WS-RR-PRIO-10 as the unreconfigured control.

Neither reconciliation is available to the pop: writing `tcb.domain :=
sc.domain` would **migrate a thread's partition** on an IPC reply, at the
instance of a holder of a capability on the reservation rather than on the
thread — the crossing WS-OD `v0.35.3` closed on the other side — and writing
`sc.domain := tcb.domain` would silently retune a reservation its capability's
holder had just configured.  So this is a fact about its two writers, as
`boundThreadPriorityConsistent` is about its three, and the residue is
registered in `docs/REGISTERED_DEBT.md` table C with the model change that
closes it.

**Nothing reads it.**  Since `v0.35.136` every arm of `effectiveSchedParams`
reports `tcb.domain` (`effectiveSchedParams_domain_eq`) and every live domain
filter reads `tcb.domain` directly (`chooseBestRunnableInDomainEffective`), so a
stale mirror changes no scheduling decision — which is what makes the residue a
verification gap rather than a partition break.  It stays a conjunct of
`schedulerInvariantBundleExtended`, whose scope is the boot and scheduler
surface: no IPC transition claims that bundle. -/
def boundThreadDomainConsistent (st : SystemState) : Prop :=
  ∀ (tid : ThreadId) (scId : SchedContextId),
    match (st.objects[tid.toObjId]? : Option KernelObject) with
    | some (.tcb tcb) =>
      tcb.schedContextBinding = .bound scId →
      match (st.objects[scId.toObjId]? : Option KernelObject) with
      | some (.schedContext sc) => tcb.domain = sc.domain
      | _ => True
    | _ => True

/-- AE3-A: Default state has empty object store — no bound threads to check. -/
theorem default_boundThreadDomainConsistent :
    boundThreadDomainConsistent (default : SystemState) := by
  intro tid _scId
  -- Default object store is empty — all lookups return none
  have hNone : (default : SystemState).objects.get? tid.toObjId = none :=
    RobinHood.RHTable.getElem?_empty 16 (by omega) tid.toObjId
  simp only [show (default : SystemState).objects[tid.toObjId]? =
    (default : SystemState).objects.get? tid.toObjId from rfl, hNone]

-- ============================================================================
-- Z4: Extended scheduler invariant bundle
-- ============================================================================

/-- Z4/AE3-A: Extended scheduler invariant bundle with 7 additional SchedContext
invariants. 16-tuple: original 9 + budgetPositive + currentBudgetPositive +
schedContextsWellFormed + replenishQueueValid + schedContextBindingConsistent +
effectiveParamsMatchRunQueue + boundThreadDomainConsistent. -/
def schedulerInvariantBundleExtended (st : SystemState) : Prop :=
  schedulerInvariantBundleFull st ∧
  budgetPositive st ∧ currentBudgetPositive st ∧
  schedContextsWellFormed st ∧ replenishQueueValid st ∧
  schedContextBindingConsistent st ∧ effectiveParamsMatchRunQueue st ∧
  boundThreadDomainConsistent st

/-- Z4: Project the original 9-tuple from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_full {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : schedulerInvariantBundleFull st :=
  h.1

/-- Z4: Project `budgetPositive` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_budgetPositive {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : budgetPositive st :=
  h.2.1

/-- Z4: Project `currentBudgetPositive` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_currentBudgetPositive {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : currentBudgetPositive st :=
  h.2.2.1

/-- Z4: Project `schedContextsWellFormed` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_schedContextsWellFormed {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : schedContextsWellFormed st :=
  h.2.2.2.1

/-- Z4: Project `replenishQueueValid` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_replenishQueueValid {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : replenishQueueValid st :=
  h.2.2.2.2.1

/-- Z4: Project `schedContextBindingConsistent` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_schedContextBindingConsistent {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : schedContextBindingConsistent st :=
  h.2.2.2.2.2.1

/-- Z4: Project `effectiveParamsMatchRunQueue` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_effectiveParamsMatchRunQueue {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : effectiveParamsMatchRunQueue st :=
  h.2.2.2.2.2.2.1

/-- AE3-A: Project `boundThreadDomainConsistent` from the extended bundle. -/
theorem schedulerInvariantBundleExtended_to_boundThreadDomainConsistent {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : boundThreadDomainConsistent st :=
  h.2.2.2.2.2.2.2

-- ============================================================================
-- WS-RC R5.G.3 / Phase P2: boundThreadDomainConsistent frame lemmas
-- ============================================================================
--
-- These frame lemmas characterise when an `objects` table update preserves
-- `boundThreadDomainConsistent`.  They are the foundational building blocks
-- for `schedContextConfigure_preserves_boundThreadDomainConsistent` (Phase
-- R2), which composes them through the operation's nested writes.

/-- WS-RC R5.G.3 / Phase P2: An object-table update at an ObjId of a NON-TCB,
    NON-SC object preserves `boundThreadDomainConsistent`.

    The invariant body case-splits on `objects[tid.toObjId]?` and (within
    `.tcb`) on `objects[scId.toObjId]?`.  Inserting a non-TCB, non-SC
    object at `oid`:
    - At `oid`, the post-state lookup returns the non-TCB / non-SC object;
      the outer match falls into the `_ => True` catch-all, vacuous.
    - Elsewhere, `getElem?_insert_ne` gives the pre-state result.

    Symmetrically for `scId.toObjId`: at `oid` the inner match falls into
    `_ => True`. -/
theorem objects_insert_non_tcb_non_sc_preserves_boundThreadDomainConsistent
    (st : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hNotSc : ∀ sc, obj ≠ .schedContext sc)
    (hObjInv : st.objects.invExt)
    (hDom : boundThreadDomainConsistent st) :
    boundThreadDomainConsistent
      { st with objects := st.objects.insert oid obj } := by
  intro tid scId
  -- Case-split on whether `tid.toObjId = oid` and `scId.toObjId = oid`.
  by_cases hTidEq : tid.toObjId = oid
  · -- post-state at tid.toObjId is `obj`; not a TCB → outer match `_ => True`.
    show (match ({ st with objects := st.objects.insert oid obj }.objects[tid.toObjId]? :
              Option KernelObject) with
          | some (.tcb tcb) => _
          | _ => True)
    have hLook : ({ st with objects := st.objects.insert oid obj }.objects)[tid.toObjId]?
                  = some obj := by
      show (st.objects.insert oid obj)[tid.toObjId]? = some obj
      have hShow : (st.objects.insert oid obj)[tid.toObjId]? =
                    (st.objects.insert oid obj).get? tid.toObjId := rfl
      rw [hShow, hTidEq]
      exact RobinHood.RHTable.getElem?_insert_self st.objects oid obj hObjInv
    rw [hLook]
    cases hObj : obj with
    | tcb t => exact absurd hObj (hNotTcb t)
    | _ => simp
  · -- post-state at tid.toObjId equals pre-state at tid.toObjId.
    have hTidNe : ¬(oid == tid.toObjId) = true := by
      intro h
      apply hTidEq
      exact (beq_iff_eq.mp h).symm
    have hLookTid : ({ st with objects := st.objects.insert oid obj }.objects)[tid.toObjId]?
                    = st.objects[tid.toObjId]? := by
      show (st.objects.insert oid obj)[tid.toObjId]? = st.objects[tid.toObjId]?
      exact RobinHood.RHTable.getElem?_insert_ne st.objects oid tid.toObjId obj hTidNe hObjInv
    show (match ({ st with objects := st.objects.insert oid obj }.objects[tid.toObjId]? :
              Option KernelObject) with
          | some (.tcb tcb) => _
          | _ => True)
    rw [hLookTid]
    cases hPre : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp
    | some preObj =>
      cases preObj with
      | tcb tcb =>
        simp only
        intro hBind
        -- Now check `scId.toObjId`:
        by_cases hScEq : scId.toObjId = oid
        · -- post-state at scId.toObjId is `obj`; not an SC → inner match `_ => True`.
          show (match ({ st with objects := st.objects.insert oid obj }.objects[scId.toObjId]? :
                    Option KernelObject) with
                | some (.schedContext sc) => _
                | _ => True)
          have hLookSc : ({ st with objects := st.objects.insert oid obj }.objects)[scId.toObjId]?
                          = some obj := by
            show (st.objects.insert oid obj)[scId.toObjId]? = some obj
            have hShow : (st.objects.insert oid obj)[scId.toObjId]? =
                          (st.objects.insert oid obj).get? scId.toObjId := rfl
            rw [hShow, hScEq]
            exact RobinHood.RHTable.getElem?_insert_self st.objects oid obj hObjInv
          rw [hLookSc]
          cases hObj : obj with
          | schedContext sc => exact absurd hObj (hNotSc sc)
          | _ => simp
        · -- post-state at scId.toObjId equals pre-state at scId.toObjId.
          have hScNe : ¬(oid == scId.toObjId) = true := by
            intro h; apply hScEq; exact (beq_iff_eq.mp h).symm
          have hLookSc : ({ st with objects := st.objects.insert oid obj }.objects)[scId.toObjId]?
                          = st.objects[scId.toObjId]? := by
            show (st.objects.insert oid obj)[scId.toObjId]? = st.objects[scId.toObjId]?
            exact RobinHood.RHTable.getElem?_insert_ne st.objects oid scId.toObjId obj hScNe hObjInv
          show (match ({ st with objects := st.objects.insert oid obj }.objects[scId.toObjId]? :
                    Option KernelObject) with
                | some (.schedContext sc) => _
                | _ => True)
          rw [hLookSc]
          -- Apply pre-state invariant
          have hPreInv : boundThreadDomainConsistent st := hDom
          have hLookTcb : st.objects[tid.toObjId]? = some (.tcb tcb) := hPre
          have hAtPair := hPreInv tid scId
          rw [hLookTcb] at hAtPair
          simp only at hAtPair
          exact hAtPair hBind
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
        | schedContext _ | reply _ => simp

/-- WS-RC R5.G.3 / Phase P2: A joint update that rewrites a SchedContext's
    `domain` to `⟨domain⟩` AND rewrites its bound TCB's `domain` to
    `⟨domain⟩` (synchronously) preserves `boundThreadDomainConsistent`,
    under additional hypotheses:

    - The SC's bound thread IS the TCB being rewritten.
    - The TCB's `schedContextBinding` points back at this SC.
    - The SC and TCB live at distinct ObjIds.
    - The pre-state satisfies `boundThreadDomainConsistent` AND
      `schedContextBindingConsistent` (the latter rules out a
      dangling-binding corner case).

    This is the workhorse frame lemma for R5.G.3's substantive
    preservation proof. -/
theorem objects_update_sync_domain_preserves_boundThreadDomainConsistent
    (st : SystemState) (scObjId : SeLe4n.ObjId) (sc : SchedContext)
    (boundTid : SeLe4n.ThreadId) (boundTcb : TCB) (domain : Nat)
    (sc' : SchedContext) (tcb' : TCB)
    (hSc : st.objects[scObjId]? = some (.schedContext sc))
    (hSCBT : sc.boundThread = some boundTid)
    (_hTcb : st.objects[boundTid.toObjId]? = some (.tcb boundTcb))
    (hTcbBind : boundTcb.schedContextBinding = .bound ⟨scObjId.toNat⟩)
    (hNeq : boundTid.toObjId ≠ scObjId)
    (hSCDom' : sc'.domain = ⟨domain⟩)
    (_hSCBT' : sc'.boundThread = sc.boundThread)
    (hTcbDom' : tcb'.domain = ⟨domain⟩)
    (hTcbBind' : tcb'.schedContextBinding = boundTcb.schedContextBinding)
    (hObjInv : st.objects.invExt)
    (hObjInvAfterSc : (st.objects.insert scObjId (.schedContext sc')).invExt)
    (hDom : boundThreadDomainConsistent st)
    (hBind : schedContextBindingConsistent st) :
    boundThreadDomainConsistent
      { st with objects :=
        (st.objects.insert scObjId (.schedContext sc')).insert boundTid.toObjId (.tcb tcb') } := by
  intro tid scId
  -- The post-state's objects are `(insert scObjId sc').insert boundTid.toObjId tcb'`.
  -- We case-split on `tid.toObjId` and `scId.toObjId` against `boundTid.toObjId` and
  -- `scObjId`.
  -- First, characterise lookups in the post-state's `objects`.
  let obj2 := (st.objects.insert scObjId (.schedContext sc')).insert boundTid.toObjId (.tcb tcb')
  have hLookBound : obj2[boundTid.toObjId]? = some (.tcb tcb') := by
    show (obj2).get? boundTid.toObjId = _
    exact RobinHood.RHTable.getElem?_insert_self _ boundTid.toObjId (.tcb tcb') hObjInvAfterSc
  have hLookSc : obj2[scObjId]? = some (.schedContext sc') := by
    show (obj2).get? scObjId = _
    have hNeBE : ¬(boundTid.toObjId == scObjId) = true := by
      intro h
      apply hNeq
      exact beq_iff_eq.mp h
    rw [RobinHood.RHTable.getElem?_insert_ne _ boundTid.toObjId scObjId (.tcb tcb') hNeBE hObjInvAfterSc]
    exact RobinHood.RHTable.getElem?_insert_self st.objects scObjId (.schedContext sc') hObjInv
  have hLookOther : ∀ (k : SeLe4n.ObjId),
      k ≠ boundTid.toObjId → k ≠ scObjId →
      obj2[k]? = st.objects[k]? := by
    intro k hkBd hkSc
    show (obj2).get? k = _
    have hNeBd : ¬(boundTid.toObjId == k) = true := by
      intro h; apply hkBd; exact (beq_iff_eq.mp h).symm
    have hNeSc : ¬(scObjId == k) = true := by
      intro h; apply hkSc; exact (beq_iff_eq.mp h).symm
    rw [RobinHood.RHTable.getElem?_insert_ne _ boundTid.toObjId k (.tcb tcb') hNeBd hObjInvAfterSc,
        RobinHood.RHTable.getElem?_insert_ne _ scObjId k (.schedContext sc') hNeSc hObjInv]
    rfl
  -- Case on tid.toObjId vs (boundTid.toObjId, scObjId).
  by_cases hTidBd : tid.toObjId = boundTid.toObjId
  · -- tid = boundTid: post-state TCB is tcb'.
    have hLookTid : obj2[tid.toObjId]? = some (.tcb tcb') := by
      rw [hTidBd]; exact hLookBound
    show (match (obj2[tid.toObjId]? : Option KernelObject) with
          | some (.tcb tcb) => _
          | _ => True)
    rw [hLookTid]
    simp only
    intro hBindNew
    -- hBindNew: tcb'.schedContextBinding = .bound scId
    -- We have tcb'.schedContextBinding = boundTcb.schedContextBinding = .bound ⟨scObjId.toNat⟩
    rw [hTcbBind', hTcbBind] at hBindNew
    -- hBindNew : SchedContextBinding.bound ⟨scObjId.toNat⟩ = .bound scId
    have hScIdEq : scId = ⟨scObjId.toNat⟩ := by
      injection hBindNew with hScIdEq
      exact hScIdEq.symm
    -- Therefore scId.toObjId = scObjId.
    have hScIdObj : scId.toObjId = scObjId := by
      rw [hScIdEq]; rfl
    show (match (obj2[scId.toObjId]? : Option KernelObject) with
          | some (.schedContext sc) => _
          | _ => True)
    have hLookScId : obj2[scId.toObjId]? = some (.schedContext sc') := by
      rw [hScIdObj]; exact hLookSc
    rw [hLookScId]
    simp only
    -- Goal: tcb'.domain = sc'.domain
    rw [hTcbDom', hSCDom']
  · -- tid ≠ boundTid
    -- Sub-case on tid.toObjId = scObjId:
    by_cases hTidSc : tid.toObjId = scObjId
    · -- tid.toObjId = scObjId: post-state is the SC, outer match `_ => True`.
      have hLookTid : obj2[tid.toObjId]? = some (.schedContext sc') := by
        rw [hTidSc]; exact hLookSc
      show (match (obj2[tid.toObjId]? : Option KernelObject) with
            | some (.tcb tcb) => _
            | _ => True)
      rw [hLookTid]; simp
    · -- tid.toObjId is neither boundTid.toObjId nor scObjId: lookup = pre-state.
      have hLookTid : obj2[tid.toObjId]? = st.objects[tid.toObjId]? :=
        hLookOther tid.toObjId hTidBd hTidSc
      show (match (obj2[tid.toObjId]? : Option KernelObject) with
            | some (.tcb tcb) => _
            | _ => True)
      rw [hLookTid]
      cases hPreObj : (st.objects[tid.toObjId]? : Option KernelObject) with
      | none => simp
      | some preObj =>
        cases preObj with
        | tcb otherTcb =>
          simp only
          intro hOtherBind
          -- Need to show: at scId.toObjId, the (otherTcb, sc-in-post-state) pair satisfies domain match.
          -- Use pre-state invariant on (tid, scId).
          have hPreAt := hDom tid scId
          rw [hPreObj] at hPreAt
          simp only at hPreAt
          have hPreSubBind := hPreAt hOtherBind
          -- Now sub-case on scId.toObjId:
          by_cases hScIdSc : scId.toObjId = scObjId
          · -- scId.toObjId = scObjId: post-state SC is sc'.
            -- We need: otherTcb.domain = sc'.domain.
            -- Pre-state: otherTcb.domain = sc.domain (since pre-state SC at scObjId = sc).
            -- But sc'.domain = ⟨domain⟩, while sc.domain might differ.
            -- HOWEVER, by schedContextBindingConsistent, sc.boundThread = some tid.
            -- But sc.boundThread = some boundTid, so tid = boundTid, contradicting hTidBd.
            exfalso
            -- From hOtherBind: otherTcb.schedContextBinding = .bound scId
            -- scId.toObjId = scObjId means scId = ⟨scObjId.toNat⟩
            -- So otherTcb.schedContextBinding = .bound ⟨scObjId.toNat⟩
            -- By schedContextBindingConsistent (forward direction):
            --   For TCB otherTcb at tid with binding .bound scId,
            --   ∃ sc'', st.objects[scId.toObjId]? = some (.schedContext sc'') ∧ sc''.boundThread = some tid
            -- scId.toObjId = scObjId, so by hSc: sc'' = sc.
            -- So sc.boundThread = some tid, but sc.boundThread = some boundTid.
            -- So tid = boundTid, contradicting hTidBd.
            obtain ⟨hBindFwd, _⟩ := hBind
            have hOtherInStore : st.objects[tid.toObjId]? = some (.tcb otherTcb) := hPreObj
            have hExists := hBindFwd tid otherTcb hOtherInStore scId hOtherBind
            obtain ⟨sc'', hScStore, hScBound⟩ := hExists
            -- scId.toObjId = scObjId, so st.objects[scId.toObjId]? = st.objects[scObjId]? = some (.schedContext sc).
            have hRewrite : st.objects[scId.toObjId]? = some (.schedContext sc) := by
              rw [hScIdSc]; exact hSc
            rw [hRewrite] at hScStore
            injection hScStore with hScScEq
            -- hScScEq : (.schedContext sc'' : KernelObject) = .schedContext sc, so sc'' = sc.
            cases hScScEq
            -- Now hScBound : sc.boundThread = some tid.
            rw [hSCBT] at hScBound
            injection hScBound with hTidEq
            -- hTidEq : boundTid = tid; so tid = boundTid.
            exact hTidBd (congrArg ThreadId.toObjId hTidEq.symm)
          · -- scId.toObjId ≠ scObjId, so look up in pre-state.
            -- Also need scId.toObjId ≠ boundTid.toObjId? Not necessarily, but if equal then
            -- post-state would have a TCB, not SC, so inner match falls to `_ => True`.
            by_cases hScIdBd : scId.toObjId = boundTid.toObjId
            · -- post-state at scId.toObjId is tcb', not SC.
              have hLookScId : obj2[scId.toObjId]? = some (.tcb tcb') := by
                rw [hScIdBd]; exact hLookBound
              show (match (obj2[scId.toObjId]? : Option KernelObject) with
                    | some (.schedContext sc) => _
                    | _ => True)
              rw [hLookScId]; simp
            · -- scId.toObjId neither bound nor sc: post-state = pre-state.
              have hLookScId : obj2[scId.toObjId]? = st.objects[scId.toObjId]? :=
                hLookOther scId.toObjId hScIdBd hScIdSc
              show (match (obj2[scId.toObjId]? : Option KernelObject) with
                    | some (.schedContext sc) => _
                    | _ => True)
              rw [hLookScId]
              exact hPreSubBind
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
          | schedContext _ | reply _ => simp

end SeLe4n.Kernel
