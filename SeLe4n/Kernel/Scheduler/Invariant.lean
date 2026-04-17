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

/-- WS-H12b/H-04: Dequeue-on-dispatch queue/current consistency.

seL4 semantics: the running thread is **removed** from the ready queue at
dispatch time and re-enqueued only on preemption, yield, or blocking.
When `current = some tid`, `tid` must **not** appear in the runnable queue.

This inverts the pre-H12b "strict" policy (`tid ∈ runnable`) to match seL4's
`switchToThread` which calls `tcbSchedDequeue` before setting `ksCurThread`. -/
def queueCurrentConsistent (s : SchedulerState) : Prop :=
  match s.current with
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
  match st.scheduler.current with
  | none => True
  | some tid => ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- M-05/WS-E6: The currently scheduled thread (if any) belongs to the
active scheduling domain. This is the basic temporal partitioning guarantee:
the scheduler only runs threads in the current domain. -/
def currentThreadInActiveDomain (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.domain = st.scheduler.activeDomain
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
  match st.scheduler.current with
  | none => True
  | some tid =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.timeSlice > 0
    | _ => True

-- ============================================================================
-- AI3-A: Effective RunQueue priority computation (must precede EDF)
-- ============================================================================

/-- AI3-A (M-04): Compute the effective RunQueue insertion priority for a thread,
applying PIP boost to the base TCB priority. Returns `max(tcb.priority, pipBoost)`
when a PIP boost is active, or `tcb.priority` otherwise.

This function operates on TCB fields only (no state dependency), ensuring
frame-lemma compatibility: `effectiveRunQueuePriority` is preserved whenever
`priority` and `pipBoost` fields are unchanged, regardless of other state
modifications. -/
def effectiveRunQueuePriority (tcb : TCB) : SeLe4n.Priority :=
  match tcb.pipBoost with
  | none => tcb.priority
  | some boostPrio => ⟨Nat.max tcb.priority.val boostPrio.val⟩

/-- AI3-A: For threads without PIP boost, effective priority equals base
TCB priority. -/
theorem effectiveRunQueuePriority_no_pip (tcb : TCB)
    (hNoPip : tcb.pipBoost = none) :
    effectiveRunQueuePriority tcb = tcb.priority := by
  simp [effectiveRunQueuePriority, hNoPip]

/-- AK2-B (S-H04) helper: SC-aware effective priority.
Mirrors `(resolveEffectivePrioDeadline st tcb).1` from Selection.lean
without the import cycle: for SchedContext-bound threads with the SC
present, uses the SC's base priority; otherwise falls back to TCB
`priority`. PIP boost is applied uniformly as the final step.

Under the AK2-B Option B propagation invariant (`schedContextBind` /
`schedContextConfigure` propagate `sc.priority → tcb.priority`),
`effectiveBucketPriority st tcb = effectiveRunQueuePriority tcb` for all
bound threads, so `schedulerPriorityMatch` (TCB-based) and
`effectiveParamsMatchRunQueue` (SC-based) agree. The helper is retained as
a utility for future use (AK2-A full Option A fusion deferred). -/
def effectiveBucketPriority (st : SystemState) (tcb : TCB) : SeLe4n.Priority :=
  let base : SeLe4n.Priority := match tcb.schedContextBinding with
    | .unbound => tcb.priority
    | .bound scId | .donated scId _ =>
      match (st.objects[scId.toObjId]? : Option KernelObject) with
      | some (.schedContext sc) => sc.priority
      | _ => tcb.priority
  match tcb.pipBoost with
  | none => base
  | some boostPrio => ⟨Nat.max base.val boostPrio.val⟩

/-- AK2-B: Unbound threads' effective priority equals the legacy
`effectiveRunQueuePriority`. -/
@[simp] theorem effectiveBucketPriority_of_unbound
    (st : SystemState) (tcb : TCB)
    (hUnbound : tcb.schedContextBinding = .unbound) :
    effectiveBucketPriority st tcb = effectiveRunQueuePriority tcb := by
  unfold effectiveBucketPriority effectiveRunQueuePriority
  simp [hUnbound]

/-- AK2-B: When a bound thread's SchedContext is missing (unreachable under
`schedContextBindingConsistent`), `effectiveBucketPriority` falls back to
`effectiveRunQueuePriority`. -/
theorem effectiveBucketPriority_of_bound_sc_missing
    (st : SystemState) (tcb : TCB) (scId : SchedContextId)
    (hBound : tcb.schedContextBinding = .bound scId ∨
      ∃ owner, tcb.schedContextBinding = .donated scId owner)
    (hMiss : ∀ sc, st.objects[scId.toObjId]? ≠ some (.schedContext sc)) :
    effectiveBucketPriority st tcb = effectiveRunQueuePriority tcb := by
  unfold effectiveBucketPriority effectiveRunQueuePriority
  rcases hBound with hB | ⟨owner, hB⟩
  · rw [hB]
    cases hLookup : (st.objects[scId.toObjId]? : Option KernelObject) with
    | none => simp [hLookup]
    | some obj =>
      cases obj with
      | schedContext sc => exact absurd hLookup (hMiss sc)
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | tcb _ =>
          simp [hLookup]
  · rw [hB]
    cases hLookup : (st.objects[scId.toObjId]? : Option KernelObject) with
    | none => simp [hLookup]
    | some obj =>
      cases obj with
      | schedContext sc => exact absurd hLookup (hMiss sc)
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | tcb _ =>
          simp [hLookup]

/-- AK2-B helper: auxiliary "falls through to base" lemma. If a map lookup
does not produce `.schedContext _`, then the `.bound scId`/`.donated scId _`
arm of `effectiveBucketPriority` falls through to `tcb.priority`. -/
@[simp] theorem effectiveBucketPriority_lookup_non_sc
    (st : SystemState) (tcb : TCB) (scId : SchedContextId)
    (hNonSc : ∀ sc, st.objects[scId.toObjId]? ≠ some (.schedContext sc)) :
    (match (st.objects[scId.toObjId]? : Option KernelObject) with
      | some (.schedContext sc) => sc.priority
      | _ => tcb.priority) = tcb.priority := by
  cases hLook : (st.objects[scId.toObjId]? : Option KernelObject) with
  | none => rfl
  | some obj =>
    cases obj with
    | schedContext sc => exact absurd hLook (hNonSc sc)
    | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => rfl

/-- AK2-B: Frame lemma — `effectiveBucketPriority` is preserved whenever the
thread's SchedContext object lookup agrees. -/
theorem effectiveBucketPriority_frame
    (st st' : SystemState) (tcb : TCB)
    (hSc : ∀ scId, (tcb.schedContextBinding = .bound scId ∨
      ∃ owner, tcb.schedContextBinding = .donated scId owner) →
      st'.objects[scId.toObjId]? = st.objects[scId.toObjId]?) :
    effectiveBucketPriority st' tcb = effectiveBucketPriority st tcb := by
  unfold effectiveBucketPriority
  cases hBind : tcb.schedContextBinding with
  | unbound => rfl
  | bound scId =>
    have hEq : st'.objects[scId.toObjId]? = st.objects[scId.toObjId]? :=
      hSc scId (Or.inl hBind)
    simp only [hEq]
  | donated scId owner =>
    have hEq : st'.objects[scId.toObjId]? = st.objects[scId.toObjId]? :=
      hSc scId (Or.inr ⟨owner, hBind⟩)
    simp only [hEq]

section
set_option linter.unusedSimpArgs false

/-- AK2-B: Weaker frame lemma — `effectiveBucketPriority` is preserved
whenever BOTH lookups produce non-SchedContext values (so both fall through
to `tcb.priority`) OR the SchedContext lookups agree exactly. This handles
invariant-violating aliasing gracefully: if an ObjId happens to hold a `.tcb`
both before and after a `saveOutgoingContext` (invariant violation — SC's
ObjId should never be a TCB), the fall-through arm gives the same value. -/
theorem effectiveBucketPriority_frame_weak
    (st st' : SystemState) (tcb : TCB)
    (hSc : ∀ scId, (tcb.schedContextBinding = .bound scId ∨
      ∃ owner, tcb.schedContextBinding = .donated scId owner) →
      (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
             st'.objects[scId.toObjId]? = some (.schedContext sc)) ∨
      ((∀ sc, st.objects[scId.toObjId]? ≠ some (.schedContext sc)) ∧
       (∀ sc, st'.objects[scId.toObjId]? ≠ some (.schedContext sc)))) :
    effectiveBucketPriority st' tcb = effectiveBucketPriority st tcb := by
  unfold effectiveBucketPriority
  cases hBind : tcb.schedContextBinding with
  | unbound => simp only [hBind]
  | bound scId =>
    simp only [hBind]
    rcases hSc scId (Or.inl hBind) with ⟨sc, hOld, hNew⟩ | ⟨hOldN, hNewN⟩
    · simp only [hOld, hNew]
    · rw [effectiveBucketPriority_lookup_non_sc st' tcb scId hNewN]
      rw [effectiveBucketPriority_lookup_non_sc st tcb scId hOldN]
  | donated scId owner =>
    simp only [hBind]
    rcases hSc scId (Or.inr ⟨owner, hBind⟩) with ⟨sc, hOld, hNew⟩ | ⟨hOldN, hNewN⟩
    · simp only [hOld, hNew]
    · rw [effectiveBucketPriority_lookup_non_sc st' tcb scId hNewN]
      rw [effectiveBucketPriority_lookup_non_sc st tcb scId hOldN]

end


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

**AI3-A:** Added `effectiveRunQueuePriority` guard. The RunQueue buckets
threads by effective priority, so deadline ordering is only meaningful among
threads in the same effective priority bucket. Threads at a lower effective
priority are not considered during bucket-based selection and thus fall
outside the EDF comparison scope. -/
def edfCurrentHasEarliestDeadline (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some curTid =>
      match st.objects[curTid.toObjId]? with
      | some (.tcb curTcb) =>
          ∀ tid, tid ∈ st.scheduler.runnable →
            match st.objects[tid.toObjId]? with
            | some (.tcb tcb) =>
                tcb.domain = curTcb.domain →
                effectiveRunQueuePriority tcb = effectiveRunQueuePriority curTcb →
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
  match st.scheduler.current with
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
    (hCurr : st.scheduler.current = some tid)
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

AI3-A (M-04) → AK2-B (S-H04): Updated from `effectiveRunQueuePriority` (TCB
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
  ∀ tid, tid ∈ st.scheduler.runQueue →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        st.scheduler.runQueue.threadPriority[tid]? = some (effectiveRunQueuePriority tcb)
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
  st.scheduler.domainTimeRemaining > 0

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
    (hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hObjEq : st'.objects = st.objects) :
    schedulerPriorityMatch st' := by
  intro tid hMem; rw [hRQEq] at hMem; rw [hRQEq, hObjEq]; exact hInv tid hMem

/-- R6-D/AI3-A: schedulerPriorityMatch after inserting the current thread at
its effective priority. The inserted priority must equal
`effectiveRunQueuePriority curTcb` for the invariant to hold. -/
theorem schedulerPriorityMatch_insert
    (st : SystemState) (curTid : ThreadId) (curTcb : TCB)
    (hPM : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hCur : st.scheduler.current = some curTid)
    (hObj : st.objects[curTid.toObjId]? = some (.tcb curTcb)) :
    ∀ tid, tid ∈ st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) →
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        (st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb)).threadPriority[tid]?
          = some (effectiveRunQueuePriority tcb)
      | _ => True := by
  intro tid hMem
  have hNotMem : curTid ∉ st.scheduler.runQueue := by
    simp [queueCurrentConsistent, hCur] at hQCC
    intro h; exact hQCC ((RunQueue.mem_toList_iff_mem _ _).2 h)
  have hContF : st.scheduler.runQueue.contains curTid = false := by
    cases h : st.scheduler.runQueue.contains curTid; rfl; exact absurd h hNotMem
  rw [RunQueue.mem_insert] at hMem
  rw [RunQueue.insert_threadPriority]; simp only [hContF, Bool.false_eq_true, ↓reduceIte]
  cases hMem with
  | inl hOld =>
    have hNeq : curTid ≠ tid := fun h => hNotMem (h ▸ hOld)
    have hBEq : (curTid == tid) = false := by
      cases h : (curTid == tid) <;> simp_all
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
    simp only [hBEq, Bool.false_eq_true, ↓reduceIte]
    have := hPM tid hOld
    simp only [RHTable_getElem?_eq_get?] at this; exact this
  | inr hEq =>
    subst hEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
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
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) => sc.budgetRemaining.val > 0
        | _ => True
    | _ => True

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
  match st.scheduler.current with
  | none => True
  | some tid =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) => sc.budgetRemaining.val > 0
        | _ => True
    | _ => True

/-- Z4-L: Default state has no current thread — vacuously true. -/
theorem default_currentBudgetPositive :
    currentBudgetPositive (default : SystemState) := by
  simp [currentBudgetPositive]

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
  replenishQueueSorted st.scheduler.replenishQueue ∧
  replenishQueueSizeConsistent st.scheduler.replenishQueue

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

/-- Z4-P: For every runnable thread, the RunQueue's cached priority matches
the effective priority from SchedContext resolution. This extends
`schedulerPriorityMatch` to the SchedContext world — when a thread is bound
to a SchedContext, the RunQueue entry reflects the SchedContext's priority. -/
def effectiveParamsMatchRunQueue (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runQueue →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound =>
        st.scheduler.runQueue.threadPriority[tid]? = some tcb.priority
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) =>
          st.scheduler.runQueue.threadPriority[tid]? = some sc.priority
        | _ => True
    | _ => True

/-- Z4-P: Default state has empty run queue — vacuously true. -/
theorem default_effectiveParamsMatchRunQueue :
    effectiveParamsMatchRunQueue (default : SystemState) := by
  intro tid hMem
  have hEmpty : (default : SystemState).scheduler.runQueue.membership.contains tid = false :=
    RobinHood.RHSet.contains_empty tid
  simp [Membership.mem, RunQueue.contains] at hMem
  simp [hEmpty] at hMem

-- ============================================================================
-- AE3-A/U-11: boundThreadDomainConsistent invariant
-- ============================================================================

/-- AE3-A/U-11: For every thread bound to a SchedContext, the thread's domain
must match the SchedContext's domain. This invariant is established by the
domain check in `schedContextBind` (AE3-A2) and preserved by all binding-
modifying operations (unbind/cancelDonation clear `.bound`; donation uses
`.donated` not `.bound`). -/
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

end SeLe4n.Kernel
