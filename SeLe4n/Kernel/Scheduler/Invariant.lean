/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

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
-- M-03/WS-E6: EDF scheduling invariant
-- ============================================================================

/-- M-03/WS-E6/WS-H6: The currently scheduled thread has the earliest deadline
among all runnable threads **in the same scheduling domain** at the same
priority level. This captures the domain-partitioned EDF policy: within equal
priority and equal domain, the thread with the most urgent deadline is selected.

**WS-H6 fix:** The original definition quantified over all runnable threads
regardless of domain, which was unprovable for a domain-aware scheduler that
only selects among same-domain candidates. Adding the domain constraint
aligns the invariant with `chooseBestRunnableInDomain` semantics. -/
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
      | some (.tcb tcb) => st.machine.regs = tcb.registerContext
      | _ => True
  | none => True

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

/-- WS-H6: The RunQueue's recorded `threadPriority` mapping matches the actual
TCB priority for every run-queue member.

This is an external-consistency predicate bridging the RunQueue's internal
`threadPriority` field to the authoritative TCB priority in the object store.
Together with `RunQueue.wellFormed`, it enables the bucket-first scheduling
proof: if a thread has the same priority as the selected candidate, it must
reside in the same priority bucket. -/
def schedulerPriorityMatch (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runQueue →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        st.scheduler.runQueue.threadPriority[tid]? = some tcb.priority
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

/-- R6-D: schedulerPriorityMatch after inserting the current thread at its priority.
    If the current thread has a TCB at its ObjId with the given priority,
    inserting it at that priority preserves the priority match. -/
theorem schedulerPriorityMatch_insert
    (st : SystemState) (curTid : ThreadId) (curTcb : TCB)
    (hPM : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hCur : st.scheduler.current = some curTid)
    (hObj : st.objects[curTid.toObjId]? = some (.tcb curTcb)) :
    ∀ tid, tid ∈ st.scheduler.runQueue.insert curTid curTcb.priority →
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        (st.scheduler.runQueue.insert curTid curTcb.priority).threadPriority[tid]? = some tcb.priority
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
    -- The goal has `if curTid == tid = true then ... else ...`
    -- After insert_threadPriority, ite on BEq
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




end SeLe4n.Kernel
