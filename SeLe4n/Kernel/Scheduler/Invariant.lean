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

/-- Scheduler invariant component #3 (M1 bundle v1): queue/current consistency.

Policy choice for this model is **strict**: when `current = some tid`, `tid` must appear in the
runnable queue. The relaxed policy (allowing absence while blocked/idle) is intentionally deferred
until explicit blocked/idle scheduler state is modeled. -/
def queueCurrentConsistent (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Minimal scheduling well-formedness condition for the bootstrap model.

At this stage the condition is intentionally identical to `queueCurrentConsistent` and is kept as
an alias so milestone wording can evolve without duplicating theorem maintenance. -/
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

/-- Invariant bundle that should eventually mirror seL4 proof obligations.

M-05 domain partitioning is treated as normative in WS-E6: whenever a current
thread exists, it must belong to `activeDomain`. -/
def kernelInvariant (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧
    runQueueUnique st.scheduler ∧
    currentThreadValid st ∧
    currentThreadInActiveDomain st

/-- Scheduler Invariant Bundle v1 entrypoint used by composed IPC/architecture bundles.

`kernelInvariant` now includes the domain-partitioning obligation
`currentThreadInActiveDomain`; this compatibility bundle intentionally keeps the
legacy triad used by cross-subsystem composition surfaces. -/
def schedulerInvariantBundle (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧ runQueueUnique st.scheduler ∧ currentThreadValid st

/-- Canonical scheduler invariant bundle for domain-partitioning semantics.

This is the normative scheduler proof surface and includes
`currentThreadInActiveDomain`. -/
abbrev canonicalSchedulerInvariantBundle (st : SystemState) : Prop :=
  kernelInvariant st

theorem schedulerWellFormed_iff_queueCurrentConsistent (s : SchedulerState) :
    schedulerWellFormed s ↔ queueCurrentConsistent s := by
  simp [schedulerWellFormed, queueCurrentConsistent]

theorem queueCurrentConsistent_when_no_current
    (s : SchedulerState)
    (hNone : s.current = none) :
    queueCurrentConsistent s := by
  simp [queueCurrentConsistent, hNone]

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

-- ============================================================================
-- M-03/WS-E6: EDF scheduling invariant
-- ============================================================================

/-- M-03/WS-E6: The currently scheduled thread has the earliest deadline
among all runnable threads at the same priority level. This captures the
EDF policy: within equal priority, the thread with the most urgent deadline
is selected. -/
def edfCurrentHasEarliestDeadline (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some curTid =>
      match st.objects[curTid.toObjId]? with
      | some (.tcb curTcb) =>
          ∀ tid, tid ∈ st.scheduler.runnable →
            match st.objects[tid.toObjId]? with
            | some (.tcb tcb) =>
                tcb.priority = curTcb.priority →
                curTcb.deadline.toNat = 0 ∨
                (tcb.deadline.toNat = 0 ∨ curTcb.deadline.toNat ≤ tcb.deadline.toNat)
            | _ => True
      | _ => True

end SeLe4n.Kernel
