import SeLe4n.Model.State

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
  | some tid => ∃ tcb : TCB, st.objects tid = some (.tcb tcb)

/-- Invariant bundle that should eventually mirror seL4 proof obligations. -/
def kernelInvariant (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧ runQueueUnique st.scheduler ∧ currentThreadValid st

/-- Scheduler Invariant Bundle v1 entrypoint used by milestone wording in the spec/docs.
This is an alias of `kernelInvariant` to keep theorem names aligned with the development guide
without changing existing proof call sites. -/
abbrev schedulerInvariantBundle (st : SystemState) : Prop :=
  kernelInvariant st

theorem schedulerWellFormed_iff_queueCurrentConsistent (s : SchedulerState) :
    schedulerWellFormed s ↔ queueCurrentConsistent s := by
  simp [schedulerWellFormed, queueCurrentConsistent]

theorem queueCurrentConsistent_when_no_current
    (s : SchedulerState)
    (hNone : s.current = none) :
    queueCurrentConsistent s := by
  simp [queueCurrentConsistent, hNone]

end SeLe4n.Kernel
