import SeLe4.Model.State

namespace SeLe4.Kernel

open SeLe4.Model

/-- Minimal scheduling well-formedness condition for the bootstrap model. -/
def schedulerWellFormed (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Invariant bundle that should eventually mirror seL4 proof obligations. -/
def kernelInvariant (st : SystemState) : Prop :=
  schedulerWellFormed st.scheduler

/-- Choose the first runnable thread, if any. -/
def chooseThread : Kernel (Option SeLe4.ThreadId) :=
  fun st =>
    match st.scheduler.runnable with
    | [] => .ok (none, st)
    | t :: _ => .ok (some t, st)

/-- Simple scheduler step for the bootstrap model. -/
def schedule : Kernel Unit := do
  let next ← chooseThread
  setCurrentThread next

/-- Placeholder syscall dispatcher with one implemented path for now. -/
def handleYield : Kernel Unit :=
  schedule

theorem setCurrentThread_preserves_wellFormed
    (st st' : SystemState)
    (tid : SeLe4.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [schedulerWellFormed, hMem]

end SeLe4.Kernel
