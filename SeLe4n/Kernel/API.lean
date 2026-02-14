import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Minimal scheduling well-formedness condition for the bootstrap model. -/
def schedulerWellFormed (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Invariant bundle that should eventually mirror seL4 proof obligations. -/
def kernelInvariant (st : SystemState) : Prop :=
  schedulerWellFormed st.scheduler

/-- Choose the first runnable thread, if any. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
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
    (tid : SeLe4n.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [schedulerWellFormed, hMem]

theorem chooseThread_returns_runnable_or_none
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThread st = .ok (next, st')) :
    st' = st ∧
      (match next with
      | none => st.scheduler.runnable = []
      | some tid => tid ∈ st.scheduler.runnable) := by
  simp [chooseThread] at hStep
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [hRun] at hStep
      cases hStep
      simp [hRun]
  | cons t ts =>
      simp [hRun] at hStep
      cases hStep
      simp [hRun]

theorem schedule_preserves_wellFormed
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simp [schedule] at hStep
  rcases hStep with ⟨next, hChoose, hSet⟩
  rcases chooseThread_returns_runnable_or_none st _ next hChoose with ⟨rfl, hNext⟩
  cases hNextCase : next with
  | none =>
      simp [setCurrentThread, schedulerWellFormed] at hSet ⊢
      cases hSet
      simp [schedulerWellFormed]
  | some tid =>
      exact setCurrentThread_preserves_wellFormed st st' tid hNext hSet

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simpa [handleYield] using schedule_preserves_wellFormed st st' hStep

end SeLe4n.Kernel
