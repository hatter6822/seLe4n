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
def schedule : Kernel Unit :=
  fun st =>
    match st.scheduler.runnable with
    | [] => setCurrentThread none st
    | t :: _ => setCurrentThread (some t) st

/-- Placeholder syscall dispatcher with one implemented path for now. -/
def handleYield : Kernel Unit :=
  schedule

theorem schedule_eq_chooseThread_then_setCurrent :
    schedule = (fun st =>
      match chooseThread st with
      | .error e => .error e
      | .ok (next, st') => setCurrentThread next st') := by
  funext st
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, chooseThread, setCurrentThread, hRun]
  | cons t ts =>
      simp [schedule, chooseThread, setCurrentThread, hRun]

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
      ((next = none ∧ st.scheduler.runnable = []) ∨
       ∃ tid, next = some tid ∧ tid ∈ st.scheduler.runnable) := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [chooseThread, hRun] at hStep
      rcases hStep with ⟨hNext, hSt⟩
      have hNext' : next = none := hNext.symm
      subst hNext'
      subst hSt
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | cons t ts =>
      simp [chooseThread, hRun] at hStep
      rcases hStep with ⟨hNext, hSt⟩
      have hNext' : next = some t := hNext.symm
      subst hNext'
      subst hSt
      exact ⟨rfl, Or.inr ⟨t, rfl, by simp⟩⟩

theorem schedule_preserves_wellFormed
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, setCurrentThread, hRun] at hStep
      cases hStep
      simp [schedulerWellFormed]
  | cons t ts =>
      simp [schedule, setCurrentThread, hRun] at hStep
      cases hStep
      simp [schedulerWellFormed]

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simpa [handleYield] using schedule_preserves_wellFormed st st' hStep

end SeLe4n.Kernel
