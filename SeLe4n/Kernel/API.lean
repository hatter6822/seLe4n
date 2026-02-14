import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Minimal scheduling well-formedness condition for the bootstrap model. -/
def schedulerWellFormed (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Scheduler invariant component #1 (M1 bundle v1): runnable queue has no duplicate TIDs. -/
def runQueueUnique (s : SchedulerState) : Prop :=
  s.runnable.Nodup

/-- Invariant bundle that should eventually mirror seL4 proof obligations. -/
def kernelInvariant (st : SystemState) : Prop :=
  schedulerWellFormed st.scheduler ∧ runQueueUnique st.scheduler

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

theorem setCurrentThread_preserves_runQueueUnique
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [runQueueUnique] using hUnique

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

theorem chooseThread_preserves_runQueueUnique
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    runQueueUnique st'.scheduler := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hUnique

theorem schedule_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : schedule st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
        simpa [schedule, hRun] using hStep)
  | cons t ts =>
      exact setCurrentThread_preserves_runQueueUnique st st' (some t) hUnique (by
        simpa [schedule, hRun] using hStep)

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simpa [handleYield] using schedule_preserves_wellFormed st st' hStep

theorem handleYield_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : handleYield st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simpa [handleYield] using schedule_preserves_runQueueUnique st st' hUnique hStep

theorem schedule_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : schedule st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨schedule_preserves_wellFormed st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2 hStep⟩

theorem handleYield_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : handleYield st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨handleYield_preserves_wellFormed st st' hStep,
    handleYield_preserves_runQueueUnique st st' hInv.2 hStep⟩

end SeLe4n.Kernel
