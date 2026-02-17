import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Choose the first runnable thread, if any. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match st.scheduler.runnable with
    | [] => .ok (none, st)
    | t :: _ => .ok (some t, st)

/-- Simple scheduler step for the bootstrap model. If the selected runnable TID does not map
to a TCB object, the scheduler clears `current` instead of selecting an invalid thread. -/
def schedule : Kernel Unit :=
  fun st =>
    match st.scheduler.runnable with
    | [] => setCurrentThread none st
    | t :: _ =>
        match st.objects t.toObjId with
        | some (.tcb _) => setCurrentThread (some t) st
        | _ => setCurrentThread none st

/-- Placeholder syscall dispatcher with one implemented path for now. -/
def handleYield : Kernel Unit :=
  schedule

theorem schedule_eq_chooseThread_then_setCurrent :
    schedule = (fun st =>
      match chooseThread st with
      | .error e => .error e
      | .ok (next, st') =>
          match next with
          | none => setCurrentThread none st'
          | some tid =>
              match st'.objects tid.toObjId with
              | some (.tcb _) => setCurrentThread (some tid) st'
              | _ => setCurrentThread none st') := by
  funext st
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, chooseThread, setCurrentThread, hRun]
  | cons t ts =>
      cases hObj : st.objects t.toObjId <;>
      simp [schedule, chooseThread, setCurrentThread, hRun, hObj]

theorem setCurrentThread_preserves_wellFormed
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [schedulerWellFormed, queueCurrentConsistent] using hMem

theorem setCurrentThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [queueCurrentConsistent, hMem]

theorem setCurrentThread_preserves_runQueueUnique
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [runQueueUnique] using hUnique

theorem setCurrentThread_none_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [currentThreadValid]

theorem setCurrentThread_some_preserves_currentThreadValid
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hObj : ∃ tcb : TCB, st.objects tid.toObjId = some (.tcb tcb))
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [currentThreadValid] using hObj

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
      simp [schedulerWellFormed, queueCurrentConsistent]
  | cons t ts =>
      cases hObj : st.objects t.toObjId with
      | none =>
          simp [schedule, setCurrentThread, hRun, hObj] at hStep
          cases hStep
          simp [schedulerWellFormed, queueCurrentConsistent]
      | some obj =>
          cases obj with
          | tcb tcb =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed, queueCurrentConsistent]
          | endpoint ep =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed, queueCurrentConsistent]
          | cnode cn =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed, queueCurrentConsistent]

theorem chooseThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hConsistent : queueCurrentConsistent st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    queueCurrentConsistent st'.scheduler := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hConsistent

theorem schedule_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, setCurrentThread, hRun] at hStep
      cases hStep
      simp [queueCurrentConsistent]
  | cons t ts =>
      cases hObj : st.objects t.toObjId with
      | none =>
          simp [schedule, setCurrentThread, hRun, hObj] at hStep
          cases hStep
          simp [queueCurrentConsistent]
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_preserves_queueCurrentConsistent st st' t
                (by simp [hRun])
                (by simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [queueCurrentConsistent]
          | cnode cn =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [queueCurrentConsistent]

theorem handleYield_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simpa [handleYield] using schedule_preserves_queueCurrentConsistent st st' hStep

theorem chooseThread_preserves_runQueueUnique
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    runQueueUnique st'.scheduler := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hUnique

theorem chooseThread_preserves_currentThreadValid
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hValid : currentThreadValid st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadValid st' := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hValid

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
      cases hObj : st.objects t.toObjId with
      | none =>
          exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
            simpa [schedule, hRun, hObj] using hStep)
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_preserves_runQueueUnique st st' (some t) hUnique (by
                simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
                simpa [schedule, hRun, hObj] using hStep)
          | cnode cn =>
              exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
                simpa [schedule, hRun, hObj] using hStep)

theorem schedule_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadValid st' := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      exact setCurrentThread_none_preserves_currentThreadValid st st' (by
        simpa [schedule, hRun] using hStep)
  | cons t ts =>
      cases hObj : st.objects t.toObjId with
      | none =>
          exact setCurrentThread_none_preserves_currentThreadValid st st' (by
            simpa [schedule, hRun, hObj] using hStep)
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_some_preserves_currentThreadValid st st' t
                ⟨tcb, hObj⟩
                (by simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              exact setCurrentThread_none_preserves_currentThreadValid st st' (by
                simpa [schedule, hRun, hObj] using hStep)
          | cnode cn =>
              exact setCurrentThread_none_preserves_currentThreadValid st st' (by
                simpa [schedule, hRun, hObj] using hStep)

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

theorem handleYield_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadValid st' := by
  simpa [handleYield] using schedule_preserves_currentThreadValid st st' hStep

theorem chooseThread_preserves_kernelInvariant
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : kernelInvariant st)
    (hStep : chooseThread st = .ok (next, st')) :
    kernelInvariant st' := by
  exact ⟨
    chooseThread_preserves_queueCurrentConsistent st st' next hInv.1 hStep,
    chooseThread_preserves_runQueueUnique st st' next hInv.2.1 hStep,
    chooseThread_preserves_currentThreadValid st st' next hInv.2.2 hStep
  ⟩

theorem schedule_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : schedule st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨schedule_preserves_queueCurrentConsistent st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2.1 hStep,
    schedule_preserves_currentThreadValid st st' hStep⟩

theorem handleYield_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : handleYield st = .ok ((), st')) :
    kernelInvariant st' := by
  simpa [handleYield] using schedule_preserves_kernelInvariant st st' hInv hStep

theorem chooseThread_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' := by
  exact chooseThread_preserves_kernelInvariant st st' next hInv hStep

theorem schedule_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact schedule_preserves_kernelInvariant st st' hInv hStep

theorem handleYield_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact handleYield_preserves_kernelInvariant st st' hInv hStep


end SeLe4n.Kernel
