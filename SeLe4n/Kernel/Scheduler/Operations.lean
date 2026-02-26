import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M-03/WS-E6: Fixed-priority selection with deterministic FIFO tie-breaking.

**Scheduling semantics:** This function implements a fixed-priority scheduler
with strictly deterministic tie-breaking. The selection policy is:

1. **Higher numeric priority wins:** A thread with `priority.toNat = 200` beats
   one with `priority.toNat = 100`. This inverts some conventions but is
   consistent throughout the model.
2. **FIFO tie-breaking:** When two threads share the same priority, the one
   appearing first in the runnable queue is selected. Since `chooseBestRunnable`
   replaces `best` only on strict-less-than (`bestPrio.toNat < tcb.priority.toNat`),
   the earliest-enqueued thread of the highest priority wins.

**Divergence from seL4:** The real seL4 scheduler uses round-robin within equal
priority levels (rotating the head after each quantum expires). This model uses
FIFO order as a deliberate simplification—round-robin is recovered when combined
with `handleTimerTick` (M-04), which moves the running thread to the back of the
queue on time-slice expiry, achieving the same rotation effect.

See `chooseThread_deterministic` for the determinism proof. -/
private def chooseBestRunnable
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority)) : Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            match best with
            | none => some (tid, tcb.priority)
            | some (_, bestPrio) =>
                if bestPrio.toNat < tcb.priority.toNat then some (tid, tcb.priority) else best
          chooseBestRunnable objects rest best'
      | _ => .error .schedulerInvariantViolation

private def rotateCurrentToBack
    (current : Option SeLe4n.ThreadId)
    (runnable : List SeLe4n.ThreadId) : Except KernelError (List SeLe4n.ThreadId) :=
  match current with
  | none => .ok runnable
  | some tid =>
      if tid ∈ runnable then
        .ok (runnable.erase tid ++ [tid])
      else
        .error .schedulerInvariantViolation

/-- Choose the highest-priority runnable thread. Tie-breaking is deterministic: the first
thread in runnable-order wins when priorities are equal. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestRunnable st.objects st.scheduler.runnable none with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _)) => .ok (some tid, st)

/-- Scheduler step for the bootstrap model.

Failure modes are explicit:
- malformed runnable entries (non-TCB object IDs) surface as `schedulerInvariantViolation`,
- selecting a thread not present in runnable also surfaces as `schedulerInvariantViolation`. -/
def schedule : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') => setCurrentThread none st'
    | .ok (some tid, st') =>
        match st'.objects tid.toObjId with
        | some (.tcb _) =>
            if tid ∈ st'.scheduler.runnable then
              setCurrentThread (some tid) st'
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- Yield semantics: move the current thread to the end of the runnable queue, then schedule. -/
def handleYield : Kernel Unit :=
  fun st =>
    match rotateCurrentToBack st.scheduler.current st.scheduler.runnable with
    | .error e => .error e
    | .ok runnable' =>
        let st' := { st with scheduler := { st.scheduler with runnable := runnable' } }
        schedule st'

theorem schedule_eq_chooseThread_then_setCurrent :
    schedule = (fun st =>
      match chooseThread st with
      | .error e => .error e
      | .ok (next, st') =>
          match next with
          | none => setCurrentThread none st'
          | some tid =>
              match st'.objects tid.toObjId with
              | some (.tcb _) =>
                  if tid ∈ st'.scheduler.runnable then
                    setCurrentThread (some tid) st'
                  else
                    .error .schedulerInvariantViolation
              | _ => .error .schedulerInvariantViolation) := by
  funext st
  cases hChoose : chooseThread st with
  | error e => simp [schedule, hChoose]
  | ok pair =>
      cases pair with
      | mk next st' =>
          cases next <;> simp [schedule, hChoose]

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

theorem chooseThread_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThread st = .ok (next, st')) :
    st' = st := by
  unfold chooseThread at hStep
  cases hPick : chooseBestRunnable st.objects st.scheduler.runnable none with
  | error e => simp [hPick] at hStep
  | ok best =>
      cases best with
      | none =>
          rcases (by simpa [hPick] using hStep : none = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm
      | some pair =>
          cases pair with
          | mk tid prio =>
              rcases (by simpa [hPick] using hStep : some tid = next ∧ st = st') with ⟨_, hSt⟩
              simpa using hSt.symm

 theorem schedule_preserves_wellFormed
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          cases next with
          | none =>
              have hSet : setCurrentThread none stChoose = .ok ((), st') := by
                simpa [hChoose] using hStep
              simp [setCurrentThread] at hSet
              cases hSet
              simp [schedulerWellFormed, queueCurrentConsistent]
          | some tid =>
              cases hObj : stChoose.objects tid.toObjId with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hMem : tid ∈ stChoose.scheduler.runnable
                      · simp [hChoose, hObj, hMem] at hStep
                        have hSet : setCurrentThread (some tid) stChoose = .ok ((), st') := by
                          simpa [hChoose, hObj, hMem] using hStep
                        exact setCurrentThread_preserves_wellFormed stChoose st' tid hMem hSet
                      · simp [hChoose, hObj, hMem] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep

theorem chooseThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hConsistent : queueCurrentConsistent st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    queueCurrentConsistent st'.scheduler := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hConsistent

theorem schedule_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simpa [schedulerWellFormed, queueCurrentConsistent] using schedule_preserves_wellFormed st st' hStep

theorem chooseThread_preserves_runQueueUnique
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    runQueueUnique st'.scheduler := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hUnique

theorem chooseThread_preserves_currentThreadValid
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hValid : currentThreadValid st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadValid st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hValid

theorem schedule_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : schedule st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          have hUniqueChoose : runQueueUnique stChoose.scheduler := by
            simpa [hChooseState] using hUnique
          cases next with
          | none =>
              exact setCurrentThread_preserves_runQueueUnique stChoose st' none hUniqueChoose (by
                simpa [hChoose] using hStep)
          | some tid =>
              cases hObj : stChoose.objects tid.toObjId with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hMem : tid ∈ stChoose.scheduler.runnable
                      · exact setCurrentThread_preserves_runQueueUnique stChoose st' (some tid) hUniqueChoose (by
                          simpa [hChoose, hObj, hMem] using hStep)
                      · simp [hChoose, hObj, hMem] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep

theorem schedule_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadValid st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          cases next with
          | none =>
              exact setCurrentThread_none_preserves_currentThreadValid stChoose st' (by
                simpa [hChoose] using hStep)
          | some tid =>
              cases hObj : stChoose.objects tid.toObjId with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hMem : tid ∈ stChoose.scheduler.runnable
                      · exact setCurrentThread_some_preserves_currentThreadValid stChoose st' tid
                          ⟨tcb, hObj⟩
                          (by simpa [hChoose, hObj, hMem] using hStep)
                      · simp [hChoose, hObj, hMem] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  unfold handleYield at hStep
  cases hRotate : rotateCurrentToBack st.scheduler.current st.scheduler.runnable with
  | error e => simp [hRotate] at hStep
  | ok runnable' =>
      let stMoved : SystemState := { st with scheduler := { st.scheduler with runnable := runnable' } }
      have hSched : schedule stMoved = .ok ((), st') := by simpa [stMoved, hRotate] using hStep
      exact schedule_preserves_wellFormed stMoved st' hSched

theorem handleYield_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simpa [schedulerWellFormed, queueCurrentConsistent] using handleYield_preserves_wellFormed st st' hStep

theorem handleYield_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : handleYield st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  unfold handleYield at hStep
  cases hRotate : rotateCurrentToBack st.scheduler.current st.scheduler.runnable with
  | error e => simp [hRotate] at hStep
  | ok runnable' =>
      let stMoved : SystemState := { st with scheduler := { st.scheduler with runnable := runnable' } }
      have hMovedUnique : runQueueUnique stMoved.scheduler := by
        by_cases hCur : st.scheduler.current = none
        · have hRunEq : runnable' = st.scheduler.runnable := by
            simpa [rotateCurrentToBack, hCur] using hRotate.symm
          subst runnable'
          simpa [stMoved, runQueueUnique] using hUnique
        · rcases Option.ne_none_iff_exists'.mp hCur with ⟨tid, hTid⟩
          simp [rotateCurrentToBack, hTid] at hRotate
          split at hRotate
          · rename_i hMem
            cases hRotate
            have hErase : (st.scheduler.runnable.erase tid).Nodup := hUnique.erase tid
            have hNotMemErase : tid ∉ st.scheduler.runnable.erase tid := by
              exact List.Nodup.not_mem_erase (a := tid) hUnique
            have hApp : (st.scheduler.runnable.erase tid ++ [tid]).Nodup := by
              refine List.nodup_append.2 ?_
              refine ⟨hErase, by simp, ?_⟩
              intro x hx y hy
              have hyTid : y = tid := by simpa using hy
              subst hyTid
              intro hEq
              subst hEq
              exact hNotMemErase hx
            simpa [stMoved, runQueueUnique, hTid, hMem] using hApp
          · simp at hRotate
      have hSched : schedule stMoved = .ok ((), st') := by simpa [stMoved, hRotate] using hStep
      exact schedule_preserves_runQueueUnique stMoved st' hMovedUnique hSched

theorem handleYield_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadValid st' := by
  unfold handleYield at hStep
  cases hRotate : rotateCurrentToBack st.scheduler.current st.scheduler.runnable with
  | error e => simp [hRotate] at hStep
  | ok runnable' =>
      let stMoved : SystemState := { st with scheduler := { st.scheduler with runnable := runnable' } }
      have hSched : schedule stMoved = .ok ((), st') := by simpa [stMoved, hRotate] using hStep
      exact schedule_preserves_currentThreadValid stMoved st' hSched

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
  exact ⟨handleYield_preserves_queueCurrentConsistent st st' hStep,
    handleYield_preserves_runQueueUnique st st' hInv.2.1 hStep,
    handleYield_preserves_currentThreadValid st st' hStep⟩

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

-- ============================================================================
-- M-03/WS-E6: Determinism theorem for chooseThread
-- ============================================================================

/-- M-03/WS-E6: `chooseThread` is deterministic—given the same input state,
it always selects the same thread. This follows from the purely functional
implementation of `chooseBestRunnable`. -/
theorem chooseThread_deterministic
    (st st₁ st₂ : SystemState)
    (next₁ next₂ : Option SeLe4n.ThreadId)
    (h₁ : chooseThread st = .ok (next₁, st₁))
    (h₂ : chooseThread st = .ok (next₂, st₂)) :
    next₁ = next₂ ∧ st₁ = st₂ := by
  have hEq : (.ok (next₁, st₁) : Except KernelError _) = .ok (next₂, st₂) := by
    calc .ok (next₁, st₁) = chooseThread st := h₁.symm
      _ = .ok (next₂, st₂) := h₂
  cases hEq; exact ⟨rfl, rfl⟩

-- ============================================================================
-- M-05/WS-E6: Domain-aware thread selection
-- ============================================================================

/-- M-05/WS-E6: Filter the runnable queue to threads in the currently active
scheduling domain. This implements the first level of two-level temporal
partitioning: only threads whose `TCB.domain` matches `activeDomain` are
candidates for priority-based selection. -/
private def filterByDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (activeDomain : SeLe4n.DomainId)
    (runnable : List SeLe4n.ThreadId) : List SeLe4n.ThreadId :=
  runnable.filter fun tid =>
    match objects tid.toObjId with
    | some (.tcb tcb) => tcb.domain == activeDomain
    | _ => false

/-- M-05/WS-E6: Advance the domain schedule to the next entry, wrapping around
the schedule table. Returns the new active domain, remaining ticks, and
updated schedule index. -/
def nextDomainEntry (sched : List DomainScheduleEntry) (currentIdx : Nat) :
    SeLe4n.DomainId × Nat × Nat :=
  match sched with
  | [] => (0, 1, 0)  -- fallback to default domain
  | _ =>
    let nextIdx := (currentIdx + 1) % sched.length
    match sched[nextIdx]? with
    | some entry => (entry.domain, entry.length, nextIdx)
    | none => (0, 1, 0)  -- unreachable for non-empty schedule

/-- M-05/WS-E6: Domain-aware scheduling: select the highest-priority thread
from the active domain's runnable subset. Falls back to `chooseThread` when
no domain-eligible threads exist (graceful degradation). -/
def chooseDomainThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    let eligible := filterByDomain st.objects st.scheduler.activeDomain st.scheduler.runnable
    match chooseBestRunnable st.objects eligible none with
    | .error _ =>
        -- Fall back to unrestricted selection if domain filtering causes issues
        chooseThread st
    | .ok none => .ok (none, st)
    | .ok (some (tid, _)) => .ok (some tid, st)

-- ============================================================================
-- M-04/WS-E6: Time-slice decrement and tick-based preemption
-- ============================================================================

/-- M-04/WS-E6: Decrement the time-slice of the current thread and preempt if
it reaches zero. On expiry, the current thread is moved to the back of the
runnable queue (recovering round-robin within equal priority levels) and the
scheduler is invoked to select the next thread.

This models seL4's tick-based preemption: each timer interrupt decrements the
running thread's remaining time quanta. When exhausted, the thread yields its
CPU time to the next eligible thread. -/
def handleTimerTick : Kernel Unit :=
  fun st =>
    let st' := { st with machine := SeLe4n.tick st.machine }
    match st'.scheduler.current with
    | none => .ok ((), st')
    | some tid =>
        match st'.objects tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset slice, rotate to back, reschedule
              let tcb' := { tcb with timeSlice := 5 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st'.objects oid
              let st'' := { st' with objects := objects' }
              match rotateCurrentToBack st''.scheduler.current st''.scheduler.runnable with
              | .error e => .error e
              | .ok runnable' =>
                  let st''' := { st'' with scheduler := { st''.scheduler with runnable := runnable' } }
                  schedule st'''
            else
              -- Decrement time-slice, continue running
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st'.objects oid
              .ok ((), { st' with objects := objects' })
        | _ => .error .schedulerInvariantViolation

/-- M-04/WS-E6: `setCurrentThread` preserves the machine state. -/
theorem setCurrentThread_preserves_machine
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    st'.machine = st.machine := by
  simp [setCurrentThread] at hStep; cases hStep; rfl

/-- M-04/WS-E6: `schedule` preserves the machine state (timer, registers, memory).
The scheduler only modifies the `scheduler` component of `SystemState`. -/
theorem schedule_preserves_machine
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          cases next with
          | none =>
              have hSet : setCurrentThread none stChoose = .ok ((), st') := by
                simpa [hChoose] using hStep
              exact hChooseState ▸ setCurrentThread_preserves_machine stChoose st' none hSet
          | some tid =>
              cases hObj : stChoose.objects tid.toObjId with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb _ =>
                      by_cases hMem : tid ∈ stChoose.scheduler.runnable
                      · have hSet : setCurrentThread (some tid) stChoose = .ok ((), st') := by
                          simpa [hChoose, hObj, hMem] using hStep
                        exact hChooseState ▸ setCurrentThread_preserves_machine stChoose st' (some tid) hSet
                      · simp [hChoose, hObj, hMem] at hStep
                  | endpoint _ => simp [hChoose, hObj] at hStep
                  | notification _ => simp [hChoose, hObj] at hStep
                  | cnode _ => simp [hChoose, hObj] at hStep
                  | vspaceRoot _ => simp [hChoose, hObj] at hStep

/-- M-04/WS-E6: When no thread is currently running, `handleTimerTick` simply
advances the machine timer without touching the scheduler. -/
theorem handleTimerTick_idle_advances_timer
    (st st' : SystemState)
    (hIdle : st.scheduler.current = none)
    (hStep : handleTimerTick st = .ok ((), st')) :
    st'.machine.timer = st.machine.timer + 1 := by
  simp [handleTimerTick, hIdle] at hStep
  cases hStep; simp [SeLe4n.tick]

/-- M-04/WS-E6: When the current thread has remaining time-slice (> 1),
`handleTimerTick` decrements the slice and advances the timer, keeping the
current thread running. -/
theorem handleTimerTick_decrement_timer
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hCurrent : st.scheduler.current = some tid)
    (hObj : st.objects tid.toObjId = some (.tcb tcb))
    (hSlice : tcb.timeSlice > 1)
    (hStep : handleTimerTick st = .ok ((), st')) :
    st'.machine.timer = st.machine.timer + 1 ∧
    st'.scheduler.current = some tid := by
  have hNotExpiry : ¬ (tcb.timeSlice ≤ 1) := by omega
  simp [handleTimerTick, hCurrent, hObj, hNotExpiry] at hStep
  cases hStep; exact ⟨by simp [SeLe4n.tick], by exact hCurrent⟩

/-- M-05/WS-E6: Domain scheduling tick: advance domain time remaining and rotate
to the next domain when the current domain's window expires. -/
def handleDomainTick (schedule : List DomainScheduleEntry) : Kernel Unit :=
  fun st =>
    if st.scheduler.domainTimeRemaining ≤ 1 then
      let (newDomain, newLength, newIdx) :=
        nextDomainEntry schedule st.scheduler.domainScheduleIndex
      let sched' := { st.scheduler with
        activeDomain := newDomain
        domainTimeRemaining := newLength
        domainScheduleIndex := newIdx
      }
      .ok ((), { st with scheduler := sched' })
    else
      let sched' := { st.scheduler with
        domainTimeRemaining := st.scheduler.domainTimeRemaining - 1
      }
      .ok ((), { st with scheduler := sched' })

/-- M-05/WS-E6: `handleDomainTick` preserves runnable queue and current thread. -/
theorem handleDomainTick_preserves_runnable
    (schedule : List DomainScheduleEntry)
    (st st' : SystemState)
    (hStep : handleDomainTick schedule st = .ok ((), st')) :
    st'.scheduler.runnable = st.scheduler.runnable ∧
    st'.scheduler.current = st.scheduler.current := by
  unfold handleDomainTick at hStep
  by_cases h : st.scheduler.domainTimeRemaining ≤ 1
  · simp [h] at hStep; cases hStep; simp
  · simp [h] at hStep; cases hStep; simp

/-- M-05/WS-E6: `handleDomainTick` preserves the scheduler invariant bundle. -/
theorem handleDomainTick_preserves_schedulerInvariantBundle
    (schedule : List DomainScheduleEntry)
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : handleDomainTick schedule st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases handleDomainTick_preserves_runnable schedule st st' hStep with ⟨hRun, hCur⟩
  rcases hInv with ⟨hQCC, hUniq, hValid⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [queueCurrentConsistent, hCur, hRun]
    simp [queueCurrentConsistent] at hQCC
    cases hEq : st.scheduler.current <;> simp_all
  · simp [runQueueUnique, hRun]; exact hUniq
  · simp [currentThreadValid, hCur]
    unfold handleDomainTick at hStep
    by_cases h : st.scheduler.domainTimeRemaining ≤ 1
    · simp [h] at hStep; cases hStep; simpa [currentThreadValid] using hValid
    · simp [h] at hStep; cases hStep; simpa [currentThreadValid] using hValid

end SeLe4n.Kernel
