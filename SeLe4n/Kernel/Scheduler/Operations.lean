import SeLe4n.Kernel.Scheduler.Invariant

/-!
# Scheduler Operations (M1 + WS-E6)

## M-03/WS-E6: Priority tie-breaking semantics

**Design choice:** When multiple runnable threads share the same (highest) priority,
`chooseBestRunnable` selects the **first thread in runnable-order** (FIFO). This
differs from seL4, where same-priority threads are scheduled in a **round-robin**
fashion with each thread receiving a full time-slice quantum before the next runs.

**Rationale:**
- FIFO tie-breaking is simpler to formalize and yields a deterministic, total
  ordering on the runnable queue without additional bookkeeping.
- The `handleYield` operation provides voluntary rotation, and the M-04
  `timerTick` preemption operation below models involuntary rotation on
  time-slice expiry, together approximating seL4 round-robin behavior.
- A full round-robin scheduler can be layered on top of this foundation in
  future work by using `timerTick` as the involuntary rotation driver.

## M-04/WS-E6: Time-slice decrement and tick-based preemption

`timerTick` models seL4's timer interrupt handler: it decrements the current
thread's `timeSlice` and, when exhausted, resets the slice and rotates the
thread to the back of the queue (involuntary yield). This closes the gap where
`MachineState.timer` existed but was never used for preemption.

## M-05/WS-E6: Domain scheduling

`nextDomain` advances the circular domain schedule, switching `currentDomain`
and resetting `domainTimeRemaining`. `chooseThreadDomain` is a domain-aware
variant of `chooseThread` that only considers threads whose TCB domain matches
`currentDomain`. Together these model seL4's two-level temporal partitioning.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

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
-- M-04/WS-E6: Time-slice decrement and tick-based preemption
-- ============================================================================

/-- M-04/WS-E6: Timer tick handler modeling seL4's `timerTick`.

Decrements the current thread's `timeSlice`. When it reaches zero:
1. Resets the time-slice to `defaultTimeSlice`.
2. Moves the current thread to the back of the runnable queue (involuntary yield).
3. Reschedules.

If no thread is current, or the current thread's time-slice is not yet exhausted,
this is a no-op (returns success with the updated time-slice only). -/
def timerTick : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .ok ((), st)
    | some tid =>
        match st.objects tid.toObjId with
        | some (.tcb tcb) =>
            let newSlice := tcb.timeSlice - 1
            if newSlice = 0 then
              -- Time-slice exhausted: reset and involuntary yield
              let tcb' := { tcb with timeSlice := defaultTimeSlice }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              let st' := { st with objects := objects' }
              handleYield st'
            else
              -- Decrement time-slice
              let tcb' := { tcb with timeSlice := newSlice }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              .ok ((), { st with objects := objects' })
        | _ => .error .schedulerInvariantViolation

/-- M-04/WS-E6: `timerTick` on an empty scheduler is a no-op. -/
theorem timerTick_no_current (st : SystemState)
    (hNone : st.scheduler.current = none) :
    timerTick st = .ok ((), st) := by
  simp [timerTick, hNone]

-- ============================================================================
-- M-05/WS-E6: Domain scheduling (two-level temporal partitioning)
-- ============================================================================

/-- M-05/WS-E6: Advance to the next entry in the circular domain schedule.

If the domain schedule is empty, this is a no-op. Otherwise, advances
`domainScheduleIdx` modulo the schedule length and sets `currentDomain`
and `domainTimeRemaining` from the new entry. Models seL4's `nextDomain`. -/
def nextDomain : Kernel Unit :=
  fun st =>
    match st.scheduler.domainSchedule with
    | [] => .ok ((), st)
    | entry :: rest =>
        let schedule := entry :: rest
        let nextIdx := (st.scheduler.domainScheduleIdx + 1) % schedule.length
        have hLen : 0 < schedule.length := by simp [schedule]
        let nextEntry := schedule[nextIdx]'(Nat.mod_lt _ hLen)
        let sched' := { st.scheduler with
          currentDomain := nextEntry.domain
          domainScheduleIdx := nextIdx
          domainTimeRemaining := nextEntry.length
        }
        .ok ((), { st with scheduler := sched' })

/-- M-05/WS-E6: Domain-aware thread selection.

Like `chooseThread` but only considers runnable threads whose TCB domain
matches `currentDomain`. Models seL4's domain-filtered scheduling. -/
private def chooseBestRunnableInDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (domain : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority)) : Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            if tcb.domain = domain then
              match best with
              | none => some (tid, tcb.priority)
              | some (_, bestPrio) =>
                  if bestPrio.toNat < tcb.priority.toNat then some (tid, tcb.priority) else best
            else
              best
          chooseBestRunnableInDomain objects rest domain best'
      | _ => .error .schedulerInvariantViolation

/-- M-05/WS-E6: Choose the highest-priority runnable thread in the current domain. -/
def chooseThreadDomain : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestRunnableInDomain st.objects st.scheduler.runnable st.scheduler.currentDomain none with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _)) => .ok (some tid, st)

/-- M-05/WS-E6: `chooseThreadDomain` does not modify state. -/
theorem chooseThreadDomain_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadDomain st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadDomain at hStep
  cases hPick : chooseBestRunnableInDomain st.objects st.scheduler.runnable st.scheduler.currentDomain none with
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

/-- M-05/WS-E6: `nextDomain` preserves the scheduler invariant bundle.
Domain switching only changes domain metadata fields, not `runnable` or `current`. -/
theorem nextDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : nextDomain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold nextDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
      simp [hSched] at hStep
      cases hStep
      exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      cases hStep
      -- The new state only changes domain metadata fields; runnable/current/objects unchanged
      exact hInv

end SeLe4n.Kernel
