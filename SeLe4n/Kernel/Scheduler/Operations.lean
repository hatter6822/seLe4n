import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M-03/WS-E6: Fixed-priority scheduling with FIFO tie-breaking.

**Semantics:** Iterates the runnable list, tracking the highest-priority thread
seen so far. When two threads have equal priority, the one appearing earlier in
the runnable list wins (FIFO tie-breaking within each priority level).

**Divergence from seL4:** Real seL4 uses round-robin rotation among equal-priority
threads within the same scheduling domain. This model uses a simpler FIFO policy
to keep transition semantics fully deterministic without requiring rotation state.
The behavioral difference: in seL4, yielding rotates the current thread to the back
of its priority class; here, `handleYield` + `chooseBestRunnable` achieves the same
effect via explicit `rotateCurrentToBack`.

**EDF (Earliest Deadline First):** Not modeled. seL4 supports sporadic-server
scheduling for mixed-criticality workloads. This model defers EDF semantics to
future work as the current scope focuses on fixed-priority correctness. -/
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

-- ============================================================================
-- M-04/WS-E6: Time-slice decrement and tick-based preemption
-- ============================================================================

/-- M-04/WS-E6: Decrement the current thread's time-slice. When the slice
reaches zero, rotate the thread to the back of the runnable queue (preemption)
and reschedule. Also advances the machine timer via `tick`.

This models seL4's timer-interrupt handler where the kernel decrements the
running thread's time budget and preempts on expiry. -/
def timerTick : Kernel Unit :=
  fun st =>
    let st' := { st with machine := SeLe4n.tick st.machine }
    match st'.scheduler.current with
    | none => .ok ((), st')
    | some tid =>
        match st'.objects tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset slice and rotate to back of queue
              let tcb' := { tcb with timeSlice := 5 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st'.objects oid
              let st'' := { st' with objects := objects' }
              match rotateCurrentToBack (some tid) st''.scheduler.runnable with
              | .error e => .error e
              | .ok runnable' =>
                  let st''' := { st'' with scheduler := { st''.scheduler with runnable := runnable' } }
                  schedule st'''
            else
              -- Decrement time-slice
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st'.objects oid
              .ok ((), { st' with objects := objects' })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-05/WS-E6: Domain scheduling — two-level temporal partitioning
-- ============================================================================

/-- M-05/WS-E6: Filter the runnable list to only threads in a given domain.
Returns threads whose `TCB.domain` matches `domain`. -/
private def filterByDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (domain : SeLe4n.DomainId) : List SeLe4n.ThreadId :=
  runnable.filter fun tid =>
    match objects tid.toObjId with
    | some (.tcb tcb) => tcb.domain == domain
    | _ => false

/-- M-05/WS-E6: Choose the highest-priority runnable thread restricted to the
active domain. This implements two-level temporal partitioning: first, only
threads whose `TCB.domain` matches `activeDomain` are considered; then,
within that set, `chooseBestRunnable` selects by priority with FIFO tie-breaking. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    let domainThreads := filterByDomain st.objects st.scheduler.runnable st.scheduler.activeDomain
    match chooseBestRunnable st.objects domainThreads none with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _)) => .ok (some tid, st)

/-- M-05/WS-E6: Switch the active scheduling domain. Only threads in the new
domain will be eligible for selection on the next scheduling decision. -/
def switchDomain (domain : SeLe4n.DomainId) : Kernel Unit :=
  fun st =>
    .ok ((), { st with scheduler := { st.scheduler with activeDomain := domain } })

/-- M-05/WS-E6: Schedule using domain-aware thread selection. Combines M-05
domain partitioning with the standard schedule logic. -/
def scheduleDomain : Kernel Unit :=
  fun st =>
    match chooseThreadInDomain st with
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
-- M-05/WS-E6: Domain scheduling preservation theorems
-- ============================================================================

/-- M-05/WS-E6: `chooseThreadInDomain` does not modify state. -/
theorem chooseThreadInDomain_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadInDomain st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadInDomain at hStep
  cases hPick : chooseBestRunnable st.objects (filterByDomain st.objects st.scheduler.runnable st.scheduler.activeDomain) none with
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

/-- M-05/WS-E6: `switchDomain` preserves the scheduler invariant bundle. -/
theorem switchDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (domain : SeLe4n.DomainId)
    (hInv : schedulerInvariantBundle st)
    (hStep : switchDomain domain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  simp [switchDomain] at hStep
  cases hStep
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent: runnable unchanged, current unchanged
    simpa [queueCurrentConsistent] using hInv.1
  · -- runQueueUnique: runnable unchanged
    simpa [runQueueUnique] using hInv.2.1
  · -- currentThreadValid: objects unchanged
    simpa [currentThreadValid] using hInv.2.2

-- ============================================================================
-- M-03/WS-E6: Scheduler determinism theorem
-- ============================================================================

/-- M-03/WS-E6: `chooseBestRunnable` is deterministic — given the same object store,
runnable list, and accumulator, it always returns the same result. This is trivially
true because the function is pure (no randomness, no non-deterministic branching). -/
theorem chooseBestRunnable_deterministic
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority))
    (r1 r2 : Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority)))
    (h1 : chooseBestRunnable objects runnable best = r1)
    (h2 : chooseBestRunnable objects runnable best = r2) :
    r1 = r2 := by
  rw [← h1, ← h2]

/-- M-03/WS-E6: `chooseThread` is deterministic — same state in, same result out. -/
theorem chooseThread_deterministic
    (st : SystemState)
    (r1 r2 : Except KernelError (Option SeLe4n.ThreadId × SystemState))
    (h1 : chooseThread st = r1)
    (h2 : chooseThread st = r2) :
    r1 = r2 := by
  rw [← h1, ← h2]

end SeLe4n.Kernel
