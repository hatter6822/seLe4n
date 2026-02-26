import SeLe4n.Kernel.Scheduler.Invariant

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

/-- WS-E6/M-03: Choose the highest-priority runnable thread.

**Fixed-priority scheduling with FIFO tie-breaking (M-03):**

This scheduler uses fixed-priority preemptive scheduling. Each thread has a
static `Priority` value; the thread with the highest numeric priority is
selected. Tie-breaking is **FIFO (first-in-first-out)**: when multiple threads
share the highest priority, the thread that appears first in `runnable` order
wins. This is deterministic and position-stable.

**Comparison with seL4:**
- seL4 uses 256 priority levels with **round-robin** within each level.
  Same-priority threads rotate after consuming their time slice.
- This model uses unbounded `Nat` priorities with FIFO tie-breaking rather
  than round-robin. The `handleYield` operation rotates the current thread
  to the back of the queue, approximating round-robin at the API level.
- seL4 distinguishes MCP (maximum controlled priority) from current priority;
  this model uses a single `Priority` field.

**Determinism guarantee:** `chooseBestRunnable` is a pure fold over the
`runnable` list. The fold is left-biased: the first thread to achieve the
maximum priority wins. Since `runnable` is a `List` (ordered), the tie-breaking
order is fully determined by the list position. -/
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
-- WS-E6/M-04: Time-slice decrement and tick-based preemption
-- ============================================================================

/-- WS-E6/M-04: Decrement the current thread's time slice by one tick.

Models seL4's tick-based preemption: when a timer interrupt fires, the current
thread's remaining time slice is decremented. If the slice reaches zero, the
thread is preempted — its slice is reset to the default (5) and the scheduler
is re-invoked to potentially select a different thread.

Returns `.ok (true, st')` when preemption occurred (time slice exhausted),
`.ok (false, st')` when the thread continues (time slice decremented but
not exhausted), and `.error` when the current thread's TCB cannot be found.

When no thread is currently running, the tick is a no-op. -/
def tickPreempt (defaultSlice : Nat := 5) : Kernel Bool :=
  fun st =>
    match st.scheduler.current with
    | none => .ok (false, st)
    | some tid =>
        match st.objects tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time slice exhausted: reset and reschedule
              let tcb' := { tcb with timeSlice := defaultSlice }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              let st' := { st with objects := objects' }
              match handleYield st' with
              | .error e => .error e
              | .ok (_, st'') => .ok (true, st'')
            else
              -- Decrement time slice
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              .ok (false, { st with objects := objects' })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- WS-E6/M-05: Domain scheduling — two-level temporal partitioning
-- ============================================================================

/-- WS-E6/M-05: Choose the highest-priority runnable thread within the active domain.

This is the domain-aware variant of `chooseThread`. Only threads whose
`TCB.domain` matches `st.scheduler.activeDomain` are considered. This
implements seL4's two-level scheduling: first select the active domain (temporal
partitioning), then apply fixed-priority scheduling within that domain. -/
private def chooseBestRunnableInDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (activeDomain : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority)) : Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            if tcb.domain = activeDomain then
              match best with
              | none => some (tid, tcb.priority)
              | some (_, bestPrio) =>
                  if bestPrio.toNat < tcb.priority.toNat then some (tid, tcb.priority) else best
            else
              best
          chooseBestRunnableInDomain objects rest activeDomain best'
      | _ => .error .schedulerInvariantViolation

/-- WS-E6/M-05: Domain-aware thread selection.

Uses `chooseBestRunnableInDomain` to select only threads whose domain matches
the scheduler's `activeDomain`. Falls back to `chooseThread` (all-domain) if
no domain-eligible threads are found, maintaining backward compatibility. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestRunnableInDomain st.objects st.scheduler.runnable st.scheduler.activeDomain none with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _)) => .ok (some tid, st)

/-- WS-E6/M-05: Advance the domain schedule by one tick.

Decrements `domainTicks`. When exhausted, rotates to the next entry in
`domainSchedule` (wrapping around), setting `activeDomain` and resetting
`domainTicks` to the new domain's budget. Returns `true` when a domain switch
occurred.

If the domain schedule is empty, this is a no-op (returns `false`). -/
def advanceDomainSchedule : Kernel Bool :=
  fun st =>
    let sched := st.scheduler
    if sched.domainTicks ≤ 1 then
      match sched.domainSchedule with
      | [] => .ok (false, st)
      | _ =>
          let nextIdx := (sched.domainScheduleIndex + 1) % sched.domainSchedule.length
          match sched.domainSchedule[nextIdx]? with
          | none => .ok (false, st)
          | some (dom, budget) =>
              let sched' := { sched with
                activeDomain := dom
                domainTicks := budget
                domainScheduleIndex := nextIdx
              }
              .ok (true, { st with scheduler := sched' })
    else
      .ok (false, { st with scheduler := { sched with domainTicks := sched.domainTicks - 1 } })

/-- WS-E6/M-04+M-05: Combined timer tick handler.

On each timer tick:
1. Advance the domain schedule (M-05).
2. Decrement the current thread's time slice (M-04).
3. If either domain switch or time-slice exhaustion occurs, reschedule.

This models seL4's timer interrupt handler which performs both domain rotation
and thread preemption in a single atomic step. -/
def timerTick (defaultSlice : Nat := 5) : Kernel Bool :=
  fun st =>
    match advanceDomainSchedule st with
    | .error e => .error e
    | .ok (domainSwitched, st') =>
        if domainSwitched then
          -- Domain switch occurred — reschedule within new domain
          match schedule st' with
          | .error e => .error e
          | .ok (_, st'') => .ok (true, st'')
        else
          -- No domain switch — handle time-slice preemption
          tickPreempt defaultSlice st'

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

end SeLe4n.Kernel
