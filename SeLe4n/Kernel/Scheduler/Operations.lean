import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- M-03/WS-E6: EDF (Earliest Deadline First) tie-breaking
-- ============================================================================

/-- M-03/WS-E6: Three-level scheduling comparison predicate.

Returns `true` when the incumbent candidate (`incTid`) should be replaced
by the challenger (`chalTid`). The three-level policy is:
1. **Priority:** higher numeric priority strictly wins.
2. **EDF:** at equal priority, earlier (lower nonzero) deadline wins.
   A nonzero deadline always beats a zero (no-deadline) challenger at
   equal priority.
3. **FIFO:** if both priority and deadline are equal (or both zero),
   the incumbent is retained (first-in-queue stability).

This mirrors seL4 MCS scheduling semantics where sporadic servers use
deadline-based selection within fixed-priority bands. -/
def isBetterCandidate
    (incPrio : SeLe4n.Priority) (incDeadline : SeLe4n.Deadline)
    (chalPrio : SeLe4n.Priority) (chalDeadline : SeLe4n.Deadline) : Bool :=
  if chalPrio.toNat > incPrio.toNat then true
  else if chalPrio.toNat < incPrio.toNat then false
  else -- equal priority: EDF tie-breaking
    match chalDeadline.toNat, incDeadline.toNat with
    | 0, _ => false  -- challenger has no deadline: never beats incumbent
    | _, 0 => true   -- challenger has deadline, incumbent doesn't: challenger wins
    | cd, id => cd < id  -- both have deadlines: earlier wins; equal = FIFO (retain incumbent)

/-- M-03/WS-E6: FIFO stability — a candidate is never strictly better than itself. -/
theorem isBetterCandidate_irrefl (prio : SeLe4n.Priority) (dl : SeLe4n.Deadline) :
    isBetterCandidate prio dl prio dl = false := by
  unfold isBetterCandidate
  simp [show ¬(prio.toNat > prio.toNat) from by omega]
  cases h : dl.toNat with
  | zero => rfl
  | succ n => simp [Nat.lt_irrefl]

/-- M-03/WS-E6: Strict ordering — if A beats B, then B does not beat A. -/
theorem isBetterCandidate_asymm
    (p1 p2 : SeLe4n.Priority) (d1 d2 : SeLe4n.Deadline)
    (h : isBetterCandidate p1 d1 p2 d2 = true) :
    isBetterCandidate p2 d2 p1 d1 = false := by
  unfold isBetterCandidate at h ⊢
  -- Goal: does (p1 as challenger) beat (p2 as incumbent)? We need false.
  -- Hypothesis h: does (p2 as challenger) beat (p1 as incumbent)? Known true.
  -- Split on the goal's priority check: p1.toNat > p2.toNat?
  by_cases hGt : p1.toNat > p2.toNat
  · -- p1 > p2: then at h, since p2 is challenger and p1 is incumbent,
    -- p2.toNat > p1.toNat is false, and p2.toNat < p1.toNat is true → h says false=true
    have : ¬(p2.toNat > p1.toNat) := by omega
    simp [this, show p2.toNat < p1.toNat from by omega] at h
  · by_cases hLt : p1.toNat < p2.toNat
    · -- p1 < p2: goal reduces to false. Done!
      simp [show ¬(p1.toNat > p2.toNat) from hGt, hLt]
    · -- p1 = p2: equal priority, EDF tie-breaking
      have hEq : p1.toNat = p2.toNat := by omega
      -- In h: p2.toNat > p1.toNat is false, p2.toNat < p1.toNat is false → EDF
      simp [show ¬(p2.toNat > p1.toNat) from by omega,
            show ¬(p2.toNat < p1.toNat) from by omega] at h
      -- In goal: p1.toNat > p2.toNat is false, p1.toNat < p2.toNat is false → EDF
      simp [hGt, show ¬(p1.toNat < p2.toNat) from hLt]
      -- h and goal are now about deadline comparisons in opposite directions
      revert h
      cases hd2 : d2.toNat with
      | zero => simp
      | succ n =>
          cases hd1 : d1.toNat with
          | zero => simp
          | succ m => simp; omega

/-- M-03/WS-E6: Three-level scheduling selection.

Folds over the runnable list accumulating the best candidate using the
three-level `isBetterCandidate` predicate. The accumulator carries
`(ThreadId × Priority × Deadline)` to avoid re-reading the object store. -/
private def chooseBestRunnable
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            match best with
            | none => some (tid, tcb.priority, tcb.deadline)
            | some (_, bestPrio, bestDl) =>
                if isBetterCandidate bestPrio bestDl tcb.priority tcb.deadline then
                  some (tid, tcb.priority, tcb.deadline)
                else best
          chooseBestRunnable objects rest best'
      | _ => .error .schedulerInvariantViolation

private def rotateCurrentToBack
    (current : Option SeLe4n.ThreadId)
    (runnable : List SeLe4n.ThreadId) : Except KernelError (List SeLe4n.ThreadId) :=
  match current with
  | none => .ok runnable
  | some tid =>
      if tid ∈ runnable then
        let q := FifoQueue.fromList (runnable.erase tid)
        .ok ((q.enqueueTail tid).toList)
      else
        .error .schedulerInvariantViolation

/-- Convert scheduler runnable list into FIFO queue record `{head, tail}`. -/
def runnableQueue (st : SystemState) : FifoQueue SeLe4n.ThreadId :=
  FifoQueue.fromList st.scheduler.runnable

/-- Enqueue one thread at runnable-queue tail in O(1) over queue record. -/
def enqueueTail (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with scheduler := { st.scheduler with runnable := ((runnableQueue st).enqueueTail tid).toList } }

/-- Dequeue one thread from runnable-queue head.
Returns the popped head (if any) and updated scheduler state. -/
def dequeueHead (st : SystemState) : Option (SeLe4n.ThreadId × SystemState) :=
  match (runnableQueue st).dequeueHead with
  | none => none
  | some (tid, q') => some (tid, { st with scheduler := { st.scheduler with runnable := q'.toList } })

/-- M-03/WS-E6: Choose the highest-priority runnable thread using three-level
deterministic selection: priority > EDF deadline > FIFO queue order.

This is a pure read operation — the system state is returned unchanged. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestRunnable st.objects st.scheduler.runnable none with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _, _)) => .ok (some tid, st)

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
-- M-04/WS-E6: Time-slice preemption
-- ============================================================================

/-- M-04/WS-E6: Default time-slice quantum (ticks per scheduling round).
Factored into a named constant so the reset value in `timerTick` stays
synchronized with `TCB.timeSlice` default. -/
def defaultTimeSlice : Nat := 5

/-- M-04/WS-E6: Handle a timer tick for the currently running thread.

Behavior:
1. If no thread is current, advance the machine timer only.
2. If the current thread's time-slice has not expired (> 1 after decrement),
   decrement and advance the machine timer.
3. If the time-slice expires (≤ 1), reset it to `defaultTimeSlice`, rotate
   the current thread to the back of the runnable queue, and reschedule.

This models seL4's `timerTick` handler which checks the thread's timeslice
on each timer interrupt and preempts on expiry. -/
def timerTick : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        -- No current thread: just advance the timer
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.objects tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, rotate, reschedule
              let tcb' := { tcb with timeSlice := defaultTimeSlice }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              let st' := { st with objects := objects', machine := tick st.machine }
              match rotateCurrentToBack (some tid) st'.scheduler.runnable with
              | .error e => .error e
              | .ok runnable' =>
                  let st'' := { st' with scheduler := { st'.scheduler with runnable := runnable' } }
                  schedule st''
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              let objects' : SeLe4n.ObjId → Option KernelObject :=
                fun oid => if oid = tid.toObjId then some (.tcb tcb') else st.objects oid
              .ok ((), { st with objects := objects', machine := tick st.machine })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-05/WS-E6: Domain scheduling
-- ============================================================================

/-- M-05/WS-E6: Filter runnable threads to those in the specified domain. -/
def filterByDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (domain : SeLe4n.DomainId) : List SeLe4n.ThreadId :=
  runnable.filter fun tid =>
    match objects tid.toObjId with
    | some (.tcb tcb) => tcb.domain == domain
    | _ => false

/-- M-05/WS-E6: Choose the best thread in the active domain using three-level
selection. If no threads exist in the active domain, falls back to unrestricted
selection to avoid starvation. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    let domainThreads := filterByDomain st.objects st.scheduler.runnable st.scheduler.activeDomain
    match chooseBestRunnable st.objects domainThreads none with
    | .error e => .error e
    | .ok none =>
        -- No threads in active domain: fall back to unrestricted selection
        chooseThread st
    | .ok (some (tid, _, _)) => .ok (some tid, st)

/-- M-05/WS-E6: Advance the domain schedule to the next entry.

If the domain schedule is empty (single-domain mode), this is a no-op.
Otherwise, it wraps the index modularly through the schedule table and
updates the active domain and time remaining. -/
def switchDomain : Kernel Unit :=
  fun st =>
    let schedule := st.scheduler.domainSchedule
    match schedule with
    | [] => .ok ((), st)  -- single-domain mode: no-op
    | _ =>
        let nextIdx := (st.scheduler.domainScheduleIndex + 1) % schedule.length
        match schedule[nextIdx]? with
        | none => .ok ((), st)  -- safety: should not happen with valid modular index
        | some entry =>
            let sched' := { st.scheduler with
              activeDomain := DomainScheduleEntry.domain entry
              domainTimeRemaining := DomainScheduleEntry.length entry
              domainScheduleIndex := nextIdx
            }
            .ok ((), { st with scheduler := sched' })

/-- M-05/WS-E6: Handle a domain tick. Decrements the domain time remaining;
if expired, switches to the next domain and reschedules. -/
def scheduleDomain : Kernel Unit :=
  fun st =>
    if st.scheduler.domainTimeRemaining ≤ 1 then
      match switchDomain st with
      | .error e => .error e
      | .ok ((), st') => schedule st'
    else
      let sched' := { st.scheduler with
        domainTimeRemaining := st.scheduler.domainTimeRemaining - 1
      }
      .ok ((), { st with scheduler := sched' })

-- ============================================================================
-- Preservation theorems
-- ============================================================================

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
      | some triple =>
          obtain ⟨tid, prio, dl⟩ := triple
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
-- M-05/WS-E6: switchDomain preserves scheduler invariant bundle
-- ============================================================================

/-- M-05/WS-E6: `switchDomain` preserves the scheduler invariant bundle.
This is substantive: it must show that changing `activeDomain`, `domainTimeRemaining`,
and `domainScheduleIndex` does not break `queueCurrentConsistent`, `runQueueUnique`,
or `currentThreadValid`, since none of those depend on domain-related fields. -/
theorem switchDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : switchDomain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
      simp [hSched] at hStep
      cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · cases hStep; exact hInv
      · rename_i _ hGet
        simp at hStep
        cases hStep
        refine ⟨?_, ?_, ?_⟩
        · -- queueCurrentConsistent: runnable and current unchanged
          exact hInv.1
        · -- runQueueUnique: runnable unchanged
          exact hInv.2.1
        · -- currentThreadValid: objects and scheduler.current unchanged
          exact hInv.2.2

/-- M-05/WS-E6: `chooseThreadInDomain` is a pure read — it does not modify state. -/
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
          -- Falls back to chooseThread which preserves state
          exact chooseThread_preserves_state st st' next (by simpa [hPick] using hStep)
      | some triple =>
          obtain ⟨tid, prio, dl⟩ := triple
          rcases (by simpa [hPick] using hStep : some tid = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm

end SeLe4n.Kernel
