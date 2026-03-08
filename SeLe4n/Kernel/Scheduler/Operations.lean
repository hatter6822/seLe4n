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

/-- WS-H6: transitivity for the strict candidate-preference relation. -/
theorem isBetterCandidate_transitive
    (p1 p2 p3 : SeLe4n.Priority) (d1 d2 d3 : SeLe4n.Deadline)
    (h12 : isBetterCandidate p1 d1 p2 d2 = true)
    (h23 : isBetterCandidate p2 d2 p3 d3 = true) :
    isBetterCandidate p1 d1 p3 d3 = true := by
  unfold isBetterCandidate at h12 h23 ⊢
  by_cases h31 : p3.toNat > p1.toNat
  · simp [h31]
  · have hLe31 : p3.toNat ≤ p1.toNat := Nat.le_of_not_gt h31
    by_cases h13 : p1.toNat < p3.toNat
    · omega
    · have hp12 : p2.toNat > p1.toNat ∨ p2.toNat = p1.toNat := by
        by_cases hp : p2.toNat > p1.toNat
        · exact Or.inl hp
        · have : p2.toNat = p1.toNat := by
            have hp' : ¬(p2.toNat < p1.toNat) := by
              intro hlt
              simp [Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt] at h12
            omega
          exact Or.inr this
      have hp23 : p3.toNat > p2.toNat ∨ p3.toNat = p2.toNat := by
        by_cases hp : p3.toNat > p2.toNat
        · exact Or.inl hp
        · have : p3.toNat = p2.toNat := by
            have hp' : ¬(p3.toNat < p2.toNat) := by
              intro hlt
              simp [Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt] at h23
            omega
          exact Or.inr this
      have hEqP : p1.toNat = p2.toNat ∧ p2.toNat = p3.toNat := by
        have hge12 : p2.toNat ≥ p1.toNat := by omega
        have hge23 : p3.toNat ≥ p2.toNat := by omega
        have hle13 : p3.toNat ≤ p1.toNat := hLe31
        omega
      rcases hEqP with ⟨hEq12, hEq23⟩
      simp [hEq12, hEq23] at h12 h23 ⊢
      revert h12 h23
      cases hd1 : d1.toNat <;> cases hd2 : d2.toNat <;> cases hd3 : d3.toNat <;> simp
      omega

/-- M-03/WS-E6: Three-level scheduling selection.

Folds over the runnable list accumulating the best candidate using the
three-level `isBetterCandidate` predicate. The accumulator carries
`(ThreadId × Priority × Deadline)` to avoid re-reading the object store. -/
private def chooseBestRunnableBy
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            if eligible tcb then
              match best with
              | none => some (tid, tcb.priority, tcb.deadline)
              | some (_, bestPrio, bestDl) =>
                  if isBetterCandidate bestPrio bestDl tcb.priority tcb.deadline then
                    some (tid, tcb.priority, tcb.deadline)
                  else
                    best
            else
              best
          chooseBestRunnableBy objects eligible rest best'
      | _ => .error .schedulerInvariantViolation

private def chooseBestRunnableInDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (activeDomain : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  chooseBestRunnableBy objects (fun tcb => tcb.domain == activeDomain) runnable best

/-- WS-G4/F-P07: Bucket-first scheduling selection.

Scans only the max-priority bucket for domain-eligible threads, reducing
best-candidate selection from O(t) to O(k) where k is the bucket size
(typically 1-3 in real systems). Falls back to full-list scan if the
max-priority bucket contains no eligible thread (e.g., all max-priority
threads are in a different domain). -/
private def chooseBestInBucket
    (objects : SeLe4n.ObjId → Option KernelObject)
    (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  let maxBucket := rq.maxPriorityBucket
  match chooseBestRunnableInDomain objects maxBucket activeDomain none with
  | .error e => .error e
  | .ok (some result) => .ok (some result)
  | .ok none =>
    -- Max-priority bucket had no eligible thread in this domain;
    -- fall back to full-list scan.
    chooseBestRunnableInDomain objects rq.toList activeDomain none

/-- WS-H6: bucket-first candidate selection is definitionally equivalent
to "scan max bucket then fallback to full scan" semantics. -/
theorem bucketFirst_fullScan_equivalence
    (objects : SeLe4n.ObjId → Option KernelObject)
    (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    chooseBestInBucket objects rq activeDomain =
      (match chooseBestRunnableInDomain objects rq.maxPriorityBucket activeDomain none with
       | .error e => .error e
       | .ok (some result) => .ok (some result)
       | .ok none => chooseBestRunnableInDomain objects rq.toList activeDomain none) := by
  rfl

/-- M-03/M-05 WS-E6/WS-G4: Choose the highest-priority runnable thread from the
active domain using deterministic selection: priority > EDF deadline > FIFO.

WS-G4/F-P07: Uses bucket-first strategy — scans only the max-priority bucket
first (O(k) where k is bucket size), falling back to full-list scan only if
the max-priority bucket has no eligible thread in the active domain.

This is a pure read operation — the system state is returned unchanged.
If no runnable thread exists in the active domain, selection returns `none`. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestInBucket st.objects.get? st.scheduler.runQueue st.scheduler.activeDomain with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _, _)) => .ok (some tid, st)

/-- WS-H12/H-03: Save current thread's machine registers to its TCB.
Returns the updated state, or the original state unchanged if there is no
current thread or the current thread's TCB is missing. -/
def saveCurrentContext (st : SystemState) : SystemState :=
  match st.scheduler.current with
  | none => st
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
          let tcb' := { tcb with registerContext := saveContext st.machine }
          { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
      | _ => st

/-- WS-H12/H-03: Restore the incoming thread's saved register context into the
machine state. Returns the updated state, or the original state unchanged if
there is no incoming thread or the TCB is missing. -/
def restoreIncomingContext (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      { st with machine := restoreContext st.machine tcb.registerContext }
  | _ => st

/-- Scheduler step for the bootstrap model.

Failure modes are explicit:
- malformed runnable entries (non-TCB object IDs) surface as `schedulerInvariantViolation`,
- selecting a thread not present in runnable also surfaces as `schedulerInvariantViolation`.

**Performance note:** Membership validation uses O(1) HashSet-backed
`tid ∈ st'.scheduler.runQueue`. WS-H6 also provides a bidirectional bridge
(`RunQueue.mem_toList_iff_mem`) for any proof obligations phrased over
`st'.scheduler.runnable` (`rq.toList`). -/
def schedule : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') => setCurrentThread none st'
    | .ok (some tid, st') =>
        match st'.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
              setCurrentThread (some tid) st'
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- WS-H12/H-03: Schedule with per-TCB context save/restore.

Wraps `schedule` with context management: saves the outgoing thread's machine
registers to its TCB, runs the scheduler, then restores the incoming thread's
saved register context into the machine. This is the preferred entry point
for context-switch-aware scheduling in the API layer. -/
def scheduleWithContext : Kernel Unit :=
  fun st =>
    -- Save outgoing thread's context
    let st' := saveCurrentContext st
    -- Run the core scheduler
    match schedule st' with
    | .error e => .error e
    | .ok ((), st'') =>
        -- Restore incoming thread's context
        match st''.scheduler.current with
        | none => .ok ((), st'')
        | some tid => .ok ((), restoreIncomingContext st'' tid)

/-- WS-G4: Yield semantics: move the current thread to the end of its priority bucket
and the flat list using `RunQueue.rotateToBack`, then schedule. -/
def handleYield : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => schedule st
    | some tid =>
        if tid ∈ st.scheduler.runQueue then
          let st' := { st with scheduler := { st.scheduler with
              runQueue := st.scheduler.runQueue.rotateToBack tid } }
          schedule st'
        else
          .error .schedulerInvariantViolation

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
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, rotate, reschedule
              let tcb' := { tcb with timeSlice := defaultTimeSlice }
              let st' := { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine }
              if tid ∈ st'.scheduler.runQueue then
                let st'' := { st' with scheduler := { st'.scheduler with
                    runQueue := st'.scheduler.runQueue.rotateToBack tid } }
                schedule st''
              else
                .error .schedulerInvariantViolation
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              .ok ((), { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- WS-H12/H-04: Dequeue-on-dispatch scheduler operations
-- ============================================================================

/-- WS-H12/H-04: Schedule with dequeue-on-dispatch semantics.

Unlike the legacy `schedule` which keeps the current thread in the runnable
queue, this variant removes the dispatched thread from the queue upon dispatch.
The dispatched thread must be re-enqueued when it is preempted, yields, or blocks.

This matches seL4's scheduling semantics where the running thread is not in
the ready queue and is re-enqueued on preemption/yield/block. -/
def scheduleDequeue : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') => setCurrentThread none st'
    | .ok (some tid, st') =>
        match st'.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
              -- Dequeue the selected thread from the run queue
              let st'' := { st' with scheduler := { st'.scheduler with
                  runQueue := st'.scheduler.runQueue.remove tid } }
              setCurrentThread (some tid) st''
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- WS-H12/H-04: Yield with dequeue-on-dispatch semantics.

Re-enqueues the current thread (which is NOT in the runnable queue under
dequeue-on-dispatch) before scheduling. -/
def handleYieldDequeue : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => scheduleDequeue st
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            -- Re-enqueue current thread (it was dequeued on dispatch)
            let st' := { st with scheduler := { st.scheduler with
                runQueue := st.scheduler.runQueue.insert tid tcb.priority } }
            scheduleDequeue st'
        | _ => .error .schedulerInvariantViolation

/-- WS-H12/H-04: Timer tick with dequeue-on-dispatch semantics.

On time-slice expiry, re-enqueues the current thread (which was dequeued on
dispatch) at the back of its priority bucket, then reschedules. -/
def timerTickDequeue : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, re-enqueue, and reschedule
              let tcb' := { tcb with timeSlice := defaultTimeSlice }
              let objs := st.objects.insert tid.toObjId (.tcb tcb')
              let st' := { st with objects := objs, machine := tick st.machine }
              -- Re-enqueue the current thread (was dequeued on dispatch)
              let st'' := { st' with scheduler := { st'.scheduler with
                  runQueue := st'.scheduler.runQueue.insert tid tcb.priority } }
              scheduleDequeue st''
            else
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              let objs := st.objects.insert tid.toObjId (.tcb tcb')
              .ok ((), { st with objects := objs, machine := tick st.machine })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- WS-H12/H-04: Dequeue-on-dispatch preservation theorems
-- ============================================================================

/-- WS-H12/H-04: `scheduleDequeue` establishes `dequeueOnDispatch`.
When `scheduleDequeue` selects a thread, it removes it from the queue,
so the dispatched thread is not in the runnable set. -/
theorem scheduleDequeue_establishes_dequeueOnDispatch
    (st st' : SystemState)
    (hStep : scheduleDequeue st = .ok ((), st')) :
    dequeueOnDispatch st'.scheduler := by
  unfold scheduleDequeue at hStep
  simp only [chooseThread] at hStep
  cases hCIB : chooseBestInBucket st.objects.get? st.scheduler.runQueue
      st.scheduler.activeDomain with
  | error e => simp [hCIB] at hStep
  | ok cibRes =>
    simp only [hCIB] at hStep
    cases cibRes with
    | none =>
      -- No thread selected → current = none → dequeueOnDispatch holds trivially
      simp only [setCurrentThread] at hStep
      cases hStep with
      | refl => simp [dequeueOnDispatch]
    | some triple =>
      obtain ⟨tid, _, _⟩ := triple
      simp at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | tcb tcb =>
          simp only [hObj] at hStep
          by_cases hOk : st.scheduler.runQueue.contains tid = true ∧
              tcb.domain = st.scheduler.activeDomain
          · simp only [hOk, setCurrentThread] at hStep
            cases hStep with
            | refl =>
              simp [dequeueOnDispatch, SchedulerState.runnable]
              exact RunQueue.not_mem_remove_toList st.scheduler.runQueue tid
          · have hOk' : ¬(st.scheduler.runQueue.contains tid = true ∧
                tcb.domain = st.scheduler.activeDomain) := by
              simpa [RunQueue.mem_iff_contains] using hOk
            simp [hOk'] at hStep
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
          simp [hObj] at hStep

-- ============================================================================
-- M-05/WS-E6: Domain scheduling
-- ============================================================================

/-- M-05/WS-E6: Compatibility alias for domain-aware scheduling selection.

`chooseThread` is now domain-aware; this entry point remains for call sites that
expect explicit domain-oriented naming. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  chooseThread

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
              current := none
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
              match st'.objects[tid.toObjId]? with
              | some (.tcb tcb) =>
                  if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
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
    (hObj : ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb))
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
  cases hPick : chooseBestInBucket st.objects.get? st.scheduler.runQueue st.scheduler.activeDomain with
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
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp [hChoose, hObj, hSchedOk] at hStep
                        have hSet : setCurrentThread (some tid) stChoose = .ok ((), st') := by
                          simpa [hChoose, hObj, hSchedOk] using hStep
                        have hMemRunnable : tid ∈ stChoose.scheduler.runnable := by
                          simpa [SchedulerState.runnable] using (RunQueue.mem_toList_iff_mem stChoose.scheduler.runQueue tid).2 hSchedOk.1
                        exact setCurrentThread_preserves_wellFormed stChoose st' tid hMemRunnable hSet
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep

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

theorem chooseThread_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : currentThreadInActiveDomain st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadInActiveDomain st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hInv

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
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · exact setCurrentThread_preserves_runQueueUnique stChoose st' (some tid) hUniqueChoose (by
                          simpa [hChoose, hObj, hSchedOk] using hStep)
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep

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
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · exact setCurrentThread_some_preserves_currentThreadValid stChoose st' tid
                          ⟨tcb, hObj⟩
                          (by simpa [hChoose, hObj, hSchedOk] using hStep)
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur] at hStep
    exact schedule_preserves_wellFormed st st' hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · exact schedule_preserves_wellFormed _ st' hStep
    · simp at hStep

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
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur] at hStep
    exact schedule_preserves_runQueueUnique st st' hUnique hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · rename_i hMem
      have hMovedUnique : runQueueUnique { st.scheduler with
          runQueue := st.scheduler.runQueue.rotateToBack tid } := by
        simp only [runQueueUnique, SchedulerState.runnable]
        exact RunQueue.toList_rotateToBack_nodup st.scheduler.runQueue tid hUnique hMem
      exact schedule_preserves_runQueueUnique _ st' hMovedUnique hStep
    · simp at hStep

theorem schedule_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
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
              cases hSet
              simp [currentThreadInActiveDomain]
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · have hSet : setCurrentThread (some tid) stChoose = .ok ((), st') := by
                          simpa [hChoose, hObj, hSchedOk] using hStep
                        cases hSet
                        simp [currentThreadInActiveDomain, hObj, hSchedOk.2]
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep

theorem handleYield_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadValid st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur] at hStep
    exact schedule_preserves_currentThreadValid st st' hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · exact schedule_preserves_currentThreadValid _ st' hStep
    · simp at hStep

theorem handleYield_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur] at hStep
    exact schedule_preserves_currentThreadInActiveDomain st st' hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · exact schedule_preserves_currentThreadInActiveDomain _ st' hStep
    · simp at hStep

theorem chooseThread_preserves_kernelInvariant
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : kernelInvariant st)
    (hStep : chooseThread st = .ok (next, st')) :
    kernelInvariant st' := by
  exact ⟨
    chooseThread_preserves_queueCurrentConsistent st st' next hInv.1 hStep,
    chooseThread_preserves_runQueueUnique st st' next hInv.2.1 hStep,
    chooseThread_preserves_currentThreadValid st st' next hInv.2.2.1 hStep,
    chooseThread_preserves_currentThreadInActiveDomain st st' next hInv.2.2.2 hStep
  ⟩

theorem schedule_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : schedule st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨schedule_preserves_queueCurrentConsistent st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2.1 hStep,
    schedule_preserves_currentThreadValid st st' hStep,
    schedule_preserves_currentThreadInActiveDomain st st' hStep⟩

theorem handleYield_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : handleYield st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨handleYield_preserves_queueCurrentConsistent st st' hStep,
    handleYield_preserves_runQueueUnique st st' hInv.2.1 hStep,
    handleYield_preserves_currentThreadValid st st' hStep,
    handleYield_preserves_currentThreadInActiveDomain st st' hStep⟩

theorem chooseThread_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    chooseThread_preserves_queueCurrentConsistent st st' next hInv.1 hStep,
    chooseThread_preserves_runQueueUnique st st' next hInv.2.1 hStep,
    chooseThread_preserves_currentThreadValid st st' next hInv.2.2 hStep
  ⟩

theorem schedule_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    schedule_preserves_queueCurrentConsistent st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2.1 hStep,
    schedule_preserves_currentThreadValid st st' hStep
  ⟩

theorem handleYield_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    handleYield_preserves_queueCurrentConsistent st st' hStep,
    handleYield_preserves_runQueueUnique st st' hInv.2.1 hStep,
    handleYield_preserves_currentThreadValid st st' hStep
  ⟩

-- ============================================================================
-- M-05/WS-E6: switchDomain preserves scheduler invariant bundle
-- ============================================================================

/-- M-05/WS-E6: `switchDomain` preserves the scheduler invariant bundle.
This is substantive: it must show that changing `activeDomain`, `domainTimeRemaining`,
and `domainScheduleIndex` does not break `queueCurrentConsistent`, `runQueueUnique`,
`currentThreadValid`, or `currentThreadInActiveDomain`. `switchDomain` now clears
`current` to maintain domain soundness across domain boundaries. -/
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
        · -- queueCurrentConsistent: current is cleared
          simp [queueCurrentConsistent]
        · -- runQueueUnique: runnable unchanged
          exact hInv.2.1
        · -- currentThreadValid: current is none
          simp [currentThreadValid]

/-- M-05/WS-E6: `scheduleDomain` preserves the active-domain current-thread
obligation when it holds in the pre-state. -/
theorem scheduleDomain_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hInv : currentThreadInActiveDomain st)
    (hStep : scheduleDomain st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
  unfold scheduleDomain at hStep
  by_cases hExpire : st.scheduler.domainTimeRemaining ≤ 1
  · simp [hExpire] at hStep
    cases hSw : switchDomain st with
    | error e => simp [hSw] at hStep
    | ok pair =>
        cases pair with
        | mk _ stSw =>
            have hSched : schedule stSw = .ok ((), st') := by simpa [hSw] using hStep
            exact schedule_preserves_currentThreadInActiveDomain stSw st' hSched
  · simp [hExpire] at hStep
    cases hStep
    simpa [currentThreadInActiveDomain] using hInv

/-- M-05/WS-E6: `scheduleDomain` preserves the scheduler invariant bundle. -/
theorem scheduleDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : scheduleDomain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold scheduleDomain at hStep
  by_cases hExpire : st.scheduler.domainTimeRemaining ≤ 1
  · simp [hExpire] at hStep
    cases hSw : switchDomain st with
    | error e => simp [hSw] at hStep
    | ok pair =>
        cases pair with
        | mk _ stSw =>
            have hSched : schedule stSw = .ok ((), st') := by simpa [hSw] using hStep
            have hSwInv : schedulerInvariantBundle stSw :=
              switchDomain_preserves_schedulerInvariantBundle st stSw hInv (by simp [hSw])
            exact schedule_preserves_schedulerInvariantBundle stSw st' hSwInv hSched
  · simp [hExpire] at hStep
    cases hStep
    exact hInv

/-- M-05/WS-E6: `chooseThreadInDomain` is a pure read — it does not modify state. -/
theorem chooseThreadInDomain_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadInDomain st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadInDomain at hStep
  exact chooseThread_preserves_state st st' next hStep

-- ============================================================================
-- WS-F4/F-03: timerTick preservation theorems
-- ============================================================================

/-- WS-F4/F-03: `timerTick` preserves `schedulerInvariantBundle`.

Cases:
1. No current thread → only machine state changes, scheduler unchanged.
2. Time-slice expired → TCB time-slice reset, rotate queue, reschedule.
   Delegates to `schedule_preserves_schedulerInvariantBundle`.
3. Time-slice not expired → TCB time-slice decremented, scheduler unchanged. -/
theorem timerTick_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : timerTick st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep; exact ⟨hQCC, hRQU, hCTV⟩
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time-slice expired: rotate + reschedule
          rw [if_pos hExpire] at hStep
          split at hStep
          · rename_i hMemRQ
            have hTidMem : tid ∈ st.scheduler.runQueue := hMemRQ
            exact schedule_preserves_schedulerInvariantBundle _ st' ⟨
              by simp only [queueCurrentConsistent, SchedulerState.runnable]
                 exact RunQueue.mem_toList_rotateToBack_self st.scheduler.runQueue tid hTidMem,
              by simp only [runQueueUnique, SchedulerState.runnable]
                 exact RunQueue.toList_rotateToBack_nodup st.scheduler.runQueue tid hRQU hTidMem,
              by unfold currentThreadValid; simp only []
                 exact ⟨{ tcb with timeSlice := defaultTimeSlice },
                        by simp⟩⟩ hStep
          · simp at hStep
        · -- Time-slice not expired: scheduler unchanged
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          refine ⟨hQCC, hRQU, ?_⟩
          unfold currentThreadValid
          simp [hCur]

/-- WS-F4/F-03: `timerTick` preserves `kernelInvariant` (including
`currentThreadInActiveDomain`). -/
theorem timerTick_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : timerTick st = .ok ((), st')) :
    kernelInvariant st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV, hDom⟩
  have hBundle := timerTick_preserves_schedulerInvariantBundle st st'
    ⟨hQCC, hRQU, hCTV⟩ hStep
  rcases hBundle with ⟨hQCC', hRQU', hCTV'⟩
  refine ⟨hQCC', hRQU', hCTV', ?_⟩
  -- Prove currentThreadInActiveDomain for st'
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep
    exact hDom
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Expired: schedule sets current → delegates to schedule
          rw [if_pos hExpire] at hStep
          split at hStep
          · exact schedule_preserves_currentThreadInActiveDomain _ st' hStep
          · simp at hStep
        · -- Not expired: domain unchanged, TCB domain unchanged
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          simp only [currentThreadInActiveDomain, hCur]
          have hDomOrig : tcb.domain = st.scheduler.activeDomain := by
            simp [currentThreadInActiveDomain, hCur, hObj] at hDom; exact hDom
          simp [hDomOrig]

-- ============================================================================
-- WS-H6: isBetterCandidate "not-better-than" transitivity
-- ============================================================================

/-- WS-H6: If A doesn't beat B and B doesn't beat C, then A doesn't beat C.
This is transitivity of the "not strictly better" relation, used in the
fold-based optimality proof. -/
private theorem isBetterCandidate_not_better_trans
    (p1 p2 p3 : SeLe4n.Priority) (d1 d2 d3 : SeLe4n.Deadline)
    (h12 : isBetterCandidate p2 d2 p1 d1 = false)
    (h23 : isBetterCandidate p3 d3 p2 d2 = false) :
    isBetterCandidate p3 d3 p1 d1 = false := by
  unfold isBetterCandidate at *
  have hp12 : ¬(p1.toNat > p2.toNat) := fun h => by simp [h] at h12
  have hp23 : ¬(p2.toNat > p3.toNat) := fun h => by simp [h] at h23
  have hp13 : ¬(p1.toNat > p3.toNat) := fun h => by omega
  simp only [hp13, ↓reduceIte]
  by_cases h1lt3 : p1.toNat < p3.toNat
  · simp [h1lt3]
  · simp only [h1lt3, ↓reduceIte]
    simp only [show ¬(p1.toNat > p2.toNat) from hp12,
               show ¬(p1.toNat < p2.toNat) from by omega, ↓reduceIte] at h12
    simp only [show ¬(p2.toNat > p3.toNat) from hp23,
               show ¬(p2.toNat < p3.toNat) from by omega, ↓reduceIte] at h23
    revert h12 h23
    cases d1.toNat <;> cases d2.toNat <;> cases d3.toNat <;> simp_all <;> omega

-- ============================================================================
-- WS-H6: chooseBestRunnableBy fold optimality
-- ============================================================================

/-- WS-H6: Combined optimality for `chooseBestRunnableBy`.
Proves simultaneously:
  (P1) no eligible thread in the list beats the result, and
  (P2) init (if any) doesn't beat the result.
These are proven together by induction to avoid circular dependency. -/
private theorem chooseBestRunnableBy_optimal_combined
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable init =
           .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    -- P1: no eligible thread in `runnable` beats result
    (∀ t, t ∈ runnable →
      ∀ tcb, objects t.toObjId = some (.tcb tcb) →
        eligible tcb = true →
          isBetterCandidate resPrio resDl tcb.priority tcb.deadline = false) ∧
    -- P2: init doesn't beat result
    (∀ initTid ip id, init = some (initTid, ip, id) →
       isBetterCandidate resPrio resDl ip id = false) := by
  induction runnable generalizing init with
  | nil =>
    simp [chooseBestRunnableBy] at hOk
    constructor
    · intro t hMem; simp at hMem
    · intro initTid ip id hInit; subst hOk; cases hInit
      exact isBetterCandidate_irrefl resPrio resDl
  | cons hd tl ih =>
    unfold chooseBestRunnableBy at hOk
    have hAllTl : ∀ t, t ∈ tl → ∃ tcb, objects t.toObjId = some (.tcb tcb) :=
      fun t hMem => hAllTcb t (List.mem_cons.mpr (Or.inr hMem))
    have hHdMem := hAllTcb hd (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨hdTcb, hHdObj⟩ := hHdMem
    simp only [hHdObj] at hOk
    -- Split on whether hd is eligible
    cases hEligB : eligible hdTcb with
    | false =>
      -- hd not eligible: best' = init, skip hd
      simp only [hEligB] at hOk
      have ⟨ihP1, ihP2⟩ := ih init hOk hAllTl
      constructor
      · intro t hMem tcb hObj hE
        simp only [List.mem_cons] at hMem
        rcases hMem with h_eq | hTl
        · have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
          rw [hHdObj] at h1; cases h1; simp [hE] at hEligB
        · exact ihP1 t hTl tcb hObj hE
      · exact ihP2
    | true =>
      simp only [hEligB, ↓reduceIte] at hOk
      -- Split on init
      cases init with
      | none =>
        -- init = none: hd becomes the new init
        have ⟨ihP1, ihP2⟩ := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
        constructor
        · intro t hMem tcb hObj hE
          simp only [List.mem_cons] at hMem
          rcases hMem with h_eq | hTl
          · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
              have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
              rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
            rw [hFlds.1, hFlds.2]
            exact ihP2 hd hdTcb.priority hdTcb.deadline rfl
          · exact ihP1 t hTl tcb hObj hE
        · intro _ ip id hNone; cases hNone
      | some triple =>
        obtain ⟨initTid, initPrio, initDl⟩ := triple
        dsimp only at hOk
        cases hBeatB : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
        | true =>
          -- hd beats init: hd becomes new best
          simp only [hBeatB, ite_true] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
          constructor
          · intro t hMem tcb hObj hE
            simp only [List.mem_cons] at hMem
            rcases hMem with h_eq | hTl
            · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
                have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
                rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
              rw [hFlds.1, hFlds.2]
              exact ihP2 hd hdTcb.priority hdTcb.deadline rfl
            · exact ihP1 t hTl tcb hObj hE
          · -- init doesn't beat result: by contradiction via transitivity
            intro _ ip id hSome; cases hSome
            have hHdNoBetter := ihP2 hd hdTcb.priority hdTcb.deadline rfl
            cases hResVsInit : isBetterCandidate resPrio resDl initPrio initDl with
            | false => rfl
            | true =>
              exact absurd (isBetterCandidate_transitive resPrio initPrio hdTcb.priority
                        resDl initDl hdTcb.deadline hResVsInit hBeatB) (by rw [hHdNoBetter]; decide)
        | false =>
          -- hd doesn't beat init: best' = init
          simp only [hBeatB] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (initTid, initPrio, initDl)) hOk hAllTl
          constructor
          · intro t hMem tcb hObj hE
            simp only [List.mem_cons] at hMem
            rcases hMem with h_eq | hTl
            · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
                have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
                rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
              rw [hFlds.1, hFlds.2]
              exact isBetterCandidate_not_better_trans hdTcb.priority initPrio resPrio
                hdTcb.deadline initDl resDl hBeatB (ihP2 initTid initPrio initDl rfl)
            · exact ihP1 t hTl tcb hObj hE
          · exact ihP2

/-- WS-H6: Specialized optimality for init = none. -/
private theorem chooseBestRunnableBy_optimal
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable none = .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    ∀ t, t ∈ runnable →
      ∀ tcb, objects t.toObjId = some (.tcb tcb) →
        eligible tcb = true →
          isBetterCandidate resPrio resDl tcb.priority tcb.deadline = false :=
  (chooseBestRunnableBy_optimal_combined objects eligible runnable none
    resTid resPrio resDl hOk hAllTcb).1

/-- WS-H6: Connection from `isBetterCandidate` optimality to the EDF predicate.
If a thread t doesn't beat the result at equal priority, the EDF condition holds. -/
private theorem noBetter_implies_edf
    (resDl tDl : SeLe4n.Deadline)
    (prio : SeLe4n.Priority)
    (hNoBetter : isBetterCandidate prio resDl prio tDl = false) :
    resDl.toNat = 0 ∨ (tDl.toNat = 0 ∨ resDl.toNat ≤ tDl.toNat) := by
  unfold isBetterCandidate at hNoBetter
  simp [show ¬(prio.toNat > prio.toNat) from by omega] at hNoBetter
  revert hNoBetter
  cases hd1 : resDl.toNat <;> cases hd2 : tDl.toNat <;> simp_all <;> omega

-- ============================================================================
-- WS-H6: timeSlicePositive preservation
-- ============================================================================

/-- WS-H6: `setCurrentThread` preserves `timeSlicePositive` — only `current` changes. -/
theorem setCurrentThread_preserves_timeSlicePositive
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hInv : timeSlicePositive st)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    timeSlicePositive st' := by
  simp [setCurrentThread] at hStep; cases hStep; exact hInv

/-- WS-H6: `chooseThread` preserves `timeSlicePositive` — state unchanged. -/
theorem chooseThread_preserves_timeSlicePositive
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : timeSlicePositive st)
    (hStep : chooseThread st = .ok (next, st')) :
    timeSlicePositive st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl; exact hInv

/-- WS-H6: `schedule` preserves `timeSlicePositive`. -/
theorem schedule_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hStep : schedule st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hState : stChoose = st := chooseThread_preserves_state st stChoose next hChoose
          have hInvC : timeSlicePositive stChoose := by rw [hState]; exact hInv
          cases next with
          | none =>
              exact setCurrentThread_preserves_timeSlicePositive stChoose st' none hInvC
                (by simpa [hChoose] using hStep)
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hOk : tid ∈ stChoose.scheduler.runQueue ∧
                          tcb.domain = stChoose.scheduler.activeDomain
                      · exact setCurrentThread_preserves_timeSlicePositive stChoose st' (some tid) hInvC
                          (by simpa [hChoose, hObj, hOk] using hStep)
                      · have hOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧
                            tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hOk
                        simp [hChoose, hObj, hOk'] at hStep
                  | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
                      simp [hChoose, hObj] at hStep

/-- WS-H6: `handleYield` preserves `timeSlicePositive`.
`rotateToBack` preserves membership, then delegates to `schedule`. -/
theorem handleYield_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hStep : handleYield st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur] at hStep
    exact schedule_preserves_timeSlicePositive st st' hInv hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · rename_i hMem
      have hInvRot : timeSlicePositive
          { st with scheduler := { st.scheduler with
              runQueue := st.scheduler.runQueue.rotateToBack tid
              current := some tid } } := by
        intro t hMemRot
        simp only [SchedulerState.runnable] at hMemRot
        have hMemOrig : t ∈ st.scheduler.runnable := by
          simp only [SchedulerState.runnable]
          exact (RunQueue.mem_toList_iff_mem _ t).mpr
            ((RunQueue.mem_rotateToBack st.scheduler.runQueue tid t).mp
              ((RunQueue.mem_toList_iff_mem _ t).mp hMemRot))
        exact hInv t hMemOrig
      exact schedule_preserves_timeSlicePositive _ st' hInvRot hStep
    · exact absurd hStep (by simp)

/-- WS-H6: `switchDomain` preserves `timeSlicePositive` — only domain fields change. -/
theorem switchDomain_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hStep : switchDomain st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · cases hStep; exact hInv
      · simp at hStep; cases hStep
        -- Only domain fields changed, objects and runnable unchanged
        exact hInv

/-- WS-H6: If two ThreadIds are not equal, their ObjIds are BEq-false.
Extracted to deduplicate the recurring inequality proof in object-store updates. -/
private theorem threadId_ne_objId_beq_false
    (tid t : SeLe4n.ThreadId) (hNe : t ≠ tid) :
    (tid.toObjId == t.toObjId) = false := by
  cases hb : (tid.toObjId == t.toObjId)
  · rfl
  · exfalso; apply hNe
    have : tid.toObjId = t.toObjId := by
      exact of_decide_eq_true (by rwa [ThreadId.toObjId, ThreadId.toObjId] at hb)
    cases tid; cases t; simp_all [ThreadId.toObjId, ObjId.ofNat, ThreadId.toNat]

/-- WS-H6: `timerTick` preserves `timeSlicePositive`.
Expired case: resets to `defaultTimeSlice` (= 5 > 0), then delegates to `schedule`.
Not-expired case: decrements, and since `timeSlice > 1`, the result is still > 0. -/
theorem timerTick_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hStep : timerTick st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep; exact hInv
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time-slice expired: reset to defaultTimeSlice, rotate, reschedule
          rw [if_pos hExpire] at hStep
          split at hStep
          · rename_i hMemRQ
            -- The intermediate state has updated objects (tid gets defaultTimeSlice)
            -- and rotated runQueue. Need timeSlicePositive for that state.
            have hInvMid : timeSlicePositive
                { st with
                  objects := st.objects.insert tid.toObjId (.tcb { tcb with timeSlice := defaultTimeSlice })
                  machine := tick st.machine
                  scheduler := { st.scheduler with
                    runQueue := st.scheduler.runQueue.rotateToBack tid
                    current := some tid } } := by
              intro t hMemRot
              simp only [SchedulerState.runnable] at hMemRot
              have hMemOrig : t ∈ st.scheduler.runnable := by
                simp only [SchedulerState.runnable]
                exact (RunQueue.mem_toList_iff_mem _ t).mpr
                  ((RunQueue.mem_rotateToBack st.scheduler.runQueue tid t).mp
                    ((RunQueue.mem_toList_iff_mem _ t).mp hMemRot))
              by_cases hEq : t = tid
              · subst hEq
                rw [HashMap_getElem?_insert]; simp [defaultTimeSlice]
              · rw [HashMap_getElem?_insert, threadId_ne_objId_beq_false tid t hEq]
                exact hInv t hMemOrig
            exact schedule_preserves_timeSlicePositive _ st' hInvMid hStep
          · simp at hStep
        · -- Time-slice not expired: decrement, timeSlice - 1 > 0
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          intro t hMem
          by_cases hEq : t = tid
          · subst hEq
            rw [HashMap_getElem?_insert]; simp; omega
          · rw [HashMap_getElem?_insert, threadId_ne_objId_beq_false tid t hEq]
            exact hInv t hMem

-- ============================================================================
-- WS-H6: EDF invariant preservation (trivial cases)
-- ============================================================================

/-- WS-H6: `setCurrentThread none` trivially preserves EDF — no current thread. -/
theorem setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold setCurrentThread at hStep
  cases hStep
  simp [edfCurrentHasEarliestDeadline]

/-- WS-H6: `switchDomain` preserves `edfCurrentHasEarliestDeadline`.
Domain switch sets `current := none` in the transition case. -/
theorem switchDomain_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hInv : edfCurrentHasEarliestDeadline st)
    (hStep : switchDomain st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · cases hStep; exact hInv
      · simp at hStep; cases hStep
        simp [edfCurrentHasEarliestDeadline]

-- ============================================================================
-- WS-H6: schedulerInvariantBundleFull composition
-- ============================================================================

/-- WS-H6: `switchDomain` preserves the full scheduler invariant bundle. -/
theorem switchDomain_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hStep : switchDomain st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hEDF⟩
  exact ⟨switchDomain_preserves_schedulerInvariantBundle st st' hBase hStep,
         switchDomain_preserves_timeSlicePositive st st' hTS hStep,
         switchDomain_preserves_edfCurrentHasEarliestDeadline st st' hEDF hStep⟩

-- ============================================================================
-- WS-H6 completion: EDF preservation for schedule, handleYield, timerTick
-- ============================================================================

/-- WS-H6: `setCurrentThread (some tid)` preserves EDF when the selected thread
satisfies the EDF deadline ordering among same-domain/same-priority candidates.

The proof uses the post-condition that `setCurrentThread` only changes
`scheduler.current`, leaving `objects` and `runnable` unchanged. -/
theorem setCurrentThread_some_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (tcbSel : TCB)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcbSel))
    (hEdfLocal : ∀ t, t ∈ st.scheduler.runnable →
      match st.objects[t.toObjId]? with
      | some (.tcb tcb) =>
          tcb.domain = tcbSel.domain →
          tcb.priority = tcbSel.priority →
          tcbSel.deadline.toNat = 0 ∨
            (tcb.deadline.toNat = 0 ∨ tcbSel.deadline.toNat ≤ tcb.deadline.toNat)
      | _ => True)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold setCurrentThread at hStep
  cases hStep
  unfold edfCurrentHasEarliestDeadline
  simp only [hObj]
  exact hEdfLocal

/-- WS-H6: If `chooseBestRunnableBy` returns `some (resTid, resPrio, resDl)`, then
`objects resTid.toObjId = some (.tcb tcb)` for some TCB with `tcb.priority = resPrio`
and `tcb.deadline = resDl`. The result's fields always correspond to the actual TCB. -/
private theorem chooseBestRunnableBy_result_fields
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable init =
      .ok (some (resTid, resPrio, resDl)))
    (hInit : ∀ iTid iPrio iDl, init = some (iTid, iPrio, iDl) →
      ∃ itcb, objects iTid.toObjId = some (.tcb itcb) ∧
        itcb.priority = iPrio ∧ itcb.deadline = iDl) :
    ∃ tcb, objects resTid.toObjId = some (.tcb tcb) ∧
      tcb.priority = resPrio ∧ tcb.deadline = resDl := by
  induction runnable generalizing init with
  | nil =>
      unfold chooseBestRunnableBy at hOk
      simp at hOk
      cases hOk
      exact hInit resTid resPrio resDl rfl
  | cons hd tl ih =>
      unfold chooseBestRunnableBy at hOk
      cases hHdObj : objects hd.toObjId with
      | none => simp [hHdObj] at hOk
      | some obj =>
          cases obj with
          | tcb hdTcb =>
              simp only [hHdObj] at hOk
              cases hElig : eligible hdTcb with
              | false =>
                  simp only [hElig] at hOk
                  exact ih init hOk hInit
              | true =>
                  simp only [hElig, ↓reduceIte] at hOk
                  cases init with
                  | none =>
                      exact ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk (by
                        intro iTid iPrio iDl hEq
                        simp at hEq; obtain ⟨rfl, rfl, rfl⟩ := hEq
                        exact ⟨hdTcb, hHdObj, rfl, rfl⟩)
                  | some triple =>
                      obtain ⟨initTid, initPrio, initDl⟩ := triple
                      dsimp only at hOk
                      cases hBeat : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
                      | true =>
                          simp only [hBeat, ite_true] at hOk
                          exact ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk (by
                            intro iTid iPrio iDl hEq
                            simp at hEq; obtain ⟨rfl, rfl, rfl⟩ := hEq
                            exact ⟨hdTcb, hHdObj, rfl, rfl⟩)
                      | false =>
                          simp only [hBeat] at hOk
                          exact ih (some (initTid, initPrio, initDl)) hOk hInit
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
              simp [hHdObj] at hOk

/-- WS-H6: If `chooseBestRunnableBy` with `init = none` returns a result, the
result thread is a member of the scanned list.

Proved via induction: the result is either the head of the list (when it becomes
the first eligible candidate) or comes from the recursive tail scan. -/
private theorem chooseBestRunnableBy_result_mem_aux
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible list init =
      .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ list → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    resTid ∈ list ∨ (∃ ip id, init = some (resTid, ip, id)) := by
  induction list generalizing init with
  | nil =>
    unfold chooseBestRunnableBy at hOk
    simp at hOk; cases hOk
    exact Or.inr ⟨resPrio, resDl, rfl⟩
  | cons hd tl ih =>
    unfold chooseBestRunnableBy at hOk
    have hAllTl : ∀ t, t ∈ tl → ∃ tcb, objects t.toObjId = some (.tcb tcb) :=
      fun t ht => hAllTcb t (List.mem_cons.mpr (Or.inr ht))
    cases hHdObj : objects hd.toObjId with
    | none => simp [hHdObj] at hOk
    | some obj =>
      cases obj with
      | tcb hdTcb =>
        simp only [hHdObj] at hOk
        cases hElig : eligible hdTcb with
        | false =>
          simp only [hElig] at hOk
          have := ih init hOk hAllTl
          exact this.elim (fun h => Or.inl (List.mem_cons.mpr (Or.inr h))) Or.inr
        | true =>
          simp only [hElig, ↓reduceIte] at hOk
          cases init with
          | none =>
            have := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
            rcases this with hTl | ⟨ip, id, hInit⟩
            · exact Or.inl (List.mem_cons.mpr (Or.inr hTl))
            · simp at hInit; obtain ⟨rfl, _, _⟩ := hInit
              exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
          | some triple =>
            obtain ⟨initTid, initPrio, initDl⟩ := triple
            dsimp only at hOk
            cases hBeat : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
            | true =>
              simp only [hBeat, ite_true] at hOk
              have := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
              rcases this with hTl | ⟨ip, id, hInit⟩
              · exact Or.inl (List.mem_cons.mpr (Or.inr hTl))
              · simp at hInit; obtain ⟨rfl, _, _⟩ := hInit
                exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
            | false =>
              simp only [hBeat] at hOk
              have := ih (some (initTid, initPrio, initDl)) hOk hAllTl
              exact this.elim (fun h => Or.inl (List.mem_cons.mpr (Or.inr h))) Or.inr
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
        simp [hHdObj] at hOk

private theorem chooseBestRunnableBy_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible list none =
      .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ list → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    resTid ∈ list := by
  have := chooseBestRunnableBy_result_mem_aux objects eligible list none
    resTid resPrio resDl hOk hAllTcb
  rcases this with hMem | ⟨_, _, hNone⟩
  · exact hMem
  · exact absurd hNone (by simp)


/-- WS-H6: Bridge from `chooseBestInBucket` to the EDF deadline ordering.

Given RunQueue well-formedness and priority-match, the result of
`chooseBestInBucket` is EDF-optimal among all domain-eligible runnable threads
at the same priority level.

The proof handles both paths of the bucket-first strategy:
- **Bucket success**: RunQueue well-formedness guarantees all same-priority
  threads reside in the same bucket, so per-bucket optimality implies global
  optimality at the same priority level.
- **Full-scan fallback**: optimality over `rq.toList` directly covers all
  runnable threads. -/
private theorem chooseBestInBucket_edf_bridge
    (st : SystemState)
    (tid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (tcbSel : TCB)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hDomEq : tcbSel.domain = st.scheduler.activeDomain)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hResult : chooseBestInBucket st.objects.get? st.scheduler.runQueue
      st.scheduler.activeDomain = .ok (some (tid, resPrio, resDl)))
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcbSel)) :
    ∀ t, t ∈ st.scheduler.runnable →
      match st.objects[t.toObjId]? with
      | some (.tcb tcb) =>
          tcb.domain = tcbSel.domain →
          tcb.priority = tcbSel.priority →
          tcbSel.deadline.toNat = 0 ∨
            (tcb.deadline.toNat = 0 ∨ tcbSel.deadline.toNat ≤ tcb.deadline.toNat)
      | _ => True := by
  -- Convert to objects.get?
  have hAllTcbGet : ∀ u, u ∈ st.scheduler.runQueue.toList →
      ∃ utcb, st.objects.get? u.toObjId = some (.tcb utcb) := by
    intro u hMu
    obtain ⟨utcb, hutcb⟩ := hAllTcb u (by simpa [SchedulerState.runnable] using hMu)
    exact ⟨utcb, hutcb⟩
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcbSel) := hObj
  -- Domain-eligibility helper
  have eligOfDom : ∀ (tcb : TCB), tcb.domain = tcbSel.domain →
      (fun tc : TCB => tc.domain == st.scheduler.activeDomain) tcb = true := by
    intro tcb htDom; simp; rw [htDom, hDomEq]
  -- Unfold chooseBestInBucket
  unfold chooseBestInBucket at hResult
  cases hBucket : chooseBestRunnableInDomain st.objects.get?
      st.scheduler.runQueue.maxPriorityBucket st.scheduler.activeDomain none with
  | error e => simp [hBucket] at hResult
  | ok bestB =>
    cases bestB with
    | none =>
      -- ── Full-scan fallback ──
      simp only [hBucket] at hResult
      cases hFull : chooseBestRunnableInDomain st.objects.get?
          st.scheduler.runQueue.toList st.scheduler.activeDomain none with
      | error e => simp [hFull] at hResult
      | ok bestF =>
        cases bestF with
        | none => simp [hFull] at hResult
        | some triple =>
          simp only [hFull] at hResult
          have hTripleEq : triple = (tid, resPrio, resDl) := by
            simp at hResult; exact hResult
          subst hTripleEq
          have hFields := chooseBestRunnableBy_result_fields st.objects.get?
            (fun tc => tc.domain == st.scheduler.activeDomain)
            st.scheduler.runQueue.toList none tid resPrio resDl hFull
            (by intro _ _ _ h; simp at h)
          obtain ⟨resTcb, hResTcb, hResPrio, hResDl⟩ := hFields
          rw [hObjGet] at hResTcb; cases hResTcb; subst hResPrio; subst hResDl
          intro t hMem
          cases hTObj : st.objects[t.toObjId]? with
          | none => simp
          | some tObj =>
            cases tObj with
            | tcb tcb =>
              intro htDom htPrio
              have hTObjGet : st.objects.get? t.toObjId = some (.tcb tcb) := hTObj
              have hMemList : t ∈ st.scheduler.runQueue.toList := by
                simpa [SchedulerState.runnable] using hMem
              have hOpt := chooseBestRunnableBy_optimal st.objects.get?
                (fun tc => tc.domain == st.scheduler.activeDomain)
                st.scheduler.runQueue.toList tid tcbSel.priority tcbSel.deadline
                hFull hAllTcbGet
              have hNoBetter := hOpt t hMemList tcb hTObjGet (eligOfDom tcb htDom)
              rw [htPrio] at hNoBetter
              exact noBetter_implies_edf tcbSel.deadline tcb.deadline tcbSel.priority hNoBetter
            | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp
    | some triple =>
      -- ── Bucket success ──
      simp only [hBucket] at hResult
      have hTripleEq : triple = (tid, resPrio, resDl) := by
        simp at hResult; exact hResult
      subst hTripleEq
      -- All bucket members have TCBs
      have hBucketAllTcb : ∀ u, u ∈ st.scheduler.runQueue.maxPriorityBucket →
          ∃ utcb, st.objects.get? u.toObjId = some (.tcb utcb) := by
        intro u hU
        have hURq := RunQueue.maxPriorityBucket_subset st.scheduler.runQueue hwf u hU
        obtain ⟨utcb, hutcb⟩ := hAllTcb u (by
          simpa [SchedulerState.runnable] using
            RunQueue.membership_implies_flat st.scheduler.runQueue u hURq)
        exact ⟨utcb, hutcb⟩
      -- Result fields
      have hFields := chooseBestRunnableBy_result_fields st.objects.get?
        (fun tc => tc.domain == st.scheduler.activeDomain)
        st.scheduler.runQueue.maxPriorityBucket none tid resPrio resDl hBucket
        (by intro _ _ _ h; simp at h)
      obtain ⟨resTcb, hResTcb, hResPrio, hResDl⟩ := hFields
      rw [hObjGet] at hResTcb; cases hResTcb; subst hResPrio; subst hResDl
      -- tid ∈ maxPriorityBucket
      have hTidInBucket : tid ∈ st.scheduler.runQueue.maxPriorityBucket :=
        chooseBestRunnableBy_result_mem st.objects.get?
          (fun tc => tc.domain == st.scheduler.activeDomain)
          st.scheduler.runQueue.maxPriorityBucket tid tcbSel.priority tcbSel.deadline
          hBucket hBucketAllTcb
      -- Extract max priority
      obtain ⟨maxPrio, hMP, hTidTP⟩ :=
        RunQueue.maxPriorityBucket_threadPriority st.scheduler.runQueue hwf tid hTidInBucket
      have hTidMem := RunQueue.maxPriorityBucket_subset st.scheduler.runQueue hwf tid hTidInBucket
      -- maxPrio = tcbSel.priority (via prioMatch)
      have hPMTid := hpm tid hTidMem
      simp only [hObj] at hPMTid
      have hMaxEqPrio : maxPrio = tcbSel.priority := Option.some.inj (hTidTP.symm.trans hPMTid)
      -- Main goal
      intro t hMem
      cases hTObj : st.objects[t.toObjId]? with
      | none => simp
      | some tObj =>
        cases tObj with
        | tcb tcb =>
          intro htDom htPrio
          -- t ∈ runQueue
          have hTInRq : t ∈ st.scheduler.runQueue := by
            rw [RunQueue.mem_iff_contains]
            exact st.scheduler.runQueue.flat_wf t
              (by simpa [SchedulerState.runnable] using hMem)
          -- threadPriority[t]? = some maxPrio (via prioMatch + tcb.priority = maxPrio)
          have hPMt := hpm t hTInRq; simp only [hTObj] at hPMt
          have hTTP : st.scheduler.runQueue.threadPriority[t]? = some maxPrio :=
            hPMt.trans (congrArg some (htPrio.trans hMaxEqPrio.symm))
          -- t ∈ maxPriorityBucket (via wellFormed)
          have hTInBucket :=
            RunQueue.mem_maxPriorityBucket_of_threadPriority st.scheduler.runQueue hwf
              t maxPrio hTInRq hTTP hMP
          -- Bucket optimality → EDF
          have hTObjGet : st.objects.get? t.toObjId = some (.tcb tcb) := hTObj
          have hOpt := chooseBestRunnableBy_optimal st.objects.get?
            (fun tc => tc.domain == st.scheduler.activeDomain)
            st.scheduler.runQueue.maxPriorityBucket tid tcbSel.priority tcbSel.deadline
            hBucket hBucketAllTcb
          have hNoBetter := hOpt t hTInBucket tcb hTObjGet (eligOfDom tcb htDom)
          rw [htPrio] at hNoBetter
          exact noBetter_implies_edf tcbSel.deadline tcb.deadline tcbSel.priority hNoBetter
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp

/-- WS-H6: `schedule` preserves `edfCurrentHasEarliestDeadline`.

When schedule selects `none`, EDF is trivially `True`. When schedule selects
`some tid`, the EDF property follows from `chooseBestInBucket_edf_bridge`.

**Hypotheses**: RunQueue well-formedness and external priority-match. -/
theorem schedule_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : schedule st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold schedule at hStep
  -- Unfold chooseThread to access chooseBestInBucket directly
  simp only [chooseThread] at hStep
  cases hCIB : chooseBestInBucket st.objects.get? st.scheduler.runQueue
      st.scheduler.activeDomain with
  | error e => simp [hCIB] at hStep
  | ok cibRes =>
    simp only [hCIB] at hStep
    cases cibRes with
    | none =>
      -- chooseThread returned none → setCurrentThread none
      exact setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline st st' hStep
    | some triple =>
      obtain ⟨tid, resPrio, resDl⟩ := triple
      -- chooseThread returned some tid
      simp at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | tcb tcbSel =>
          simp only [hObj] at hStep
          by_cases hSchedOk : st.scheduler.runQueue.contains tid = true ∧
              tcbSel.domain = st.scheduler.activeDomain
          · simp only [hSchedOk] at hStep
            exact setCurrentThread_some_preserves_edfCurrentHasEarliestDeadline
              st st' tid tcbSel hObj
              (chooseBestInBucket_edf_bridge st tid resPrio resDl tcbSel
                hwf hpm hSchedOk.2 hAllTcb hCIB hObj)
              hStep
          · exfalso; simp [hSchedOk] at hStep
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
          simp [hObj] at hStep

/-- WS-H6: `handleYield` preserves `edfCurrentHasEarliestDeadline`.

`handleYield` rotates the current thread in its priority bucket and then
calls `schedule`, which re-selects the best candidate from scratch.

The EDF property is **re-established** (not merely preserved) by the
`schedule` call. The rotation preserves RunQueue well-formedness and
priority-match because it only reorders elements within a bucket without
changing `threadPriority`, `membership`, or `objects`. -/
theorem handleYield_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : handleYield st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- no current thread → delegates directly to schedule
    simp only [hCur] at hStep
    exact schedule_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hAllTcb hStep
  | some curTid =>
    simp only [hCur] at hStep
    -- handleYield checks membership, rotates, then calls schedule
    by_cases hMemRQ : curTid ∈ st.scheduler.runQueue
    · rw [if_pos hMemRQ] at hStep
      -- hStep is definitionally equal to schedule of the rotated state
      exact schedule_preserves_edfCurrentHasEarliestDeadline _ st'
        (RunQueue.rotateToBack_preserves_wellFormed st.scheduler.runQueue hwf curTid)
        (fun t hMem => by
          simp only [RunQueue.rotateToBack_threadPriority]
          exact hpm t ((RunQueue.rotateToBack_mem_iff _ _ _).mp hMem))
        (fun t hMem => by
          simp only [SchedulerState.runnable, RunQueue.toList] at hMem
          exact hAllTcb t (by
            simp only [SchedulerState.runnable, RunQueue.toList]
            exact RunQueue.rotateToBack_flat_subset st.scheduler.runQueue curTid t hMem))
        hStep
    · have : ¬(st.scheduler.runQueue.contains curTid = true) := by
        rwa [← RunQueue.mem_iff_contains]
      simp [this] at hStep

/-- WS-H6: `timerTick` preserves `edfCurrentHasEarliestDeadline`.

- **No current thread**: scheduler unchanged, EDF trivially holds.
- **Time-slice not expired**: only the TCB's `timeSlice` field is
  decremented; `scheduler.current` and thread deadlines are unchanged,
  so EDF is preserved.
- **Time-slice expired**: TCB time-slice reset, queue rotation, and
  `schedule` call re-establish EDF from scratch. -/
theorem timerTick_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hEdf : edfCurrentHasEarliestDeadline st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : timerTick st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep
    unfold edfCurrentHasEarliestDeadline; simp [hCur]
  | some curTid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb curTcb =>
        simp only [hObj] at hStep
        by_cases hExpire : curTcb.timeSlice ≤ 1
        · -- Time-slice expired: reset, rotate, reschedule
          rw [if_pos hExpire] at hStep
          -- st.scheduler.runQueue is unchanged (only objects/machine changed)
          -- The if-then checks membership, rotates, and calls schedule
          by_cases hMemRQ : curTid ∈ st.scheduler.runQueue
          · rw [if_pos (show curTid ∈ _ from hMemRQ)] at hStep
            exact schedule_preserves_edfCurrentHasEarliestDeadline _ st'
              (RunQueue.rotateToBack_preserves_wellFormed st.scheduler.runQueue hwf curTid)
              (fun t hMem => by
                simp only [RunQueue.rotateToBack_threadPriority, HashMap_getElem?_insert]
                have hMem' := (RunQueue.rotateToBack_mem_iff _ _ _).mp hMem
                by_cases hEq : curTid.toObjId == t.toObjId
                · simp only [hEq, ite_true]
                  have := hpm t hMem'
                  rw [show t.toObjId = curTid.toObjId from (eq_of_beq hEq).symm, hObj] at this
                  exact this
                · simp only [hEq]; exact hpm t hMem')
              (fun t hMem => by
                simp only [SchedulerState.runnable, RunQueue.toList] at hMem
                have hMemOrig : t ∈ st.scheduler.runnable := by
                  simp only [SchedulerState.runnable, RunQueue.toList]
                  exact RunQueue.rotateToBack_flat_subset st.scheduler.runQueue curTid t hMem
                obtain ⟨tcbOrig, hTcbOrig⟩ := hAllTcb t hMemOrig
                simp only [HashMap_getElem?_insert]
                by_cases hEq : curTid.toObjId == t.toObjId
                · simp only [hEq, ite_true]
                  exact ⟨{ curTcb with timeSlice := defaultTimeSlice }, rfl⟩
                · simp only [hEq]; exact ⟨tcbOrig, hTcbOrig⟩)
              hStep
          · rw [if_neg hMemRQ] at hStep; simp at hStep
        · -- Time-slice not expired: only timeSlice changes
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          -- Transfer from hEdf: objects only differ at curTid (timeSlice field)
          unfold edfCurrentHasEarliestDeadline at hEdf ⊢
          simp only [hCur] at hEdf ⊢
          rw [hObj] at hEdf
          -- Simplify curTid lookup via insert-self
          simp only [HashMap_getElem?_insert, beq_self_eq_true, ite_true]
          intro t hMem
          specialize hEdf t hMem
          by_cases hEq : curTid.toObjId == t.toObjId
          · -- Same ObjId: both curTid and t map to modified curTcb
            simp only [hEq, ite_true]
            -- Same thread: deadline ≤ deadline is trivially true
            intro _ _; exact Or.inr (Or.inr (Nat.le_refl _))
          · -- Different ObjId: lookup unchanged
            simp only [hEq]; exact hEdf
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
        simp [hObj] at hStep

-- ============================================================================
-- WS-H6: Full scheduler invariant bundle composition theorems
-- ============================================================================

/-- WS-H6: `schedule` preserves the full scheduler invariant bundle. -/
theorem schedule_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hEDF⟩
  exact ⟨schedule_preserves_schedulerInvariantBundle st st' hBase hStep,
         schedule_preserves_timeSlicePositive st st' hTS hStep,
         schedule_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hAllTcb hStep⟩

/-- WS-H6: `handleYield` preserves the full scheduler invariant bundle. -/
theorem handleYield_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hEDF⟩
  exact ⟨handleYield_preserves_schedulerInvariantBundle st st' hBase hStep,
         handleYield_preserves_timeSlicePositive st st' hTS hStep,
         handleYield_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hAllTcb hStep⟩

/-- WS-H6: `timerTick` preserves the full scheduler invariant bundle. -/
theorem timerTick_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hStep : timerTick st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hEDF⟩
  exact ⟨timerTick_preserves_schedulerInvariantBundle st st' ⟨hBase.1, hBase.2.1, hBase.2.2⟩ hStep,
         timerTick_preserves_timeSlicePositive st st' hTS hStep,
         timerTick_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hEDF hAllTcb hStep⟩
