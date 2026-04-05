/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.PriorityInheritance.BoundedInversion

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-A1: SchedulerStep inductive
-- ============================================================================

/-- D5-A1: Abstract representation of a single scheduler-relevant transition.
Each constructor carries the parameters needed to invoke the corresponding
kernel function. This defines the alphabet of the scheduler trace model. -/
inductive SchedulerStep where
  | timerTick
  | timerTickBudget (tid : ThreadId) (tcb : TCB)
  | schedule
  | scheduleEffective
  | handleYield
  | handleYieldWithBudget
  | switchDomain
  | processReplenishmentsDue (currentTime : Nat)
  | ipcTimeoutTick (scId : SchedContextId)
  deriving Repr

-- ============================================================================
-- D5-A2: SchedulerTrace type
-- ============================================================================

/-- D5-A2: A scheduler trace is a sequence of (step, resulting-state) pairs.
The first element's state is the initial state; each subsequent state is
the result of applying the step to the previous state. -/
abbrev SchedulerTrace := List (SchedulerStep × SystemState)

-- ============================================================================
-- D5-A3: Step precondition mapping
-- ============================================================================

/-- D5-A3: Maps each scheduler step to its precondition on the pre-state.
Extracted from the `if` guards and `match` branches in each kernel function. -/
def stepPrecondition (step : SchedulerStep) (st : SystemState) : Prop :=
  match step with
  | .timerTick => True
  | .timerTickBudget tid tcb =>
      st.scheduler.current = some tid ∧
      st.objects[tid.toObjId]? = some (.tcb tcb)
  | .schedule => True
  | .scheduleEffective => True
  | .handleYield => st.scheduler.current.isSome
  | .handleYieldWithBudget => st.scheduler.current.isSome
  | .switchDomain => st.scheduler.domainSchedule.length > 0
  | .processReplenishmentsDue currentTime =>
      st.scheduler.replenishQueue.hasDue currentTime
  | .ipcTimeoutTick scId =>
      ∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
        sc.budgetRemaining.isZero

-- ============================================================================
-- D5-A4 helper: Step execution function
-- ============================================================================

/-- D5-A4 helper: Step execution function mapping SchedulerStep to the
corresponding kernel transition. Returns `.ok nextState` on success. -/
def stepPost (step : SchedulerStep) (st : SystemState) : Except KernelError SystemState :=
  match step with
  | .timerTick =>
    match timerTick st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .timerTickBudget tid tcb =>
    match timerTickBudget st tid tcb with
    | .ok (st', _preempted) => .ok st'
    | .error e => .error e
  | .schedule =>
    match schedule st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .scheduleEffective =>
    match scheduleEffective st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .handleYield =>
    match handleYield st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .handleYieldWithBudget =>
    match handleYieldWithBudget st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .switchDomain =>
    match switchDomain st with
    | .ok ((), st') => .ok st'
    | .error e => .error e
  | .processReplenishmentsDue currentTime =>
    let (rq', dueIds) := st.scheduler.replenishQueue.popDue currentTime
    let st' := dueIds.foldl (fun acc scId =>
      match acc.objects[scId.toObjId]? with
      | some (.schedContext sc) =>
        let sc' := processReplenishments sc currentTime
        { acc with objects := acc.objects.insert scId.toObjId (.schedContext sc') }
      | _ => acc
    ) { st with scheduler := { st.scheduler with replenishQueue := rq' } }
    .ok st'
  | .ipcTimeoutTick scId =>
    .ok (timeoutBlockedThreads st scId)

-- ============================================================================
-- D5-A4: Valid trace predicate
-- ============================================================================

/-- D5-A4: A valid trace is inductively defined: each step's precondition
holds on the previous state, and applying the step produces the next state
in the trace. Empty traces and singleton traces are trivially valid. -/
inductive ValidTrace : SystemState → SchedulerTrace → Prop where
  | nil (st : SystemState) : ValidTrace st []
  | cons (st : SystemState) (step : SchedulerStep) (st' : SystemState)
         (rest : SchedulerTrace)
         (hPre : stepPrecondition step st)
         (hPost : stepPost step st = .ok st')
         (hRest : ValidTrace st' rest) :
         ValidTrace st ((step, st') :: rest)

-- ============================================================================
-- D5-B1: selectedAt — thread is current at trace index
-- ============================================================================

/-- D5-B: Extract the state at trace index `k`. -/
def traceStateAt (trace : SchedulerTrace) (k : Nat) : Option SystemState :=
  match trace.drop k with
  | (_, st) :: _ => some st
  | [] => none

/-- D5-B1: Thread `tid` is the current (selected) thread at trace index `k`. -/
def selectedAt (trace : SchedulerTrace) (k : Nat) (tid : ThreadId) : Prop :=
  match traceStateAt trace k with
  | some st => st.scheduler.current = some tid
  | none => False

-- ============================================================================
-- D5-B2: runnableAt — thread is in run queue at trace index
-- ============================================================================

/-- D5-B2: Thread `tid` is in the run queue at trace index `k`. -/
def runnableAt (trace : SchedulerTrace) (k : Nat) (tid : ThreadId) : Prop :=
  match traceStateAt trace k with
  | some st => st.scheduler.runQueue.contains tid = true
  | none => False

-- ============================================================================
-- D5-B3: budgetAvailableAt — thread's SchedContext has sufficient budget
-- ============================================================================

/-- D5-B3: Thread's bound SchedContext has positive remaining budget at index `k`. -/
def budgetAvailableAt (trace : SchedulerTrace) (k : Nat) (tid : ThreadId) : Prop :=
  match traceStateAt trace k with
  | some st =>
    match st.objects[tid.toObjId]? with
    | some (KernelObject.tcb tcb) => hasSufficientBudget st tcb = true
    | _ => False
  | none => False

-- ============================================================================
-- D5-B4: selectedAt implies not runnableAt
-- ============================================================================

/-- D5-B4: Selected thread is current, not in run queue. Follows from
dequeue-on-dispatch: `queueCurrentConsistent` ensures the current thread
has been removed from the run queue before execution begins. -/
theorem selectedAt_implies_not_in_runQueue
    (st : SystemState) (tid : ThreadId)
    (hSel : st.scheduler.current = some tid)
    (hQCC : queueCurrentConsistent st.scheduler) :
    tid ∉ st.scheduler.runnable := by
  simp [queueCurrentConsistent] at hQCC
  rw [hSel] at hQCC
  exact hQCC

-- ============================================================================
-- D5-B5: selectedAt implies budgetAvailableAt (conditional)
-- ============================================================================

/-- D5-B5: Unbound threads always pass the budget check, so they are always
budget-eligible for scheduling. This follows directly from `hasSufficientBudget`
returning `true` for unbound threads. -/
theorem budget_always_available_unbound
    (st : SystemState) (tcb : TCB)
    (hUnbound : tcb.schedContextBinding = .unbound) :
    hasSufficientBudget st tcb = true := by
  simp [hasSufficientBudget, hUnbound]

/-- D5-B5: A thread with positive SchedContext budget passes the budget check.
This connects the concrete budget value to the scheduling eligibility predicate. -/
theorem budget_available_when_positive
    (st : SystemState) (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hLookup : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hPos : sc.budgetRemaining.val > 0) :
    hasSufficientBudget st tcb = true := by
  simp [hasSufficientBudget, hBound, hLookup, Budget.isPositive]
  omega

-- ============================================================================
-- D5-C: Counting predicates
-- ============================================================================

/-- D5-C helper: Extract effective priority for a thread ID from system state. -/
def resolveEffectivePriority (st : SystemState) (tid : ThreadId)
    : Option (Priority × Deadline × DomainId) :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) => effectivePriority st tcb
  | _ => none

/-- D5-C: Count threads in the run queue with effective priority ≥ target's
effective priority in the same domain. -/
def countHigherOrEqualEffectivePriority (st : SystemState)
    (targetPrio : Priority) (targetDomain : DomainId) : Nat :=
  st.scheduler.runQueue.flat.foldl (fun count otherTid =>
    match resolveEffectivePriority st otherTid with
    | some (p, _, d) =>
      if d.val = targetDomain.val && p.val ≥ targetPrio.val then count + 1
      else count
    | none => count
  ) 0

/-- D5-C: Maximum SchedContext budget among threads at same-or-higher effective
priority in the same domain. Returns 0 if no such threads exist. -/
def maxBudgetInBand (st : SystemState) (targetPrio : Priority)
    (targetDomain : DomainId) : Nat :=
  st.scheduler.runQueue.flat.foldl (fun maxB otherTid =>
    match resolveEffectivePriority st otherTid with
    | some (p, _, d) =>
      if d.val = targetDomain.val && p.val ≥ targetPrio.val then
        match st.objects[otherTid.toObjId]? with
        | some (.tcb otherTcb) =>
          match otherTcb.schedContextBinding with
          | .bound scId | .donated scId _ =>
            match st.objects[scId.toObjId]? with
            | some (.schedContext sc) => Nat.max maxB sc.budget.val
            | _ => maxB
          -- AC2-C: Unbound threads use the system default time-slice as their
          -- effective budget for liveness analysis.
          | .unbound => Nat.max maxB st.scheduler.configDefaultTimeSlice
        | _ => maxB
      else maxB
    | none => maxB
  ) 0

/-- D5-C: Maximum SchedContext period among threads at same-or-higher effective
priority in the same domain. Unbound threads contribute period=0. -/
def maxPeriodInBand (st : SystemState) (targetPrio : Priority)
    (targetDomain : DomainId) : Nat :=
  st.scheduler.runQueue.flat.foldl (fun maxP otherTid =>
    match resolveEffectivePriority st otherTid with
    | some (p, _, d) =>
      if d.val = targetDomain.val && p.val ≥ targetPrio.val then
        match st.objects[otherTid.toObjId]? with
        | some (.tcb otherTcb) =>
          match otherTcb.schedContextBinding with
          | .bound scId | .donated scId _ =>
            match st.objects[scId.toObjId]? with
            | some (.schedContext sc) => Nat.max maxP sc.period.val
            | _ => maxP
          | .unbound => maxP
        | _ => maxP
      else maxP
    | none => maxP
  ) 0

/-- D5-C: 0-indexed position of thread `tid` in its priority bucket.
Returns `none` if thread is not in the run queue. -/
def bucketPosition (st : SystemState) (tid : ThreadId) : Option Nat :=
  match st.scheduler.runQueue.threadPriority.get? tid with
  | none => none
  | some prio =>
    let bucket := (st.scheduler.runQueue.byPriority[prio]?).getD []
    match bucket.findIdx? (· == tid) with
    | some idx => some idx
    | none => none

-- ============================================================================
-- D5-C: Counting predicate basic properties
-- ============================================================================

/-- D5-C: `countHigherOrEqualEffectivePriority` with an empty run queue is 0.
This is the base case for WCRT reasoning on systems with no contention. -/
theorem countHigherOrEqual_empty (st : SystemState)
    (prio : Priority) (dom : DomainId)
    (hEmpty : st.scheduler.runQueue.flat = []) :
    countHigherOrEqualEffectivePriority st prio dom = 0 := by
  simp [countHigherOrEqualEffectivePriority, hEmpty]

end SeLe4n.Kernel.Liveness
