/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.IPC.Operations.Timeout

namespace SeLe4n.Kernel

open SeLe4n.Model

-- WS-H12c: Frame lemmas — context save/restore do not affect scheduler state.

@[simp] theorem saveOutgoingContext_scheduler (st : SystemState) :
    (saveOutgoingContext st).scheduler = st.scheduler := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj =>
          revert h
          cases obj <;> intro h <;> simp_all

@[simp] theorem restoreIncomingContext_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).scheduler = st.scheduler := by
  simp only [restoreIncomingContext]
  cases h : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      revert h
      cases obj <;> intro h <;> simp_all

@[simp] theorem restoreIncomingContext_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).objects = st.objects := by
  simp only [restoreIncomingContext]
  cases h : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      revert h
      cases obj <;> intro h <;> simp_all

/-- `saveOutgoingContext` preserves the existence of a TCB at any object ID.
If `st.objects[oid]? = some (.tcb tcb)`, then there exists a TCB at `oid`
in `(saveOutgoingContext st).objects` as well. -/
theorem saveOutgoingContext_preserves_tcb
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact ⟨tcb, h⟩
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact ⟨tcb, h⟩
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == oid
              · simp [hEq]
              · simp [hEq]; exact ⟨tcb, h⟩
          | endpoint _ => exact ⟨tcb, h⟩
          | notification _ => exact ⟨tcb, h⟩
          | cnode _ => exact ⟨tcb, h⟩
          | vspaceRoot _ => exact ⟨tcb, h⟩
          | untyped _ => exact ⟨tcb, h⟩
          | schedContext _ => exact ⟨tcb, h⟩

/-- `saveOutgoingContext` preserves all TCB fields except `registerContext`. -/
theorem saveOutgoingContext_tcb_fields
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') ∧
      tcb'.domain = tcb.domain ∧
      tcb'.priority = tcb.priority ∧
      tcb'.deadline = tcb.deadline ∧
      tcb'.timeSlice = tcb.timeSlice := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == oid
              · simp only [hEq, ite_true]
                have hEq' := beq_iff_eq.mp hEq
                subst hEq'
                rw [hOut] at h; cases h
                exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
              · simp [hEq]; exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | endpoint _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | notification _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | cnode _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | vspaceRoot _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | untyped _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | schedContext _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩

/-- When `st.objects[oid]?` is not a TCB (i.e., `none` or a non-TCB object),
`saveOutgoingContext` preserves the lookup unchanged. This is because the only
insert targets `outTid.toObjId` where a TCB exists — if `oid` had no TCB, it
cannot be that key. -/
theorem saveOutgoingContext_preserves_non_tcb_lookup
    (st : SystemState) (oid : SeLe4n.ObjId)
    (hNonTcb : ∀ tcb, st.objects[oid]? ≠ some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects[oid]? = st.objects[oid]? := by
  simp only [saveOutgoingContext]
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => rfl
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              have hNe : ¬(outTid.toObjId == oid) := by
                intro hEq
                have hEq' := beq_iff_eq.mp hEq
                subst hEq'; exact hNonTcb outTcb hOut
              simp [hNe]
          | endpoint _ => rfl
          | notification _ => rfl
          | cnode _ => rfl
          | vspaceRoot _ => rfl
          | untyped _ => rfl
          | schedContext _ => rfl

/-- `saveOutgoingContext` preserves `timeSlicePositive`. The context save only
changes `registerContext` on the outgoing TCB — no scheduler or time-slice
field is modified. -/
theorem saveOutgoingContext_preserves_timeSlicePositive
    (st : SystemState) (hInv : timeSlicePositive st)
    (hObjInv : st.objects.invExt) :
    timeSlicePositive (saveOutgoingContext st) := by
  intro tid hMem
  have hSched : (saveOutgoingContext st).scheduler = st.scheduler := saveOutgoingContext_scheduler st
  have hMemOrig : tid ∈ st.scheduler.runnable := by rwa [← hSched]
  have hOrig := hInv tid hMemOrig
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact hOrig
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact hOrig
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == tid.toObjId
              · -- Same key: inserted TCB has same timeSlice as original
                simp [hEq]
                have hEq' := beq_iff_eq.mp hEq
                rw [hEq'] at hOut; simp [hOut] at hOrig; exact hOrig
              · simp [hEq]; exact hOrig
          | endpoint _ => exact hOrig
          | notification _ => exact hOrig
          | cnode _ => exact hOrig
          | vspaceRoot _ => exact hOrig
          | untyped _ => exact hOrig
          | schedContext _ => exact hOrig

/-- `saveOutgoingContext` preserves `objects.invExt`. The context save
inserts a TCB at an existing key, which preserves the Robin Hood invariant. -/
theorem saveOutgoingContext_preserves_objects_invExt
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects.invExt := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact hObjInv
  | some outTid =>
      dsimp only
      cases hObj : st.objects[outTid.toObjId]? with
      | none => simp; exact hObjInv
      | some obj =>
          cases obj with
          | tcb outTcb =>
              dsimp only
              exact RHTable_insert_preserves_invExt st.objects _ _ hObjInv
          | _ => simp; exact hObjInv

/-- `restoreIncomingContext` preserves `timeSlicePositive`. The context restore
only changes `machine.regs` — objects and scheduler state are unchanged. -/
private theorem restoreIncomingContext_preserves_timeSlicePositive
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : timeSlicePositive st) :
    timeSlicePositive (restoreIncomingContext st tid) := by
  intro t hMem
  have hSched : (restoreIncomingContext st tid).scheduler = st.scheduler := restoreIncomingContext_scheduler st tid
  have hMemOrig : t ∈ st.scheduler.runnable := by rwa [← hSched]
  have hOrig := hInv t hMemOrig
  simp only [restoreIncomingContext_objects]; exact hOrig

/-- WS-H12c: After `restoreIncomingContext st tid`, when `st.objects[tid.toObjId]?`
is a TCB, the machine register file equals that TCB's `registerContext`. -/
theorem restoreIncomingContext_establishes_context
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    (restoreIncomingContext st tid).machine.regs = tcb.registerContext := by
  simp only [restoreIncomingContext, hTcb]

/-- WS-H12c: `restoreIncomingContext` does not change the machine state when
the given thread ID does not correspond to a TCB in the object store. -/
@[simp] theorem restoreIncomingContext_machine_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ tcb, st.objects[tid.toObjId]? ≠ some (.tcb tcb)) :
    (restoreIncomingContext st tid).machine = st.machine := by
  unfold restoreIncomingContext
  cases hObj : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj =>
      cases obj with
      | tcb t => exact absurd hObj (h t)
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rfl

/-- WS-H12b/H-04 + WS-H12c/H-03: Scheduler step with dequeue-on-dispatch and
inline context switch semantics.

Failure modes are explicit:
- malformed runnable entries (non-TCB object IDs) surface as `schedulerInvariantViolation`,
- selecting a thread not present in runnable also surfaces as `schedulerInvariantViolation`.

**Dequeue-on-dispatch (H-04):** After validation, the selected thread is
removed from the run queue before being set as current. This matches seL4's
`switchToThread` → `tcbSchedDequeue` semantics. The dispatched thread is
re-enqueued only on preemption (`timerTick`), yield (`handleYield`), or
domain switch (`switchDomain`).

**Inline context switch (H-03):** The context switch is performed directly
inside `schedule` rather than as separate save/restore helpers. This matches
seL4's `switchToThread` design where the context switch is an integral part
of thread dispatch. The transition:
1. Save outgoing: if `current = some outTid`, store `machine.regs` into
   the outgoing TCB's `registerContext`.
2. Dequeue incoming thread from the run queue.
3. Restore incoming: load `inTcb.registerContext` into `machine.regs`.
4. Set `current` to the incoming thread.

This ensures `contextMatchesCurrent` (machine.regs = currentThread.registerContext)
is established atomically by `schedule` itself.

**Performance note:** Membership validation uses O(1) HashSet-backed
`tid ∈ st'.scheduler.runQueue`.

**U8-D/U-L26: Starvation and fairness:** This is a strict fixed-priority
preemptive scheduler matching seL4's classic scheduling model. Starvation
freedom is NOT a property of this scheduler — a continuously runnable
high-priority thread will indefinitely preempt lower-priority threads.
seL4 delegates starvation prevention to user-level policy (e.g., MCS
scheduling extensions, which are not yet modeled in seLe4n).

**V5-D/V5-E design note:** `schedule` uses the unchecked `saveOutgoingContext` /
`restoreIncomingContext` internally because all 20+ preservation proofs
(`schedule_preserves_schedulerInvariantBundle`, etc.) unfold these functions by
name. The checked variants (`saveOutgoingContextChecked` / `restoreIncomingContextChecked`)
return `SystemState × Bool` for defense-in-depth at API boundaries; equivalence
theorems (`saveOutgoingContextChecked_fst_eq`, `restoreIncomingContextChecked_fst_eq`)
guarantee the state component is identical. Under `currentThreadValid`, the
`false` branches are unreachable. -/
def schedule : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') =>
        -- WS-H12c: save outgoing context before going idle
        let stSaved := saveOutgoingContext st'
        setCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            -- AF1-G: Domain check uses static `tcb.domain`, safe under
            -- `boundThreadDomainConsistent` (AE3-A: sc.domain = tcb.domain).
            if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
              -- WS-H12c: save outgoing thread's register context
              let stSaved := saveOutgoingContext st'
              -- WS-H12b: dequeue before dispatch (seL4 tcbSchedDequeue)
              let stDequeued := { stSaved with scheduler := { stSaved.scheduler with
                  runQueue := stSaved.scheduler.runQueue.remove tid } }
              -- WS-H12c: restore incoming thread's register context
              let stRestored := restoreIncomingContext stDequeued tid
              setCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- WS-H12b/H-04 + WS-H12c/H-03: Yield semantics with dequeue-on-dispatch.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
Yield re-enqueues the current thread at the back of its priority bucket
(insert + rotateToBack), then calls schedule to select a new thread.

Context save/restore is handled inline by `schedule`: the outgoing thread's
registers are saved to its TCB and the incoming thread's registers are
restored from its TCB, establishing `contextMatchesCurrent` atomically.

This mirrors seL4's `handleYield` → `tcbSchedDequeue` + `tcbSchedAppend`
(append = enqueue at tail) → `rescheduleRequired` → `schedule()`. -/
def handleYield : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        -- V5-F (M-DEF-6): Return `.invalidArgument` when no thread is current
        -- instead of falling through to `schedule`. Yielding requires a current
        -- thread to re-enqueue. Without one, the yield is a no-op error —
        -- callers should check `current` before invoking yield.
        .error .invalidArgument
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            -- WS-H12b: re-enqueue at back of priority bucket, then schedule
            -- AF1-H (AE3-E/S-03): Re-enqueues at tcb.priority (static base), not
            -- effective priority. Intentional: yield surrenders the current timeslice
            -- and moves the thread to the back of its priority band. PIP boost
            -- determines scheduling ORDER at selection time (via
            -- `chooseBestRunnableEffective`) but not yield POSITION — a boosted
            -- thread yields from its base band, not its boosted position. The
            -- 48-proof-site debt for effective-priority insertion is tracked but
            -- yield semantics make this a non-bug: the thread re-enters the queue
            -- at the priority it was originally assigned.
            let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
            let st' := { st with scheduler := { st.scheduler with runQueue := rq' } }
            schedule st'
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-04/WS-E6: Time-slice preemption
-- ============================================================================

/-- M-04/WS-E6/V5-L: Default time-slice quantum (ticks per scheduling round).
Factored into a named constant for backward compatibility. New code should
prefer `st.scheduler.configDefaultTimeSlice` which is configurable per
scheduler instance. This constant remains for use in contexts where no
`SchedulerState` is available (e.g., frozen operations). -/
def defaultTimeSlice : Nat := 5

/-- WS-H12b/H-04 + WS-H12c/H-03: Handle a timer tick with dequeue-on-dispatch
and inline context switch semantics.

Behavior:
1. If no thread is current, advance the machine timer only.
2. If the current thread's time-slice has not expired (> 1 after decrement),
   decrement and advance the machine timer.
3. If the time-slice expires (≤ 1), reset it to `defaultTimeSlice`,
   re-enqueue the current thread into the run queue, and reschedule.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
On preemption, we insert it back (seL4's `tcbSchedEnqueue(current)`)
before calling `schedule()`. Context save/restore is handled inline by
`schedule`: the outgoing thread's registers are saved to its TCB and
the incoming thread's registers are restored, establishing
`contextMatchesCurrent` atomically. -/
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
              -- Time-slice expired: reset, re-enqueue, reschedule
              -- AC2-C: Now uses configurable `configDefaultTimeSlice` from scheduler
              -- state (initialized to `defaultTimeSlice` = 5). Preservation proofs
              -- carry an `hConfigTS` hypothesis requiring `configDefaultTimeSlice > 0`.
              let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
              let st' := { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine }
              -- WS-H12b: re-enqueue current thread before schedule.
              -- V5-M (L-SCH-2): The re-enqueue uses `tcb.priority` (pre-reset
              -- value) rather than reading from the updated TCB. This is correct
              -- because `timerTick` only modifies `timeSlice` — priority is
              -- immutable during a tick. The pre-reset TCB and post-reset TCB
              -- have identical `priority` fields, so using either is equivalent.
              let st'' := { st' with scheduler := { st'.scheduler with
                  runQueue := st'.scheduler.runQueue.insert tid tcb.priority } }
              schedule st''
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              .ok ((), { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-G: System-level replenishment processing
-- ============================================================================

/-- Z4-G1: Pop all due replenishment entries from the system replenish queue.
Returns the list of SchedContextIds that are due for replenishment and the
remaining queue. Wraps `ReplenishQueue.popDue` at the system level. -/
def popDueReplenishments (st : SystemState) (now : Nat)
    : ReplenishQueue × List SeLe4n.SchedContextId :=
  st.scheduler.replenishQueue.popDue now

/-- Z4-G2: Refill a single SchedContext's budget via CBS replenishment processing.
Looks up the SchedContext, calls `processReplenishments` and `cbsUpdateDeadline`,
writes the updated object back to the store. No-op if the SchedContext is not found
or is not a SchedContext object. -/
def refillSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (now : Nat) : SystemState :=
  match st.objects[scId.toObjId]? with
  | some (.schedContext sc) =>
    let processed := processReplenishments sc now
    let updated := cbsUpdateDeadline processed now true
    { st with objects := st.objects.insert scId.toObjId (.schedContext updated) }
  | _ => st

/-- Z4-G3: Process all due replenishments and re-enqueue threads whose budget
was restored. Pops due entries from the replenish queue, refills each
SchedContext, and for any bound thread whose budget went from 0 to positive,
enqueues it in the RunQueue.

Z6-F: No timeout action needed during replenishment. Replenishment *restores*
budget, which is the opposite of timeout. Threads blocked on IPC whose
SchedContext is replenished should remain blocked — they now have budget
again. Only `timerTickBudget`'s budget-exhaustion branch (Z4-F3) triggers
`timeoutBlockedThreads`, ensuring that timeouts fire only when
`budgetRemaining = 0`. This guard is correct by construction: this function
never calls `timeoutBlockedThreads`. -/
def processReplenishmentsDue (st : SystemState) (now : Nat) : SystemState :=
  let (remainingQueue, dueIds) := popDueReplenishments st now
  let st' := { st with scheduler := { st.scheduler with
    replenishQueue := remainingQueue } }
  dueIds.foldl (fun acc scId =>
    let wasExhausted := match acc.objects[scId.toObjId]? with
      | some (.schedContext sc) => sc.budgetRemaining.isZero
      | _ => false
    let refilled := refillSchedContext acc scId now
    -- If the SchedContext's bound thread was budget-exhausted and is now refilled,
    -- re-enqueue the thread into the RunQueue
    match refilled.objects[scId.toObjId]? with
    | some (.schedContext sc) =>
      if wasExhausted && sc.budgetRemaining.isPositive then
        match sc.boundThread with
        | some tid =>
          -- Only re-enqueue if the thread is not already current or in queue
          -- AG1-A: Use effective priority (base + PIP boost) for RunQueue insertion
          if tid ∈ refilled.scheduler.runQueue then refilled
          else if refilled.scheduler.current == some tid then refilled
          else { refilled with scheduler := { refilled.scheduler with
            runQueue := refilled.scheduler.runQueue.insert tid (resolveInsertPriority refilled tid sc) } }
        | none => refilled
      else refilled
    | _ => refilled
  ) st'

-- ============================================================================
-- Z6-E: Timeout blocked threads on budget expiry
-- ============================================================================

/-- Z6-E: Helper to determine if a TCB's IPC state is a blocking state
that should be timed out, and returns the endpoint ID and queue type. -/
private def tcbBlockingInfo (tcb : TCB) : Option (SeLe4n.ObjId × Bool) :=
  match tcb.ipcState with
  | .blockedOnSend epId => some (epId, false)      -- sendQ
  | .blockedOnReceive epId => some (epId, true)     -- receiveQ
  | .blockedOnCall epId => some (epId, false)       -- sendQ (Call uses sendQ)
  | .blockedOnReply epId _ => some (epId, false)    -- not in queue but still blocked
  | _ => none

/-- Z6-E: Timeout all threads blocked on IPC whose SchedContext budget
has been exhausted.

When a SchedContext's budget reaches zero, any thread that was relying on
that SchedContext's budget to bound its IPC blocking time must be unblocked.
This function looks up the per-SchedContext thread index (`scThreadIndex`)
to find threads with `schedContextBinding.scId? = some scId`, then calls
`timeoutThread` to unblock each from its respective endpoint queue.

**Complexity**: O(1) RHTable lookup + O(k) iteration where k is the number
of threads referencing the exhausted SchedContext (typically 1–3 due to the
1:1 binding model + IPC donation). This replaces the prior O(n) full
object-store scan (finding S-05/AE3-K).

**Frequency**: Budget exhaustion is rare under well-configured CBS admission
control. The admission check (`admissionControl` in Budget.lean) ensures
total bandwidth ≤ 1.0, so exhaustion occurs only when a thread fully consumes
its allocated budget within a single period.

Note: threads in `blockedOnReply` are also timed out. In seL4 MCS, this
handles the case where a client's donated budget expires while the server
is running — the client is unblocked with a timeout error (Z6-E integration
with Z7 donation). -/
def timeoutBlockedThreads (st : SystemState) (scId : SeLe4n.SchedContextId)
    : SystemState × List (SeLe4n.ThreadId × KernelError) :=
  -- S-05/PERF-O1: O(1) RHTable lookup replaces O(n) object store scan
  let tids := st.scThreadIndex[scId]?.getD []
  tids.foldl (fun (acc : SystemState × List (SeLe4n.ThreadId × KernelError)) tid =>
    let (st', errs) := acc
    match (st'.objects[tid.toObjId]? : Option KernelObject) with
    | some (.tcb tcb) =>
      match tcbBlockingInfo tcb with
      | some (epId, isReceiveQ) =>
        match timeoutThread epId isReceiveQ tid st' with
        | .ok st'' => (st'', errs)
        -- AG1-B: Collect errors instead of silently swallowing.
        -- Under crossSubsystemInvariant, timeoutThread failures are unreachable.
        -- A non-empty error list indicates an invariant violation.
        | .error e => (st', errs ++ [(tid, e)])
      | none => (st', errs)  -- not blocked on IPC
    | _ => (st', errs)  -- index entry for non-TCB (invariant violation)
  ) (st, [])

-- ============================================================================
-- Z4-F: SchedContext-aware budget decrement (timerTickBudget)
-- ============================================================================

/-- Z4-F: SchedContext-aware timer tick budget handling.

Dispatches on the current thread's `schedContextBinding`:
- **Unbound** (Z4-F1): Delegates to the existing time-slice decrement logic.
- **Bound, budget > 1** (Z4-F2): Decrements the SchedContext budget by 1 tick.
- **Bound, budget ≤ 1** (Z4-F3): Budget exhausted — schedules a replenishment
  entry, inserts into the system replenish queue, preempts the current thread
  (re-enqueue + reschedule).

Returns `(updatedState, wasPreempted)`. Callers use `wasPreempted` to decide
whether to call `schedule`. -/
def timerTickBudget (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    : Except KernelError (SystemState × Bool) :=
  match tcb.schedContextBinding with
  | .unbound =>
    -- Z4-F1: Legacy path — mirrors `timerTick` exactly.
    -- AC2-C: Now uses configurable `configDefaultTimeSlice` from scheduler state,
    -- matching the updated `timerTick`. See timerTick for proof chain details.
    if tcb.timeSlice ≤ 1 then
      let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
      let st' := { st with objects := st.objects.insert tid.toObjId (.tcb tcb'),
                           machine := tick st.machine }
      let st'' := { st' with scheduler := { st'.scheduler with
          runQueue := st'.scheduler.runQueue.insert tid tcb.priority } }
      .ok (st'', true)
    else
      let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
      .ok ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb'),
                      machine := tick st.machine }, false)
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) =>
      if sc.budgetRemaining.val ≤ 1 then
        -- Z4-F3: Budget exhausted — schedule replenishment and preempt.
        -- CBS semantics: `consumedAmount` is the full remaining budget (not 1 tick),
        -- because the entire period's consumed budget is recorded for replenishment.
        -- `now` is captured pre-tick: replenishment is scheduled relative to when
        -- budget was consumed, not after the timer advances (standard CBS timing).
        let now := st.machine.timer
        let consumedAmount : Budget := ⟨sc.budgetRemaining.val⟩
        let sc' := consumeBudget sc 1
        let sc'' := scheduleReplenishment sc' now consumedAmount
        let sc''' := cbsUpdateDeadline sc'' now true
        -- Write updated SchedContext back
        let st' := { st with
          objects := st.objects.insert scId.toObjId (.schedContext sc'''),
          machine := tick st.machine }
        -- Insert into system replenish queue for future refill
        let rq := st'.scheduler.replenishQueue.insert scId (now + sc.period.val)
        -- AG1-A: Re-enqueue current thread at effective priority (base + PIP boost)
        let st'' := { st' with scheduler := { st'.scheduler with
          replenishQueue := rq,
          runQueue := st'.scheduler.runQueue.insert tid (resolveInsertPriority st' tid sc) } }
        -- Z6-E: Timeout any threads blocked on IPC whose timeout was bounded
        -- by this SchedContext. Budget is now 0, so all such threads must unblock.
        -- AG1-B: Errors are collected for diagnostic purposes. Under
        -- crossSubsystemInvariant, the error list should always be empty.
        let (st''', _timeoutErrors) := timeoutBlockedThreads st'' scId
        .ok (st''', true)
      else
        -- Z4-F2: Budget remains — decrement and continue
        let sc' := consumeBudget sc 1
        let st' := { st with
          objects := st.objects.insert scId.toObjId (.schedContext sc'),
          machine := tick st.machine }
        .ok (st', false)
    | _ =>
      -- SchedContext not found — fall back to legacy path (defensive)
      .ok ({ st with machine := tick st.machine }, false)

-- ============================================================================
-- Z4-I: Budget-aware schedule (must precede timerTickWithBudget)
-- ============================================================================

/-- Z4-I: SchedContext-aware schedule that uses effective thread selection.

Identical to `schedule` but uses `chooseThreadEffective` which filters
by budget eligibility and resolves effective priorities from SchedContext.
Threads with exhausted CBS budgets are automatically skipped during selection.
The original `schedule` is preserved for backward compatibility. -/
def scheduleEffective : Kernel Unit :=
  fun st =>
    match chooseThreadEffective st with
    | .error e => .error e
    | .ok (none, st') =>
        let stSaved := saveOutgoingContext st'
        setCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
              let stSaved := saveOutgoingContext st'
              let stDequeued := { stSaved with scheduler := { stSaved.scheduler with
                  runQueue := stSaved.scheduler.runQueue.remove tid } }
              let stRestored := restoreIncomingContext stDequeued tid
              setCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-H: Integrated timerTick with replenishment and budget
-- ============================================================================

/-- Z4-H: Extended timer tick with CBS replenishment and budget accounting.

This replaces the original `timerTick` as the primary timer entry point.
Processing order:
1. Process due replenishments (may re-enqueue budget-restored threads)
2. Handle current thread's budget (unbound: time-slice; bound: CBS budget)
3. If preempted, call `schedule` to select next thread

The original `timerTick` is preserved as `timerTickLegacy` for backward
compatibility with existing preservation proofs. -/
def timerTickWithBudget : Kernel Unit :=
  fun st =>
    -- Step 1: Process due replenishments
    let now := st.machine.timer
    let stReplenished := processReplenishmentsDue st now
    -- Step 2: Handle current thread's budget
    match stReplenished.scheduler.current with
    | none =>
      -- No current thread: just advance the timer
      .ok ((), { stReplenished with machine := tick stReplenished.machine })
    | some tid =>
      match stReplenished.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        match timerTickBudget stReplenished tid tcb with
        | .error e => .error e
        | .ok (st', true) =>
          -- Preempted: reschedule using effective selection
          scheduleEffective st'
        | .ok (st', false) =>
          -- Not preempted: continue
          .ok ((), st')
      | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-J: Budget-aware handleYield
-- ============================================================================

/-- Z4-J: Extended yield with SchedContext budget handling.

When a SchedContext-bound thread yields:
1. Charges remaining budget as consumed (schedule replenishment for it)
2. Inserts replenishment entry into system queue
3. Re-enqueues at updated deadline/priority
4. Calls `schedule` to select next thread

Unbound threads use the existing yield path (insert + rotateToBack). -/
def handleYieldWithBudget : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .invalidArgument
    | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        match tcb.schedContextBinding with
        | .unbound =>
          -- Legacy yield: re-enqueue at back of priority bucket
          let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
          let st' := { st with scheduler := { st.scheduler with runQueue := rq' } }
          scheduleEffective st'
        | .bound scId | .donated scId _ =>
          match st.objects[scId.toObjId]? with
          | some (.schedContext sc) =>
            -- Charge remaining budget and schedule replenishment
            let now := st.machine.timer
            let consumedAmount : Budget := ⟨sc.budgetRemaining.val⟩
            let sc' := { sc with budgetRemaining := Budget.zero, isActive := false }
            let sc'' := scheduleReplenishment sc' now consumedAmount
            -- Insert into replenish queue
            let rq := st.scheduler.replenishQueue.insert scId (now + sc.period.val)
            -- Write updated SchedContext
            let st' := { st with
              objects := st.objects.insert scId.toObjId (.schedContext sc''),
              scheduler := { st.scheduler with replenishQueue := rq } }
            -- AG1-A: Re-enqueue thread at effective priority (base + PIP boost)
            let rq' := st'.scheduler.runQueue.insert tid (resolveInsertPriority st' tid sc)
            let st'' := { st' with scheduler := { st'.scheduler with runQueue := rq' } }
            scheduleEffective st''
          | _ =>
            -- SchedContext not found — fall back to legacy yield
            let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
            let st' := { st with scheduler := { st.scheduler with runQueue := rq' } }
            scheduleEffective st'
      | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-05/WS-E6: Domain scheduling
-- ============================================================================

/-- M-05/WS-E6: Compatibility alias for domain-aware scheduling selection.

`chooseThread` is now domain-aware; this entry point remains for call sites that
expect explicit domain-oriented naming. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  chooseThread

/-- WS-H12b/H-04: Advance the domain schedule to the next entry.

If the domain schedule is empty (single-domain mode), this is a no-op.
Otherwise, saves the outgoing thread's register context (U-M39), re-enqueues
the current thread (if any) into the run queue, wraps the index modularly
through the schedule table, and updates the active domain and time remaining.

This function is self-contained: it embeds `saveOutgoingContext` internally
so callers do not need to save context before calling. The save occurs before
`current` is set to `none`, ensuring registers are captured while the outgoing
thread identity is still known.

Under dequeue-on-dispatch, the outgoing thread must return to the
runnable pool for its next domain slot.

**Dual-state pattern (S-05)**: This function reads scheduler state from `st`
(the original state) but returns a state based on `stSaved` (after context
save via `saveOutgoingContext`). This split is correct because:
- `saveOutgoingContext` only modifies `objects` (saves the outgoing thread's
  register file into its TCB). It does NOT modify `scheduler`.
- Therefore `st.scheduler = stSaved.scheduler` — all scheduler field reads
  from `st` yield the same values as reads from `stSaved`.
- The result must use `stSaved` (not `st`) as the base because the returned
  state must include the saved register context in the object store.
- Formal guarantee: `saveOutgoingContext_scheduler` (Core.lean:19)
  mechanizes the proof that `(saveOutgoingContext st).scheduler = st.scheduler`. -/
def switchDomain : Kernel Unit :=
  fun st =>
    let schedule := st.scheduler.domainSchedule
    match schedule with
    | [] => .ok ((), st)  -- single-domain mode: no-op
    | _ =>
        let nextIdx := (st.scheduler.domainScheduleIndex + 1) % schedule.length
        match schedule[nextIdx]? with
        -- LOW-04: This branch is unreachable when `schedulerInvariantBundleFull` holds.
        -- `nextIdx` is computed as `(idx + 1) % schedule.length`, which guarantees
        -- `0 ≤ nextIdx < schedule.length` for any non-empty schedule. The
        -- `domainScheduleEntriesPositive` predicate (9th conjunct) further ensures all
        -- entries are valid. The defensive fallback (return unchanged state) is retained
        -- because silently absorbing an impossible case is safer in a kernel than panicking.
        -- See `switchDomain_index_in_bounds` below for the formal proof.
        | none => .ok ((), st)
        | some entry =>
            -- U-M39: Save outgoing context before clearing current
            let stSaved := saveOutgoingContext st
            -- WS-H12b: re-enqueue current thread before domain switch
            -- All reads use st (not stSaved) to keep scheduler computation identical
            let rq' := match st.scheduler.current with
              | none => st.scheduler.runQueue
              | some tid =>
                  match st.objects[tid.toObjId]? with
                  | some (.tcb tcb) => st.scheduler.runQueue.insert tid tcb.priority
                  | _ => st.scheduler.runQueue
            let sched' := { st.scheduler with
              runQueue := rq'
              current := none
              activeDomain := DomainScheduleEntry.domain entry
              domainTimeRemaining := DomainScheduleEntry.length entry
              domainScheduleIndex := nextIdx
            }
            .ok ((), { stSaved with scheduler := sched' })

/-- LOW-04: The modular index computation in `switchDomain` always produces a valid
index into a non-empty domain schedule. This formalizes the argument that the
`| none =>` fallback branch is unreachable when the schedule is non-empty. -/
theorem switchDomain_index_in_bounds
    (schedule : List DomainScheduleEntry)
    (idx : Nat) (hNe : schedule ≠ []) :
    ((idx + 1) % schedule.length) < schedule.length := by
  have hPos : 0 < schedule.length := by
    cases schedule with
    | nil => exact absurd rfl hNe
    | cons _ _ => simp
  exact Nat.mod_lt _ hPos

/-- Corollary: the `List.getElem?` lookup in `switchDomain` always returns `some`
for a non-empty schedule, confirming the `| none =>` branch is dead code. -/
theorem switchDomain_index_lookup_isSome
    (schedule : List DomainScheduleEntry)
    (idx : Nat) (hNe : schedule ≠ []) :
    (schedule[(idx + 1) % schedule.length]?).isSome = true := by
  have hBound := switchDomain_index_in_bounds schedule idx hNe
  simp [List.getElem?_eq_getElem hBound]

/-- `switchDomain` preserves `objects.invExt`. In no-op branches the state is
unchanged; in the active branch the objects come from `saveOutgoingContext`,
which preserves the Robin Hood invariant. -/
theorem switchDomain_preserves_objects_invExt
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hObjInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · obtain ⟨_, rfl⟩ := hStep; exact hObjInv
      · simp at hStep; obtain ⟨_, rfl⟩ := hStep; dsimp
        exact saveOutgoingContext_preserves_objects_invExt st hObjInv

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
-- V8-G3: ThreadState synchronization
-- ============================================================================

/-- V8-G3: Infer the `ThreadState` for a thread based on observable system state.
This is the canonical definition of what each `ThreadState` value means:
- `Running`: thread is `scheduler.current`
- `Ready`: thread is in the run queue
- `BlockedSend`/`BlockedRecv`/`BlockedCall`/`BlockedReply`/`BlockedNotif`: matches `ipcState`
- `Inactive`: none of the above (ipcState.ready but not queued/current) -/
def inferThreadState (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) : ThreadState :=
  if st.scheduler.current == some tid then .Running
  else if tid ∈ st.scheduler.runQueue then .Ready
  else match tcb.ipcState with
  | .blockedOnSend _ => .BlockedSend
  | .blockedOnReceive _ => .BlockedRecv
  | .blockedOnCall _ => .BlockedCall
  | .blockedOnNotification _ => .BlockedNotif
  | .blockedOnReply _ _ => .BlockedReply
  | .ready => .Inactive

/-- V8-G3: Synchronize all TCB `threadState` fields to match observable state.
Idempotent: calling this twice produces the same result.
This function is called after kernel operations to maintain the `threadState`
field without modifying the operations themselves (preserving all existing proofs). -/
def syncThreadStates (st : SystemState) : SystemState :=
  let objs := st.objects.fold (init := st.objects) fun acc oid obj =>
    match obj with
    | .tcb tcb =>
      let expected := inferThreadState st ⟨oid.toNat⟩ tcb
      if tcb.threadState == expected then acc
      else acc.insert oid (.tcb { tcb with threadState := expected })
    | _ => acc
  { st with objects := objs }

/-- V8-G2: ThreadState consistency predicate — the `threadState` field of every
TCB matches the state inferred from queue membership and IPC state. -/
def threadStateConsistent (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (tcb : TCB),
    st.objects[oid]? = some (.tcb tcb) →
    tcb.threadState = inferThreadState st ⟨oid.toNat⟩ tcb

end SeLe4n.Kernel

