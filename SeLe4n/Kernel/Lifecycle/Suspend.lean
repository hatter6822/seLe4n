/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Scheduler.Operations

/-! # D1: Thread Suspension & Resumption

Implements `suspendThread` and `resumeThread` as first-class kernel operations.
These are the seL4 equivalents of `seL4_TCB_Suspend` and `seL4_TCB_Resume`.

## Suspension sequence (D1-G)

1. Validate thread exists and is not already Inactive
2. Cancel IPC blocking (remove from endpoint/notification queues)
3. Cancel SchedContext donation (return to original owner)
4. Remove from scheduler run queue
5. Clear pending state (message, timeout, queue links)
6. Set `threadState := .Inactive`
7. If suspended thread was current, trigger reschedule

## Resumption sequence (D1-H)

1. Validate thread exists and is Inactive
2. Set `threadState := .Ready`, `ipcState := .ready`
3. Insert into run queue at effective priority
4. If resumed thread has higher priority than current, reschedule
-/

namespace SeLe4n.Kernel.Lifecycle.Suspend

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D1-C: cancelIpcBlocking
-- ============================================================================

/-- Helper: update a TCB's ipcState and queue links to ready/detached.
    Only modifies `objects` field of the state. -/
private def clearTcbIpcFields (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb') =>
    { st with objects := st.objects.insert tid.toObjId (.tcb { tcb' with
        ipcState := .ready
        queuePrev := none
        queueNext := none
        queuePPrev := none }) }
  | _ => st

/-- Helper: clearTcbIpcFields preserves the scheduler. -/
theorem clearTcbIpcFields_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).scheduler = st.scheduler := by
  unfold clearTcbIpcFields; split <;> rfl

/-- Helper: clearTcbIpcFields preserves the serviceRegistry. -/
theorem clearTcbIpcFields_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).serviceRegistry = st.serviceRegistry := by
  unfold clearTcbIpcFields; split <;> rfl

/-- Helper: clearTcbIpcFields preserves lifecycle. -/
theorem clearTcbIpcFields_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).lifecycle = st.lifecycle := by
  unfold clearTcbIpcFields; split <;> rfl

def cancelIpcBlocking (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState :=
  match tcb.ipcState with
  | .ready => st
  | .blockedOnSend _ | .blockedOnReceive _ | .blockedOnCall _ =>
    clearTcbIpcFields (removeFromAllEndpointQueues st tid) tid
  | .blockedOnReply _ _ =>
    clearTcbIpcFields st tid
  | .blockedOnNotification _ =>
    clearTcbIpcFields (removeFromAllNotificationWaitLists st tid) tid

-- ============================================================================
-- D1-D: cancelDonation
-- ============================================================================

/-- D1-D: Cancel any SchedContext donation for a thread being suspended.
If `.donated`, return to original owner via `cleanupDonatedSchedContext`.
If `.bound`, unbind the SchedContext. If `.unbound`, no-op.
Postcondition: the thread's `schedContextBinding = .unbound`. -/
def cancelDonation (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState :=
  match tcb.schedContextBinding with
  | .unbound => st
  | .bound scId =>
    -- Unbind: clear the SchedContext's boundThread
    let st1 : SystemState := match st.objects[scId.toObjId]? with
      | some (.schedContext sc) =>
        let sc' := { sc with boundThread := none }
        { st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
      | _ => st
    -- Clear TCB binding
    match st1.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      let tcb'' := { tcb' with schedContextBinding := .unbound }
      { st1 with objects := st1.objects.insert tid.toObjId (.tcb tcb'') }
    | _ => st1
  | .donated _ _ =>
    cleanupDonatedSchedContext st tid

-- ============================================================================
-- D1-F: clearPendingState
-- ============================================================================

/-- D1-F: Clear transient state on a TCB being suspended. Zeroes out
pending message, timeout budget, and queue link fields to ensure clean
state when the thread is Inactive. -/
def clearPendingState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
    { st with objects := st.objects.insert tid.toObjId (.tcb { tcb with
        pendingMessage := none
        timeoutBudget := none
        queuePrev := none
        queueNext := none
        queuePPrev := none }) }
  | _ => st

-- ============================================================================
-- D1-G: suspendThread (composite)
-- ============================================================================

/-- D1-G: Suspend a thread — the complete suspension sequence.

Validates the target thread exists and is not already Inactive, then
performs the full cleanup pipeline: IPC blocking cancellation, donation
cleanup, run queue removal, pending state clearing, and thread state
transition to Inactive. If the suspended thread was the current thread,
triggers a reschedule.

Returns `invalidArgument` if the target is not a TCB, `invalidState` if
the thread is already Inactive. -/
def suspendThread (st : SystemState) (tid : SeLe4n.ThreadId)
    : Except KernelError SystemState :=
  -- G1: TCB lookup + state validation
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
    if tcb.threadState == .Inactive then .error .illegalState
    else
      -- G2: Cancel IPC blocking
      let st := cancelIpcBlocking st tid tcb
      -- Re-lookup TCB after IPC cleanup (state may have changed)
      let tcb' := match st.objects[tid.toObjId]? with
        | some (.tcb t) => t | _ => tcb
      -- G3: Cancel donation
      let st := _root_.SeLe4n.Kernel.Lifecycle.Suspend.cancelDonation st tid tcb'
      -- G4: Remove from run queue
      let st := removeRunnable st tid
      -- G5: Clear pending state
      let st := clearPendingState st tid
      -- G6: Set threadState := .Inactive
      let st := match st.objects[tid.toObjId]? with
        | some (.tcb tcb'') =>
          { st with objects := st.objects.insert tid.toObjId (.tcb { tcb'' with
              threadState := .Inactive }) }
        | _ => st
      -- G7: If suspended thread was current, trigger reschedule
      if st.scheduler.current == some tid then
        match schedule st with
        | .ok ((), st') => .ok st'
        | .error e => .error e
      else
        .ok st
  | _ => .error .invalidArgument

-- ============================================================================
-- D1-H: resumeThread
-- ============================================================================

/-- D1-H: Resume a suspended thread — transition from Inactive to Ready.

Validates the target is a TCB in Inactive state, sets threadState to Ready
and ipcState to ready, inserts into the run queue at the thread's priority,
and triggers a reschedule if the resumed thread has higher priority than
the current thread.

Returns `invalidArgument` if not a TCB, `invalidState` if not Inactive. -/
def resumeThread (st : SystemState) (tid : SeLe4n.ThreadId)
    : Except KernelError SystemState :=
  -- H1: TCB lookup
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
    -- H2: State validation — must be Inactive
    if tcb.threadState != .Inactive then .error .illegalState
    else
      -- H3: Set threadState := .Ready, ipcState := .ready
      let tcb' := { tcb with threadState := .Ready, ipcState := .ready }
      let st := { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
      -- H4: Insert into run queue at effective priority
      let st := ensureRunnable st tid
      -- H5: Conditional preemption check
      -- If the resumed thread has higher priority than current, reschedule
      let needsReschedule : Bool := match st.scheduler.current with
        | some curTid =>
          match st.objects[curTid.toObjId]? with
          | some (.tcb curTcb) => tcb'.priority.val > curTcb.priority.val
          | _ => true  -- No valid current → always reschedule
        | none => false  -- No current thread → no preemption needed
      if needsReschedule then
        match schedule st with
        | .ok ((), st') => .ok st'
        | .error e => .error e
      else
        .ok st
  | _ => .error .invalidArgument

end SeLe4n.Kernel.Lifecycle.Suspend
