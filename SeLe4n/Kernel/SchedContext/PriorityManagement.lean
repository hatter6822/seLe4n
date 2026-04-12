/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations

/-! # D2: Priority Management Operations

Implements `setPriorityOp` and `setMCPriorityOp` as capability-controlled
operations for modifying thread scheduling priority through the SchedContext
subsystem. In seL4's MCS model, priority is a property of the scheduling
context, not the thread directly.

## MCP Authority Model

The Maximum Controlled Priority (MCP) ceiling prevents privilege escalation:
a thread can only set another thread's priority up to its own MCP. This
ensures the authority hierarchy is monotonically non-increasing.

## Priority Update Path

- If the target thread has a bound SchedContext (`.bound` or `.donated`),
  the SchedContext's priority is updated (it owns the scheduling priority).
- If unbound, the TCB's priority field is updated directly.

## Run Queue Migration

When priority changes for a thread currently in the run queue, the thread
is removed and re-inserted at the new priority bucket to maintain correct
scheduling order.
-/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D2-D: validatePriorityAuthority
-- ============================================================================

/-- D2-D: Validate that the caller has sufficient MCP authority to assign
the given priority. Returns `illegalAuthority` if `targetPriority > caller.mcp`.
This is the MCP ceiling check — the primary defense against priority escalation. -/
def validatePriorityAuthority (callerTcb : TCB) (targetPriority : SeLe4n.Priority)
    : Except KernelError Unit :=
  if targetPriority.val ≤ callerTcb.maxControlledPriority.val then .ok ()
  else .error .illegalAuthority

-- ============================================================================
-- D2-E: setPriorityOp
-- ============================================================================

/-- Helper: get the current effective priority value for a thread, resolving
through SchedContext binding. Returns the TCB priority if unbound, or the
SchedContext priority if bound/donated.

**Invariant dependency**: For bound/donated threads, this function requires
`schedContextBindingConsistent` (Invariant/Defs.lean) to guarantee the
referenced SchedContext exists. If it does not (invariant violation), the
function defensively falls back to `tcb.priority`. This fallback path is
dead code when system invariants hold. -/
def getCurrentPriority (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority :=
  match tcb.schedContextBinding with
  | .unbound => tcb.priority
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => sc.priority
    | _ => tcb.priority

/-- Helper: update the priority of a thread's scheduling source (SchedContext
or TCB) and store the updated object. Returns the updated state.

**Invariant dependency**: For bound/donated threads, requires
`schedContextBindingConsistent` to guarantee the SchedContext exists.
If it does not (invariant violation), the function defensively returns
the state unchanged. This no-op path is dead code when invariants hold. -/
def updatePrioritySource (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (newPriority : SeLe4n.Priority) : SystemState :=
  match tcb.schedContextBinding with
  | .unbound =>
    -- Update TCB priority directly
    let tcb' := { tcb with priority := newPriority }
    { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
  | .bound scId | .donated scId _ =>
    -- Update SchedContext priority
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) =>
      let sc' := { sc with priority := newPriority }
      { st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
    | _ => st  -- SchedContext missing — no-op (consistency violation)

/-- Helper: if a thread is in the run queue, remove it and re-insert at
the effective priority (new base priority with PIP boost applied). This
maintains correct run queue bucket placement.

AI3-B (M-22): The insertion priority accounts for PIP boost. When a thread
has an active `pipBoost`, the RunQueue placement uses
`max(newPriority, pipBoost)` to ensure PIP-boosted threads retain elevated
scheduling band after priority changes. Without this, a `setPriorityOp` on
a PIP-boosted thread would drop it to the new base priority, causing
priority inversion for the entire blocking chain. -/
def migrateRunQueueBucket (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : SystemState :=
  if tid ∈ st.scheduler.runQueue then
    let rq := st.scheduler.runQueue.remove tid
    -- AI3-B (M-22): Apply PIP boost to new priority
    let effectivePrio := match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => match tcb.pipBoost with
        | none => newPriority
        | some boostPrio => ⟨Nat.max newPriority.val boostPrio.val⟩
      | _ => newPriority  -- defensive fallback: no TCB found
    let rq := rq.insert tid effectivePrio
    { st with scheduler := { st.scheduler with runQueue := rq } }
  else
    st

/-- D2-E: Set the scheduling priority of a target thread.

Sequence:
1. Look up caller TCB, validate MCP authority
2. Look up target TCB
3. Update priority on SchedContext (if bound) or TCB (if unbound)
4. If target is in run queue, perform bucket migration (remove + re-insert)
5. If target is current and priority decreased, trigger reschedule

Returns `invalidArgument` if caller or target is not a TCB.
Returns `illegalAuthority` if `newPriority > caller.maxControlledPriority`. -/
def setPriorityOp (st : SystemState) (callerTid targetTid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : Except KernelError SystemState :=
  -- E1: Caller TCB lookup + MCP authority check
  match st.objects[callerTid.toObjId]? with
  | some (.tcb callerTcb) =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error e => .error e
    | .ok () =>
      -- E2: Target TCB lookup
      match st.objects[targetTid.toObjId]? with
      | some (.tcb targetTcb) =>
        -- E3: Update priority source (SchedContext or TCB)
        let oldPriority := getCurrentPriority st targetTcb
        let st := updatePrioritySource st targetTid targetTcb newPriority
        -- E4: Run queue bucket migration
        let st := migrateRunQueueBucket st targetTid newPriority
        -- E5: Conditional preemption check
        -- If target is current and priority decreased, reschedule
        if st.scheduler.current == some targetTid &&
           newPriority.val < oldPriority.val then
          match schedule st with
          | .ok ((), st') => .ok st'
          | .error e => .error e
        else
          .ok st
      | _ => .error .invalidArgument
  | _ => .error .invalidArgument

-- ============================================================================
-- D2-F: setMCPriorityOp
-- ============================================================================

/-- D2-F: Set the Maximum Controlled Priority (MCP) of a target thread.

The MCP ceiling determines the maximum priority a thread can assign to
other threads (or itself). Reducing MCP may retroactively cap the thread's
current priority (seL4 behavior).

Sequence:
1. Look up caller TCB, validate `newMCP ≤ caller.maxControlledPriority`
2. Look up target TCB, update `maxControlledPriority := newMCP`
3. If target's current priority exceeds new MCP, cap it to MCP
4. If priority was capped and target is in run queue, perform bucket migration

Returns `invalidArgument` if caller or target is not a TCB.
Returns `illegalAuthority` if `newMCP > caller.maxControlledPriority`. -/
def setMCPriorityOp (st : SystemState) (callerTid targetTid : SeLe4n.ThreadId)
    (newMCP : SeLe4n.Priority) : Except KernelError SystemState :=
  -- F1: Caller MCP authority validation (reuses validatePriorityAuthority for consistency)
  match st.objects[callerTid.toObjId]? with
  | some (.tcb callerTcb) =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error e => .error e
    | .ok () =>
      -- F2: Target TCB lookup + MCP update
      match st.objects[targetTid.toObjId]? with
      | some (.tcb targetTcb) =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        let st := { st with objects := st.objects.insert targetTid.toObjId (.tcb targetTcb') }
        -- F3: Priority capping — if current priority exceeds new MCP, cap it
        let currentPrio := getCurrentPriority st targetTcb'
        if currentPrio.val > newMCP.val then
          -- Cap priority to MCP ceiling
          let st := updatePrioritySource st targetTid targetTcb' newMCP
          -- F4: Run queue migration + preemption check for capped priority
          let st := migrateRunQueueBucket st targetTid newMCP
          if st.scheduler.current == some targetTid then
            match schedule st with
            | .ok ((), st') => .ok st'
            | .error e => .error e
          else
            .ok st
        else
          .ok st
      | _ => .error .invalidArgument
  | _ => .error .invalidArgument

end SeLe4n.Kernel.SchedContext.PriorityManagement
