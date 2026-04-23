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

## AN5-D (SC-M02) — Closure-form preservation theorems

The preservation theorems for `setPriorityOp` and `setMCPriorityOp`
(in `SchedContext/Invariant/PriorityPreservation.lean`) carry an
`hSchedProj` closure hypothesis representing the optional preemption-
schedule call. This is structurally the same pattern as the `H-07`
finding for information-flow projection theorems (see
`docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` §H-07).

**Discharge plan**: AN6-A performs the substantive discharge of
projection closure-form theorems. The priority-management closure form
follows the same recipe: frame lemmas in
`Scheduler/Operations/Preservation.lean` (specifically
`schedule_preserves_schedulerInvariantBundle` and its domain/EDF
companions) compose to eliminate the closure. AN5-D retains the
closure-form version at this phase; AN6-A's discharge recipe applies
here unchanged. -/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D2-D: validatePriorityAuthority
-- ============================================================================

/-- AK8-D (WS-AK / C-M05): Hardware priority ceiling. Matches seL4 MCS and
the `MAX_PRIORITY = 255` constant exposed by the Rust ABI (`sele4n-types`)
and `decodeSchedContextConfigureArgsChecked` (AK3-J). Any priority value
above this cap cannot be encoded into the platform's 8-bit priority register
file and would be truncated at the ABI boundary — validation rejects it
instead. -/
def maxHardwarePriority : Nat := 255

/-- D2-D: Validate that the caller has sufficient MCP authority to assign
the given priority. Returns `illegalAuthority` if `targetPriority > caller.mcp`.
This is the MCP ceiling check — the primary defense against priority escalation.

**AK8-D (WS-AK / C-M05) — MCP bound rationale:** `maxControlledPriority` is
an unbounded `Nat` in the Lean model. Standard seL4 MCS semantics allow a
root task with `maxControlledPriority = ∞` to set arbitrary priority on any
child; that matches the reference specification (seL4 Manual §5.2 —
"Priorities and MCPs") and is a deliberate design choice rather than a bug.

However, the ABI transport layer truncates priorities to 8 bits (matching
ARM GIC-400 `IPRIORITYR` and seL4's `seL4_MaxPrio = 255`). To surface this
truncation point explicitly at the model layer, we additionally validate
`targetPriority ≤ maxHardwarePriority`. This produces the same
`illegalAuthority` result as the MCP ceiling violation and matches the
existing `decodeSchedContextConfigureArgsChecked` bound from AK3-J. -/
def validatePriorityAuthority (callerTcb : TCB) (targetPriority : SeLe4n.Priority)
    : Except KernelError Unit :=
  if targetPriority.val > maxHardwarePriority then .error .illegalAuthority
  else if targetPriority.val ≤ callerTcb.maxControlledPriority.val then .ok ()
  else .error .illegalAuthority

/-- AK8-D (WS-AK / C-M05): Soundness — if `validatePriorityAuthority`
succeeds, the target priority fits in the platform's 8-bit priority
register width. This witnesses that every priority assigned via the
priority-management API path is representable in hardware, independent of
how the Lean-level `maxControlledPriority` is configured. -/
theorem validatePriorityAuthority_bound
    (callerTcb : TCB) (newPri : SeLe4n.Priority)
    (h : validatePriorityAuthority callerTcb newPri = .ok ()) :
    newPri.val ≤ maxHardwarePriority := by
  unfold validatePriorityAuthority at h
  by_cases hLt : newPri.val > maxHardwarePriority
  · simp [hLt] at h
  · exact Nat.le_of_not_lt hLt

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
dead code when system invariants hold.

**AK8-E (WS-AK / C-M06) — Error-surfacing variant**: this lookup-tolerant
signature is preserved for backward compatibility and for proof contexts
where the `schedContextBindingConsistent` invariant has already been
established at the call site. Production dispatch paths should prefer
`getCurrentPriorityChecked` (below), which surfaces the "bound to
non-existent SchedContext" case as `.error .schedContextNotFound` rather
than silently masking it. -/
def getCurrentPriority (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority :=
  match tcb.schedContextBinding with
  | .unbound => tcb.priority
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => sc.priority
    | _ => tcb.priority

/-- AK8-E (WS-AK / C-M06): Error-surfacing variant of `getCurrentPriority`.

Returns `.error .objectNotFound` if the TCB's `schedContextBinding` is
`.bound scId` or `.donated scId _` but the referenced SchedContext is not
present in the object store (indicating a `schedContextBindingConsistent`
invariant violation). Returns `.ok sc.priority` when the binding resolves
cleanly, and `.ok tcb.priority` for unbound threads.

The error variant reuses `.objectNotFound` (rather than introducing a new
`.schedContextNotFound` variant) to keep the Rust ABI discriminant range
stable at 49 entries — the missing-binding scenario is a genuine
"referenced object not in store" case and matches the semantics of the
existing variant.

This variant is the preferred entry point for production kernel-entry paths
that read priority for a potentially-bound TCB (e.g., preemption checks in
`setPriorityOp`/`setMCPriorityOp`). The untagged lookup-tolerant
`getCurrentPriority` remains available for proof-layer code where the
binding invariant is established as a precondition. -/
def getCurrentPriorityChecked (st : SystemState) (tcb : TCB)
    : Except KernelError SeLe4n.Priority :=
  match tcb.schedContextBinding with
  | .unbound => .ok tcb.priority
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => .ok sc.priority
    | _ => .error .objectNotFound

/-- AK8-E (C-M06): Soundness — when `getCurrentPriorityChecked` returns
`.ok p`, the result matches the lookup-tolerant `getCurrentPriority`. This
allows existing proofs that reason about `getCurrentPriority` to transport
to the checked variant's success case. -/
theorem getCurrentPriorityChecked_ok_eq_getCurrentPriority
    (st : SystemState) (tcb : TCB) (p : SeLe4n.Priority)
    (hOk : getCurrentPriorityChecked st tcb = .ok p) :
    getCurrentPriority st tcb = p := by
  unfold getCurrentPriorityChecked at hOk
  unfold getCurrentPriority
  split at hOk
  · -- unbound branch
    exact Except.ok.inj hOk
  · -- bound branch
    split at hOk
    · exact Except.ok.inj hOk
    · cases hOk
  · -- donated branch
    split at hOk
    · exact Except.ok.inj hOk
    · cases hOk

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
    -- AI3-B (M-22): Apply PIP boost to new priority.
    -- AK2-J (S-M08): The defensive fallback (TCB missing — unreachable under
    -- `runnableThreadsAreTCBs`) now takes the max of `newPriority` and the
    -- RunQueue's cached priority for `tid`. Any PIP boost previously recorded
    -- in the RunQueue is therefore preserved rather than silently erased.
    let effectivePrio := match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => match tcb.pipBoost with
        | none => newPriority
        | some boostPrio => ⟨Nat.max newPriority.val boostPrio.val⟩
      | _ =>
        match st.scheduler.runQueue.threadPriority[tid]? with
        | some rqPrio => ⟨Nat.max newPriority.val rqPrio.val⟩
        | none => newPriority
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
Returns `illegalAuthority` if `newPriority > caller.maxControlledPriority`.

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: both
`callerTid` and `targetTid` have type `ValidThreadId`. The Lean type
system forbids any caller from feeding `ThreadId.sentinel` for either
argument. Uses `vCallerTid.val` / `vTargetTid.val` directly in the body
so `split at` tactics in preservation proofs work cleanly. -/
def setPriorityOp (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority) : Except KernelError SystemState :=
  -- E1: Caller TCB lookup + MCP authority check
  match st.objects[vCallerTid.val.toObjId]? with
  | some (.tcb callerTcb) =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error e => .error e
    | .ok () =>
      -- E2: Target TCB lookup
      match st.objects[vTargetTid.val.toObjId]? with
      | some (.tcb targetTcb) =>
        -- E3: Update priority source (SchedContext or TCB)
        let oldPriority := getCurrentPriority st targetTcb
        let st := updatePrioritySource st vTargetTid.val targetTcb newPriority
        -- E4: Run queue bucket migration
        let st := migrateRunQueueBucket st vTargetTid.val newPriority
        -- E5: Conditional preemption check
        -- If target is current and priority decreased, reschedule
        if st.scheduler.current == some vTargetTid.val &&
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
Returns `illegalAuthority` if `newMCP > caller.maxControlledPriority`.

**AL8 (WS-AL / AK7-E.cascade)**: `callerTid` / `targetTid` are
`ValidThreadId` for compile-time sentinel rejection. -/
def setMCPriorityOp (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority) : Except KernelError SystemState :=
  -- F1: Caller MCP authority validation (reuses validatePriorityAuthority for consistency)
  match st.objects[vCallerTid.val.toObjId]? with
  | some (.tcb callerTcb) =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error e => .error e
    | .ok () =>
      -- F2: Target TCB lookup + MCP update
      match st.objects[vTargetTid.val.toObjId]? with
      | some (.tcb targetTcb) =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        let st := { st with objects := st.objects.insert vTargetTid.val.toObjId (.tcb targetTcb') }
        -- F3: Priority capping — if current priority exceeds new MCP, cap it
        let currentPrio := getCurrentPriority st targetTcb'
        if currentPrio.val > newMCP.val then
          -- Cap priority to MCP ceiling
          let st := updatePrioritySource st vTargetTid.val targetTcb' newMCP
          -- F4: Run queue migration + preemption check for capped priority
          let st := migrateRunQueueBucket st vTargetTid.val newMCP
          if st.scheduler.current == some vTargetTid.val then
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
