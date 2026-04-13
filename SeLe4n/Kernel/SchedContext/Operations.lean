/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.SchedContext.ReplenishQueue
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Model.State

/-! # SchedContext Operations — WS-Z Phase Z5

Capability-controlled operations to bind threads to scheduling contexts,
configure scheduling parameters, and enforce admission control. These
operations make execution a capability-controlled resource.

## Operations:
- `validateSchedContextParams`: Parameter validation for configure
- `collectSchedContexts`: Collect all SchedContexts for admission control
- `schedContextConfigure`: Configure SchedContext parameters with validation
- `schedContextBind`: Bind a thread to a SchedContext (bidirectional)
- `schedContextUnbind`: Unbind a thread from a SchedContext
- `schedContextYieldTo`: Budget transfer between SchedContexts (kernel-internal)
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- Z5-F1: Parameter validation
-- ============================================================================

/-- Maximum priority value (seL4: 255). -/
def maxPriorityVal : Nat := 255

/-- Maximum number of scheduling domains (seL4: 16). -/
def numDomainsVal : Nat := 16

/-- Z5-F1: Validate SchedContext configuration parameters.
Returns error if any parameter violates well-formedness constraints:
- `period > 0` (required for CBS)
- `budget ≤ period` (cannot use more than 100% of a period)
- `priority ≤ maxPriority` (within valid priority range)
- `domain < numDomains` (within valid domain range) -/
def validateSchedContextParams (budget period priority _deadline domain : Nat)
    : Except KernelError Unit :=
  if period == 0 then .error .invalidArgument
  else if budget > period then .error .invalidArgument
  else if priority > maxPriorityVal then .error .invalidArgument
  else if domain ≥ numDomainsVal then .error .invalidArgument
  else .ok ()

-- ============================================================================
-- Z5-F2: Admission control
-- ============================================================================

/-- Z5-F2: Collect all SchedContext objects from the object store for admission
control, optionally excluding a specific SchedContext (used when reconfiguring
an existing SchedContext to avoid double-counting its bandwidth). -/
def collectSchedContexts (st : SystemState) (excludeId : Option ObjId := none)
    : List SchedContext :=
  st.objectIndex.filterMap fun oid =>
    if excludeId == some oid then none
    else match (st.objects[oid]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) => some sc
    | _ => none

/-- Z5-F2: Check admission control — total bandwidth including candidate
must not exceed 100% (1000 per-mille). When reconfiguring an existing
SchedContext, `excludeId` prevents the old configuration from being
double-counted. -/
def checkAdmission (st : SystemState) (candidate : SchedContext)
    (excludeId : Option ObjId := none) : Bool :=
  admissionCheck (collectSchedContexts st excludeId) candidate

-- ============================================================================
-- Z5-F3: schedContextConfigure
-- ============================================================================

/-- Z5-F3: Configure a SchedContext's scheduling parameters.
1. Validates parameters (period > 0, budget ≤ period, etc.)
2. Checks admission control (total bandwidth ≤ 100%)
3. Updates the SchedContext object in the store -/
def schedContextConfigure (scId : ObjId) (budget period priority deadline domain : Nat)
    : Kernel Unit :=
  fun st =>
    match validateSchedContextParams budget period priority deadline domain with
    | .error e => .error e
    | .ok () =>
      match (st.objects[scId]? : Option KernelObject) with
      | some (KernelObject.schedContext sc) =>
        let updated : SchedContext :=
          { sc with
            budget := ⟨budget⟩
            period := ⟨period⟩
            priority := ⟨priority⟩
            deadline := ⟨deadline⟩
            domain := ⟨domain⟩
            budgetRemaining := ⟨budget⟩
            -- AE3-F/U-14: Reset replenishment list to a single fresh entry
            -- with the new budget amount. Prevents stale entries from prior
            -- configuration referencing outdated budget/period values.
            replenishments := [{ amount := ⟨budget⟩, eligibleAt := st.machine.timer }] }
        if checkAdmission st updated (some scId) then
          storeObject scId (KernelObject.schedContext updated) st
        else
          .error .resourceExhausted
      | _ => .error .objectNotFound

-- ============================================================================
-- Z5-G1/G2/G3: schedContextBind
-- ============================================================================

/-- Z5-G1/G2/G3: Bind a thread to a SchedContext.
1. Precondition: SchedContext has no bound thread, TCB is unbound
2. Set bidirectional binding (sc.boundThread, tcb.schedContextBinding)
3. Write both updated objects to store
4. If thread is in RunQueue, remove and re-insert at SchedContext priority
   to maintain `effectiveParamsMatchRunQueue` invariant -/
def schedContextBind (scId : ObjId) (threadId : ThreadId) : Kernel Unit :=
  fun st =>
    match (st.objects[scId]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) =>
      -- Z5-G1: Precondition check — SchedContext must not already have a bound thread
      if sc.boundThread.isSome then .error .illegalState
      else
        match (st.objects[threadId.toObjId]? : Option KernelObject) with
        | some (KernelObject.tcb tcb) =>
          -- AE3-A/U-11: Domain consistency check — reject cross-domain binding.
          -- The domain filter (chooseBestRunnableInDomainEffective) uses tcb.domain
          -- but effective priority resolves from sc.domain. Mismatched domains would
          -- cause a thread to pass the domain filter by TCB domain but be prioritized
          -- by SchedContext domain.
          if tcb.domain != sc.domain then .error .invalidArgument
          else
          -- Z5-G1: Precondition check — TCB must be unbound.
          -- AI6-D (L-13): `schedContextBind` checks `tcb.schedContextBinding`
          -- (binding state: `.unbound`) but NOT the thread's operational state
          -- (`ipcState`, scheduler state). This matches seL4 MCS semantics
          -- where SchedContext binding is independent of thread execution
          -- state — binding can occur while a thread is blocked, ready, or in
          -- any other operational state. Operational safety is ensured by the
          -- SchedContext invariant bundle (Invariant/Defs.lean), not by
          -- per-bind state checks.
          match tcb.schedContextBinding with
          | .unbound =>
            -- Z5-G2: Bidirectional binding
            let scIdTyped : SchedContextId := ⟨scId.toNat⟩
            let updatedSc := { sc with boundThread := some threadId }
            let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.bound scIdTyped }
            -- Write both updated objects
            let st1 := { st with objects := st.objects.insert scId (KernelObject.schedContext updatedSc) }
            let st2 := { st1 with objects := st1.objects.insert threadId.toObjId (KernelObject.tcb updatedTcb) }
            -- Z5-G3: If thread is in RunQueue, remove and re-insert at
            -- SchedContext-derived priority. Under dequeue-on-dispatch, only
            -- runnable-but-not-current threads are in the RunQueue. After bind,
            -- the effective priority resolves from the SchedContext, so we must
            -- update the RunQueue entry to match.
            -- AE3-J/SC-09: Run queue insertion uses pre-update sc.priority.
            -- AG1-A: Now uses effective priority (base + PIP boost) to ensure
            -- PIP-boosted threads are placed in the correct bucket.
            let st3 := if threadId ∈ st2.scheduler.runQueue then
              let rqRemoved := st2.scheduler.runQueue.remove threadId
              let rqInserted := rqRemoved.insert threadId (resolveInsertPriority st2 threadId sc)
              { st2 with scheduler := { st2.scheduler with runQueue := rqInserted } }
            else st2
            -- S-05/PERF-O1: Add thread to per-SchedContext thread index
            let st4 := { st3 with scThreadIndex :=
              (scThreadIndexAdd st3.scThreadIndex scIdTyped threadId) }
            .ok ((), st4)
          | _ => .error .illegalState
        | _ => .error .objectNotFound
    | _ => .error .objectNotFound

-- ============================================================================
-- Z5-H1/H2/H3: schedContextUnbind
-- ============================================================================

/-- Z5-H1/H2/H3: Unbind a thread from a SchedContext.
1. Verify the SchedContext has a bound thread
2. (H1) If bound thread is the current thread, clear current to trigger
   rescheduling — prevents unbinding the running thread without preemption
3. (H2) If thread is in RunQueue, remove it (it will be re-enqueued at
   legacy TCB priority by the next schedule call if still runnable)
4. Clear both sides of the bidirectional binding
5. (H3) Remove SchedContext from replenish queue -/
def schedContextUnbind (scId : ObjId) : Kernel Unit :=
  fun st =>
    match (st.objects[scId]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        match (st.objects[tid.toObjId]? : Option KernelObject) with
        | some (KernelObject.tcb tcb) =>
          -- Z5-H1: Preemption guard — if bound thread is current, clear current
          -- to force rescheduling. Under dequeue-on-dispatch, the current thread
          -- is not in the RunQueue, so clearing current is sufficient.
          let st0 := if st.scheduler.current == some tid then
            { st with scheduler := { st.scheduler with current := none } }
          else st
          -- Z5-H2: If thread is in RunQueue (runnable but not current), remove it.
          -- After unbind the thread reverts to legacy priority; the next schedule
          -- call will re-enqueue it correctly if still runnable.
          let st1 := if tid ∈ st0.scheduler.runQueue then
            { st0 with scheduler := { st0.scheduler with
                runQueue := st0.scheduler.runQueue.remove tid } }
          else st0
          -- Z5-H2 cont: Clear both sides of the binding
          let updatedSc := { sc with boundThread := none, isActive := false }
          let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.unbound }
          let st2 := { st1 with objects := st1.objects.insert scId (KernelObject.schedContext updatedSc) }
          let st3 := { st2 with objects := st2.objects.insert tid.toObjId (KernelObject.tcb updatedTcb) }
          -- Z5-H3: Remove SchedContext from replenish queue
          let scIdTyped : SchedContextId := ⟨scId.toNat⟩
          let cleanedQueue := ReplenishQueue.remove st3.scheduler.replenishQueue scIdTyped
          let st4 := { st3 with scheduler := { st3.scheduler with replenishQueue := cleanedQueue } }
          -- S-05/PERF-O1: Remove thread from per-SchedContext thread index
          let st5 := { st4 with scThreadIndex :=
            (scThreadIndexRemove st4.scThreadIndex scIdTyped tid) }
          .ok ((), st5)
        -- Bound thread's TCB not found — clear SC side anyway
        | _ =>
          let updatedSc := { sc with boundThread := none, isActive := false }
          let st1 := { st with objects := st.objects.insert scId (KernelObject.schedContext updatedSc) }
          let scIdTyped : SchedContextId := ⟨scId.toNat⟩
          let cleanedQueue := ReplenishQueue.remove st1.scheduler.replenishQueue scIdTyped
          let st2 := { st1 with scheduler := { st1.scheduler with replenishQueue := cleanedQueue } }
          -- S-05/PERF-O1: Remove stale index entry even when TCB is missing
          let st3 := { st2 with scThreadIndex :=
            (scThreadIndexRemove st2.scThreadIndex scIdTyped tid) }
          .ok ((), st3)
    | _ => .error .objectNotFound

-- ============================================================================
-- Z5-I1/I2: schedContextYieldTo (kernel-internal)
-- ============================================================================

/-- Z5-I1/I2: Transfer budget from one SchedContext to another.
Kernel-internal helper for hierarchical scheduling. Not a userspace syscall.
Transfers `budgetRemaining` from source to target, capped at target's
configured `budget`. If the target's bound thread was budget-starved
(budget was 0, now > 0), enqueue it in the RunQueue.

AF4-G (AF-30, AF-47): `schedContextYieldTo` is a KERNEL-INTERNAL helper,
not a syscall entry point. No capability check is performed here because
this function operates below the capability layer — callers are responsible
for validating access rights before invoking. It is a pure function
(returns `SystemState`, not monadic) because the yield operation has a
well-defined fallback for every input: pattern-match failures on missing
or non-SchedContext objects return `st` unchanged (identity fallback),
and budget transfer is always well-defined (capped at target's configured
budget via `min`). Cross-subsystem invariant preservation is proven by
`schedContextYieldTo_crossSubsystemInvariant_bridge` in CrossSubsystem.lean. -/
def schedContextYieldTo (st : SystemState) (fromScId targetScId : SchedContextId)
    : SystemState :=
  match (st.objects[fromScId.toObjId]? : Option KernelObject) with
  | some (KernelObject.schedContext fromSc) =>
    match (st.objects[targetScId.toObjId]? : Option KernelObject) with
    | some (KernelObject.schedContext targetSc) =>
      -- Z5-I1: Transfer budget from source to target
      let transferAmount := fromSc.budgetRemaining.val
      let newTargetBudget := min (targetSc.budgetRemaining.val + transferAmount) targetSc.budget.val
      let wasBudgetStarved := targetSc.budgetRemaining.val == 0
      let updatedFrom := { fromSc with budgetRemaining := Budget.zero, isActive := false }
      let updatedTarget := { targetSc with
        budgetRemaining := ⟨newTargetBudget⟩
        isActive := newTargetBudget > 0 }
      let st1 := { st with objects := st.objects.insert fromScId.toObjId (KernelObject.schedContext updatedFrom) }
      let st2 := { st1 with objects := st1.objects.insert targetScId.toObjId (KernelObject.schedContext updatedTarget) }
      -- Z5-I2: If target's bound thread was budget-starved and now has budget,
      -- enqueue it in RunQueue so it becomes schedulable again.
      if wasBudgetStarved && newTargetBudget > 0 then
        match targetSc.boundThread with
        | some tid =>
          -- AG1-A: Use effective priority (base + PIP boost) for RunQueue insertion
          if tid ∉ st2.scheduler.runQueue && st2.scheduler.current != some tid then
            { st2 with scheduler := { st2.scheduler with
                runQueue := st2.scheduler.runQueue.insert tid (resolveInsertPriority st2 tid targetSc) } }
          else st2
        | none => st2
      else st2
    | _ => st
  | _ => st

end SeLe4n.Kernel.SchedContextOps
