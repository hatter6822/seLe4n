/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.SchedContext.ReplenishQueue
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
control. Uses the object index to iterate. -/
def collectSchedContexts (st : SystemState) : List SchedContext :=
  st.objectIndex.filterMap fun oid =>
    match (st.objects[oid]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) => some sc
    | _ => none

/-- Z5-F2: Check admission control — total bandwidth including candidate
must not exceed 100% (1000 per-mille). -/
def checkAdmission (st : SystemState) (candidate : SchedContext) : Bool :=
  admissionCheck (collectSchedContexts st) candidate

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
            budgetRemaining := ⟨budget⟩ }
        if checkAdmission st updated then
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
3. Write both updated objects to store -/
def schedContextBind (scId : ObjId) (threadId : ThreadId) : Kernel Unit :=
  fun st =>
    match (st.objects[scId]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) =>
      -- Z5-G1: Precondition check — SchedContext must not already have a bound thread
      if sc.boundThread.isSome then .error .illegalState
      else
        match (st.objects[threadId.toObjId]? : Option KernelObject) with
        | some (KernelObject.tcb tcb) =>
          -- Z5-G1: Precondition check — TCB must be unbound
          match tcb.schedContextBinding with
          | .unbound =>
            -- Z5-G2: Bidirectional binding
            let scIdTyped : SchedContextId := ⟨scId.toNat⟩
            let updatedSc := { sc with boundThread := some threadId }
            let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.bound scIdTyped }
            -- Write both updated objects
            let st1 := { st with objects := st.objects.insert scId (KernelObject.schedContext updatedSc) }
            let st2 := { st1 with objects := st1.objects.insert threadId.toObjId (KernelObject.tcb updatedTcb) }
            .ok ((), st2)
          | _ => .error .illegalState
        | _ => .error .objectNotFound
    | _ => .error .objectNotFound

-- ============================================================================
-- Z5-H1/H2/H3: schedContextUnbind
-- ============================================================================

/-- Z5-H1/H2/H3: Unbind a thread from a SchedContext.
1. Verify the SchedContext has a bound thread
2. Clear both sides of the bidirectional binding
3. Remove SchedContext from replenish queue -/
def schedContextUnbind (scId : ObjId) : Kernel Unit :=
  fun st =>
    match (st.objects[scId]? : Option KernelObject) with
    | some (KernelObject.schedContext sc) =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        match (st.objects[tid.toObjId]? : Option KernelObject) with
        | some (KernelObject.tcb tcb) =>
          -- Z5-H2: Clear both sides of the binding
          let updatedSc := { sc with boundThread := none, isActive := false }
          let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.unbound }
          let st1 := { st with objects := st.objects.insert scId (KernelObject.schedContext updatedSc) }
          let st2 := { st1 with objects := st1.objects.insert tid.toObjId (KernelObject.tcb updatedTcb) }
          -- Z5-H3: Remove SchedContext from replenish queue
          let scIdTyped : SchedContextId := ⟨scId.toNat⟩
          let cleanedQueue := ReplenishQueue.remove st2.scheduler.replenishQueue scIdTyped
          let st3 := { st2 with scheduler := { st2.scheduler with replenishQueue := cleanedQueue } }
          .ok ((), st3)
        -- Bound thread's TCB not found — clear SC side anyway
        | _ =>
          let updatedSc := { sc with boundThread := none, isActive := false }
          let st1 := { st with objects := st.objects.insert scId (KernelObject.schedContext updatedSc) }
          let scIdTyped : SchedContextId := ⟨scId.toNat⟩
          let cleanedQueue := ReplenishQueue.remove st1.scheduler.replenishQueue scIdTyped
          let st2 := { st1 with scheduler := { st1.scheduler with replenishQueue := cleanedQueue } }
          .ok ((), st2)
    | _ => .error .objectNotFound

-- ============================================================================
-- Z5-I1/I2: schedContextYieldTo (kernel-internal)
-- ============================================================================

/-- Z5-I1/I2: Transfer budget from one SchedContext to another.
Kernel-internal helper for hierarchical scheduling. Not a userspace syscall.
Transfers `budgetRemaining` from source to target, capped at target's
configured `budget`. -/
def schedContextYieldTo (st : SystemState) (fromScId targetScId : SchedContextId)
    : SystemState :=
  match (st.objects[fromScId.toObjId]? : Option KernelObject) with
  | some (KernelObject.schedContext fromSc) =>
    match (st.objects[targetScId.toObjId]? : Option KernelObject) with
    | some (KernelObject.schedContext targetSc) =>
      -- Z5-I1: Transfer budget from source to target
      let transferAmount := fromSc.budgetRemaining.val
      let newTargetBudget := min (targetSc.budgetRemaining.val + transferAmount) targetSc.budget.val
      let updatedFrom := { fromSc with budgetRemaining := Budget.zero, isActive := false }
      let updatedTarget := { targetSc with
        budgetRemaining := ⟨newTargetBudget⟩
        isActive := newTargetBudget > 0 }
      let st1 := { st with objects := st.objects.insert fromScId.toObjId (KernelObject.schedContext updatedFrom) }
      { st1 with objects := st1.objects.insert targetScId.toObjId (KernelObject.schedContext updatedTarget) }
    | _ => st
  | _ => st

end SeLe4n.Kernel.SchedContextOps
