/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.PriorityManagement

/-! # D2-G/H/I/J: Priority Management Preservation Theorems

Transport lemmas, frame preservation, and authority non-escalation proofs
for `setPriorityOp` and `setMCPriorityOp`.
-/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- Transport lemmas — updatePrioritySource
-- ============================================================================

theorem updatePrioritySource_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).scheduler = st.scheduler := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

theorem updatePrioritySource_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).serviceRegistry = st.serviceRegistry := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

theorem updatePrioritySource_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).lifecycle = st.lifecycle := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

-- ============================================================================
-- Transport lemmas — migrateRunQueueBucket
-- ============================================================================

theorem migrateRunQueueBucket_objects_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (newPrio : SeLe4n.Priority) :
    (migrateRunQueueBucket st tid newPrio).objects = st.objects := by
  unfold migrateRunQueueBucket; split <;> rfl

theorem migrateRunQueueBucket_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (newPrio : SeLe4n.Priority) :
    (migrateRunQueueBucket st tid newPrio).serviceRegistry = st.serviceRegistry := by
  unfold migrateRunQueueBucket; split <;> rfl

theorem migrateRunQueueBucket_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (newPrio : SeLe4n.Priority) :
    (migrateRunQueueBucket st tid newPrio).lifecycle = st.lifecycle := by
  unfold migrateRunQueueBucket; split <;> rfl

-- ============================================================================
-- Transport lemmas — updatePrioritySource (additional fields)
-- ============================================================================

theorem updatePrioritySource_irqHandlers_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).irqHandlers = st.irqHandlers := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

theorem updatePrioritySource_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).machine = st.machine := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

theorem updatePrioritySource_objectIndex_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPrio : SeLe4n.Priority) :
    (updatePrioritySource st tid tcb newPrio).objectIndex = st.objectIndex := by
  unfold updatePrioritySource
  split <;> (first | rfl | (split <;> rfl))

-- ============================================================================
-- Transport lemmas — migrateRunQueueBucket (additional fields)
-- ============================================================================

theorem migrateRunQueueBucket_irqHandlers_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (newPrio : SeLe4n.Priority) :
    (migrateRunQueueBucket st tid newPrio).irqHandlers = st.irqHandlers := by
  unfold migrateRunQueueBucket; split <;> rfl

theorem migrateRunQueueBucket_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (newPrio : SeLe4n.Priority) :
    (migrateRunQueueBucket st tid newPrio).machine = st.machine := by
  unfold migrateRunQueueBucket; split <;> rfl

-- ============================================================================
-- D2-J: Authority non-escalation theorems
-- ============================================================================

/-- D2-J: validatePriorityAuthority success implies the priority is bounded.
    Direct from the `if` guard in the definition. -/
theorem validatePriorityAuthority_ok_bounded
    (callerTcb : TCB) (targetPriority : SeLe4n.Priority)
    (hOk : validatePriorityAuthority callerTcb targetPriority = .ok ()) :
    targetPriority.val ≤ callerTcb.maxControlledPriority.val := by
  simp [validatePriorityAuthority] at hOk
  exact hOk

/-- D2-J: After `setPriorityOp` succeeds, the new priority does not exceed
the caller's MCP. Direct proof from the validation check in D2-D. -/
theorem setPriority_authority_bounded
    (st st' : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority)
    (hOk : setPriorityOp st vCallerTid vTargetTid newPriority = .ok st')
    (callerTcb : TCB)
    (hCaller : st.objects[vCallerTid.val.toObjId]? = some (.tcb callerTcb)) :
    newPriority.val ≤ callerTcb.maxControlledPriority.val := by
  -- Reduce to the validatePriorityAuthority check
  have hVal := validatePriorityAuthority_ok_bounded callerTcb newPriority
  unfold setPriorityOp at hOk
  rw [hCaller] at hOk
  -- If validatePriorityAuthority fails, setPriorityOp returns .error,
  -- so it cannot equal .ok st'. Therefore it must succeed.
  match hv : validatePriorityAuthority callerTcb newPriority with
  | .error e => simp [hv] at hOk
  | .ok () => exact hVal hv

/-- D2-J: After `setMCPriorityOp` succeeds, the new MCP does not exceed
the caller's MCP. -/
theorem setMCPriority_authority_bounded
    (st st' : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority)
    (hOk : setMCPriorityOp st vCallerTid vTargetTid newMCP = .ok st')
    (callerTcb : TCB)
    (hCaller : st.objects[vCallerTid.val.toObjId]? = some (.tcb callerTcb)) :
    newMCP.val ≤ callerTcb.maxControlledPriority.val := by
  -- Reduce to the validatePriorityAuthority check
  have hVal := validatePriorityAuthority_ok_bounded callerTcb newMCP
  unfold setMCPriorityOp at hOk
  rw [hCaller] at hOk
  -- If validatePriorityAuthority fails, setMCPriorityOp returns .error
  -- so it cannot equal .ok st'. Therefore it must succeed.
  match hv : validatePriorityAuthority callerTcb newMCP with
  | .error e =>
    simp [hv] at hOk
  | .ok () =>
    exact hVal hv

end SeLe4n.Kernel.SchedContext.PriorityManagement
