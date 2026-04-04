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
    (st st' : SystemState) (callerTid targetTid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority)
    (hOk : setPriorityOp st callerTid targetTid newPriority = .ok st')
    (callerTcb : TCB)
    (hCaller : st.objects[callerTid.toObjId]? = some (.tcb callerTcb)) :
    newPriority.val ≤ callerTcb.maxControlledPriority.val := by
  unfold setPriorityOp at hOk
  rw [hCaller] at hOk
  simp only [] at hOk
  unfold validatePriorityAuthority at hOk
  -- The if-then-else: if ≤ then .ok () else .error
  -- If ¬≤, the match on .error would not produce .ok st'
  -- So the ≤ branch must hold
  split at hOk
  · -- validatePriorityAuthority returned .error: hOk : .error _ = .ok _, impossible
    exact absurd hOk (by intro h; exact nomatch h)
  · -- validatePriorityAuthority returned .ok (): validation passed
    -- heq✝ tells us (if newPrio ≤ mcp then .ok else .error) = .ok ()
    -- which means the if-guard was true
    rename_i heq
    simp at heq
    exact heq

/-- D2-J: After `setMCPriorityOp` succeeds, the new MCP does not exceed
the caller's MCP. -/
theorem setMCPriority_authority_bounded
    (st st' : SystemState) (callerTid targetTid : SeLe4n.ThreadId)
    (newMCP : SeLe4n.Priority)
    (hOk : setMCPriorityOp st callerTid targetTid newMCP = .ok st')
    (callerTcb : TCB)
    (hCaller : st.objects[callerTid.toObjId]? = some (.tcb callerTcb)) :
    newMCP.val ≤ callerTcb.maxControlledPriority.val := by
  unfold setMCPriorityOp at hOk
  rw [hCaller] at hOk
  simp only [] at hOk
  -- The if guard: if newMCP > caller.mcp then .error else ...
  split at hOk
  · -- guard true (newMCP > caller.mcp): .error = .ok is impossible
    exact absurd hOk (by intro h; exact nomatch h)
  · -- guard false (¬ newMCP > caller.mcp): proceed
    rename_i hNotGt; omega

end SeLe4n.Kernel.SchedContext.PriorityManagement
