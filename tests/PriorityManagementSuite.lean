/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState
import SeLe4n.Kernel.SchedContext.Types

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.SchedContext.PriorityManagement
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Kernel.RobinHood

namespace SeLe4n.Testing.PriorityManagementSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"priority check passed [{label}]"
  else
    throw <| IO.userError s!"priority check failed [{label}]"

/-- Helper: construct a test TCB with given priority and MCP. -/
private def mkTcb (tid : Nat) (prio : Nat := 10) (mcp : Nat := 0xFF)
    (binding : SchedContextBinding := .unbound)
    (state : ThreadState := .Ready) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := ⟨0⟩,
    threadState := state, maxControlledPriority := ⟨mcp⟩,
    schedContextBinding := binding }

/-- Helper: build a minimal SystemState with objects. -/
private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none)
    (runnable : List SeLe4n.ThreadId := []) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
    runnable := runnable
  }
  builder.buildChecked

-- ============================================================================
-- D2-M1: setPriorityOp — success cases
-- ============================================================================

/-- PM-001: setPriority within MCP succeeds for unbound thread. -/
private def pm001_setPriorityWithinMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "target priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "target TCB not found"
  | .error e => throw <| IO.userError s!"setPriority should succeed, got {repr e}"

/-- PM-002: setPriority at exactly MCP boundary succeeds. -/
private def pm002_setPriorityAtMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨100⟩ with
  | .ok _ => expect "setPriority at MCP boundary succeeds" true
  | .error e => throw <| IO.userError s!"setPriority at MCP should succeed, got {repr e}"

-- ============================================================================
-- D2-M2: setPriorityOp — error cases
-- ============================================================================

/-- PM-003: setPriority above MCP returns illegalAuthority. -/
private def pm003_setPriorityAboveMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨101⟩ with
  | .ok _ => throw <| IO.userError "setPriority above MCP should fail"
  | .error e =>
    expect "error is illegalAuthority" (e == .illegalAuthority)

/-- PM-004: setPriority with missing caller returns invalidArgument. -/
private def pm004_setPriorityMissingCaller : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨99⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [(⟨2⟩, .tcb (mkTcb 2 (prio := 30)))]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok _ => throw <| IO.userError "missing caller should fail"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- PM-005: setPriority with missing target returns invalidArgument. -/
private def pm005_setPriorityMissingTarget : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100)))]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok _ => throw <| IO.userError "missing target should fail"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

-- ============================================================================
-- D2-M3: setMCPriorityOp tests
-- ============================================================================

/-- PM-006: setMCPriority within caller's MCP succeeds. -/
private def pm006_setMCPriorityWithinMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 150)))
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨100⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "target MCP updated to 100" (tcb.maxControlledPriority == ⟨100⟩)
    | _ => throw <| IO.userError "target TCB not found"
  | .error e => throw <| IO.userError s!"setMCPriority should succeed, got {repr e}"

/-- PM-007: setMCPriority above caller's MCP returns illegalAuthority. -/
private def pm007_setMCPriorityAboveMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 150)))
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨101⟩ with
  | .ok _ => throw <| IO.userError "setMCPriority above MCP should fail"
  | .error e =>
    expect "error is illegalAuthority" (e == .illegalAuthority)

/-- PM-008: setMCPriority caps existing priority when new MCP < current priority. -/
private def pm008_setMCPriorityCapsExisting : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  -- Target has priority 80, we set MCP to 50 — priority should be capped to 50
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80) (mcp := 150)))
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "target MCP set to 50" (tcb.maxControlledPriority == ⟨50⟩)
      -- Priority should be capped: unbound thread priority updated in TCB
      expect "target priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "target TCB not found"
  | .error e => throw <| IO.userError s!"setMCPriority should succeed, got {repr e}"

-- ============================================================================
-- D2-M4: SchedContext binding tests
-- ============================================================================

/-- PM-009: setPriority on SchedContext-bound thread updates SchedContext priority. -/
private def pm009_setPriorityBoundThread : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨30⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    -- SchedContext priority should be updated
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "SchedContext priority updated to 80" (sc'.priority == ⟨80⟩)
    | _ => throw <| IO.userError "SchedContext not found"
  | .error e => throw <| IO.userError s!"setPriority bound should succeed, got {repr e}"

/-- PM-010: setPriority on unbound thread updates TCB priority directly. -/
private def pm010_setPriorityUnboundThread : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨60⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "TCB priority updated to 60" (tcb.priority == ⟨60⟩)
    | _ => throw <| IO.userError "target TCB not found"
  | .error e => throw <| IO.userError s!"setPriority unbound should succeed, got {repr e}"

/-- PM-010b: setMCPriority caps priority on SchedContext-bound thread. -/
private def pm010b_setMCPriorityCapsSchedContextBound : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨80⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  -- Target is bound to SchedContext with priority 80, we set MCP to 50
  -- Priority should be capped: SchedContext priority should become 50
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 150) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok st' =>
    -- Verify MCP was updated on TCB
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "MCP updated to 50" (tcb.maxControlledPriority == ⟨50⟩)
    | _ => throw <| IO.userError "target TCB not found"
    -- Verify SchedContext priority was capped to 50
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "SchedContext priority capped to 50" (sc'.priority == ⟨50⟩)
    | _ => throw <| IO.userError "SchedContext not found after MCP cap"
  | .error e => throw <| IO.userError s!"setMCPriority bound cap should succeed, got {repr e}"

-- ============================================================================
-- D2-M5: MCP authority transitivity
-- ============================================================================

/-- PM-011: MCP authority is transitive — A (MCP=100) sets B's MCP to 80,
B cannot set C's priority above 80. -/
private def pm011_mcpTransitivity : IO Unit := do
  let tidA : SeLe4n.ThreadId := ⟨1⟩
  let tidB : SeLe4n.ThreadId := ⟨2⟩
  let tidC : SeLe4n.ThreadId := ⟨3⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 200))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 20) (mcp := 200)))
  ]
  -- Step 1: A sets B's MCP to 80
  match setMCPriorityOp st ⟨tidA, by decide⟩ ⟨tidB, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    -- Step 2: B tries to set C's priority to 90 (above B's new MCP of 80) — should fail
    match setPriorityOp st' ⟨tidB, by decide⟩ ⟨tidC, by decide⟩ ⟨90⟩ with
    | .ok _ => throw <| IO.userError "B should not set priority above its MCP"
    | .error e =>
      expect "transitive MCP blocks escalation" (e == .illegalAuthority)
  | .error e => throw <| IO.userError s!"step 1 failed: {repr e}"

-- ============================================================================
-- D2-M6: Self-priority tests
-- ============================================================================

/-- PM-012: Thread sets its own priority within its MCP. -/
private def pm012_selfSetPriority : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100)))
  ]
  match setPriorityOp st ⟨tid, by decide⟩ ⟨tid, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "self priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"self setPriority should succeed, got {repr e}"

-- ============================================================================
-- D2-M7: Frozen operation tests
-- ============================================================================

/-- Helper: construct a minimal empty FrozenSystemState. -/
private def emptyFrozenState : FrozenSystemState := {
  objects := freezeMap (RHTable.empty 16)
  irqHandlers := freezeMap (RHTable.empty 16)
  asidTable := freezeMap (RHTable.empty 16)
  serviceRegistry := freezeMap (RHTable.empty 16)
  interfaceRegistry := freezeMap (RHTable.empty 16)
  services := freezeMap (RHTable.empty 16)
  cdtChildMap := freezeMap (RHTable.empty 16)
  cdtParentMap := freezeMap (RHTable.empty 16)
  cdtSlotNode := freezeMap (RHTable.empty 16)
  cdtNodeSlot := freezeMap (RHTable.empty 16)
  cdtEdges := []
  cdtNextNode := ⟨0⟩
  scheduler := {
    byPriority := freezeMap (RHTable.empty 16)
    threadPriority := freezeMap (RHTable.empty 16)
    membership := freezeMap (RHTable.empty 16)
    current := none
    activeDomain := ⟨0⟩
    domainTimeRemaining := 5
    domainSchedule := []
    domainScheduleIndex := 0
    configDefaultTimeSlice := 5
    replenishQueue := { entries := [], size := 0 }
  }
  objectTypes := freezeMap (RHTable.empty 16)
  capabilityRefs := freezeMap (RHTable.empty 16)
  machine := default
  objectIndex := []
  objectIndexSet := freezeMap (RHTable.empty 16)
  scThreadIndex := freezeMap (RHTable.empty 16)
  tlb := TlbState.empty
}

private def mkFrozenState (objs : List (ObjId × FrozenKernelObject)) : FrozenSystemState :=
  let rt := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  { emptyFrozenState with objects := freezeMap rt }

/-- PM-013: Frozen setPriority succeeds within MCP. -/
private def pm013_frozenSetPriority : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match frozenSetPriority callerTid targetTid ⟨80⟩ fst with
  | .ok ((), fst') =>
    match fst'.objects.get? targetTid.toObjId with
    | some (.tcb tcb) =>
      expect "frozen priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "frozen TCB not found"
  | .error e => throw <| IO.userError s!"frozen setPriority should succeed, got {repr e}"

/-- PM-014: Frozen setPriority above MCP fails. -/
private def pm014_frozenSetPriorityAboveMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match frozenSetPriority callerTid targetTid ⟨101⟩ fst with
  | .ok _ => throw <| IO.userError "frozen setPriority above MCP should fail"
  | .error e =>
    expect "frozen error is illegalAuthority" (e == .illegalAuthority)

/-- PM-015: Frozen setMCPriority succeeds and caps priority. -/
private def pm015_frozenSetMCPriority : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80) (mcp := 150)))
  ]
  match frozenSetMCPriority callerTid targetTid ⟨50⟩ fst with
  | .ok ((), fst') =>
    match fst'.objects.get? targetTid.toObjId with
    | some (.tcb tcb) =>
      expect "frozen MCP set to 50" (tcb.maxControlledPriority == ⟨50⟩)
      expect "frozen priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "frozen TCB not found"
  | .error e => throw <| IO.userError s!"frozen setMCPriority should succeed, got {repr e}"

-- =============================================================================
-- AK2-B: Option B priority propagation regression tests
-- =============================================================================

/-- AK2-B-01: `schedContextBind` propagates `sc.priority` into `tcb.priority`. -/
private def pm_ak2b_01_bindPropagatesPriority : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨77⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := none
  }
  let st := mkState [
    (targetTid.toObjId, .tcb (mkTcb 42 (prio := 10) (mcp := 200))),
    (scObjId, .schedContext sc)
  ]
  match SeLe4n.Kernel.SchedContextOps.schedContextBind ⟨scObjId, by decide⟩ ⟨targetTid, by decide⟩ st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "tcb.priority propagated from sc.priority (10 -> 77)"
        (tcb.priority == ⟨77⟩)
    | _ => throw <| IO.userError "bound TCB not found"
  | .error e =>
    throw <| IO.userError s!"schedContextBind failed: {repr e}"

/-- AK2-B-02: `schedContextConfigure` on already-bound SchedContext
propagates the new priority into the bound TCB. -/
private def pm_ak2b_02_configurePropagatesPriority : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  -- Pre-state: sc.priority = 50, tcb.priority = 50 (after bind)
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let st := mkState [
    (targetTid.toObjId, .tcb (mkTcb 42 (prio := 50) (mcp := 200)
      (binding := .bound scId))),
    (scObjId, .schedContext sc)
  ]
  -- Reconfigure to sc.priority = 123
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 0 st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "tcb.priority propagated from new sc.priority (50 -> 123)"
        (tcb.priority == ⟨123⟩)
    | _ => throw <| IO.userError "bound TCB not found"
    match st'.objects[scObjId]? with
    | some (.schedContext sc') =>
      expect "sc.priority updated to 123" (sc'.priority == ⟨123⟩)
    | _ => throw <| IO.userError "SC not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

/-- AK2-B-03: `schedContextConfigure` re-buckets the bound thread in the
RunQueue when SC priority changes. Prior to this test the configure path
left the thread in its old bucket, violating `schedulerPriorityMatch`. -/
private def pm_ak2b_03_configureRebucketsBoundThread : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let stBase := mkState [
    (targetTid.toObjId, .tcb (mkTcb 42 (prio := 50) (mcp := 200)
      (binding := .bound scId))),
    (scObjId, .schedContext sc)
  ]
  -- Insert the bound thread into the RunQueue at its current priority 50.
  let st : SystemState := { stBase with scheduler :=
    { stBase.scheduler with
      runQueue := stBase.scheduler.runQueue.insert targetTid ⟨50⟩ } }
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 0 st with
  | .ok ((), st') =>
    -- After reconfigure, the RunQueue's cached priority for this thread
    -- must match the new priority (123), not the old (50).
    match st'.scheduler.runQueue.threadPriority[targetTid]? with
    | some prio =>
      expect "RunQueue bucket migrated to new priority (50 -> 123)"
        (prio == ⟨123⟩)
    | none =>
        throw <| IO.userError
          "RunQueue missing thread after reconfigure (thread was present before)"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

-- =============================================================================
-- AK2-E: CBS admission ceiling-round regression
-- =============================================================================

/-- AK2-E-01: `Bandwidth.utilization` is ceiling-round for a non-divisible
ratio. For `budget = 1`, `period = 3`: `1 * 1000 / 3 = 333` (truncation)
but `(1 * 1000 + 3 - 1) / 3 = 334` (ceiling). Verifies admission slightly
over-estimates rather than under-estimates. -/
private def pm_ak2e_01_utilizationCeiling : IO Unit := do
  let bw : SeLe4n.Kernel.Bandwidth := { budget := 1, period := 3 }
  expect "utilization uses ceiling-round (expected 334, got truncation 333 would fail)"
    (bw.utilization == 334)

/-- AK2-E-02: Ceiling-round is an upper bound — for exact ratios it equals
the truncated result. For `budget = 1`, `period = 2`: `1 * 1000 / 2 = 500`
both truncation and ceiling (no rounding needed). -/
private def pm_ak2e_02_utilizationExact : IO Unit := do
  let bw : SeLe4n.Kernel.Bandwidth := { budget := 1, period := 2 }
  expect "utilization for exact ratio (500)" (bw.utilization == 500)

/-- AK2-E-03: Period 0 returns 0 (invalid bandwidth guard unchanged). -/
private def pm_ak2e_03_utilizationZeroPeriod : IO Unit := do
  let bw : SeLe4n.Kernel.Bandwidth := { budget := 5, period := 0 }
  expect "utilization is 0 when period is 0" (bw.utilization == 0)

-- =============================================================================
-- AK2-F: ReplenishQueue strict < comparator regression (FIFO within tie)
-- =============================================================================

/-- AK2-F-01: Two replenishments at the SAME eligibility time — the first
inserted appears BEFORE the second in the queue (FIFO). Prior to AK2-F
the `≤` comparator placed the later insertion first (LIFO). -/
private def pm_ak2f_01_replenishFifoOnTie : IO Unit := do
  let sc1 : SeLe4n.SchedContextId := ⟨101⟩
  let sc2 : SeLe4n.SchedContextId := ⟨102⟩
  let q0 : SeLe4n.Kernel.ReplenishQueue := SeLe4n.Kernel.ReplenishQueue.empty
  -- Insert sc1 first, then sc2 at the same eligibility time (100).
  let q1 := q0.insert sc1 100
  let q2 := q1.insert sc2 100
  match q2.entries with
  | (firstId, firstTime) :: (secondId, secondTime) :: [] =>
    expect "first entry eligibility time is 100" (firstTime == 100)
    expect "second entry eligibility time is 100" (secondTime == 100)
    expect "sc1 (first-inserted) is at position 0 (FIFO)"
      (firstId == sc1)
    expect "sc2 (second-inserted) is at position 1 (FIFO)"
      (secondId == sc2)
  | _ =>
      throw <| IO.userError
        s!"unexpected queue shape: {repr q2.entries}"

/-- AK2-F-02: Insertion maintains sorted order across distinct times. -/
private def pm_ak2f_02_replenishSortedAcrossTimes : IO Unit := do
  let sc1 : SeLe4n.SchedContextId := ⟨201⟩
  let sc2 : SeLe4n.SchedContextId := ⟨202⟩
  let sc3 : SeLe4n.SchedContextId := ⟨203⟩
  let q0 : SeLe4n.Kernel.ReplenishQueue := SeLe4n.Kernel.ReplenishQueue.empty
  -- Insert out of order: sc3@300, sc1@100, sc2@200.
  let q := ((q0.insert sc3 300).insert sc1 100).insert sc2 200
  let times := q.entries.map Prod.snd
  expect "queue sorted ascending by eligibility time"
    (times == [100, 200, 300])

-- ============================================================================
-- AK8-D (WS-AK / C-M05): Hardware priority ceiling (maxHardwarePriority = 255)
-- ============================================================================

/-- AK8-D-01: `setPriorityOp` rejects a priority above `maxHardwarePriority`
(256) with `.illegalAuthority`, even when the caller's MCP is set to a
value exceeding the hardware ceiling. -/
private def pm_ak8d_01_hardwarePriorityCeilingRejects : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  -- Caller MCP = 1000 (above hardware cap). Still must reject priority > 255.
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 1000))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨256⟩ with
  | .ok _ => throw <| IO.userError "priority 256 above hardware ceiling should be rejected"
  | .error e => expect "error is illegalAuthority" (e == .illegalAuthority)

/-- AK8-D-02: `setPriorityOp` accepts priority exactly `maxHardwarePriority`
(255) when the caller's MCP permits it. -/
private def pm_ak8d_02_maxHardwarePriorityAccepts : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 255))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨255⟩ with
  | .ok _ => expect "priority 255 (at ceiling) accepted" true
  | .error e =>
    throw <| IO.userError s!"priority 255 at hardware ceiling should succeed, got {repr e}"

/-- AK8-D-03: `setMCPriorityOp` also rejects MCP values above
`maxHardwarePriority`. -/
private def pm_ak8d_03_setMCPriorityHardwareCeilingRejects : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 1000))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 100)))
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨500⟩ with
  | .ok _ => throw <| IO.userError "MCP 500 above hardware ceiling should be rejected"
  | .error e => expect "error is illegalAuthority" (e == .illegalAuthority)

end SeLe4n.Testing.PriorityManagementSuite

open SeLe4n.Testing.PriorityManagementSuite in
def main : IO Unit := do
  IO.println "=== D2 Priority Management Test Suite ==="
  IO.println "--- D2-M1: setPriority success cases ---"
  pm001_setPriorityWithinMCP
  pm002_setPriorityAtMCP
  IO.println "--- D2-M2: setPriority error cases ---"
  pm003_setPriorityAboveMCP
  pm004_setPriorityMissingCaller
  pm005_setPriorityMissingTarget
  IO.println "--- D2-M3: setMCPriority tests ---"
  pm006_setMCPriorityWithinMCP
  pm007_setMCPriorityAboveMCP
  pm008_setMCPriorityCapsExisting
  IO.println "--- D2-M4: SchedContext binding ---"
  pm009_setPriorityBoundThread
  pm010_setPriorityUnboundThread
  pm010b_setMCPriorityCapsSchedContextBound
  IO.println "--- D2-M5: MCP transitivity ---"
  pm011_mcpTransitivity
  IO.println "--- D2-M6: Self-priority ---"
  pm012_selfSetPriority
  IO.println "--- D2-M7: Frozen operations ---"
  pm013_frozenSetPriority
  pm014_frozenSetPriorityAboveMCP
  pm015_frozenSetMCPriority
  IO.println "--- AK2-B: Option B priority propagation ---"
  pm_ak2b_01_bindPropagatesPriority
  pm_ak2b_02_configurePropagatesPriority
  pm_ak2b_03_configureRebucketsBoundThread
  IO.println "--- AK2-E: CBS admission ceiling-round ---"
  pm_ak2e_01_utilizationCeiling
  pm_ak2e_02_utilizationExact
  pm_ak2e_03_utilizationZeroPeriod
  IO.println "--- AK2-F: ReplenishQueue FIFO within tie ---"
  pm_ak2f_01_replenishFifoOnTie
  pm_ak2f_02_replenishSortedAcrossTimes
  IO.println "--- AK8-D: hardware priority ceiling ---"
  pm_ak8d_01_hardwarePriorityCeilingRejects
  pm_ak8d_02_maxHardwarePriorityAccepts
  pm_ak8d_03_setMCPriorityHardwareCeilingRejects
  IO.println "=== All D2 priority management tests passed (27 tests) ==="
