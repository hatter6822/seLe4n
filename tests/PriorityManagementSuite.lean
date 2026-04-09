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
  match setPriorityOp st callerTid targetTid ⟨80⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-001 target priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "PM-001 target TCB not found"
  | .error e => throw <| IO.userError s!"PM-001 setPriority should succeed, got {repr e}"

/-- PM-002: setPriority at exactly MCP boundary succeeds. -/
private def pm002_setPriorityAtMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st callerTid targetTid ⟨100⟩ with
  | .ok _ => expect "PM-002 setPriority at MCP boundary succeeds" true
  | .error e => throw <| IO.userError s!"PM-002 setPriority at MCP should succeed, got {repr e}"

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
  match setPriorityOp st callerTid targetTid ⟨101⟩ with
  | .ok _ => throw <| IO.userError "PM-003 setPriority above MCP should fail"
  | .error e =>
    expect "PM-003 error is illegalAuthority" (e == .illegalAuthority)

/-- PM-004: setPriority with missing caller returns invalidArgument. -/
private def pm004_setPriorityMissingCaller : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨99⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [(⟨2⟩, .tcb (mkTcb 2 (prio := 30)))]
  match setPriorityOp st callerTid targetTid ⟨50⟩ with
  | .ok _ => throw <| IO.userError "PM-004 missing caller should fail"
  | .error e =>
    expect "PM-004 error is invalidArgument" (e == .invalidArgument)

/-- PM-005: setPriority with missing target returns invalidArgument. -/
private def pm005_setPriorityMissingTarget : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100)))]
  match setPriorityOp st callerTid targetTid ⟨50⟩ with
  | .ok _ => throw <| IO.userError "PM-005 missing target should fail"
  | .error e =>
    expect "PM-005 error is invalidArgument" (e == .invalidArgument)

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
  match setMCPriorityOp st callerTid targetTid ⟨100⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-006 target MCP updated to 100" (tcb.maxControlledPriority == ⟨100⟩)
    | _ => throw <| IO.userError "PM-006 target TCB not found"
  | .error e => throw <| IO.userError s!"PM-006 setMCPriority should succeed, got {repr e}"

/-- PM-007: setMCPriority above caller's MCP returns illegalAuthority. -/
private def pm007_setMCPriorityAboveMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 150)))
  ]
  match setMCPriorityOp st callerTid targetTid ⟨101⟩ with
  | .ok _ => throw <| IO.userError "PM-007 setMCPriority above MCP should fail"
  | .error e =>
    expect "PM-007 error is illegalAuthority" (e == .illegalAuthority)

/-- PM-008: setMCPriority caps existing priority when new MCP < current priority. -/
private def pm008_setMCPriorityCapsExisting : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  -- Target has priority 80, we set MCP to 50 — priority should be capped to 50
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80) (mcp := 150)))
  ]
  match setMCPriorityOp st callerTid targetTid ⟨50⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-008 target MCP set to 50" (tcb.maxControlledPriority == ⟨50⟩)
      -- Priority should be capped: unbound thread priority updated in TCB
      expect "PM-008 target priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "PM-008 target TCB not found"
  | .error e => throw <| IO.userError s!"PM-008 setMCPriority should succeed, got {repr e}"

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
  match setPriorityOp st callerTid targetTid ⟨80⟩ with
  | .ok st' =>
    -- SchedContext priority should be updated
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "PM-009 SchedContext priority updated to 80" (sc'.priority == ⟨80⟩)
    | _ => throw <| IO.userError "PM-009 SchedContext not found"
  | .error e => throw <| IO.userError s!"PM-009 setPriority bound should succeed, got {repr e}"

/-- PM-010: setPriority on unbound thread updates TCB priority directly. -/
private def pm010_setPriorityUnboundThread : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match setPriorityOp st callerTid targetTid ⟨60⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-010 TCB priority updated to 60" (tcb.priority == ⟨60⟩)
    | _ => throw <| IO.userError "PM-010 target TCB not found"
  | .error e => throw <| IO.userError s!"PM-010 setPriority unbound should succeed, got {repr e}"

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
  match setMCPriorityOp st callerTid targetTid ⟨50⟩ with
  | .ok st' =>
    -- Verify MCP was updated on TCB
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-010b MCP updated to 50" (tcb.maxControlledPriority == ⟨50⟩)
    | _ => throw <| IO.userError "PM-010b target TCB not found"
    -- Verify SchedContext priority was capped to 50
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "PM-010b SchedContext priority capped to 50" (sc'.priority == ⟨50⟩)
    | _ => throw <| IO.userError "PM-010b SchedContext not found after MCP cap"
  | .error e => throw <| IO.userError s!"PM-010b setMCPriority bound cap should succeed, got {repr e}"

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
  match setMCPriorityOp st tidA tidB ⟨80⟩ with
  | .ok st' =>
    -- Step 2: B tries to set C's priority to 90 (above B's new MCP of 80) — should fail
    match setPriorityOp st' tidB tidC ⟨90⟩ with
    | .ok _ => throw <| IO.userError "PM-011 B should not set priority above its MCP"
    | .error e =>
      expect "PM-011 transitive MCP blocks escalation" (e == .illegalAuthority)
  | .error e => throw <| IO.userError s!"PM-011 step 1 failed: {repr e}"

-- ============================================================================
-- D2-M6: Self-priority tests
-- ============================================================================

/-- PM-012: Thread sets its own priority within its MCP. -/
private def pm012_selfSetPriority : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100)))
  ]
  match setPriorityOp st tid tid ⟨80⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "PM-012 self priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "PM-012 TCB not found"
  | .error e => throw <| IO.userError s!"PM-012 self setPriority should succeed, got {repr e}"

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
      expect "PM-013 frozen priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "PM-013 frozen TCB not found"
  | .error e => throw <| IO.userError s!"PM-013 frozen setPriority should succeed, got {repr e}"

/-- PM-014: Frozen setPriority above MCP fails. -/
private def pm014_frozenSetPriorityAboveMCP : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  match frozenSetPriority callerTid targetTid ⟨101⟩ fst with
  | .ok _ => throw <| IO.userError "PM-014 frozen setPriority above MCP should fail"
  | .error e =>
    expect "PM-014 frozen error is illegalAuthority" (e == .illegalAuthority)

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
      expect "PM-015 frozen MCP set to 50" (tcb.maxControlledPriority == ⟨50⟩)
      expect "PM-015 frozen priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "PM-015 frozen TCB not found"
  | .error e => throw <| IO.userError s!"PM-015 frozen setMCPriority should succeed, got {repr e}"

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
  IO.println "=== All D2 priority management tests passed (16 tests) ==="
