-- SPDX-License-Identifier: GPL-3.0-or-later
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
open SeLe4n.Kernel.Concurrency (bootCoreId)
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
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
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
private def emptyFrozenState : FrozenSystemState :=
  SeLe4n.Testing.emptyFrozenSystemState

private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  SeLe4n.Testing.frozenStateOf objs

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
  let st : SystemState := { stBase with scheduler := stBase.scheduler.setRunQueueOnCore bootCoreId ((stBase.scheduler.runQueueOnCore bootCoreId).insert targetTid ⟨50⟩) }
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 0 st with
  | .ok ((), st') =>
    -- After reconfigure, the RunQueue's cached priority for this thread
    -- must match the new priority (123), not the old (50).
    match (st'.scheduler.runQueueOnCore bootCoreId).threadPriority[targetTid]? with
    | some prio =>
      expect "RunQueue bucket migrated to new priority (50 -> 123)"
        (prio == ⟨123⟩)
    | none =>
        throw <| IO.userError
          "RunQueue missing thread after reconfigure (thread was present before)"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

-- =============================================================================
-- R5.G (DEEP-SCH-06): Domain propagation in schedContextConfigure
-- =============================================================================

/-- R5.G-01: `schedContextConfigure` propagates a new domain into the bound
    TCB.  Pre-R5 the `boundThreadDomainConsistent` invariant could drift on
    every reconfigure that changed `sc.domain` without touching `tcb.domain`. -/
private def pm_r5g_01_configurePropagatesDomain : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  -- Pre-state: sc.domain = 0, tcb.domain = 0 (consistent at bind time).
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
  -- Reconfigure to domain = 3 (priority unchanged at 50).
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 50 0 3 st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "tcb.domain propagated from new sc.domain (0 -> 3)"
        (tcb.domain == ⟨3⟩)
    | _ => throw <| IO.userError "bound TCB not found"
    match st'.objects[scObjId]? with
    | some (.schedContext sc') =>
      expect "sc.domain updated to 3" (sc'.domain == ⟨3⟩)
    | _ => throw <| IO.userError "SC not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

/-- R5.G-02: When the new domain matches the existing TCB domain, the
    propagation block is a no-op (state otherwise unchanged). -/
private def pm_r5g_02_configureDomainNoopWhenEqual : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  -- Pre-state: both at domain = 5.
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨5⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let st := mkState [
    (targetTid.toObjId, .tcb { mkTcb 42 (prio := 50) (mcp := 200)
      (binding := .bound scId) with domain := ⟨5⟩ }),
    (scObjId, .schedContext sc)
  ]
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 50 0 5 st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "tcb.domain preserved at 5 (no-op propagation)"
        (tcb.domain == ⟨5⟩)
    | _ => throw <| IO.userError "bound TCB not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

/-- R5.G-03: Joint priority+domain reconfigure propagates both fields. -/
private def pm_r5g_03_configurePropagatesBothFields : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
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
  -- Reconfigure to priority = 123, domain = 7.
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 7 st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "tcb.priority updated to 123" (tcb.priority == ⟨123⟩)
      expect "tcb.domain updated to 7" (tcb.domain == ⟨7⟩)
    | _ => throw <| IO.userError "bound TCB not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

/-- R5.G-04: substantive invariant preservation — after
    `schedContextConfigure` succeeds on a state where the bound TCB and
    SC start with matching domains, the
    `boundThreadDomainConsistent` invariant continues to hold (the
    domain propagation block ensures the SC and TCB domains move in
    lockstep).

    This is the runtime witness for
    `schedContextConfigure_preserves_boundThreadDomainConsistent`. -/
private def pm_r5g_04_substantive_invariant_preservation : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let initTcb := { mkTcb 42 (prio := 50) (mcp := 200) (binding := .bound scId)
                   with domain := ⟨0⟩ }
  let st := mkState [
    (targetTid.toObjId, .tcb initTcb),
    (scObjId, .schedContext sc)
  ]
  -- Pre-state: tcb.domain = 0 = sc.domain (consistent).
  -- Reconfigure to domain = 7.
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 50 0 7 st with
  | .ok ((), st') =>
    -- Post-state: both should have domain = 7.
    match st'.objects[targetTid.toObjId]?, st'.objects[scObjId]? with
    | some (.tcb tcb'), some (.schedContext sc') =>
      -- boundThreadDomainConsistent at (targetTid, scId) requires tcb'.domain = sc'.domain.
      expect "tcb'.domain = sc'.domain (invariant preserved)"
        (tcb'.domain == sc'.domain)
      expect "tcb'.domain = ⟨7⟩ (post-propagation)" (tcb'.domain == ⟨7⟩)
      expect "sc'.domain = ⟨7⟩" (sc'.domain == ⟨7⟩)
    | _, _ => throw <| IO.userError "bound TCB or SC not found"
  | .error e => throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

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

-- ============================================================================
-- WS-OD (v0.35.3): a donated scheduling context does not carry the donor's
-- priority
-- ============================================================================
--
-- The finding: `updatePrioritySource` classified `.bound scId` and
-- `.donated scId owner` alike, so `.tcbSetPriority` / `.tcbSetMCPriority` on a
-- thread *holding* a donated context wrote the **donor's**
-- `SchedContext.priority`.  The syscall is authorised by a TCB-write right over
-- the target and the caller's MCP ceiling, neither of which says anything about
-- the donor, so a principal with authority over a passive server could retune a
-- client's scheduling parameter — and the client received it when the donation
-- returned.
--
-- Every check below is written so it FAILS on the pre-fix kernel and cannot be
-- satisfied by the write merely disappearing: each asserts *which* object moved
-- and *which* did not, and `pm_od_06` is the `.bound` control that the write
-- still happens where it should.

/-- The donee's own base priority, distinct from the donor's band so the two
readings are distinguishable. -/
private def odDoneePriority : Nat := 30

/-- The donor's band, carried by the reservation. -/
private def odDonorPriority : Nat := 70

/-- The donor's domain, carried by the reservation and deliberately **not** the
donee's (`mkTcb` builds every thread in domain `0`), so every assertion about
which domain a donee is reported in discriminates rather than passing by
coincidence. -/
private def odDonorDomain : Nat := 3

/-- The donated reservation: the donor's priority, deadline and domain, held by
the donee (`boundThread`), exactly as `donateSchedContext` leaves it — a
donation crosses domains freely, unlike `schedContextBind`, which refuses a
cross-domain bind. -/
private def odDonatedSc (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    : SeLe4n.Kernel.SchedContext :=
  { scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨odDonorPriority⟩, deadline := ⟨500⟩, domain := ⟨odDonorDomain⟩,
    budgetRemaining := ⟨100⟩, boundThread := some holder }

/-- A caller (1) with authority, a passive server (2) holding a donated context,
and the donor client (3) whose reservation it is. -/
private def odDonationState (scId : SeLe4n.SchedContextId) : SystemState :=
  mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := odDoneePriority)
                  (binding := .donated scId ⟨3⟩))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := odDonorPriority))),
    (scId.toObjId, .schedContext (odDonatedSc scId ⟨2⟩))
  ]

/-- WS-OD-PRIO-01: the classifier.  A `.bound` thread **owns** its reservation;
an `.unbound` or `.donated` one owns none, so its thread-owned parameters (base
priority and domain) stay on its own TCB.  This is the single decision every
reader and writer of those parameters is built on, so it is checked directly
rather than only through its consequences. -/
private def pm_od_01_prioritySourceClassifier : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  expect "the classifier: a `.bound` thread owns its reservation"
    ((SchedContextBinding.bound scId).ownScId? == some scId)
  expect "the classifier: an `.unbound` thread owns none"
    ((SchedContextBinding.unbound).ownScId? == none)
  expect "the classifier: a `.donated` thread owns none — it runs on a lent one"
    ((SchedContextBinding.donated scId ⟨3⟩).ownScId? == none)
  -- ...while `scId?`, the reservation a thread RUNS ON, does name it: the two
  -- questions are distinct, which is the whole of the donation semantics.
  expect "the budget question still names the donor's reservation"
    ((SchedContextBinding.donated scId ⟨3⟩).scId? == some scId)
  -- ...and ownership never names a context the thread is not running on.
  expect "the classifier narrows `scId?` rather than resolving independently"
    (match (SchedContextBinding.bound scId).ownScId? with
     | some s => (SchedContextBinding.bound scId).scId? == some s
     | none   => false)

/-- WS-OD-PRIO-02: every priority READER prefers the donee's own band, while the
deadline and domain still come from the donated reservation.  A check on the
priority alone would be satisfied by a kernel that had dropped the reservation
entirely, so the deadline and domain are asserted in the same breath. -/
private def pm_od_02_donatedReadsPreferTheTcb : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := odDonationState scId
  match st.getTcb? ⟨2⟩ with
  | none => throw <| IO.userError "donee TCB not found"
  | some donee =>
    expect "getCurrentPriority reads the donee's own 30"
      (getCurrentPriority st donee == ⟨odDoneePriority⟩)
    expect "getCurrentPriorityChecked cannot fail on a donee, and reads 30"
      (match getCurrentPriorityChecked st donee with
       | .ok p => p == ⟨odDoneePriority⟩
       | .error _ => false)
    expect "resolveEffectivePrioDeadline: the donee's 30 on the donor's deadline 500"
      (decide (resolveEffectivePrioDeadline st donee = (⟨odDoneePriority⟩, ⟨500⟩)))
    -- The donor's DEADLINE (reservation-owned) with the donee's own priority
    -- and domain (thread-owned).  The reservation sits in domain 3 and the
    -- donee in 0, so the third component discriminates.
    expect "effectiveSchedParams: the donee's own 30 and domain 0, the donor's deadline 500"
      (decide (effectiveSchedParams st donee = (⟨odDoneePriority⟩, ⟨500⟩, ⟨0⟩)))
    expect "NEGATIVE (the defect): the donee is not reported in the donor's domain 3"
      (!((effectiveSchedParams st donee).2.2 == ⟨odDonorDomain⟩))
    expect "effectiveBucketPriority is the TCB-only reading the run queue records"
      (effectiveBucketPriority st donee == effectiveRunQueuePriority donee)
    -- NEGATIVE (the defect): none of the readings is the donor's band.
    expect "NEGATIVE (the defect): no reader returns the donor's 70"
      (!(getCurrentPriority st donee == ⟨odDonorPriority⟩) &&
       !((resolveEffectivePrioDeadline st donee).1 == ⟨odDonorPriority⟩) &&
       !(effectiveBucketPriority st donee == ⟨odDonorPriority⟩))

/-- WS-OD-PRIO-03: **the security regression.**  `setPriorityOp` on the donee
writes the donee's TCB and leaves the donor's reservation — and the donor's own
TCB — untouched.  Pre-fix this wrote `SchedContext.priority := 80`. -/
private def pm_od_03_setPriorityOnDoneeSparesTheDonor : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := odDonationState scId
  match setPriorityOp st ⟨⟨1⟩, by decide⟩ ⟨⟨2⟩, by decide⟩ ⟨80⟩ with
  | .error e => throw <| IO.userError s!"setPriority on a donee should succeed, got {repr e}"
  | .ok st' =>
    match st'.objects[(⟨2⟩ : SeLe4n.ThreadId).toObjId]? with
    | some (.tcb donee') =>
      expect "the donee's OWN priority is updated to 80" (donee'.priority == ⟨80⟩)
      expect "...and the donation binding is untouched"
        (decide (donee'.schedContextBinding = .donated scId ⟨3⟩))
    | _ => throw <| IO.userError "donee TCB not found after setPriority"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "THE FIX: the donor's reservation keeps its own priority 70"
        (sc'.priority == ⟨odDonorPriority⟩)
      let scRef := odDonatedSc scId ⟨2⟩
      expect "...and the reservation is otherwise untouched"
        (sc'.budget == scRef.budget && sc'.period == scRef.period &&
         sc'.deadline == scRef.deadline && sc'.domain == scRef.domain &&
         sc'.budgetRemaining == scRef.budgetRemaining &&
         sc'.boundThread == scRef.boundThread)
    | _ => throw <| IO.userError "donated SchedContext not found after setPriority"
    match st'.objects[(⟨3⟩ : SeLe4n.ThreadId).toObjId]? with
    | some (.tcb donor') =>
      expect "the donor thread's own priority is untouched"
        (donor'.priority == ⟨odDonorPriority⟩)
    | _ => throw <| IO.userError "donor TCB not found after setPriority"

/-- WS-OD-PRIO-04: the same for the MCP-capping path, which reaches
`updatePrioritySource` through `setMCPriorityOp`'s cap branch rather than
directly.  Two syscall arms, one write helper — so the fix has to cover both,
and this is the check that it does. -/
private def pm_od_04_setMCPriorityCapOnDoneeSparesTheDonor : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := odDonationState scId
  -- The donee's current priority is 30; capping MCP to 20 must cap it.
  match setMCPriorityOp st ⟨⟨1⟩, by decide⟩ ⟨⟨2⟩, by decide⟩ ⟨20⟩ with
  | .error e => throw <| IO.userError s!"setMCPriority on a donee should succeed, got {repr e}"
  | .ok st' =>
    match st'.objects[(⟨2⟩ : SeLe4n.ThreadId).toObjId]? with
    | some (.tcb donee') =>
      expect "the donee's MCP ceiling is lowered to 20"
        (donee'.maxControlledPriority == ⟨20⟩)
      expect "...and its OWN priority is capped to 20" (donee'.priority == ⟨20⟩)
    | _ => throw <| IO.userError "donee TCB not found after setMCPriority"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "THE FIX: the MCP cap does not reach the donor's reservation"
        (sc'.priority == ⟨odDonorPriority⟩)
    | _ => throw <| IO.userError "donated SchedContext not found after setMCPriority"

/-- WS-OD-PRIO-05: the frozen mirror answers the same question the same way.
`frozenSetPriority` is `updatePrioritySource`'s second implementation, and one
question answered in two places is how this class of defect survives a fix. -/
private def pm_od_05_frozenSetPriorityOnDoneeSparesTheDonor : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := odDoneePriority)
                  (binding := .donated scId ⟨3⟩))),
    (scId.toObjId, .schedContext (odDonatedSc scId ⟨2⟩))
  ]
  match frozenSetPriority ⟨1⟩ ⟨2⟩ ⟨80⟩ fst with
  | .error e => throw <| IO.userError s!"frozen setPriority on a donee should succeed, got {repr e}"
  | .ok ((), fst') =>
    match fst'.objects.get? (⟨2⟩ : SeLe4n.ThreadId).toObjId with
    | some (.tcb donee') =>
      expect "frozen: the donee's OWN priority is updated to 80"
        (donee'.priority == ⟨80⟩)
    | _ => throw <| IO.userError "frozen donee TCB not found"
    match fst'.objects.get? scId.toObjId with
    | some (.schedContext sc') =>
      expect "frozen: the donor's reservation keeps its own priority 70"
        (sc'.priority == ⟨odDonorPriority⟩)
    | _ => throw <| IO.userError "frozen donated SchedContext not found"

/-- WS-OD-PRIO-06: **the control.**  On a `.bound` thread the write still lands
in the reservation and *not* in the TCB, so none of the checks above can be
satisfied by the priority write having simply been removed.  This is the
relation-preserving direction: the token (`updatePrioritySource` writing a
SchedContext) is still there; only which binding reaches it has changed. -/
private def pm_od_06_boundControlStillWritesTheReservation : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { odDonatedSc scId ⟨2⟩ with priority := ⟨odDoneePriority⟩ }
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := odDoneePriority) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match setPriorityOp st ⟨⟨1⟩, by decide⟩ ⟨⟨2⟩, by decide⟩ ⟨80⟩ with
  | .error e => throw <| IO.userError s!"setPriority on a bound thread should succeed, got {repr e}"
  | .ok st' =>
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "control: a BOUND thread's reservation is still written to 80"
        (sc'.priority == ⟨80⟩)
    | _ => throw <| IO.userError "bound SchedContext not found after setPriority"
    match st'.objects[(⟨2⟩ : SeLe4n.ThreadId).toObjId]? with
    | some (.tcb tcb') =>
      expect "control: a BOUND thread's TCB priority is NOT the write target"
        (tcb'.priority == ⟨odDoneePriority⟩)
    | _ => throw <| IO.userError "bound TCB not found after setPriority"
  -- ...and the reader agrees with the writer on that arm too.
  match st.getTcb? ⟨2⟩ with
  | some tcb =>
    expect "control: a BOUND thread reads its reservation's priority"
      (getCurrentPriority st tcb == ⟨odDoneePriority⟩)
  | none => throw <| IO.userError "bound TCB not found"

/-- WS-OD-PRIO-07: **the mirror crossing.**  `schedContextConfigure` propagates
**both** thread-owned parameters — base priority and domain — into
`sc.boundThread`'s TCB, and after a donation `boundThread` is the **donee**.  So
a caller holding a capability on the *client's* reservation could rewrite the
*server's* own base priority and migrate its scheduling domain, permanently:
the donee keeps both fields after the donation returns.  Each propagation exists
only to maintain a `.bound`-only invariant (`boundThreadPriorityConsistent`,
`boundThreadDomainConsistent`), so both are gated on the bound thread **owning**
this reservation (`schedContextConfigurePropagates`).  The reservation itself is
still reconfigured — the caller does hold its capability — which is what
distinguishes the gate from the operation failing, and its budget and period
still reach the donee, which reads them. -/
private def pm_od_07_configureOnDonatedReservationSparesTheDonee : IO Unit := do
  let doneeTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some doneeTid
  }
  let st := mkState [
    (doneeTid.toObjId, .tcb (mkTcb 42 (prio := odDoneePriority) (mcp := 200)
      (binding := .donated scId ⟨7⟩))),
    (scObjId, .schedContext sc)
  ]
  -- Reconfigure to priority 123 in domain 5 — both thread-owned parameters,
  -- both different from the donee's own.
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 5 st with
  | .error e => throw <| IO.userError s!"schedContextConfigure failed: {repr e}"
  | .ok ((), st') =>
    match st'.objects[scObjId]? with
    | some (.schedContext sc') =>
      expect "the reservation IS reconfigured (the caller holds its capability)"
        (sc'.priority == ⟨123⟩ && sc'.domain == ⟨5⟩)
      expect "...including its reservation-owned parameters, which a donee does read"
        (sc'.budget == ⟨100⟩ && sc'.period == ⟨200⟩)
    | _ => throw <| IO.userError "SC not found after configure"
    match st'.objects[doneeTid.toObjId]? with
    | some (.tcb donee') =>
      expect "THE FIX: the donee's own base priority is NOT rewritten"
        (donee'.priority == ⟨odDoneePriority⟩)
      expect "THE FIX: nor is its domain — a client cannot migrate a server's partition"
        (donee'.domain == ⟨0⟩)
    | _ => throw <| IO.userError "donee TCB not found after configure"

/-- WS-OD-PRIO-08: the control for `pm_od_07`.  On a `.bound` thread the
propagation still fires, so the gate cannot be satisfied by the propagation
having been removed.  (`pm_ak2b_02` asserts the same equality; this restates it
beside the negative it controls, where a reader can see the pair.) -/
private def pm_od_08_configureBoundControlStillPropagates : IO Unit := do
  let boundTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some boundTid
  }
  let st := mkState [
    (boundTid.toObjId, .tcb (mkTcb 42 (prio := 50) (mcp := 200)
      (binding := .bound scId))),
    (scObjId, .schedContext sc)
  ]
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 5 st with
  | .error e => throw <| IO.userError s!"schedContextConfigure failed: {repr e}"
  | .ok ((), st') =>
    match st'.objects[boundTid.toObjId]? with
    | some (.tcb tcb') =>
      expect "control: a BOUND thread's priority IS propagated (50 -> 123)"
        (tcb'.priority == ⟨123⟩)
      expect "control: ...and so is its domain (0 -> 5), so neither half is dead"
        (tcb'.domain == ⟨5⟩)
    | _ => throw <| IO.userError "bound TCB not found after configure"

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
  IO.println "--- R5.G: schedContextConfigure domain propagation ---"
  pm_r5g_01_configurePropagatesDomain
  pm_r5g_02_configureDomainNoopWhenEqual
  pm_r5g_03_configurePropagatesBothFields
  pm_r5g_04_substantive_invariant_preservation
  IO.println "--- WS-OD (v0.35.3): a donee runs at its OWN priority ---"
  pm_od_01_prioritySourceClassifier
  pm_od_02_donatedReadsPreferTheTcb
  pm_od_03_setPriorityOnDoneeSparesTheDonor
  pm_od_04_setMCPriorityCapOnDoneeSparesTheDonor
  pm_od_05_frozenSetPriorityOnDoneeSparesTheDonor
  pm_od_06_boundControlStillWritesTheReservation
  pm_od_07_configureOnDonatedReservationSparesTheDonee
  pm_od_08_configureBoundControlStillPropagates
  IO.println "=== All D2 priority management tests passed (38 tests) ==="
