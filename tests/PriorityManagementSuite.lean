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
import SeLe4n.Testing.BootCoreOps

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId
  LockKey)
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
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
    threadState := state, maxControlledPriority := ⟨mcp⟩,
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (binding), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode (binding) }

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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨80⟩ with
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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨100⟩ with
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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨101⟩ with
  | .ok _ => throw <| IO.userError "setPriority above MCP should fail"
  | .error e =>
    expect "error is illegalAuthority" (e == .illegalAuthority)

/-- PM-004: setPriority with missing caller returns invalidArgument. -/
private def pm004_setPriorityMissingCaller : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨99⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [(⟨2⟩, .tcb (mkTcb 2 (prio := 30)))]
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok _ => throw <| IO.userError "missing caller should fail"
  | .error e =>
    expect "error is invalidArgument" (e == (.invalidArgument 0))

/-- PM-005: setPriority with missing target returns invalidArgument. -/
private def pm005_setPriorityMissingTarget : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 100)))]
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok _ => throw <| IO.userError "missing target should fail"
  | .error e =>
    expect "error is invalidArgument" (e == (.invalidArgument 0))

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
  match bootSetMCPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨100⟩ with
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
  match bootSetMCPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨101⟩ with
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
  match bootSetMCPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
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

/-- PM-009: setPriority on a SchedContext-bound thread writes the thread's own
priority and leaves its context untouched (WS-SX SX6.4: seL4-MCS's context
carries no priority; `invokeTCB_ThreadControlSched` writes `tcbPriority`). -/
private def pm009_setPriorityBoundThread : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    budgetRemaining := ⟨100⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid)
  }
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) => expect "bound TCB priority updated to 80" (tcb.priority == ⟨80⟩)
    | _ => throw <| IO.userError "target TCB not found"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') => expect "SchedContext untouched" (sc' == sc)
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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨60⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "TCB priority updated to 60" (tcb.priority == ⟨60⟩)
    | _ => throw <| IO.userError "target TCB not found"
  | .error e => throw <| IO.userError s!"setPriority unbound should succeed, got {repr e}"

/-- PM-010b: setMCPriority caps priority on a SchedContext-bound thread: the
cap writes the thread's own base priority and leaves its context untouched. -/
private def pm010b_setMCPriorityCapsSchedContextBound : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    budgetRemaining := ⟨100⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid)
  }
  -- Target runs at 80; we set MCP to 50, so the cap must fire.
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80) (mcp := 150) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match bootSetMCPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "MCP updated to 50" (tcb.maxControlledPriority == ⟨50⟩)
      expect "TCB base priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "target TCB not found"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') => expect "SchedContext untouched by the cap" (sc' == sc)
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
  match bootSetMCPriority st ⟨tidA, by decide⟩ ⟨tidB, by decide⟩ ⟨80⟩ with
  | .ok st' =>
    -- Step 2: B tries to set C's priority to 90 (above B's new MCP of 80) — should fail
    match bootSetPriority st' ⟨tidB, by decide⟩ ⟨tidC, by decide⟩ ⟨90⟩ with
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
  match bootSetPriority st ⟨tid, by decide⟩ ⟨tid, by decide⟩ ⟨80⟩ with
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
-- AK2-B's propagation, retired by WS-SX SX6.4: bind and configure write no
-- thread priority or domain
-- =============================================================================

/-- AK2-B-01 (WS-SX SX6.4): `schedContextBind` writes the two binding links
alone, as seL4-MCS's `schedContext_bindTCB` does: the thread keeps its own
priority and domain, and a thread in a domain other than 0 binds (seL4 checks
no domain at bind). -/
private def pm_bindKeepsThreadPriorityAndDomain : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    budgetRemaining := ⟨100⟩, boundThreadCode := 0
  }
  let st := mkState [
    (targetTid.toObjId, .tcb { mkTcb 42 (prio := 10) (mcp := 200) with domain := ⟨2⟩ }),
    (scObjId, .schedContext sc)
  ]
  match SeLe4n.Kernel.SchedContextOps.schedContextBind ⟨scObjId, by decide⟩ ⟨targetTid, by decide⟩ st with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "bind keeps tcb.priority (10)" (tcb.priority == ⟨10⟩)
      expect "bind keeps tcb.domain (2)" (tcb.domain == ⟨2⟩)
      expect "bind writes the binding" (tcb.schedContextBinding == .bound scId)
    | _ => throw <| IO.userError "bound TCB not found"
  | .error e =>
    throw <| IO.userError s!"schedContextBind failed: {repr e}"

/-- AK2-B-02 (WS-SX SX6.4): `schedContextConfigure` on an already-bound
SchedContext writes the context alone: the badge word is stored, bit 0 of the
flags word is the sporadic flag, and the bound thread's priority and domain
are untouched (seL4-MCS's `invokeSchedControl_ConfigureFlags`). -/
private def pm_configureWritesContextAlone : IO Unit := do
  let targetTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    budgetRemaining := ⟨100⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid)
  }
  let st := mkState [
    (targetTid.toObjId, .tcb { mkTcb 42 (prio := 50) (mcp := 200)
      (binding := .bound scId) with domain := ⟨3⟩ }),
    (scObjId, .schedContext sc)
  ]
  let configure (flags : UInt64) :=
    SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 0
      0xFEEDFACECAFEBEEF flags st
  match configure 1 with
  | .ok ((), st') =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "configure keeps the bound tcb.priority (50)" (tcb.priority == ⟨50⟩)
      expect "configure keeps the bound tcb.domain (3)" (tcb.domain == ⟨3⟩)
    | _ => throw <| IO.userError "bound TCB not found"
    match st'.objects[scObjId]? with
    | some (.schedContext sc') =>
      expect "badge stored verbatim" (sc'.badge == 0xFEEDFACECAFEBEEF)
      expect "flags bit 0 sets sporadic" (sc'.sporadic == true)
    | _ => throw <| IO.userError "SC not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"
  match configure 0xFFFFFFFFFFFFFFFE with
  | .ok ((), st') =>
    match st'.objects[scObjId]? with
    | some (.schedContext sc') =>
      expect "flags bits above bit 0 are ignored" (sc'.sporadic == false)
    | _ => throw <| IO.userError "SC not found"
  | .error e =>
    throw <| IO.userError s!"schedContextConfigure failed: {repr e}"

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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨256⟩ with
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
  match bootSetPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨255⟩ with
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
  match bootSetMCPriority st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨500⟩ with
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
-- and *which* did not.  WS-SX SX6.4 closed the class structurally: a context
-- carries no priority, so the checks now assert the donated context is left
-- exactly as it was.

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
    budgetRemaining := ⟨100⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some holder) }

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

/-- WS-OD: the classifier.  A `.bound` thread **owns** its reservation;
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

/-- WS-OD: every priority READER prefers the donee's own band, while the
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
      (effectiveBucketPriority st donee == donee.boostedPriority)
    -- NEGATIVE (the defect): none of the readings is the donor's band.
    expect "NEGATIVE (the defect): no reader returns the donor's 70"
      (!(getCurrentPriority st donee == ⟨odDonorPriority⟩) &&
       !((resolveEffectivePrioDeadline st donee).1 == ⟨odDonorPriority⟩) &&
       !(effectiveBucketPriority st donee == ⟨odDonorPriority⟩))

/-- WS-OD: **the security regression.**  `setPriorityOp` on the donee
writes the donee's TCB and leaves the donor's reservation — and the donor's own
TCB — untouched.  Pre-fix this wrote the reservation's priority (a field WS-SX
SX6.4 removed: a context carries no priority). -/
private def pm_od_03_setPriorityOnDoneeSparesTheDonor : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := odDonationState scId
  match bootSetPriority st ⟨⟨1⟩, by decide⟩ ⟨⟨2⟩, by decide⟩ ⟨80⟩ with
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
      expect "THE FIX: the donor's reservation is untouched"
        (sc' == odDonatedSc scId ⟨2⟩)
    | _ => throw <| IO.userError "donated SchedContext not found after setPriority"
    match st'.objects[(⟨3⟩ : SeLe4n.ThreadId).toObjId]? with
    | some (.tcb donor') =>
      expect "the donor thread's own priority is untouched"
        (donor'.priority == ⟨odDonorPriority⟩)
    | _ => throw <| IO.userError "donor TCB not found after setPriority"

/-- WS-OD: the same for the MCP-capping path, which reaches
`updatePrioritySource` through `setMCPriorityOp`'s cap branch rather than
directly.  Two syscall arms, one write helper — so the fix has to cover both,
and this is the check that it does. -/
private def pm_od_04_setMCPriorityCapOnDoneeSparesTheDonor : IO Unit := do
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := odDonationState scId
  -- The donee's current priority is 30; capping MCP to 20 must cap it.
  match bootSetMCPriority st ⟨⟨1⟩, by decide⟩ ⟨⟨2⟩, by decide⟩ ⟨20⟩ with
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
        (sc' == odDonatedSc scId ⟨2⟩)
    | _ => throw <| IO.userError "donated SchedContext not found after setMCPriority"

/-- WS-OD: the frozen mirror answers the same question the same way.
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
      expect "frozen: the donor's reservation is untouched"
        (sc' == odDonatedSc scId ⟨2⟩)
    | _ => throw <| IO.userError "frozen donated SchedContext not found"

/-- **`v0.35.99`: the frozen surface writes the same home as the live one, and
the differential is what says so.**  `v0.35.98` fixed the live writer and left `frozenSetPriority`
writing the reservation alone, so the *same* operation produced divergent states
— reported on PR #897.  This drives the live and frozen demotes on corresponding
fixtures and compares both fields, which is the only assertion that could have
caught it: each surface's own per-object checks passed throughout. -/
private def pm_frozenBasePriorityAgreesWithTheLiveWrite : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, budgetRemaining := ⟨100⟩,
      boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid) }
  let liveSt := mkState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  match bootSetPriority liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ with
  | .error e => throw <| IO.userError s!"live setPriority should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetPriority callerTid targetTid ⟨10⟩ frozenSt with
    | .error e => throw <| IO.userError s!"frozen setPriority should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      let liveTcbPrio := (liveAfter.getTcb? targetTid).map (·.priority)
      let frozenTcbPrio := (frozenLookupTcb frozenAfter targetTid).map (·.priority)
      expect "live demote writes the thread" (liveTcbPrio == some ⟨10⟩)
      expect "frozen demote writes the thread — the half that once diverged"
        (frozenTcbPrio == some ⟨10⟩)
      expect "...and neither surface writes the context"
        ((liveAfter.getSchedContext? scId) == some sc &&
          (frozenAfter.getSchedContext? scId) == some sc)

/-- **`v0.35.101`: and the write RE-BUCKETS, which neither witness above could
see.**  Reported on PR #897.

`v0.35.99` closed the field half and left the queue: the frozen run queue is
keyed by `TCB.boostedPriority` (`priority.raisedBy pipBoost`), so a base write
moves a queued thread's bucket exactly as a boost write does, and
`frozenWriteBasePriority` wrote the field and stopped.  `frozenChooseThread` folds
`byPriority`, so the frozen kernel went on ordering the thread by the band the
write had just removed -- and a later `frozenEnsureRunnable`, which appends when
the thread is absent from the bucket for its *new* priority, would have left it in
**two**.  The live `setPriorityOp` composes `migrateRunQueueBucket` onto
`updatePrioritySource` for precisely this reason.

**Why the two witnesses above are structurally blind to it, and the fixture defect
that made them so.**  `mkState`'s `runnable` defaults to `[]` while
`frozenStateOf` queues **every** `.ready` TCB at its own priority -- so those
fixtures do not correspond: the frozen side queues threads the live side does not,
and the live `migrateRunQueueBucket` is therefore the identity on them.  Comparing
buckets there would have compared a populated frozen queue against an empty live
one and failed for the wrong reason.  This one passes `runnable := [targetTid]` so
both surfaces queue the target, and the control below asserts that correspondence
before anything is measured -- because a bucket comparison whose two sides start
out different measures the fixture. -/
private def pm_frozenBasePriorityRebucketsLikeTheLiveWrite : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, budgetRemaining := ⟨100⟩,
      boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid) }
  -- The caller is priority 50 as well, so bucket 50 has a second member: a
  -- re-bucket that dropped the whole bucket rather than the one thread would
  -- pass against a singleton and fail here.
  let objs : List (ObjId × KernelObject) := [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let liveSt := mkState objs (runnable := [callerTid, targetTid])
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  -- The live bucket read through the TCB run-queue links: the queue walk filtered
  -- to the threads linked at band `p` (the ghost `atPriority` is proof-only).
  let liveBucket (st : SystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.runQueueWalk bootCoreId).filter
      (fun t => st.queuedPriorityOn bootCoreId t == some (⟨p⟩ : SeLe4n.Priority))
  let frozenBucket (st : FrozenSystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.scheduler.byPriority.get? ⟨p⟩).getD []
  expect "control: both surfaces start with the target queued at 50"
    (liveBucket liveSt 50 == [callerTid, targetTid]
      && frozenBucket frozenSt 50 == [callerTid, targetTid])
  match bootSetPriority liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ with
  | .error e => throw <| IO.userError s!"live setPriority should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetPriority callerTid targetTid ⟨10⟩ frozenSt with
    | .error e => throw <| IO.userError s!"frozen setPriority should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      expect "control: the live demote moves the target to bucket 10"
        (liveBucket liveAfter 10 == [targetTid] && liveBucket liveAfter 50 == [callerTid])
      expect "PAYOFF: ...and so does the frozen demote -- the half that diverged"
        (frozenBucket frozenAfter 10 == [targetTid])
      expect "PAYOFF: ...leaving the caller alone in bucket 50"
        (frozenBucket frozenAfter 50 == [callerTid])
      expect "...so the two surfaces agree on both buckets"
        (frozenBucket frozenAfter 10 == liveBucket liveAfter 10
          && frozenBucket frozenAfter 50 == liveBucket liveAfter 50)

/-- **`v0.35.101`: the MC-priority ceiling re-buckets too**, because it caps
through the same shared writer.  Swept rather than reported, as the `v0.35.99`
ceiling divergence was: a fix applied to one of two callers of a shared helper
leaves the class open, and here the helper is the fix, so the sibling is covered
by construction -- which is the point of this witness rather than an argument
against having it. -/
private def pm_frozenCeilingRebucketsLikeTheLiveWrite : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  -- The reservation carries the live band (80) and the TCB's own field agrees,
  -- so the thread is queued at 80 and the ceiling at 20 must move it.
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, budgetRemaining := ⟨100⟩,
      boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid) }
  let objs : List (ObjId × KernelObject) := [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let liveSt := mkState objs (runnable := [targetTid])
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  -- The live bucket read through the TCB run-queue links: the queue walk filtered
  -- to the threads linked at band `p` (the ghost `atPriority` is proof-only).
  let liveBucket (st : SystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.runQueueWalk bootCoreId).filter
      (fun t => st.queuedPriorityOn bootCoreId t == some (⟨p⟩ : SeLe4n.Priority))
  let frozenBucket (st : FrozenSystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.scheduler.byPriority.get? ⟨p⟩).getD []
  expect "control: both surfaces start with the target queued at 80"
    (liveBucket liveSt 80 == [targetTid] && frozenBucket frozenSt 80 == [targetTid])
  match bootSetMCPriority liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨20⟩ with
  | .error e => throw <| IO.userError s!"live setMCPriority should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetMCPriority callerTid targetTid ⟨20⟩ frozenSt with
    | .error e => throw <| IO.userError s!"frozen setMCPriority should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      expect "control: the live cap moves the target to bucket 20"
        (liveBucket liveAfter 20 == [targetTid] && liveBucket liveAfter 80 == [])
      expect "PAYOFF: ...and so does the frozen cap"
        (frozenBucket frozenAfter 20 == [targetTid] && frozenBucket frozenAfter 80 == [])

-- ============================================================================
-- A bound thread's base priority lives on the thread (`v0.35.98`, WS-SX SX6.4)
-- ============================================================================

/-- **The decisive one.**  A demotion must survive the thread's next block and
wake: `enqueueRunnableOnCore` inserts at `TCB.boostedPriority`, so the demotion
must land on the thread itself (seL4-MCS's `tcbPriority`; the context carries no
priority). -/
private def pm_basePrioritySurvivesBlockAndWake : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, budgetRemaining := ⟨100⟩,
      boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid) }
  let st := mkState [
    (callerTid.toObjId, .tcb (mkTcb callerTid.toNat (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb targetTid.toNat (prio := 50)
        (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ] (runnable := [targetTid])
  let blockAndWake : SystemState → SystemState := fun s =>
    enqueueRunnableOnCore (s.runRemoveOnCore bootCoreId targetTid) bootCoreId targetTid
  let bucketOf : SystemState → Option SeLe4n.Priority := fun s =>
    (s.queuedPriorityOn bootCoreId targetTid)
  expect "the fixture starts queued at its band" (bucketOf st == some ⟨50⟩)
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩
          bootCoreId with
  | .error e => throw <| IO.userError s!"setPriority should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "the demotion re-buckets immediately" (bucketOf st1 == some ⟨10⟩)
    expect "the demotion SURVIVES a block and wake"
      (bucketOf (blockAndWake st1) == some ⟨10⟩)

-- ============================================================================
-- `v0.35.167` (WS-RR RR8.12 Cut C3b-i): the priority arms' resolved
-- scheduler-domain footprint
-- ============================================================================
--
-- `schedLockSet_priorityControlOnCore` is `schedFootprintOfCores` of the two
-- arms' shared SM8.B write set with an **empty** replenish segment.  Both halves
-- are measurable on a state and neither is stated of one by any theorem: the
-- write set names the target's *home* core beside the executing one -- so a
-- demotion issued from another PE declares the queue whose bucket it actually
-- migrates -- and a priority change moves no scheduling context, which is the
-- empty segment's exact half.

/-- PM-FP-01: the priority footprint names the target's home core and the
executing core, and **no** replenish-queue lock; the live arm writes none either.
The syscall is issued from core 1 against a target homed on core 0, so the two
members are distinct -- a footprint resolved at the executing core alone would
declare neither the queue the bucket migration writes nor a lock it needs. -/
private def pm_fp_01_priorityFootprintNamesHomeAndExecutingCores : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, budgetRemaining := ⟨100⟩,
      boundThreadCode := SeLe4n.ThreadId.optCode (some targetTid) }
  let st := mkState [
    (callerTid.toObjId, .tcb (mkTcb callerTid.toNat (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb targetTid.toNat (prio := 50)
        (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ] (runnable := [targetTid])
  let fp := schedLockSet_priorityControlOnCore st targetTid core1
  expect "PM-FP-01 precondition: the target is homed on core 0 and the syscall runs on core 1"
    (determineTargetCore st targetTid == bootCoreId && core1 != bootCoreId)
  expect "PM-FP-01 the footprint names the target's home core's run-queue write lock"
    (decide ((LockKey.runQueue bootCoreId,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "PM-FP-01 ...and the executing core's, which the demotion's preemption point writes"
    (decide ((LockKey.runQueue core1,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "PM-FP-01 ...and no replenish-queue write lock on any core"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      !decide ((LockKey.replenishQueue c,
        SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp)))
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-FP-01 setPriority should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "PM-FP-01 the live arm re-buckets on the target's own home core"
      ((st1.queuedPriorityOn bootCoreId targetTid) == some ⟨10⟩)
    expect "PM-FP-01 ...and writes no replenish queue on any core -- the empty segment's exact half"
      (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
        (st1.releaseEntriesOn c)
          == (st.releaseEntriesOn c)))
  -- the ceiling arm shares the write set, so it shares the footprint.
  match setMCPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-FP-01 setMCPriority should succeed, got {repr e}"
  | .ok (st2, _) =>
    expect "PM-FP-01 the ceiling arm writes no replenish queue either"
      (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
        (st2.releaseEntriesOn c)
          == (st.releaseEntriesOn c)))


-- ============================================================================
-- A priority change on a reply-blocked waiter re-walks the server's boost
-- ============================================================================

/-- A server on core 2 holding a boost lent by a waiter on the boot core: the
waiter (priority 50) is blocked on the server's reply, so the server's
`pipBoost` is 50.  The caller may set any priority. -/
private def pipWaiterState (callerTid serverTid waiterTid : SeLe4n.ThreadId)
    (waiterBinding : SchedContextBinding := .unbound)
    (extra : List (ObjId × KernelObject) := []) : SystemState :=
  let core2 : SeLe4n.Kernel.Concurrency.CoreId := ⟨2, by decide⟩
  mkState ([
    (callerTid.toObjId, .tcb (mkTcb callerTid.toNat (prio := 200))),
    (serverTid.toObjId, .tcb { mkTcb serverTid.toNat (prio := 10) with
      pipBoostCode := SeLe4n.Priority.optCode (some ⟨50⟩), cpuAffinity := some core2 }),
    (waiterTid.toObjId, .tcb ((mkTcb waiterTid.toNat (prio := 50) (binding := waiterBinding)).setIpcState (.blockedOnReply ⟨70⟩ (some serverTid))))
  ] ++ extra)

private def serverBoost (st : SystemState) (serverTid : SeLe4n.ThreadId) :
    Option SeLe4n.Priority :=
  match st.objects[serverTid.toObjId]? with
  | some (.tcb tcb) => tcb.pipBoost
  | _ => none

/-- PM-PIP-01: raising and lowering a reply-blocked waiter's priority moves the
boost its server holds; before the fix the server kept the boost computed from
the waiter's old priority. -/
private def pm_pip_01_setPriorityReboostsServer : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let serverTid : SeLe4n.ThreadId := ⟨2⟩
  let waiterTid : SeLe4n.ThreadId := ⟨3⟩
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let core2 : SeLe4n.Kernel.Concurrency.CoreId := ⟨2, by decide⟩
  let st := pipWaiterState callerTid serverTid waiterTid
  expect "PM-PIP-01 precondition: the server holds the waiter's boost"
    (serverBoost st serverTid == some ⟨50⟩)
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨waiterTid, by decide⟩ ⟨90⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-PIP-01 raise should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "PM-PIP-01 raising the waiter raises the server's boost (50 -> 90)"
      (serverBoost st1 serverTid == some ⟨90⟩)
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨waiterTid, by decide⟩ ⟨20⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-PIP-01 lower should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "PM-PIP-01 lowering the waiter lowers the server's boost (50 -> 20)"
      (serverBoost st1 serverTid == some ⟨20⟩)
  match setMCPriorityOnCore st ⟨callerTid, by decide⟩ ⟨waiterTid, by decide⟩ ⟨30⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-PIP-01 ceiling should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "PM-PIP-01 a ceiling that caps the waiter lowers the server's boost (50 -> 30)"
      (serverBoost st1 serverTid == some ⟨30⟩)
  let fp := schedLockSet_priorityControlOnCore st waiterTid core1
  expect "PM-PIP-01 the footprint names the server's home core, where the re-walk re-buckets"
    (decide ((LockKey.runQueue core2,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))

/-- PM-PIP-02 (WS-SX SX6.4): a configure of a reply-blocked waiter's bound
context moves no priority, so its server's boost is left where it was
(seL4-MCS's configure writes the context alone). -/
private def pm_pip_02_configureLeavesServerBoost : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let serverTid : SeLe4n.ThreadId := ⟨2⟩
  let waiterTid : SeLe4n.ThreadId := ⟨3⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    budgetRemaining := ⟨100⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some waiterTid)
  }
  let st := pipWaiterState callerTid serverTid waiterTid (.bound scId)
    [(scObjId, .schedContext sc)]
  expect "PM-PIP-02 precondition: the server holds the waiter's boost"
    (serverBoost st serverTid == some ⟨50⟩)
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 0 7 1 st with
  | .error e => throw <| IO.userError s!"PM-PIP-02 configure should succeed, got {repr e}"
  | .ok ((), st1) =>
    expect "PM-PIP-02 the configure leaves the server's boost at 50"
      (serverBoost st1 serverTid == some ⟨50⟩)

-- ============================================================================
-- WS-SX SX6.4 (D11): the authority is extra capability 0
-- ============================================================================

/-- The caller's CSpace root: CNode 10, radix 3, behind a 61-bit guard so a
64-bit CPtr names its slot by its low three bits. -/
private def authRootCap : Capability :=
  { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read, .write, .grant],
    cnodeGuardSize := 61 }

private def authTcb (tid : Nat) (mcp : Nat) (spaces : Bool := true) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨10⟩, domain := ⟨0⟩, maxControlledPriority := ⟨mcp⟩,
    spaceCells := if spaces then #v[some authRootCap, none, none, none] else #v[none, none, none, none],
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- CNode 10's slots: 1 the caller's own thread, 2 a second thread, 3 an
endpoint; 4 empty. -/
private def authCNode : CNode :=
  CNode.ofList 3
    [(SeLe4n.Slot.ofNat 1, { target := .object ⟨1⟩, rights := AccessRightSet.ofList [.write] }),
     (SeLe4n.Slot.ofNat 2, { target := .object ⟨2⟩, rights := AccessRightSet.ofList [.write] }),
     (SeLe4n.Slot.ofNat 3, { target := .object ⟨60⟩, rights := AccessRightSet.ofList [.read] })]

private def authState (callerSpaces : Bool := true) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects :=
      [(⟨1⟩, .tcb (authTcb 1 200 callerSpaces)), (⟨2⟩, .tcb (authTcb 2 40)),
       (⟨10⟩, .cnode authCNode), (⟨60⟩, .endpoint {})] }
  builder.buildChecked

private def authorityOf (st : SystemState) (cap? : Option Nat) :
    Except KernelError SeLe4n.ThreadId :=
  (resolvePriorityAuthority st ⟨1⟩ (cap?.map SeLe4n.CPtr.ofNat)).map (·.val)

/-- PM-AUTH-01: the thread capability named as extra capability 0 is the
authority, the caller's own or another thread's. -/
private def pm_auth_01_threadCapabilityIsTheAuthority : IO Unit := do
  expect "own thread capability is the authority"
    (match authorityOf authState (some 1) with | .ok t => t == ⟨1⟩ | .error _ => false)
  expect "another thread's capability is the authority"
    (match authorityOf authState (some 2) with | .ok t => t == ⟨2⟩ | .error _ => false)

/-- PM-AUTH-02: no extra capability is a truncated message; an empty slot or a
capability that is not a thread capability is invalid capability 1; an
unresolvable address is a lookup failure. -/
private def pm_auth_02_refusals : IO Unit := do
  expect "no extra capability is truncatedMessage"
    (match authorityOf authState none with | .error .truncatedMessage => true | _ => false)
  expect "an endpoint capability is invalidCapability 1"
    (match authorityOf authState (some 3) with | .error (.invalidCapability 1) => true | _ => false)
  expect "an empty slot is invalidCapability 1"
    (match authorityOf authState (some 4) with | .error (.invalidCapability 1) => true | _ => false)
  expect "an unresolvable address is a lookup failure"
    (match authorityOf (authState false) (some 2) with
     | .error (.failedLookup _ _) => true | _ => false)

/-- PM-AUTH-03: the authority's ceiling bounds the new priority, not the
caller's: thread 2's ceiling (40) refuses 100, which the caller's (200) admits. -/
private def pm_auth_03_authorityCeilingBounds : IO Unit := do
  let st := authState
  let target : SeLe4n.ValidThreadId := ⟨⟨2⟩, by decide⟩
  let viaCaller := match resolvePriorityAuthority st ⟨1⟩ (some (SeLe4n.CPtr.ofNat 1)) with
    | .ok a => (setPriorityOnCore st a target ⟨100⟩ bootCoreId).toBool
    | .error _ => false
  let viaOther := match resolvePriorityAuthority st ⟨1⟩ (some (SeLe4n.CPtr.ofNat 2)) with
    | .ok a => (setPriorityOnCore st a target ⟨100⟩ bootCoreId).toBool
    | .error _ => true
  expect "the caller's ceiling admits 100" viaCaller
  expect "the other thread's ceiling refuses 100" (!viaOther)

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
  IO.println "--- bind and configure write no thread priority or domain ---"
  pm_bindKeepsThreadPriorityAndDomain
  pm_configureWritesContextAlone
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
  IO.println "--- WS-OD (v0.35.3): a donee runs at its OWN priority ---"
  pm_od_01_prioritySourceClassifier
  pm_od_02_donatedReadsPreferTheTcb
  pm_od_03_setPriorityOnDoneeSparesTheDonor
  pm_od_04_setMCPriorityCapOnDoneeSparesTheDonor
  pm_od_05_frozenSetPriorityOnDoneeSparesTheDonor
  IO.println "--- `v0.35.136`: the two `bound*Consistent` pairs are writer facts ---"
  IO.println "--- `v0.35.98`: the bound thread's base priority has two homes ---"
  pm_basePrioritySurvivesBlockAndWake
  IO.println "--- `v0.35.99`: the frozen mirror writes both homes too ---"
  pm_frozenBasePriorityAgreesWithTheLiveWrite
  pm_frozenBasePriorityRebucketsLikeTheLiveWrite
  pm_frozenCeilingRebucketsLikeTheLiveWrite
  IO.println "--- `v0.35.167`: the priority arms' resolved scheduler footprint ---"
  pm_fp_01_priorityFootprintNamesHomeAndExecutingCores
  IO.println "--- A reply-blocked waiter's priority change re-walks its server's boost ---"
  pm_pip_01_setPriorityReboostsServer
  pm_pip_02_configureLeavesServerBoost
  IO.println "--- WS-SX SX6.4: the priority authority is extra capability 0 ---"
  pm_auth_01_threadCapabilityIsTheAuthority
  pm_auth_02_refusals
  pm_auth_03_authorityCeilingBounds
  IO.println "=== All D2 priority management tests passed (50 tests) ==="
