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

/-- PM-010b: setMCPriority caps priority on SchedContext-bound thread.

WS-RR (`v0.35.133`): the fixture used to carry `tcb.priority = 30` beside a bound
reservation at 80 -- a state `boundThreadPriorityConsistent` forbids, and one the
old two-homes reading made meaningful because the cap consulted the RESERVATION's
field.  With `TCB.priority` the base's one home the cap reads the thread, so the
state the kernel actually maintains is the one to test: both homes at 80, capped
to 50, and **both** asserted afterwards -- the TCB assertion being the one the
suite never made and the one that would have caught `v0.35.98`. -/
private def pm010b_setMCPriorityCapsSchedContextBound : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨80⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  -- Target runs at 80 and its reservation is configured to 80 (the propagation
  -- `schedContextBind` establishes); we set MCP to 50, so the cap must fire.
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80) (mcp := 150) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok st' =>
    -- Verify MCP was updated on TCB, and that the cap wrote the thread's own
    -- base priority -- the one home every scheduling decision reads.
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "MCP updated to 50" (tcb.maxControlledPriority == ⟨50⟩)
      expect "TCB base priority capped to 50" (tcb.priority == ⟨50⟩)
    | _ => throw <| IO.userError "target TCB not found"
    -- ...and that the configured band on the reservation moved with it, which is
    -- what keeps `boundThreadPriorityConsistent` true across the cap.
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "SchedContext priority capped to 50" (sc'.priority == ⟨50⟩)
    | _ => throw <| IO.userError "SchedContext not found after MCP cap"
  | .error e => throw <| IO.userError s!"setMCPriority bound cap should succeed, got {repr e}"

/-- PM-010c: the MCP cap reads the THREAD's band, not its reservation's.

The discriminating witness for `v0.35.133`, and the only shape that can be one:
on a state satisfying `boundThreadPriorityConsistent` the two readings agree by
construction, so what separates them is a **drifted** state -- exactly the state
`v0.35.98` produced, where a demotion wrote one home and left the mirror stale.

Here the thread runs at 30 and its reservation still reads 80.  The new MCP is 50.
The thread's band is already below the ceiling, so the cap must NOT fire and
nothing may be rewritten; the retired reading saw the reservation's 80, capped,
and would have driven the thread's band DOWN to 50 on the strength of a field no
scheduling decision consults.  A revert of the one-home collapse fails here. -/
private def pm010c_setMCPriorityReadsThreadNotReservation : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨51⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨80⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some targetTid
  }
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30) (mcp := 150) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc)
  ]
  -- The retired resolver's answer, computed beside the live one so the
  -- assertions below are known to discriminate rather than merely to pass.
  let retiredReservationReading : SeLe4n.Priority := sc.priority
  expect "the two readings disagree on this state"
    (!(retiredReservationReading == ⟨30⟩))
  match setMCPriorityOp st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨50⟩ with
  | .ok st' =>
    match st'.objects[targetTid.toObjId]? with
    | some (.tcb tcb) =>
      expect "MCP updated to 50" (tcb.maxControlledPriority == ⟨50⟩)
      expect "the thread keeps its own band -- no cap fired" (tcb.priority == ⟨30⟩)
    | _ => throw <| IO.userError "target TCB not found"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "the stale mirror is left alone -- the cap did not consult it"
        (sc'.priority == ⟨80⟩)
    | _ => throw <| IO.userError "SchedContext not found"
  | .error e => throw <| IO.userError s!"setMCPriority should succeed, got {repr e}"

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
      (effectiveBucketPriority st donee == donee.boostedPriority)
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
      -- **Corrected at `v0.35.98`.**  This asserted `tcb'.priority ==
      -- odDoneePriority` — that a bound thread's own TCB is *not* written —
      -- which was the defect rather than the contract: the base priority of a
      -- `.bound` thread has two homes and every run-queue insert reads the TCB
      -- one, so leaving it stale reverted the demotion at the thread's next
      -- wake.  What WS-OD (`v0.35.3`) actually guarantees is the *donee* split
      -- asserted by `pm_od_03` / `pm_od_04` above (a donee's update spares the
      -- **donor's** reservation), not that a bound thread's TCB is spared.
      expect "control: a BOUND thread's TCB priority moves with its reservation"
        (tcb'.priority == ⟨80⟩)
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

/-- WS-RR-PRIO-09 (PR #897's review, `v0.35.136`): **a reservation reconfigured
while on loan comes back disagreeing** — the refutation of
`boundThreadPriorityConsistent` and `boundThreadDomainConsistent` as *invariants*.

The review reported the priority half through `.tcbSetPriority` on the unbound
donor.  Sweeping for the shape found a second route that breaks **both**
predicates with one syscall and no TCB capability at all, and it is the one this
witness drives, because every step of it is a live operation:

1. the reservation is on loan (`.donated`), which is the state `applyCallDonation`
   leaves on every passive-server call;
2. `schedContextConfigure` rewrites `sc.priority` and `sc.domain` — and
   propagates to nobody, since `schedContextConfigurePropagates` reads the
   donee's `ownScId?`, which is `none` (WS-OD `v0.35.3`, and `pm_od_07` is that
   assertion);
3. `returnDonatedSchedContext`'s bottom arm rebinds the **origin** `.bound scId`,
   writing neither `TCB.priority` nor `TCB.domain` nor either of the
   reservation's.

So the post-pop state has a `.bound` thread whose two priority homes and two
domain homes both disagree.  Neither reconciliation is available: writing
`tcb.priority := sc.priority` would undo a demotion by an IPC reply, and writing
`sc.priority := tcb.priority` would silently retune a band the SchedContext
capability's holder set (and is projection-visible besides).  The predicates are
therefore facts about `schedContextBind`, `schedContextConfigureBoundPropagate`
and `updatePrioritySource`, not invariants of the system.

**No scheduling decision is affected**, which is what `v0.35.133` and `v0.35.136`
bought: every band read is `tcb.priority` and every domain filter is
`tcb.domain`, so the origin resumes demoted and in its own partition, as it
should.  The assertions below read the *fields*, not a resolver, because the
claim is about the pair rather than about what the scheduler does with it. -/
private def pm_od_09_reconfiguredLoanComesBackDisagreeing : IO Unit := do
  let originTid : SeLe4n.ThreadId := ⟨7⟩
  let doneeTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some doneeTid,
    donationOrigin := some originTid
  }
  -- The origin has given up its binding and waits on its reply — the shape
  -- `donateSchedContext` leaves and `donationRecipientAcceptable` requires.
  -- Its own band and partition agree with the reservation's at this point.
  let st := mkState [
    (originTid.toObjId, .tcb (mkTcb 7 (prio := 50) (mcp := 200)
      (binding := .unbound))),
    (doneeTid.toObjId, .tcb (mkTcb 42 (prio := odDoneePriority) (mcp := 200)
      (binding := .donated scId originTid))),
    (scObjId, .schedContext sc)
  ]
  -- Step 2: the SchedContext capability's holder retunes the reservation while
  -- it is on loan.  Priority 50 -> 123 and domain 0 -> 5, propagated to nobody.
  match SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scObjId, by decide⟩ 100 200 123 0 5 st with
  | .error e => throw <| IO.userError s!"configure on the loaned reservation failed: {repr e}"
  | .ok ((), stCfg) =>
    expect "the loan's origin is untouched by the reconfiguration"
      (match stCfg.objects[originTid.toObjId]? with
       | some (.tcb t) => t.priority == ⟨50⟩ && t.domain == ⟨0⟩
       | _ => false)
    -- Step 3: the server replies, and the bottom arm hands the reservation back.
    match returnDonatedSchedContext stCfg doneeTid scId originTid none with
    | .error e => throw <| IO.userError s!"the donation pop failed: {repr e}"
    | .ok stPop =>
      match stPop.objects[originTid.toObjId]?, stPop.objects[scObjId]? with
      | some (.tcb origin'), some (.schedContext sc') =>
        expect "the pop rebinds the origin .bound"
          (origin'.schedContextBinding == .bound scId)
        expect "REFUTATION: its two priority homes disagree (50 vs 123)"
          (origin'.priority == ⟨50⟩ && sc'.priority == ⟨123⟩)
        expect "REFUTATION: its two domain homes disagree (0 vs 5)"
          (origin'.domain == ⟨0⟩ && sc'.domain == ⟨5⟩)
      | _, _ => throw <| IO.userError "origin TCB or SC not found after the pop"

/-- WS-RR-PRIO-10: the control for `pm_od_09`, and what makes it a statement
about the **reconfiguration** rather than about the pop.

The same fixture and the same pop, with step 2 omitted: the reservation is handed
back exactly as it was lent, and both pairs agree.  So the pop is not what breaks
the agreement — it is what *installs the binding under which the agreement is
asserted*, which is precisely why no write available to it can repair one. -/
private def pm_od_10_unreconfiguredLoanComesBackAgreeing : IO Unit := do
  let originTid : SeLe4n.ThreadId := ⟨7⟩
  let doneeTid : SeLe4n.ThreadId := ⟨42⟩
  let scObjId : SeLe4n.ObjId := ⟨100⟩
  let scId : SeLe4n.SchedContextId := ⟨100⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨100⟩, period := ⟨200⟩,
    priority := ⟨50⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩, boundThread := some doneeTid,
    donationOrigin := some originTid
  }
  let st := mkState [
    (originTid.toObjId, .tcb (mkTcb 7 (prio := 50) (mcp := 200)
      (binding := .unbound))),
    (doneeTid.toObjId, .tcb (mkTcb 42 (prio := odDoneePriority) (mcp := 200)
      (binding := .donated scId originTid))),
    (scObjId, .schedContext sc)
  ]
  match returnDonatedSchedContext st doneeTid scId originTid none with
  | .error e => throw <| IO.userError s!"the donation pop failed: {repr e}"
  | .ok stPop =>
    match stPop.objects[originTid.toObjId]?, stPop.objects[scObjId]? with
    | some (.tcb origin'), some (.schedContext sc') =>
      expect "control: the pop rebinds the origin .bound here too"
        (origin'.schedContextBinding == .bound scId)
      expect "control: with no reconfiguration the priority homes agree"
        (origin'.priority == sc'.priority)
      expect "control: ...and so do the domain homes"
        (origin'.domain == sc'.domain)
    | _, _ => throw <| IO.userError "origin TCB or SC not found after the pop"

/-- **`v0.35.99`: the frozen surface writes both homes too, and the differential
is what says so.**  `v0.35.98` fixed the live writer and left `frozenSetPriority`
writing the reservation alone, so the *same* operation produced divergent states
— reported on PR #897.  This drives the live and frozen demotes on corresponding
fixtures and compares both fields, which is the only assertion that could have
caught it: each surface's own per-object checks passed throughout. -/
private def pm_frozenBasePriorityAgreesWithTheLiveWrite : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, priority := ⟨50⟩,
      deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨100⟩,
      boundThread := some targetTid }
  let liveSt := mkState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 50) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  match setPriorityOp liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ with
  | .error e => throw <| IO.userError s!"live setPriority should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetPriority callerTid targetTid ⟨10⟩ frozenSt with
    | .error e => throw <| IO.userError s!"frozen setPriority should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      let liveTcbPrio := (liveAfter.getTcb? targetTid).map (·.priority)
      let liveScPrio := (liveAfter.getSchedContext? scId).map (·.priority)
      let frozenTcbPrio := (frozenLookupTcb frozenAfter targetTid).map (·.priority)
      let frozenScPrio := (frozenAfter.getSchedContext? scId).map (·.priority)
      expect "live demote writes both homes" (liveTcbPrio == some ⟨10⟩ && liveScPrio == some ⟨10⟩)
      expect "frozen demote writes the reservation" (frozenScPrio == some ⟨10⟩)
      expect "frozen demote writes the THREAD too — the half that diverged"
        (frozenTcbPrio == some ⟨10⟩)
      expect "...so the two surfaces agree on the thread's base priority"
        (frozenTcbPrio == liveTcbPrio)
      expect "...and on the reservation's" (frozenScPrio == liveScPrio)

/-- **`v0.35.99`: the MC-priority ceiling reaches the same question.**  Found by
sweeping the sibling rather than by a report: the frozen capping compared against
`targetTcb.priority` where the live one compared against `threadBasePriority` —
the *reservation* for a `.bound` thread — and wrote the capped value to the TCB
alone where the live path writes both homes.  Two mirror-image divergences on one
operation.

**WS-RR (`v0.35.133`) narrowed the question and this witness with it.**  With
`TCB.priority` the base's one home, *both* surfaces now compare the ceiling
against the thread's own field, so the divergence this test was written for has no
state left to arise on — which is what a structural closure looks like from the
test's side.  What survives, and is what it now pins, is the agreement itself, on
**both** branches of the cap: it must fire identically where the thread's band
exceeds the ceiling, and it must decline identically where it does not.  The
second half carries the *drifted* state the retired reading depended on, because a
surface still consulting the reservation would cap there and the other would not —
so a revert of the collapse on either surface fails this witness. -/
private def pm_frozenCeilingAgreesWithTheLiveWrite : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  -- (a) THE CAP FIRES.  A state the kernel maintains: the thread runs at 80 and
  -- its reservation is configured to 80, so `boundThreadPriorityConsistent`
  -- holds and the ceiling of 20 is below the band on either reading.
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, priority := ⟨80⟩,
      deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨100⟩,
      boundThread := some targetTid }
  let objs : List (ObjId × KernelObject) := [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let liveSt := mkState objs
  -- `FrozenKernelObject.tcb` carries the LIVE `TCB`, so the two stores are built
  -- from the same records; only the wrapper differs, hence the second list.
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  match setMCPriorityOp liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨20⟩ with
  | .error e => throw <| IO.userError s!"live setMCPriority should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetMCPriority callerTid targetTid ⟨20⟩ frozenSt with
    | .error e => throw <| IO.userError s!"frozen setMCPriority should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      let liveScPrio := (liveAfter.getSchedContext? scId).map (·.priority)
      let liveTcbPrio := (liveAfter.getTcb? targetTid).map (·.priority)
      let frozenScPrio := (frozenAfter.getSchedContext? scId).map (·.priority)
      let frozenTcbPrio := (frozenLookupTcb frozenAfter targetTid).map (·.priority)
      let frozenMcp := (frozenLookupTcb frozenAfter targetTid).map (·.maxControlledPriority)
      expect "the ceiling lands on the frozen TCB" (frozenMcp == some ⟨20⟩)
      expect "live: the ceiling caps the thread's own band to 20" (liveTcbPrio == some ⟨20⟩)
      expect "live: ...and the configured band moves with it" (liveScPrio == some ⟨20⟩)
      expect "frozen: the ceiling caps the thread's own band too"
        (frozenTcbPrio == some ⟨20⟩)
      expect "frozen: ...and the reservation too — it wrote the TCB alone before"
        (frozenScPrio == some ⟨20⟩)
      expect "...so the two surfaces agree on both homes"
        (frozenScPrio == liveScPrio && frozenTcbPrio == liveTcbPrio)
  -- (b) THE CAP DECLINES, IDENTICALLY, ON A DRIFTED STATE.  The thread runs at
  -- 10 and its reservation still reads 80 — the shape `v0.35.98` produced.  Under
  -- the retired two-homes reading the ceiling of 20 was compared against 80 and
  -- fired; under one home it is compared against 10 and does not.  A surface that
  -- still consults the reservation caps here while the other does not, so this is
  -- the half that separates the two readings on both surfaces at once.
  let driftedObjs : List (ObjId × KernelObject) := [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 10) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  match setMCPriorityOp (mkState driftedObjs) ⟨callerTid, by decide⟩
          ⟨targetTid, by decide⟩ ⟨20⟩ with
  | .error e => throw <| IO.userError s!"live setMCPriority (drifted) should succeed, got {repr e}"
  | .ok liveAfter =>
    match frozenSetMCPriority callerTid targetTid ⟨20⟩ (mkFrozenState [
            (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
            (targetTid.toObjId, .tcb (mkTcb 2 (prio := 10) (binding := .bound scId))),
            (scId.toObjId, .schedContext sc) ]) with
    | .error e =>
      throw <| IO.userError s!"frozen setMCPriority (drifted) should succeed, got {repr e}"
    | .ok ((), frozenAfter) =>
      let liveTcbPrio := (liveAfter.getTcb? targetTid).map (·.priority)
      let liveScPrio := (liveAfter.getSchedContext? scId).map (·.priority)
      let frozenTcbPrio := (frozenLookupTcb frozenAfter targetTid).map (·.priority)
      let frozenScPrio := (frozenAfter.getSchedContext? scId).map (·.priority)
      expect "live: the drifted thread keeps its band — no cap fired"
        (liveTcbPrio == some ⟨10⟩ && liveScPrio == some ⟨80⟩)
      expect "frozen: and so does the frozen one"
        (frozenTcbPrio == some ⟨10⟩ && frozenScPrio == some ⟨80⟩)
      expect "...so the two surfaces decline together"
        (frozenTcbPrio == liveTcbPrio && frozenScPrio == liveScPrio)

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
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, priority := ⟨50⟩,
      deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨100⟩,
      boundThread := some targetTid }
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
  let liveBucket (st : SystemState) (p : Nat) : List SeLe4n.ThreadId :=
    ((st.scheduler.runQueueOnCore bootCoreId).byPriority[(⟨p⟩ : SeLe4n.Priority)]?).getD []
  let frozenBucket (st : FrozenSystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.scheduler.byPriority.get? ⟨p⟩).getD []
  expect "control: both surfaces start with the target queued at 50"
    (liveBucket liveSt 50 == [callerTid, targetTid]
      && frozenBucket frozenSt 50 == [callerTid, targetTid])
  match setPriorityOp liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ with
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
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, priority := ⟨80⟩,
      deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨100⟩,
      boundThread := some targetTid }
  let objs : List (ObjId × KernelObject) := [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let liveSt := mkState objs (runnable := [targetTid])
  let frozenSt := mkFrozenState [
    (callerTid.toObjId, .tcb (mkTcb 1 (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb 2 (prio := 80) (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ]
  let liveBucket (st : SystemState) (p : Nat) : List SeLe4n.ThreadId :=
    ((st.scheduler.runQueueOnCore bootCoreId).byPriority[(⟨p⟩ : SeLe4n.Priority)]?).getD []
  let frozenBucket (st : FrozenSystemState) (p : Nat) : List SeLe4n.ThreadId :=
    (st.scheduler.byPriority.get? ⟨p⟩).getD []
  expect "control: both surfaces start with the target queued at 80"
    (liveBucket liveSt 80 == [targetTid] && frozenBucket frozenSt 80 == [targetTid])
  match setMCPriorityOp liveSt ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨20⟩ with
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
-- The bound thread's base priority has two homes (`v0.35.98`)
-- ============================================================================

/-- The reading `updatePrioritySource`'s `.bound` arm had until `v0.35.98`: the
reservation alone.  It lives here, `private`, and nowhere else — a witness that
cannot name what it replaced cannot show that the replacement changed anything,
and every assertion below is *computed against both* so the suite is known to
discriminate rather than merely to pass. -/
private def reservationOnlyPriorityWrite (st : SystemState)
    (scId : SeLe4n.SchedContextId) (p : SeLe4n.Priority) : SystemState :=
  st.updateSchedContext scId fun sc => { sc with priority := p }

/-- Shared fixture: a thread **bound** to a reservation, the two homes of its
base priority in sync at 50 (the state `schedContextBind` leaves), queued on the
boot core at that band. -/
private def boundInSyncState (callerTid targetTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : SystemState :=
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, budget := ⟨100⟩, period := ⟨200⟩, priority := ⟨50⟩,
      deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨100⟩,
      boundThread := some targetTid }
  mkState [
    (callerTid.toObjId, .tcb (mkTcb callerTid.toNat (prio := 50) (mcp := 200))),
    (targetTid.toObjId, .tcb (mkTcb targetTid.toNat (prio := 50)
        (binding := .bound scId))),
    (scId.toObjId, .schedContext sc) ] (runnable := [targetTid])

/-- Both homes move.  `pm_od_06` already asserts the reservation half; this adds
the thread half, which is the one that was missing — and which every run-queue
insert in the kernel reads. -/
private def pm_basePriorityWritesBothHomes : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := boundInSyncState callerTid targetTid scId
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩
          bootCoreId with
  | .error e => throw <| IO.userError s!"setPriority should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "bound demote writes the reservation"
      ((st1.getSchedContext? scId).map (·.priority) == some ⟨10⟩)
    expect "bound demote writes the thread"
      ((st1.getTcb? targetTid).map (·.priority) == some ⟨10⟩)
    -- the retired reading, on the same state: the thread half never moved
    let stOld := migrateRunQueueBucketOnCore
      (reservationOnlyPriorityWrite st scId ⟨10⟩) targetTid ⟨10⟩ bootCoreId
    expect "the retired reading left the thread at its old band"
      ((stOld.getTcb? targetTid).map (·.priority) == some ⟨50⟩)

/-- **The decisive one.**  A demotion must survive the thread's next block and
wake: `enqueueRunnableOnCore` inserts at `TCB.boostedPriority`, so a reservation
write alone put the thread back in the band the demotion had just removed —
permanently, since every later wake reads the same field. -/
private def pm_basePrioritySurvivesBlockAndWake : IO Unit := do
  let callerTid : SeLe4n.ThreadId := ⟨1⟩
  let targetTid : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := ⟨50⟩
  let st := boundInSyncState callerTid targetTid scId
  let blockAndWake : SystemState → SystemState := fun s =>
    let rq := (s.scheduler.runQueueOnCore bootCoreId).remove targetTid
    let sched := s.scheduler.setRunQueueOnCore bootCoreId rq
    let s' : SystemState := { s with scheduler := sched }
    enqueueRunnableOnCore s' bootCoreId targetTid
  let bucketOf : SystemState → Option SeLe4n.Priority := fun s =>
    (s.scheduler.runQueueOnCore bootCoreId).threadPriority[targetTid]?
  expect "the fixture starts queued at its bound band" (bucketOf st == some ⟨50⟩)
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩
          bootCoreId with
  | .error e => throw <| IO.userError s!"setPriority should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "the demotion re-buckets immediately" (bucketOf st1 == some ⟨10⟩)
    expect "the demotion SURVIVES a block and wake"
      (bucketOf (blockAndWake st1) == some ⟨10⟩)
    -- the retired reading, driven through the same block and wake
    let stOld := migrateRunQueueBucketOnCore
      (reservationOnlyPriorityWrite st scId ⟨10⟩) targetTid ⟨10⟩ bootCoreId
    expect "the retired reading also re-bucketed immediately"
      (bucketOf stOld == some ⟨10⟩)
    expect "...and the retired reading REVERTED the demotion on the wake"
      (bucketOf (blockAndWake stOld) == some ⟨50⟩)

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
  let st := boundInSyncState callerTid targetTid scId
  let fp := schedLockSet_priorityControlOnCore st targetTid core1
  expect "PM-FP-01 precondition: the target is homed on core 0 and the syscall runs on core 1"
    (determineTargetCore st targetTid == bootCoreId && core1 != bootCoreId)
  expect "PM-FP-01 the footprint names the target's home core's run-queue write lock"
    (decide ((SchedLockId.runQueue ⟨bootCoreId⟩,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "PM-FP-01 ...and the executing core's, which the demotion's preemption point writes"
    (decide ((SchedLockId.runQueue ⟨core1⟩,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "PM-FP-01 ...and no replenish-queue write lock on any core"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      !decide ((SchedLockId.replenishQueue ⟨c⟩,
        SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp)))
  match setPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-FP-01 setPriority should succeed, got {repr e}"
  | .ok (st1, _) =>
    expect "PM-FP-01 the live arm re-buckets on the target's own home core"
      ((st1.scheduler.runQueueOnCore bootCoreId).threadPriority[targetTid]? == some ⟨10⟩)
    expect "PM-FP-01 ...and writes no replenish queue on any core -- the empty segment's exact half"
      (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
        (st1.scheduler.replenishQueueOnCore c).entries
          == (st.scheduler.replenishQueueOnCore c).entries))
  -- the ceiling arm shares the write set, so it shares the footprint.
  match setMCPriorityOnCore st ⟨callerTid, by decide⟩ ⟨targetTid, by decide⟩ ⟨10⟩ core1 with
  | .error e => throw <| IO.userError s!"PM-FP-01 setMCPriority should succeed, got {repr e}"
  | .ok (st2, _) =>
    expect "PM-FP-01 the ceiling arm writes no replenish queue either"
      (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
        (st2.scheduler.replenishQueueOnCore c).entries
          == (st.scheduler.replenishQueueOnCore c).entries))


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
  pm010c_setMCPriorityReadsThreadNotReservation
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
  IO.println "--- `v0.35.136`: the two `bound*Consistent` pairs are writer facts ---"
  pm_od_09_reconfiguredLoanComesBackDisagreeing
  pm_od_10_unreconfiguredLoanComesBackAgreeing
  IO.println "--- `v0.35.98`: the bound thread's base priority has two homes ---"
  pm_basePriorityWritesBothHomes
  pm_basePrioritySurvivesBlockAndWake
  IO.println "--- `v0.35.99`: the frozen mirror writes both homes too ---"
  pm_frozenBasePriorityAgreesWithTheLiveWrite
  pm_frozenCeilingAgreesWithTheLiveWrite
  pm_frozenBasePriorityRebucketsLikeTheLiveWrite
  pm_frozenCeilingRebucketsLikeTheLiveWrite
  IO.println "--- `v0.35.167`: the priority arms' resolved scheduler footprint ---"
  pm_fp_01_priorityFootprintNamesHomeAndExecutingCores
  IO.println "=== All D2 priority management tests passed (45 tests) ==="
