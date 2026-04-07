/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.Scheduler.PriorityInheritance
import SeLe4n.Kernel.IPC.Operations.Donation

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.PriorityInheritance
open SeLe4n.Kernel.RobinHood

namespace SeLe4n.Testing.PriorityInheritanceSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"pip check passed [{label}]"
  else
    throw <| IO.userError s!"pip check failed [{label}]"

private def mkTcb (tid : Nat) (prio : Nat := 10)
    (ipcState : ThreadIpcState := .ready)
    (state : ThreadState := .Ready)
    (pipBoost : Option SeLe4n.Priority := none) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := ⟨0⟩,
    ipcState := ipcState, threadState := state,
    pipBoost := pipBoost }

private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none)
    (runnable : List SeLe4n.ThreadId := []) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
    runnable := runnable
  }
  builder.buildChecked

-- PIP-001: pipBoost field defaults to none
private def pip001_defaultPipBoostNone : IO Unit := do
  let tcb := mkTcb 1
  expect "PIP-001 pipBoost defaults to none" (tcb.pipBoost == none)

-- PIP-002: effectivePriority with no pipBoost returns base priority
private def pip002_effectivePriorityNoPip : IO Unit := do
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 50)))]
  let tcb := mkTcb 1 (prio := 50)
  match effectivePriority st tcb with
  | some (prio, _, _) =>
    expect "PIP-002 effective priority = base priority" (prio == ⟨50⟩)
  | none => throw <| IO.userError "PIP-002 effectivePriority returned none"

-- PIP-003: effectivePriority with pipBoost returns max(base, boost)
private def pip003_effectivePriorityWithPip : IO Unit := do
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 30) (pipBoost := some ⟨80⟩)))]
  let tcb := mkTcb 1 (prio := 30) (pipBoost := some ⟨80⟩)
  match effectivePriority st tcb with
  | some (prio, _, _) =>
    expect "PIP-003 effective priority = max(30, 80) = 80" (prio == ⟨80⟩)
  | none => throw <| IO.userError "PIP-003 effectivePriority returned none"

-- PIP-004: effectivePriority with lower pipBoost keeps base
private def pip004_effectivePriorityLowerPip : IO Unit := do
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 (prio := 80) (pipBoost := some ⟨30⟩)))]
  let tcb := mkTcb 1 (prio := 80) (pipBoost := some ⟨30⟩)
  match effectivePriority st tcb with
  | some (prio, _, _) =>
    expect "PIP-004 effective priority = max(80, 30) = 80" (prio == ⟨80⟩)
  | none => throw <| IO.userError "PIP-004 effectivePriority returned none"

-- PIP-005: waitersOf returns empty for thread with no waiters
private def pip005_waitersOfEmpty : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 30)))
  ]
  let waiters := waitersOf st ⟨1⟩
  expect "PIP-005 no waiters for thread 1" (waiters.length == 0)

-- PIP-006: waitersOf returns correct waiters
private def pip006_waitersOfFound : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (state := .Ready))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply)))
  ]
  let waiters := waitersOf st ⟨1⟩
  expect "PIP-006 thread 2 is a waiter of thread 1" (waiters.length == 1)

-- PIP-007: computeMaxWaiterPriority returns highest waiter priority
private def pip007_computeMaxWaiterPriority : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 50)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply)))
  ]
  match computeMaxWaiterPriority st ⟨1⟩ with
  | some prio =>
    expect "PIP-007 max waiter priority = 80" (prio == ⟨80⟩)
  | none => throw <| IO.userError "PIP-007 should find waiters"

-- PIP-008: updatePipBoost sets pipBoost correctly
private def pip008_updatePipBoost : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply)))
  ]
  let st' := updatePipBoost st ⟨1⟩
  match st'.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb tcb) =>
    expect "PIP-008 pipBoost set to 80" (tcb.pipBoost == some ⟨80⟩)
  | _ => throw <| IO.userError "PIP-008 TCB not found after updatePipBoost"

-- PIP-009: blockingChain returns empty for non-blocked thread
private def pip009_blockingChainEmpty : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 50) (state := .Ready)))
  ]
  let chain := blockingChain st ⟨1⟩
  expect "PIP-009 blocking chain empty for non-blocked thread" (chain.length == 0)

-- PIP-010: blockingChain follows blockedOnReply chain
private def pip010_blockingChainFollows : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨2⟩))
      (state := .BlockedReply))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 50)
      (ipcState := .blockedOnReply ⟨101⟩ (some ⟨3⟩))
      (state := .BlockedReply))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 30) (state := .Ready)))
  ]
  let chain := blockingChain st ⟨1⟩
  expect "PIP-010 chain from 1 has length 2" (chain.length == 2)

-- PIP-011: propagatePriorityInheritance boosts transitive chain
private def pip011_propagateTransitive : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 10) (state := .Ready))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 20)
      (ipcState := .blockedOnReply ⟨101⟩ (some ⟨1⟩))
      (state := .BlockedReply))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨2⟩))
      (state := .BlockedReply)))
  ]
  let st' := propagatePriorityInheritance st ⟨2⟩
  match st'.objects[(⟨2⟩ : ObjId)]? with
  | some (.tcb tcb2) =>
    expect "PIP-011 thread 2 pipBoost >= 80" (match tcb2.pipBoost with
      | some p => p.val >= 80
      | none => false)
  | _ => throw <| IO.userError "PIP-011 thread 2 TCB not found"

-- PIP-012: revertPriorityInheritance clears pipBoost when no waiters
private def pip012_revertClearsPipBoost : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (pipBoost := some ⟨80⟩) (state := .Ready)))
  ]
  let st' := revertPriorityInheritance st ⟨1⟩
  match st'.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb tcb) =>
    expect "PIP-012 pipBoost cleared when no waiters" (tcb.pipBoost == none)
  | _ => throw <| IO.userError "PIP-012 TCB not found after revert"

-- PIP-013: PIP does not affect threads outside blocking chain
private def pip013_doesNotAffectOthers : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (state := .Ready))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply))),
    (⟨4⟩, .tcb (mkTcb 4 (prio := 60) (state := .Ready)))
  ]
  let st' := propagatePriorityInheritance st ⟨1⟩
  match st'.objects[(⟨4⟩ : ObjId)]? with
  | some (.tcb tcb4) =>
    expect "PIP-013 thread 4 unaffected" (tcb4.pipBoost == none)
  | _ => throw <| IO.userError "PIP-013 thread 4 TCB not found"

-- PIP-014: effectivePriority with SchedContext-bound thread and pipBoost
private def pip014_effectivePrioritySchedContextBound : IO Unit := do
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := ⟨10⟩, budget := ⟨100⟩, period := ⟨1000⟩,
    priority := ⟨40⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨100⟩
  }
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 10
  let tcb : TCB := { mkTcb 1 (prio := 20) (pipBoost := some ⟨90⟩)
    with schedContextBinding := .bound scId }
  let st := mkState [
    (⟨1⟩, .tcb tcb),
    (⟨10⟩, .schedContext sc)
  ]
  match effectivePriority st tcb with
  | some (prio, _, _) =>
    -- base = 40 (from SC), boost = 90, so max(40, 90) = 90
    expect "PIP-014 SC-bound + pipBoost: max(40,90) = 90" (prio == ⟨90⟩)
  | none => throw <| IO.userError "PIP-014 effectivePriority returned none"

-- PIP-015: blockingGraphEdges returns correct edges
private def pip015_blockingGraphEdges : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨2⟩))
      (state := .BlockedReply))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 50) (state := .Ready))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 30) (state := .Ready)))
  ]
  let edges := blockingGraphEdges st
  expect "PIP-015 exactly 1 blocking edge" (edges.length == 1)
  match edges.head? with
  | some (waiter, server) =>
    expect "PIP-015 edge is (1, 2)" (waiter == ⟨1⟩ && server == ⟨2⟩)
  | none => throw <| IO.userError "PIP-015 no edges found"

-- PIP-016: chainContains helper works correctly
private def pip016_chainContains : IO Unit := do
  let chain : List SeLe4n.ThreadId := [⟨2⟩, ⟨3⟩, ⟨4⟩]
  expect "PIP-016 chain contains 3" (chainContains chain ⟨3⟩)
  expect "PIP-016 chain does not contain 5" (!chainContains chain ⟨5⟩)

-- PIP-017: propagatePriorityInheritance preserves scheduler.current (frame)
private def pip017_framePreservesCurrent : IO Unit := do
  let st := mkState
    [ (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (state := .Ready))),
      (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
        (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
        (state := .BlockedReply))) ]
    (current := some ⟨1⟩)
  let st' := propagatePriorityInheritance st ⟨1⟩
  expect "PIP-017 scheduler.current preserved" (st'.scheduler.current == some ⟨1⟩)

-- PIP-018: revertPriorityInheritance preserves machine state (frame)
private def pip018_framePreservesMachine : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (pipBoost := some ⟨80⟩) (state := .Ready)))
  ]
  let st' := revertPriorityInheritance st ⟨1⟩
  -- Machine state is preserved — verify via timer field (MachineState has no BEq)
  expect "PIP-018 machine timer preserved" (st'.machine.timer == st.machine.timer)

-- PIP-019: updatePipBoost with thread in run queue performs bucket migration
private def pip019_runQueueBucketMigration : IO Unit := do
  -- Thread 1 is in run queue at priority 30, gets boosted to 80 by waiter
  let st := mkState
    [ (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (state := .Ready))),
      (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
        (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
        (state := .BlockedReply))) ]
    (runnable := [⟨1⟩])
  let st' := updatePipBoost st ⟨1⟩
  -- Thread 1 should still be in run queue (membership preserved)
  expect "PIP-019 thread 1 still in run queue" (⟨1⟩ ∈ st'.scheduler.runQueue)
  -- Check pipBoost was set
  match st'.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb tcb) =>
    expect "PIP-019 pipBoost set to 80" (tcb.pipBoost == some ⟨80⟩)
  | _ => throw <| IO.userError "PIP-019 TCB not found"

-- PIP-020: Multiple waiters — computeMaxWaiterPriority picks highest
private def pip020_multipleWaitersMax : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 10))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 40)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply))),
    (⟨3⟩, .tcb (mkTcb 3 (prio := 90)
      (ipcState := .blockedOnReply ⟨101⟩ (some ⟨1⟩))
      (state := .BlockedReply))),
    (⟨4⟩, .tcb (mkTcb 4 (prio := 60)
      (ipcState := .blockedOnReply ⟨102⟩ (some ⟨1⟩))
      (state := .BlockedReply)))
  ]
  match computeMaxWaiterPriority st ⟨1⟩ with
  | some prio =>
    expect "PIP-020 max of 3 waiters (40,90,60) = 90" (prio == ⟨90⟩)
  | none => throw <| IO.userError "PIP-020 should find waiters"

-- PIP-021: propagate with zero fuel is identity
private def pip021_propagateZeroFuel : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 30) (state := .Ready))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨1⟩))
      (state := .BlockedReply)))
  ]
  let st' := propagatePriorityInheritance st ⟨1⟩ (fuel := 0)
  -- With zero fuel, no propagation happens — pipBoost unchanged
  match st'.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb tcb) =>
    expect "PIP-021 zero fuel = no change" (tcb.pipBoost == none)
  | _ => throw <| IO.userError "PIP-021 TCB not found"

-- PIP-022: blockingServer returns correct server
private def pip022_blockingServer : IO Unit := do
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (prio := 80)
      (ipcState := .blockedOnReply ⟨100⟩ (some ⟨2⟩))
      (state := .BlockedReply))),
    (⟨2⟩, .tcb (mkTcb 2 (prio := 50) (state := .Ready)))
  ]
  match blockingServer st ⟨1⟩ with
  | some server => expect "PIP-022 server of 1 is 2" (server == ⟨2⟩)
  | none => throw <| IO.userError "PIP-022 should find blocking server"
  match blockingServer st ⟨2⟩ with
  | some _ => throw <| IO.userError "PIP-022 thread 2 should have no server"
  | none => expect "PIP-022 thread 2 has no server" true

end SeLe4n.Testing.PriorityInheritanceSuite

open SeLe4n.Testing.PriorityInheritanceSuite in
def main : IO Unit := do
  IO.println "=== Priority Inheritance Protocol Test Suite ==="
  IO.println ""
  pip001_defaultPipBoostNone
  pip002_effectivePriorityNoPip
  pip003_effectivePriorityWithPip
  pip004_effectivePriorityLowerPip
  pip005_waitersOfEmpty
  pip006_waitersOfFound
  pip007_computeMaxWaiterPriority
  pip008_updatePipBoost
  pip009_blockingChainEmpty
  pip010_blockingChainFollows
  pip011_propagateTransitive
  pip012_revertClearsPipBoost
  pip013_doesNotAffectOthers
  pip014_effectivePrioritySchedContextBound
  pip015_blockingGraphEdges
  pip016_chainContains
  pip017_framePreservesCurrent
  pip018_framePreservesMachine
  pip019_runQueueBucketMigration
  pip020_multipleWaitersMax
  pip021_propagateZeroFuel
  pip022_blockingServer
  IO.println ""
  IO.println s!"=== All {22} PIP tests passed ==="
