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
  builder.build

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
  IO.println ""
  IO.println "=== All PIP tests passed ==="
