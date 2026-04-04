/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState
import SeLe4n.Kernel.SchedContext.Types

open SeLe4n.Model
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Kernel.RobinHood

namespace SeLe4n.Testing.SuspendResumeSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"suspend-resume check passed [{label}]"
  else
    throw <| IO.userError s!"suspend-resume check failed [{label}]"

/-- Helper: construct a test TCB with given state. -/
private def mkTcb (tid : Nat) (state : ThreadState := .Ready)
    (prio : Nat := 10) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := ⟨0⟩,
    threadState := state }

/-- Helper: build a minimal SystemState with objects. -/
private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
  }
  builder.build

-- ============================================================================
-- D1-Q1: suspendThread tests
-- ============================================================================

/-- SR-001: Suspend a Ready thread — should succeed, thread becomes Inactive. -/
private def sr001_suspendReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "SR-001 thread is Inactive" (tcb.threadState == .Inactive)
    | _ => throw <| IO.userError "SR-001 TCB not found after suspend"
  | .error e => throw <| IO.userError s!"SR-001 suspend should succeed, got {repr e}"

/-- SR-002: Suspend an already Inactive thread — should fail with illegalState. -/
private def sr002_suspendInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match suspendThread st tid with
  | .ok _ => throw <| IO.userError "SR-002 should fail for Inactive thread"
  | .error e =>
    expect "SR-002 error is illegalState" (e == .illegalState)

/-- SR-003: Suspend a non-existent thread — should fail with invalidArgument. -/
private def sr003_suspendMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st tid with
  | .ok _ => throw <| IO.userError "SR-003 should fail for missing thread"
  | .error e =>
    expect "SR-003 error is invalidArgument" (e == .invalidArgument)

/-- SR-004: Suspend clears pending state (pendingMessage, timeoutBudget, queue links). -/
private def sr004_suspendClearsPending : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with
    pendingMessage := some { registers := #[], caps := #[], badge := SeLe4n.Badge.mk 42 }
    timeoutBudget := some (SeLe4n.SchedContextId.ofNat 100) }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-004 pendingMessage cleared" tcb'.pendingMessage.isNone
      expect "SR-004 timeoutBudget cleared" tcb'.timeoutBudget.isNone
      expect "SR-004 queuePrev cleared" tcb'.queuePrev.isNone
      expect "SR-004 queueNext cleared" tcb'.queueNext.isNone
    | _ => throw <| IO.userError "SR-004 TCB not found"
  | .error e => throw <| IO.userError s!"SR-004 suspend should succeed, got {repr e}"

-- ============================================================================
-- D1-Q2: resumeThread tests
-- ============================================================================

/-- SR-005: Resume an Inactive thread — should succeed, thread becomes Ready. -/
private def sr005_resumeInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match resumeThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "SR-005 thread is Ready" (tcb.threadState == .Ready)
      expect "SR-005 ipcState is ready" (tcb.ipcState == .ready)
    | _ => throw <| IO.userError "SR-005 TCB not found after resume"
  | .error e => throw <| IO.userError s!"SR-005 resume should succeed, got {repr e}"

/-- SR-006: Resume a non-Inactive thread — should fail with illegalState. -/
private def sr006_resumeReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match resumeThread st tid with
  | .ok _ => throw <| IO.userError "SR-006 should fail for Ready thread"
  | .error e =>
    expect "SR-006 error is illegalState" (e == .illegalState)

/-- SR-007: Resume a non-existent thread — should fail with invalidArgument. -/
private def sr007_resumeMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match resumeThread st tid with
  | .ok _ => throw <| IO.userError "SR-007 should fail for missing thread"
  | .error e =>
    expect "SR-007 error is invalidArgument" (e == .invalidArgument)

/-- SR-008: Suspend then resume roundtrip — thread returns to Ready. -/
private def sr008_suspendResumeRoundtrip : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st tid with
  | .ok st' =>
    match resumeThread st' tid with
    | .ok st'' =>
      match st''.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        expect "SR-008 thread is Ready after roundtrip" (tcb.threadState == .Ready)
      | _ => throw <| IO.userError "SR-008 TCB not found"
    | .error e => throw <| IO.userError s!"SR-008 resume failed: {repr e}"
  | .error e => throw <| IO.userError s!"SR-008 suspend failed: {repr e}"

-- ============================================================================
-- D1-Q3: Frozen operation tests
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
  }
  objectTypes := freezeMap (RHTable.empty 16)
  capabilityRefs := freezeMap (RHTable.empty 16)
  machine := default
  objectIndex := []
  objectIndexSet := freezeMap (RHTable.empty 16)
  tlb := TlbState.empty
}

private def mkFrozenState (objs : List (ObjId × FrozenKernelObject)) : FrozenSystemState :=
  let rt := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  { emptyFrozenState with objects := freezeMap rt }

/-- SR-009: Frozen suspend — Ready thread becomes Inactive. -/
private def sr009_frozenSuspend : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match frozenSuspendThread tid fst with
  | .ok ((), fst') =>
    match fst'.objects.get? tid.toObjId with
    | some (.tcb tcb) =>
      expect "SR-009 frozen thread is Inactive" (tcb.threadState == .Inactive)
    | _ => throw <| IO.userError "SR-009 frozen TCB not found"
  | .error e => throw <| IO.userError s!"SR-009 frozen suspend should succeed, got {repr e}"

/-- SR-010: Frozen resume — Inactive thread becomes Ready. -/
private def sr010_frozenResume : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match frozenResumeThread tid fst with
  | .ok ((), fst') =>
    match fst'.objects.get? tid.toObjId with
    | some (.tcb tcb) =>
      expect "SR-010 frozen thread is Ready" (tcb.threadState == .Ready)
    | _ => throw <| IO.userError "SR-010 frozen TCB not found"
  | .error e => throw <| IO.userError s!"SR-010 frozen resume should succeed, got {repr e}"

/-- SR-011: Frozen suspend of Inactive thread fails. -/
private def sr011_frozenSuspendInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match frozenSuspendThread tid fst with
  | .ok _ => throw <| IO.userError "SR-011 frozen suspend should fail for Inactive"
  | .error e =>
    expect "SR-011 frozen error is illegalState" (e == .illegalState)

-- ============================================================================
-- D1-Q4: IPC blocked state tests
-- ============================================================================

/-- SR-012: Suspend a thread blocked on send — IPC state cleared to ready. -/
private def sr012_suspendBlockedOnSend : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnSend epId
    threadState := .BlockedSend }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-012 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-012 ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "SR-012 TCB not found"
  | .error e => throw <| IO.userError s!"SR-012 suspend should succeed, got {repr e}"

/-- SR-013: Suspend a thread blocked on receive — IPC state cleared. -/
private def sr013_suspendBlockedOnReceive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnReceive epId
    threadState := .BlockedRecv }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-013 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-013 ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "SR-013 TCB not found"
  | .error e => throw <| IO.userError s!"SR-013 suspend should succeed, got {repr e}"

/-- SR-014: Suspend a thread blocked on call — IPC state cleared. -/
private def sr014_suspendBlockedOnCall : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnCall epId
    threadState := .BlockedCall }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-014 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-014 ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "SR-014 TCB not found"
  | .error e => throw <| IO.userError s!"SR-014 suspend should succeed, got {repr e}"

/-- SR-015: Suspend a thread blocked on reply — IPC state cleared. -/
private def sr015_suspendBlockedOnReply : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnReply epId none
    threadState := .BlockedReply }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-015 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-015 ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "SR-015 TCB not found"
  | .error e => throw <| IO.userError s!"SR-015 suspend should succeed, got {repr e}"

/-- SR-016: Suspend a thread blocked on notification — IPC state cleared. -/
private def sr016_suspendBlockedOnNotification : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let notifId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnNotification notifId
    threadState := .BlockedNotif }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-016 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-016 ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "SR-016 TCB not found"
  | .error e => throw <| IO.userError s!"SR-016 suspend should succeed, got {repr e}"

-- ============================================================================
-- D1-Q5: SchedContext binding tests
-- ============================================================================

/-- SR-017: Suspend a thread with bound SchedContext — binding cleared. -/
private def sr017_suspendBoundSchedContext : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 50
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, boundThread := some ⟨1⟩ }
  let tcb := { mkTcb 1 .Ready with schedContextBinding := .bound scId }
  let st := mkState [(⟨1⟩, .tcb tcb), (⟨50⟩, .schedContext sc)]
  match suspendThread st tid with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "SR-017 thread is Inactive" (tcb'.threadState == .Inactive)
      expect "SR-017 schedContextBinding is unbound"
        (tcb'.schedContextBinding == .unbound)
    | _ => throw <| IO.userError "SR-017 TCB not found"
  | .error e => throw <| IO.userError s!"SR-017 suspend should succeed, got {repr e}"

-- ============================================================================
-- D1-Q6: Wrong-object-type negatives
-- ============================================================================

/-- SR-018: Suspend targeting an Endpoint — should fail with invalidArgument. -/
private def sr018_suspendEndpoint : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let ep : Endpoint := {}
  let st := mkState [(⟨1⟩, .endpoint ep)]
  match suspendThread st tid with
  | .ok _ => throw <| IO.userError "SR-018 should fail for non-TCB"
  | .error e =>
    expect "SR-018 error is invalidArgument" (e == .invalidArgument)

/-- SR-019: Resume targeting an Endpoint — should fail with invalidArgument. -/
private def sr019_resumeEndpoint : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let ep : Endpoint := {}
  let st := mkState [(⟨1⟩, .endpoint ep)]
  match resumeThread st tid with
  | .ok _ => throw <| IO.userError "SR-019 should fail for non-TCB"
  | .error e =>
    expect "SR-019 error is invalidArgument" (e == .invalidArgument)

-- ============================================================================
-- D1-Q7: Additional frozen operation tests
-- ============================================================================

/-- SR-020: Frozen resume of Ready thread fails with illegalState. -/
private def sr020_frozenResumeReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match frozenResumeThread tid fst with
  | .ok _ => throw <| IO.userError "SR-020 frozen resume should fail for Ready"
  | .error e =>
    expect "SR-020 frozen error is illegalState" (e == .illegalState)

/-- SR-021: Frozen suspend-resume roundtrip. -/
private def sr021_frozenRoundtrip : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match frozenSuspendThread tid fst with
  | .ok ((), fst') =>
    match frozenResumeThread tid fst' with
    | .ok ((), fst'') =>
      match fst''.objects.get? tid.toObjId with
      | some (.tcb tcb) =>
        expect "SR-021 frozen roundtrip thread is Ready" (tcb.threadState == .Ready)
      | _ => throw <| IO.userError "SR-021 frozen TCB not found"
    | .error e => throw <| IO.userError s!"SR-021 frozen resume failed: {repr e}"
  | .error e => throw <| IO.userError s!"SR-021 frozen suspend failed: {repr e}"

end SeLe4n.Testing.SuspendResumeSuite

open SeLe4n.Testing.SuspendResumeSuite in
def main : IO Unit := do
  IO.println "=== D1 Suspend/Resume Test Suite ==="
  IO.println "--- D1-Q1: suspendThread ---"
  sr001_suspendReady
  sr002_suspendInactive
  sr003_suspendMissing
  sr004_suspendClearsPending
  IO.println "--- D1-Q2: resumeThread ---"
  sr005_resumeInactive
  sr006_resumeReady
  sr007_resumeMissing
  sr008_suspendResumeRoundtrip
  IO.println "--- D1-Q3: Frozen Operations ---"
  sr009_frozenSuspend
  sr010_frozenResume
  sr011_frozenSuspendInactive
  IO.println "--- D1-Q4: IPC Blocked States ---"
  sr012_suspendBlockedOnSend
  sr013_suspendBlockedOnReceive
  sr014_suspendBlockedOnCall
  sr015_suspendBlockedOnReply
  sr016_suspendBlockedOnNotification
  IO.println "--- D1-Q5: SchedContext Binding ---"
  sr017_suspendBoundSchedContext
  IO.println "--- D1-Q6: Wrong-Object-Type Negatives ---"
  sr018_suspendEndpoint
  sr019_resumeEndpoint
  IO.println "--- D1-Q7: Additional Frozen Operations ---"
  sr020_frozenResumeReady
  sr021_frozenRoundtrip
  IO.println "=== All D1 suspend/resume tests passed (21 tests) ==="
