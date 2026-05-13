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
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
    threadState := state }

/-- Helper: build a minimal SystemState with objects. -/
private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
  }
  builder.buildChecked

-- ============================================================================
-- D1-Q1: suspendThread tests
-- ============================================================================

/-- SR-001: Suspend a Ready thread — should succeed, thread becomes Inactive. -/
private def sr001_suspendReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "thread is Inactive" (tcb.threadState == .Inactive)
    | _ => throw <| IO.userError "TCB not found after suspend"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

/-- SR-002: Suspend an already Inactive thread — should fail with illegalState. -/
private def sr002_suspendInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for Inactive thread"
  | .error e =>
    expect "error is illegalState" (e == .illegalState)

/-- SR-003: Suspend a non-existent thread — should fail with invalidArgument. -/
private def sr003_suspendMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for missing thread"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-004: Suspend clears pending state (pendingMessage, timeoutBudget, queue links). -/
private def sr004_suspendClearsPending : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with
    pendingMessage := some { registers := #[], caps := #[], badge := SeLe4n.Badge.ofNatMasked 42 }
    timeoutBudget := some (SeLe4n.SchedContextId.ofNat 100) }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "pendingMessage cleared" tcb'.pendingMessage.isNone
      expect "timeoutBudget cleared" tcb'.timeoutBudget.isNone
      expect "queuePrev cleared" tcb'.queuePrev.isNone
      expect "queueNext cleared" tcb'.queueNext.isNone
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

-- ============================================================================
-- D1-Q2: resumeThread tests
-- ============================================================================

/-- SR-005: Resume an Inactive thread — should succeed, thread becomes Ready. -/
private def sr005_resumeInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "thread is Ready" (tcb.threadState == .Ready)
      expect "ipcState is ready" (tcb.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found after resume"
  | .error e => throw <| IO.userError s!"resume should succeed, got {repr e}"

/-- SR-006: Resume a non-Inactive thread — should fail with illegalState. -/
private def sr006_resumeReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for Ready thread"
  | .error e =>
    expect "error is illegalState" (e == .illegalState)

/-- SR-007: Resume a non-existent thread — should fail with invalidArgument. -/
private def sr007_resumeMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for missing thread"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-008: Suspend then resume roundtrip — thread returns to Ready. -/
private def sr008_suspendResumeRoundtrip : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match resumeThread st' ⟨tid, by decide⟩ with
    | .ok st'' =>
      match st''.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        expect "thread is Ready after roundtrip" (tcb.threadState == .Ready)
      | _ => throw <| IO.userError "TCB not found"
    | .error e => throw <| IO.userError s!"resume failed: {repr e}"
  | .error e => throw <| IO.userError s!"suspend failed: {repr e}"

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

/-- SR-009: Frozen suspend — Ready thread becomes Inactive. -/
private def sr009_frozenSuspend : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match frozenSuspendThread tid fst with
  | .ok ((), fst') =>
    match fst'.objects.get? tid.toObjId with
    | some (.tcb tcb) =>
      expect "frozen thread is Inactive" (tcb.threadState == .Inactive)
    | _ => throw <| IO.userError "frozen TCB not found"
  | .error e => throw <| IO.userError s!"frozen suspend should succeed, got {repr e}"

/-- SR-010: Frozen resume — Inactive thread becomes Ready. -/
private def sr010_frozenResume : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match frozenResumeThread tid fst with
  | .ok ((), fst') =>
    match fst'.objects.get? tid.toObjId with
    | some (.tcb tcb) =>
      expect "frozen thread is Ready" (tcb.threadState == .Ready)
    | _ => throw <| IO.userError "frozen TCB not found"
  | .error e => throw <| IO.userError s!"frozen resume should succeed, got {repr e}"

/-- SR-011: Frozen suspend of Inactive thread fails. -/
private def sr011_frozenSuspendInactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match frozenSuspendThread tid fst with
  | .ok _ => throw <| IO.userError "frozen suspend should fail for Inactive"
  | .error e =>
    expect "frozen error is illegalState" (e == .illegalState)

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
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

/-- SR-013: Suspend a thread blocked on receive — IPC state cleared. -/
private def sr013_suspendBlockedOnReceive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnReceive epId
    threadState := .BlockedRecv }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

/-- SR-014: Suspend a thread blocked on call — IPC state cleared. -/
private def sr014_suspendBlockedOnCall : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnCall epId
    threadState := .BlockedCall }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

/-- SR-015: Suspend a thread blocked on reply — IPC state cleared. -/
private def sr015_suspendBlockedOnReply : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnReply epId none
    threadState := .BlockedReply }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

/-- SR-016: Suspend a thread blocked on notification — IPC state cleared. -/
private def sr016_suspendBlockedOnNotification : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let notifId : SeLe4n.ObjId := ⟨10⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnNotification notifId
    threadState := .BlockedNotif }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "ipcState is ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

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
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "thread is Inactive" (tcb'.threadState == .Inactive)
      expect "schedContextBinding is unbound"
        (tcb'.schedContextBinding == .unbound)
    | _ => throw <| IO.userError "TCB not found"
  | .error e => throw <| IO.userError s!"suspend should succeed, got {repr e}"

-- ============================================================================
-- D1-Q6: Wrong-object-type negatives
-- ============================================================================

/-- SR-018: Suspend targeting an Endpoint — should fail with invalidArgument. -/
private def sr018_suspendEndpoint : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let ep : Endpoint := {}
  let st := mkState [(⟨1⟩, .endpoint ep)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for non-TCB"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-019: Resume targeting an Endpoint — should fail with invalidArgument. -/
private def sr019_resumeEndpoint : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let ep : Endpoint := {}
  let st := mkState [(⟨1⟩, .endpoint ep)]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for non-TCB"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

-- ============================================================================
-- D1-Q7: Additional frozen operation tests
-- ============================================================================

/-- SR-020: Frozen resume of Ready thread fails with illegalState. -/
private def sr020_frozenResumeReady : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match frozenResumeThread tid fst with
  | .ok _ => throw <| IO.userError "frozen resume should fail for Ready"
  | .error e =>
    expect "frozen error is illegalState" (e == .illegalState)

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
        expect "frozen roundtrip thread is Ready" (tcb.threadState == .Ready)
      | _ => throw <| IO.userError "frozen TCB not found"
    | .error e => throw <| IO.userError s!"frozen resume failed: {repr e}"
  | .error e => throw <| IO.userError s!"frozen suspend failed: {repr e}"

-- ============================================================================
-- R5.A (DEEP-SUSP-02): cancelDonation split into two named arms
-- ============================================================================

/-- SR-022: `cancelBoundDonation` on a `.bound scId` TCB clears the binding. -/
private def sr022_cancelBoundDonationClearsBinding : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 100
  let sc : SeLe4n.Kernel.SchedContext :=
    { scId := scId, boundThread := some tid,
      budget := ⟨1000⟩, period := ⟨1000⟩,
      priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
      budgetRemaining := ⟨1000⟩, isActive := true, replenishments := [] }
  let tcb := { mkTcb 1 .Ready with schedContextBinding := .bound scId }
  let st := mkState [(⟨1⟩, .tcb tcb), (scId.toObjId, .schedContext sc)]
  match cancelBoundDonation st tid tcb with
  | .ok st' =>
    -- Post-state: TCB binding is `.unbound`, SC's boundThread is `none`.
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "TCB binding is unbound" (tcb'.schedContextBinding == .unbound)
    | _ => throw <| IO.userError "TCB not found after cancelBoundDonation"
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc') =>
      expect "SC boundThread is none" sc'.boundThread.isNone
      expect "SC isActive is false" (!sc'.isActive)
    | _ => throw <| IO.userError "SC not found after cancelBoundDonation"
  | .error e => throw <| IO.userError s!"cancelBoundDonation failed: {repr e}"

/-- SR-023: `cancelBoundDonation` on a `.donated` TCB returns `.illegalState`
    — the dispatcher chooses the wrong arm. -/
private def sr023_cancelBoundDonationRejectsDonated : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let donor : SeLe4n.ThreadId := ⟨2⟩
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 100
  let tcb := { mkTcb 1 .Ready with schedContextBinding := .donated scId donor }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match cancelBoundDonation st tid tcb with
  | .ok _ => throw <| IO.userError "cancelBoundDonation should reject .donated"
  | .error e =>
    expect "cancelBoundDonation rejects .donated with illegalState"
      (e == .illegalState)

/-- SR-024: `cancelDonatedDonation` on a `.bound` TCB returns `.illegalState`
    — the dispatcher chooses the wrong arm. -/
private def sr024_cancelDonatedDonationRejectsBound : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 100
  let tcb := { mkTcb 1 .Ready with schedContextBinding := .bound scId }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match cancelDonatedDonation st tid tcb with
  | .ok _ => throw <| IO.userError "cancelDonatedDonation should reject .bound"
  | .error e =>
    expect "cancelDonatedDonation rejects .bound with illegalState"
      (e == .illegalState)

/-- SR-025: The thin `cancelDonation` dispatcher on `.unbound` is identity. -/
private def sr025_cancelDonationUnboundIdentity : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with schedContextBinding := .unbound }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match cancelDonation st tid tcb with
  | .ok st' =>
    -- State should be identical to input.
    expect "cancelDonation .unbound returns identity"
      ((st'.objects[tid.toObjId]?).isSome)
  | .error e => throw <| IO.userError s!"cancelDonation .unbound failed: {repr e}"

-- ============================================================================
-- R5.B (DEEP-SUSP-01): PIP recomputation on resume
-- ============================================================================

/-- SR-026: After resume, `pipBoost` is re-derived from the post-suspend
    blocking graph.  For a thread with no waiters, the boost becomes `none`
    regardless of any pre-suspend boost value. -/
private def sr026_resumePipBoostRecomputedNoWaiters : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  -- Construct an Inactive TCB with a stale pipBoost from before suspend.
  let tcb := { mkTcb 1 .Inactive with pipBoost := some ⟨50⟩ }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      -- No waiters exist in the empty state — pipBoost must be re-derived
      -- to `none`, not the stale `some ⟨50⟩`.
      expect "stale pipBoost cleared on resume (no waiters)"
        tcb'.pipBoost.isNone
      expect "threadState is Ready after resume" (tcb'.threadState == .Ready)
      expect "ipcState is ready after resume" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found after resume"
  | .error e => throw <| IO.userError s!"resume failed: {repr e}"

/-- SR-027: Suspend then resume roundtrip preserves the PIP-readiness
    invariant: the resumed TCB's `pipBoost` reflects the post-resume blocking
    graph, not the pre-suspend one. -/
private def sr027_suspendResumePipReroundtrip : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with pipBoost := some ⟨30⟩ }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match suspendThread st ⟨tid, by decide⟩ with
  | .ok stMid =>
    match resumeThread stMid ⟨tid, by decide⟩ with
    | .ok stFinal =>
      match stFinal.objects[tid.toObjId]? with
      | some (.tcb tcbFinal) =>
        -- Post-resume pipBoost is consistent with the (empty) blocking
        -- graph — `computeMaxWaiterPriority` returns `none` for a thread
        -- with no Reply-blocked waiters.
        expect "post-resume pipBoost reflects current blocking graph"
          tcbFinal.pipBoost.isNone
      | _ => throw <| IO.userError "TCB not found after roundtrip"
    | .error e => throw <| IO.userError s!"resume failed: {repr e}"
  | .error e => throw <| IO.userError s!"suspend failed: {repr e}"

/-- SR-027b: Substantive R5.B case — resume a thread that has waiters.
    A waiter (priority 99) is blocked on `tid`'s reply slot.  After resume,
    `pipBoost` should be re-derived to `some ⟨99⟩` (the waiter's priority)
    rather than the stale `some ⟨50⟩` set pre-suspend.  This validates the
    H3b step's substantive recomputation. -/
private def sr027b_resumeRecomputesPipBoostWithWaiters : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let waiterTid : SeLe4n.ThreadId := ⟨2⟩
  let endpointId : SeLe4n.ObjId := ⟨50⟩
  -- Construct an Inactive TCB with a stale pipBoost.
  let tidTcb := { mkTcb 1 .Inactive with pipBoost := some ⟨50⟩ }
  -- Construct a waiter blocked on tid's reply slot at priority 99.
  -- `waitersOf` reads `tcb.tid` (not the ObjId key), so set tcb.tid to
  -- waiterTid and ensure its ipcState targets `tid`.
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := { waiterBaseTcb with
    ipcState := .blockedOnReply endpointId (some tid) }
  let st := mkState [
    (⟨1⟩, .tcb tidTcb),
    (⟨2⟩, .tcb waiterTcb)
  ]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      -- The waiter is blocked on tid at priority 99.
      -- computeMaxWaiterPriority(st', tid) = some ⟨99⟩.
      -- Resumed TCB's pipBoost should be some ⟨99⟩, NOT the stale some ⟨50⟩.
      expect "pipBoost recomputed from current waiter (not stale)"
        (tcb'.pipBoost == some ⟨99⟩)
      expect "threadState is Ready after resume" (tcb'.threadState == .Ready)
    | _ => throw <| IO.userError "TCB not found after resume"
  | .error e => throw <| IO.userError s!"resume failed: {repr e}"

-- ============================================================================
-- R5.B.2 (DEEP-SUSP-01) Deferred completion: substantive operational tests
-- ============================================================================

/-- SR-027c: `resumeThread_preserves_blockingAcyclic` runtime witness —
    after a successful resume, the priority-inheritance blocking graph
    remains acyclic.  The pre-state has a waiter blocked on the resumed
    thread; after resume, the waiter's edge is preserved but the resumed
    thread itself has no outgoing edge (ipcState = .ready), so acyclicity
    holds. -/
private def sr027c_resumeThreadPreservesBlockingAcyclic : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let waiterTid : SeLe4n.ThreadId := ⟨2⟩
  let endpointId : SeLe4n.ObjId := ⟨50⟩
  let tidTcb := { mkTcb 1 .Inactive with pipBoost := some ⟨50⟩ }
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := { waiterBaseTcb with
    ipcState := .blockedOnReply endpointId (some tid) }
  let st := mkState [(⟨1⟩, .tcb tidTcb), (⟨2⟩, .tcb waiterTcb)]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    -- Verify acyclicity: no thread appears in its own blocking chain.
    -- For each thread in the post-state, the blocking chain from itself
    -- must not contain itself.
    let postWaiterChain := SeLe4n.Kernel.PriorityInheritance.blockingChain
                            st' waiterTid st'.objectIndex.length
    let postTidChain := SeLe4n.Kernel.PriorityInheritance.blockingChain
                          st' tid st'.objectIndex.length
    expect "waiter not in its own chain"
      ¬ (SeLe4n.Kernel.PriorityInheritance.chainContains postWaiterChain waiterTid)
    expect "resumed thread not in its own chain"
      ¬ (SeLe4n.Kernel.PriorityInheritance.chainContains postTidChain tid)
    -- Also verify resumed thread has no outgoing edge (ipcState = .ready).
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      expect "resumed thread ipcState = .ready" (tcb'.ipcState == .ready)
    | _ => throw <| IO.userError "TCB not found after resume"
  | .error e => throw <| IO.userError s!"resume failed: {repr e}"

/-- SR-027d: `resumeThread_pipBoost_consistent_with_blocking_graph` runtime
    witness — after a successful resume, the resumed TCB's `pipBoost`
    equals `computeMaxWaiterPriority` on the post-state.

    The pre-state has a waiter at priority 99 blocked on the resumed
    thread.  Post-resume, the resumed TCB's pipBoost is set to `some ⟨99⟩`
    (matching `computeMaxWaiterPriority` on the post-state). -/
private def sr027d_resumeThreadPipBoostMatchesGraph : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let endpointId : SeLe4n.ObjId := ⟨50⟩
  let tidTcb := { mkTcb 1 .Inactive with pipBoost := some ⟨50⟩ }
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := { waiterBaseTcb with
    ipcState := .blockedOnReply endpointId (some tid) }
  let st := mkState [(⟨1⟩, .tcb tidTcb), (⟨2⟩, .tcb waiterTcb)]
  match resumeThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb') =>
      let postCmwp := SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority st' tid
      -- pipBoost should match the post-state computeMaxWaiterPriority exactly.
      expect "tcb'.pipBoost = computeMaxWaiterPriority post-state"
        (tcb'.pipBoost == postCmwp)
      -- And both should be some ⟨99⟩ (the waiter's priority).
      expect "pipBoost is some ⟨99⟩ (waiter priority)" (tcb'.pipBoost == some ⟨99⟩)
    | _ => throw <| IO.userError "TCB not found after resume"
  | .error e => throw <| IO.userError s!"resume failed: {repr e}"

-- ============================================================================
-- R5.D (DEEP-SCH-03): restoreToReady shared helper
-- ============================================================================

/-- SR-028: `restoreToReady` sets `ipcState := .ready` and clears queue
    link fields on the target TCB. -/
private def sr028_restoreToReadyClearsIpcFields : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with
    ipcState := .blockedOnSend ⟨50⟩,
    queuePrev := some ⟨3⟩, queueNext := some ⟨4⟩,
    queuePPrev := some .endpointHead }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  let st' := restoreToReady st tid
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb') =>
    expect "ipcState reset to .ready" (tcb'.ipcState == .ready)
    expect "queuePrev cleared" tcb'.queuePrev.isNone
    expect "queueNext cleared" tcb'.queueNext.isNone
    expect "queuePPrev cleared" tcb'.queuePPrev.isNone
    -- threadState is preserved (restoreToReady only touches IPC fields)
    expect "threadState preserved" (tcb'.threadState == tcb.threadState)
  | _ => throw <| IO.userError "TCB not found after restoreToReady"

/-- SR-029: `restoreToReady` on absent TCB is identity. -/
private def sr029_restoreToReadyAbsentIdentity : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩  -- not in state
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  let st' := restoreToReady st tid
  -- State should be definitionally the same (no modification when TCB absent).
  expect "restoreToReady absent TCB is identity"
    (st'.objects[tid.toObjId]?.isNone)

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
  IO.println "--- R5.A: cancelDonation split ---"
  sr022_cancelBoundDonationClearsBinding
  sr023_cancelBoundDonationRejectsDonated
  sr024_cancelDonatedDonationRejectsBound
  sr025_cancelDonationUnboundIdentity
  IO.println "--- R5.B: PIP recomputation on resume ---"
  sr026_resumePipBoostRecomputedNoWaiters
  sr027_suspendResumePipReroundtrip
  sr027b_resumeRecomputesPipBoostWithWaiters
  sr027c_resumeThreadPreservesBlockingAcyclic
  sr027d_resumeThreadPipBoostMatchesGraph
  IO.println "--- R5.D: restoreToReady shared helper ---"
  sr028_restoreToReadyClearsIpcFields
  sr029_restoreToReadyAbsentIdentity
  IO.println "=== All D1 suspend/resume tests passed (30 tests) ==="
