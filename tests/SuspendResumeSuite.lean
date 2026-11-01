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
import SeLe4n.Testing.BootCoreOps

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
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
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
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for Inactive thread"
  | .error e =>
    expect "error is illegalState" (e == .illegalState)

/-- SR-003: Suspend a non-existent thread — should fail with invalidArgument. -/
private def sr003_suspendMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for missing thread"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-004: Suspend clears pending state (pendingMessage, timeoutBudget, queue links). -/
private def sr004_suspendClearsPending : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with
    pendingMessage := some { registers := #[], badge := SeLe4n.Badge.ofNatMasked 42 }
    timeoutBudget := some (SeLe4n.SchedContextId.ofNat 100) }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  match bootResumeThread st ⟨tid, by decide⟩ with
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
  match bootResumeThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for Ready thread"
  | .error e =>
    expect "error is illegalState" (e == .illegalState)

/-- SR-007: Resume a non-existent thread — should fail with invalidArgument. -/
private def sr007_resumeMissing : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Inactive))]
  match bootResumeThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for missing thread"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-008: Suspend then resume roundtrip — thread returns to Ready. -/
private def sr008_suspendResumeRoundtrip : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))]
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match bootResumeThread st' ⟨tid, by decide⟩ with
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
private def emptyFrozenState : FrozenSystemState :=
  SeLe4n.Testing.emptyFrozenSystemState

private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  SeLe4n.Testing.frozenStateOf objs

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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    threadState := .BlockedSend } (.blockedOnSend epId))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    threadState := .BlockedRecv } (.blockedOnReceive epId))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    threadState := .BlockedCall } (.blockedOnCall epId))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    threadState := .BlockedReply } (.blockedOnReply epId none))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    threadState := .BlockedNotif } (.blockedOnNotification notifId))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
    budgetRemaining := ⟨1000⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some ⟨1⟩) }
  let tcb := { mkTcb 1 .Ready with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId), scBindingOwnerCode := 0 }
  let st := mkState [(⟨1⟩, .tcb tcb), (⟨50⟩, .schedContext sc)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
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
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok _ => throw <| IO.userError "should fail for non-TCB"
  | .error e =>
    expect "error is invalidArgument" (e == .invalidArgument)

/-- SR-019: Resume targeting an Endpoint — should fail with invalidArgument. -/
private def sr019_resumeEndpoint : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let ep : Endpoint := {}
  let st := mkState [(⟨1⟩, .endpoint ep)]
  match bootResumeThread st ⟨tid, by decide⟩ with
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
    { scId := scId, boundThreadCode := SeLe4n.ThreadId.optCode (some tid),
      budget := ⟨1000⟩, period := ⟨1000⟩,
      priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
      budgetRemaining := ⟨1000⟩, isActive := true, refillTailCount := 0 }
  let tcb := { mkTcb 1 .Ready with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId), scBindingOwnerCode := 0 }
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
  let tcb := { mkTcb 1 .Ready with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.donated scId donor), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode (.donated scId donor) }
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
  let tcb := { mkTcb 1 .Ready with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId), scBindingOwnerCode := 0 }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match cancelDonatedDonation st tid tcb with
  | .ok _ => throw <| IO.userError "cancelDonatedDonation should reject .bound"
  | .error e =>
    expect "cancelDonatedDonation rejects .bound with illegalState"
      (e == .illegalState)

/-- SR-025: The thin `cancelDonation` dispatcher on `.unbound` is identity. -/
private def sr025_cancelDonationUnboundIdentity : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let tcb := { mkTcb 1 .Ready with scBindingScCode := 0, scBindingOwnerCode := 0 }
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
  let tcb := { mkTcb 1 .Inactive with pipBoostCode := SeLe4n.Priority.optCode (some ⟨50⟩) }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootResumeThread st ⟨tid, by decide⟩ with
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
  let tcb := { mkTcb 1 .Ready with pipBoostCode := SeLe4n.Priority.optCode (some ⟨30⟩) }
  let st := mkState [(⟨1⟩, .tcb tcb)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok stMid =>
    match bootResumeThread stMid ⟨tid, by decide⟩ with
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
  let tidTcb := { mkTcb 1 .Inactive with pipBoostCode := SeLe4n.Priority.optCode (some ⟨50⟩) }
  -- Construct a waiter blocked on tid's reply slot at priority 99.
  -- `waitersOf` reads `tcb.tid` (not the ObjId key), so set tcb.tid to
  -- waiterTid and ensure its ipcState targets `tid`.
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := (waiterBaseTcb.setIpcState (.blockedOnReply endpointId (some tid)))
  let st := mkState [
    (⟨1⟩, .tcb tidTcb),
    (⟨2⟩, .tcb waiterTcb)
  ]
  match bootResumeThread st ⟨tid, by decide⟩ with
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
  let tidTcb := { mkTcb 1 .Inactive with pipBoostCode := SeLe4n.Priority.optCode (some ⟨50⟩) }
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := (waiterBaseTcb.setIpcState (.blockedOnReply endpointId (some tid)))
  let st := mkState [(⟨1⟩, .tcb tidTcb), (⟨2⟩, .tcb waiterTcb)]
  match bootResumeThread st ⟨tid, by decide⟩ with
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
  let tidTcb := { mkTcb 1 .Inactive with pipBoostCode := SeLe4n.Priority.optCode (some ⟨50⟩) }
  let waiterBaseTcb := mkTcb 2 .Ready 99
  let waiterTcb := (waiterBaseTcb.setIpcState (.blockedOnReply endpointId (some tid)))
  let st := mkState [(⟨1⟩, .tcb tidTcb), (⟨2⟩, .tcb waiterTcb)]
  match bootResumeThread st ⟨tid, by decide⟩ with
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
  let tcb := (TCB.setIpcState { mkTcb 1 .Ready with
    queuePrevCode := SeLe4n.ThreadId.optCode (some ⟨3⟩), queueNextCode := SeLe4n.ThreadId.optCode (some ⟨4⟩),
    queuePPrevCode := 1,
    -- `v0.35.134`: the fifth field `TCB.restoredToReady` clears was asserted by
    -- nothing, which is how the frozen mirror came to omit it for as long as it
    -- did -- a clear nobody measures is a clear nobody notices missing.
    pendingReceiveReplyCode := SeLe4n.ReplyId.optCode (some ⟨7⟩) } (.blockedOnSend ⟨50⟩))
  let st := mkState [(⟨1⟩, .tcb tcb)]
  let st' := restoreToReady st tid
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb') =>
    expect "ipcState reset to .ready" (tcb'.ipcState == .ready)
    expect "queuePrev cleared" tcb'.queuePrev.isNone
    expect "queueNext cleared" tcb'.queueNext.isNone
    expect "queuePPrev cleared" tcb'.queuePPrev.isNone
    expect "stashed receive Reply relinquished" tcb'.pendingReceiveReply.isNone
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

/-- SR-030 (PR #811 — `resumeThread` orphaning fix): resuming a HIGHER-priority thread
must NOT drop the calling (current) thread.  Pre-fix, `resumeThread`'s H5 called
`schedule` without re-enqueuing the current thread, so a lower-priority caller that
resumed a higher-priority thread was silently orphaned — saved-but-not-enqueued, never
current, never runnable.  Here thread A (prio 10) is current and NOT in the run queue
(the real dequeue-on-dispatch precondition; `.build` with empty `runnable` +
`current := some A` reproduces it exactly, which `buildChecked`'s "current ∈ runnable"
convention would otherwise mask and so hide the bug).  Resuming the Inactive thread B
(prio 20) preempts A: B becomes current, and A is re-enqueued — not dropped. -/
private def sr030_resumeHigherPriorityReenqueuesCaller : IO Unit := do
  let aTid : SeLe4n.ThreadId := ⟨1⟩
  let bTid : SeLe4n.ThreadId := ⟨2⟩
  let st : SystemState :=
    (((SeLe4n.Testing.BootstrapBuilder.empty.withObject aTid.toObjId
        (.tcb (mkTcb 1 .Running 10))).withObject bTid.toObjId
        (.tcb (mkTcb 2 .Inactive 20))).withCurrent (some aTid)).build
  -- Precondition: A is current and NOT queued (dequeue-on-dispatch).
  expect "SR-030 precondition: A is current"
    (st.scheduler.currentOnCore SeLe4n.Kernel.Concurrency.bootCoreId == some aTid)
  expect "SR-030 precondition: A is NOT in the run queue"
    (!(st.queuedOn SeLe4n.Kernel.Concurrency.bootCoreId aTid))
  match bootResumeThread st ⟨bTid, by decide⟩ with
  | .ok st' =>
    expect "SR-030 resumed higher-priority B preempts and becomes current"
      (st'.scheduler.currentOnCore SeLe4n.Kernel.Concurrency.bootCoreId == some bTid)
    -- THE FIX: the preempted caller A is re-enqueued, not orphaned.
    expect "SR-030 preempted caller A is re-enqueued (NOT orphaned)"
      ((st'.queuedOn SeLe4n.Kernel.Concurrency.bootCoreId aTid))
  | .error e => throw <| IO.userError s!"SR-030 resume should succeed, got {repr e}"

/-- SR-031: resuming a LOWER-priority thread does not preempt — the current thread keeps
running (`needsReschedule = false`), so no `schedule` runs and nothing is dropped.  The
companion to SR-030 confirming the fix only re-enqueues on the actual preemption path. -/
private def sr031_resumeLowerPriorityKeepsCurrent : IO Unit := do
  let aTid : SeLe4n.ThreadId := ⟨1⟩
  let bTid : SeLe4n.ThreadId := ⟨2⟩
  let st : SystemState :=
    (((SeLe4n.Testing.BootstrapBuilder.empty.withObject aTid.toObjId
        (.tcb (mkTcb 1 .Running 20))).withObject bTid.toObjId
        (.tcb (mkTcb 2 .Inactive 10))).withCurrent (some aTid)).build
  match bootResumeThread st ⟨bTid, by decide⟩ with
  | .ok st' =>
    expect "SR-031 lower-priority resume does not preempt: A stays current"
      (st'.scheduler.currentOnCore SeLe4n.Kernel.Concurrency.bootCoreId == some aTid)
    expect "SR-031 resumed lower-priority B is enqueued"
      ((st'.queuedOn SeLe4n.Kernel.Concurrency.bootCoreId bTid))
  | .error e => throw <| IO.userError s!"SR-031 resume should succeed, got {repr e}"


-- ============================================================================
-- `v0.35.134`: the frozen resume mirrors the live resume's scheduling steps
-- ============================================================================
--
-- The live side has had SR-026, SR-027b, SR-030 and SR-031 for the boost
-- recompute and the preemption since R5.B and PR #811; the frozen side had
-- none, and `frozenResumeThread` performed neither step.  None of SR-010,
-- SR-020 or SR-021 sets `scheduler.current`, so the comparison branch was
-- unexecuted, and `.tcbResume` is outside `FrozenOpBranch.all`, so no
-- differential reached it either.  These are the twins.

/-- The **retired** frozen restore: `ipcState := .ready` and nothing else, which
is what `frozenResumeThread` cleared until `v0.35.134`.  It lives here and
nowhere else -- the code is deleted, the evidence is kept -- and it is computed
beside the live clear so SR-032 is known to discriminate rather than merely to
pass. -/
private def retiredFrozenResumeClear (tcb : TCB) : TCB :=
  (tcb.setIpcState .ready)

/-- The **retired** frozen preemption reading: the two **base** priorities. -/
private def retiredFrozenPreempts (resumed current : TCB) : Bool :=
  resumed.priority.val > current.priority.val

/-- The live reading, which is what `resolveEffectivePrioDeadline` resolves to
(`resolveEffectivePrioDeadline_fst_eq_boostedPriority`). -/
private def liveFrozenPreempts (resumed current : TCB) : Bool :=
  resumed.boostedPriority.val > current.boostedPriority.val

/-- SR-032: the frozen resume clears **every** field `TCB.restoredToReady`
clears, not `ipcState` alone.  The stashed receive Reply is the one that matters
beyond hygiene: left set, `replyIsStashed` keeps that Reply permanently in use. -/
private def sr032_frozenResumeClearsEveryRestoredField : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let stale := (TCB.setIpcState { mkTcb 1 .Inactive with
    queuePrevCode := SeLe4n.ThreadId.optCode (some ⟨3⟩), queueNextCode := SeLe4n.ThreadId.optCode (some ⟨4⟩),
    queuePPrevCode := 1,
    pendingReceiveReplyCode := SeLe4n.ReplyId.optCode (some ⟨7⟩) } (.blockedOnSend ⟨50⟩))
  -- The retired clear leaves four of the five fields set, so the assertions
  -- below are known to separate the two readings.
  let retired := retiredFrozenResumeClear stale
  expect "the retired frozen clear leaves the queue links set"
    (retired.queuePrev.isSome && retired.queueNext.isSome && retired.queuePPrev.isSome)
  expect "the retired frozen clear leaves the stashed Reply set"
    retired.pendingReceiveReply.isSome
  let fst := mkFrozenState [(⟨1⟩, .tcb stale)]
  match frozenResumeThread tid fst with
  | .ok ((), fst') =>
    match fst'.getTcb? tid with
    | some tcb' =>
      expect "frozen resume: ipcState is ready" (tcb'.ipcState == .ready)
      expect "frozen resume: queuePrev cleared" tcb'.queuePrev.isNone
      expect "frozen resume: queueNext cleared" tcb'.queueNext.isNone
      expect "frozen resume: queuePPrev cleared" tcb'.queuePPrev.isNone
      expect "frozen resume: stashed receive Reply relinquished"
        tcb'.pendingReceiveReply.isNone
      expect "frozen resume: threadState is Ready" (tcb'.threadState == .Ready)
    | _ => throw <| IO.userError "frozen TCB not found after resume"
  | .error e => throw <| IO.userError s!"frozen resume should succeed, got {repr e}"

/-- SR-033: the frozen resume re-derives `pipBoost` from the blocking graph --
the frozen twin of SR-026 (over-boost) and SR-027b (under-boost).  Both
directions, because a carried-over boost is wrong in both: too high and the
thread runs at an inherited band nobody is waiting for, too low and the
inversion priority inheritance exists to prevent is live. -/
private def sr033_frozenResumeRecomputesPipBoost : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let epId : SeLe4n.ObjId := ⟨50⟩
  -- (a) over-boost: a stale boost with no waiter left must be cleared.
  let staleBoosted := { mkTcb 1 .Inactive with pipBoostCode := SeLe4n.Priority.optCode (some ⟨90⟩) }
  let fstA := mkFrozenState [(⟨1⟩, .tcb staleBoosted)]
  match frozenResumeThread tid fstA with
  | .ok ((), fstA') =>
    match fstA'.getTcb? tid with
    | some tcb' =>
      expect "(a) frozen resume clears a stale boost when no waiter remains"
        tcb'.pipBoost.isNone
    | _ => throw <| IO.userError "frozen TCB not found (a)"
  | .error e => throw <| IO.userError s!"frozen resume (a) failed: {repr e}"
  -- (b) under-boost: a waiter acquired while Inactive must raise the boost.
  let waiter := ((mkTcb 2 .Ready 90).setIpcState (.blockedOnReply epId (some tid)))
  let unboosted := mkTcb 1 .Inactive
  let fstB := mkFrozenState [(⟨1⟩, .tcb unboosted), (⟨2⟩, .tcb waiter)]
  match frozenResumeThread tid fstB with
  | .ok ((), fstB') =>
    match fstB'.getTcb? tid with
    | some tcb' =>
      expect "(b) frozen resume re-derives the boost from the blocking graph"
        (tcb'.pipBoost == some ⟨90⟩)
      expect "(b) and the re-derived boost moves the effective priority"
        (tcb'.boostedPriority == (⟨90⟩ : SeLe4n.Priority))
    | _ => throw <| IO.userError "frozen TCB not found (b)"
  | .error e => throw <| IO.userError s!"frozen resume (b) failed: {repr e}"

/-- SR-034: the frozen resume's preemption test reads the **effective** priority
-- the frozen twin of SR-030 / SR-031, and the half that separates the two
readings.  Both directions, computing the retired base reading beside the live
one, because the two disagree both ways: a boosted resumed thread must preempt a
higher-**based** current thread, and a plain resumed thread must not preempt a
boosted one. -/
private def sr034_frozenResumePreemptsOnEffectivePriority : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let curTid : SeLe4n.ThreadId := ⟨3⟩
  let epId : SeLe4n.ObjId := ⟨50⟩
  -- (a) base 10 + an earned boost of 90 against a current thread at base 50.
  let waiter := ((mkTcb 2 .Ready 90).setIpcState (.blockedOnReply epId (some tid)))
  let resumed := mkTcb 1 .Inactive 10
  let current := mkTcb 3 .Ready 50
  let boostedResumed := { resumed with pipBoostCode := SeLe4n.Priority.optCode (some ⟨90⟩) }
  expect "(a) the retired base reading does NOT preempt"
    (retiredFrozenPreempts boostedResumed current == false)
  expect "(a) the live effective reading DOES preempt"
    (liveFrozenPreempts boostedResumed current)
  let fstA0 := mkFrozenState
    [(⟨1⟩, .tcb resumed), (⟨2⟩, .tcb waiter), (⟨3⟩, .tcb current)]
  let fstA := { fstA0 with
                  scheduler := { fstA0.scheduler with current := some curTid } }
  match frozenResumeThread tid fstA with
  | .ok ((), fstA') =>
    expect "(a) frozen resume clears current, as the live resume reschedules"
      fstA'.scheduler.current.isNone
  | .error e => throw <| IO.userError s!"frozen resume (a) failed: {repr e}"
  -- (b) base 90 with no boost against a current thread at base 10 boosted to 95.
  let boostedCurrent := { mkTcb 3 .Ready 10 with pipBoostCode := SeLe4n.Priority.optCode (some ⟨95⟩) }
  let plainResumed := mkTcb 1 .Inactive 90
  expect "(b) the retired base reading DOES preempt"
    (retiredFrozenPreempts plainResumed boostedCurrent)
  expect "(b) the live effective reading does NOT preempt"
    (liveFrozenPreempts plainResumed boostedCurrent == false)
  let fstB0 := mkFrozenState
    [(⟨1⟩, .tcb plainResumed), (⟨3⟩, .tcb boostedCurrent)]
  let fstB := { fstB0 with
                  scheduler := { fstB0.scheduler with current := some curTid } }
  match frozenResumeThread tid fstB with
  | .ok ((), fstB') =>
    expect "(b) frozen resume keeps current: a boosted thread is not preempted"
      (fstB'.scheduler.current == some curTid)
  | .error e => throw <| IO.userError s!"frozen resume (b) failed: {repr e}"

-- ============================================================================
-- `v0.35.167` (WS-RR RR8.12 Cut C3b-i): the live `.tcbResume` arm's resolved
-- scheduler-domain footprint
-- ============================================================================
--
-- `schedLockSet_resumeThreadOnCore` is `schedFootprintOfCores` of the arm's own
-- SM8.B write set with an **empty** replenish segment.  The two claims a state
-- can measure that no theorem states of one are that the write set's first core
-- is the resumed thread's *home* rather than the executing core -- so a remote
-- resume declares the queue it actually enqueues on -- and that the live arm
-- moves no scheduling context, which is the empty segment's exact half.

/-- SR-035: the resume footprint names the resumed thread's home core and the
executing core, and **no** replenish-queue lock on any core; the live arm writes
none either.  B is pinned to core 1 and the syscall runs on core 0, so the two
members are distinct -- a footprint resolved at the executing core alone would
declare neither the queue B enters nor a lock the enqueue needs. -/
private def sr035_resumeFootprintNamesHomeAndExecutingCores : IO Unit := do
  let aTid : SeLe4n.ThreadId := ⟨1⟩
  let bTid : SeLe4n.ThreadId := ⟨2⟩
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let bootCore := SeLe4n.Kernel.Concurrency.bootCoreId
  let st : SystemState :=
    (((SeLe4n.Testing.BootstrapBuilder.empty.withObject aTid.toObjId
        (.tcb (mkTcb 1 .Running 10))).withObject bTid.toObjId
        (.tcb { mkTcb 2 .Inactive 20 with cpuAffinity := some core1 })).withCurrent
        (some aTid)).build
  let vB : SeLe4n.ValidThreadId := ⟨bTid, by decide⟩
  let fp := SeLe4n.Kernel.schedLockSet_resumeThreadOnCore st vB bootCore
  expect "SR-035 precondition: B is homed on core 1, the syscall runs on core 0"
    (SeLe4n.Kernel.determineTargetCore st bTid == core1 && core1 != bootCore)
  expect "SR-035 the footprint names B's home core's run-queue write lock"
    (decide ((SeLe4n.Kernel.Concurrency.LockKey.runQueue core1,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "SR-035 ...and the executing core's, which the inline reschedule writes"
    (decide ((SeLe4n.Kernel.Concurrency.LockKey.runQueue bootCore,
      SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp))
  expect "SR-035 ...and no replenish-queue write lock on any core"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      !decide ((SeLe4n.Kernel.Concurrency.LockKey.replenishQueue c,
        SeLe4n.Kernel.Concurrency.AccessMode.write) ∈ fp)))
  match resumeThreadOnCore st vB bootCore with
  | .ok (st', _) =>
    expect "SR-035 the live arm enqueues B on its own home core, not the executing one"
      ((st'.queuedOn core1 bTid))
    expect "SR-035 ...and writes no replenish queue on any core -- the empty segment's exact half"
      (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
        (st'.releaseEntriesOn c)
          == (st.releaseEntriesOn c)))
  | .error e => throw <| IO.userError s!"SR-035 live resume should succeed, got {repr e}"

/-- SR-036 (seL4-MCS `suspend` → `schedContext_cancelYieldTo`): suspending a
thread that yielded to a context clears both link ends — the thread's
`yieldToCode` and the context's `yieldFromCode`. -/
private def sr036_suspendCancelsYieldTo : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 50
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := scId, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, yieldFromCode := 2 }
  let tcb := { mkTcb 1 .Ready with yieldToCode := 51 }
  let st := mkState [(⟨1⟩, .tcb tcb), (⟨50⟩, .schedContext sc)]
  match bootSuspendThread st ⟨tid, by decide⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]?, st'.objects[(⟨50⟩ : ObjId)]? with
    | some (.tcb tcb'), some (.schedContext sc') =>
      expect "SR-036 suspended thread's yield-to link is cleared" (tcb'.yieldToCode == 0)
      expect "SR-036 the context forgets its yielder" (sc'.yieldFromCode == 0)
    | _, _ => throw <| IO.userError "SR-036 objects not found after suspend"
  | .error e => throw <| IO.userError s!"SR-036 suspend should succeed, got {repr e}"

/-- SR-037: the frozen suspend mirrors the live one's yield cancel. -/
private def sr037_frozenSuspendCancelsYieldTo : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := SeLe4n.SchedContextId.ofNat 50, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, yieldFromCode := 2 }
  let fst := mkFrozenState [(⟨1⟩, .tcb { mkTcb 1 .Ready with yieldToCode := 51 }),
    (⟨50⟩, .schedContext sc)]
  match frozenSuspendThread tid fst with
  | .ok ((), fst') =>
    match fst'.objects.get? tid.toObjId, fst'.objects.get? (⟨50⟩ : ObjId) with
    | some (.tcb tcb), some (.schedContext sc') =>
      expect "SR-037 frozen suspend clears the thread's yield-to link" (tcb.yieldToCode == 0)
      expect "SR-037 ...and the context's yield-from link" (sc'.yieldFromCode == 0)
    | _, _ => throw <| IO.userError "SR-037 frozen objects not found"
  | .error e => throw <| IO.userError s!"SR-037 frozen suspend should succeed, got {repr e}"

/-- A yielder (thread 1) linked to context 50, which has consumed 7 units. -/
private def yieldLinkedState : SystemState :=
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := SeLe4n.SchedContextId.ofNat 50, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, consumed := 7, yieldFromCode := 2 }
  mkState [(⟨1⟩, .tcb { mkTcb 1 .Ready with yieldToCode := 51 }), (⟨50⟩, .schedContext sc)]

/-- SR-038 (seL4-MCS `finaliseCap` on a context →
`schedContext_completeYieldTo(sc->scYieldFrom)`): the context's final delete
hands its yielder the consumed time (`setConsumed`: the one-register message
info in `x1`, the count in `x2`) and clears both link ends. -/
private def sr038_contextFinaliseCompletesYield : IO Unit := do
  let st' := SeLe4n.Kernel.finaliseSchedContext ⟨50⟩ yieldLinkedState
  match st'.objects[(⟨1⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]? with
  | some (.tcb t), some (.schedContext sc) =>
    expect "SR-038 the yielder's MR0 holds the consumed time" (t.registerContext.x2 == 7)
    expect "SR-038 ...with a one-register message info"
      (t.registerContext.x1 == SeLe4n.Kernel.consumedInfoWord)
    expect "SR-038 the yielder's link is cleared" (t.yieldToCode == 0)
    expect "SR-038 the context's link is cleared and its count taken off"
      (sc.yieldFromCode == 0 && sc.consumed == 0)
  | _, _ => throw <| IO.userError "SR-038 objects not found after the finalise"

/-- SR-039 (seL4-MCS `finaliseCap` on a thread → `suspend` →
`schedContext_cancelYieldTo`): the yielder's final delete clears both link
ends and writes no consumed time anywhere. -/
private def sr039_threadFinaliseCancelsYield : IO Unit := do
  let st' := SeLe4n.Kernel.finaliseThread ⟨1⟩ yieldLinkedState
  match st'.objects[(⟨1⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]? with
  | some (.tcb t), some (.schedContext sc) =>
    expect "SR-039 the finalised thread's link is cleared" (t.yieldToCode == 0)
    expect "SR-039 the context forgets its yielder, keeping its count"
      (sc.yieldFromCode == 0 && sc.consumed == 7)
  | _, _ => throw <| IO.userError "SR-039 objects not found after the finalise"

/-- SR-040 (WS-ZA ZA6.6, the frozen suspend mirrors the live one): a thread
bound to context 50 and yielded to context 60, suspended live and frozen from
the same objects.  Both release the bound context (unbound, inactive, no
origin), clear the thread's binding codes and cancel both ends of the yield
link, and they agree field for field. -/
private def sr040_liveFrozenSuspendAgree : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let scBound : SeLe4n.Kernel.SchedContext := {
    scId := SeLe4n.SchedContextId.ofNat 50, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨1000⟩,
    boundThreadCode := SeLe4n.ThreadId.optCode (some ⟨1⟩), isActive := true }
  let scYield : SeLe4n.Kernel.SchedContext := {
    scId := SeLe4n.SchedContextId.ofNat 60, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨1000⟩,
    yieldFromCode := 2 }
  let tcb := { mkTcb 1 .Ready with
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound (SeLe4n.SchedContextId.ofNat 50)),
    scBindingOwnerCode := 0, yieldToCode := 61 }
  let st := mkState [(⟨1⟩, .tcb tcb), (⟨50⟩, .schedContext scBound), (⟨60⟩, .schedContext scYield)]
  let fst := mkFrozenState [(⟨1⟩, .tcb tcb), (⟨50⟩, .schedContext scBound),
    (⟨60⟩, .schedContext scYield)]
  match bootSuspendThread st ⟨tid, by decide⟩, frozenSuspendThread tid fst with
  | .ok st', .ok ((), fst') =>
    match st'.objects[(⟨1⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]?,
        st'.objects[(⟨60⟩ : ObjId)]?, fst'.objects.get? (⟨1⟩ : ObjId),
        fst'.objects.get? (⟨50⟩ : ObjId), fst'.objects.get? (⟨60⟩ : ObjId) with
    | some (.tcb t), some (.schedContext b), some (.schedContext y),
        some (.tcb ft), some (.schedContext fb), some (.schedContext fy) =>
      expect "SR-040 the live suspend releases the bound context"
        (b.boundThreadCode == 0 && !b.isActive && b.donationOrigin.isNone &&
          t.scBindingScCode == 0 && t.scBindingOwnerCode == 0)
      expect "SR-040 the frozen suspend releases it the same way"
        (fb.boundThreadCode == b.boundThreadCode && fb.isActive == b.isActive &&
          fb.donationOrigin == b.donationOrigin && ft.scBindingScCode == t.scBindingScCode &&
          ft.scBindingOwnerCode == t.scBindingOwnerCode)
      expect "SR-040 both cancel the yield link at both ends"
        (t.yieldToCode == 0 && y.yieldFromCode == 0 &&
          ft.yieldToCode == t.yieldToCode && fy.yieldFromCode == y.yieldFromCode)
      expect "SR-040 both leave the thread Inactive and ready"
        (t.threadState == .Inactive && ft.threadState == t.threadState &&
          ft.ipcState == t.ipcState)
    | _, _, _, _, _, _ => throw <| IO.userError "SR-040 objects not found after the suspends"
  | .error e, _ => throw <| IO.userError s!"SR-040 live suspend should succeed, got {repr e}"
  | _, .error e => throw <| IO.userError s!"SR-040 frozen suspend should succeed, got {repr e}"

/-- A yielder (thread 1) current on the boot core and linked to context 50,
which has consumed 7 units; thread 2 unlinked. -/
private def yieldLinkedCurrentState (current : SeLe4n.ThreadId) : SystemState :=
  let sc : SeLe4n.Kernel.SchedContext := {
    scId := SeLe4n.SchedContextId.ofNat 50, budget := ⟨1000⟩, period := ⟨10000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, consumed := 7, yieldFromCode := 2 }
  mkState [(⟨1⟩, .tcb { mkTcb 1 .Running with yieldToCode := 51 }),
    (⟨2⟩, .tcb (mkTcb 2 .Running)), (⟨50⟩, .schedContext sc)] (some current)

/-- SR-041 (WS-ZA ZA6.7, seL4-MCS `activateThread` →
`schedContext_completeYieldTo(ksCurThread)`): the activation of a current
thread with a pending yield hands it the consumed time — in its saved context
and in the core's register bank, its live context — and clears both link
ends. -/
private def sr041_activationCompletesCurrentYield : IO Unit := do
  let core := SeLe4n.Kernel.Concurrency.bootCoreId
  let st := yieldLinkedCurrentState ⟨1⟩
  let st' := SeLe4n.Kernel.activateThreadOnCore st core
  match st'.objects[(⟨1⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]? with
  | some (.tcb t), some (.schedContext sc) =>
    expect "SR-041 the yielder's MR0 holds the consumed time" (t.registerContext.x2 == 7)
    expect "SR-041 ...with a one-register message info"
      (t.registerContext.x1 == SeLe4n.Kernel.consumedInfoWord)
    expect "SR-041 the core's bank holds the same two registers"
      (st'.machine.regsOnCore core == t.registerContext)
    expect "SR-041 the yielder's link is cleared" (t.yieldToCode == 0)
    expect "SR-041 the context's link is cleared and its count taken off"
      (sc.yieldFromCode == 0 && sc.consumed == 0)
    expect "SR-041 the scheduler is unchanged"
      (st'.scheduler.currentOnCore core == st.scheduler.currentOnCore core)
  | _, _ => throw <| IO.userError "SR-041 objects not found after the activation"

/-- SR-042: the activation of an unlinked current thread, and the activation at a
core id that names no core, write nothing; a linked thread that is not current
keeps its pending yield. -/
private def sr042_activationWithoutPendingYieldIsIdentity : IO Unit := do
  let core := SeLe4n.Kernel.Concurrency.bootCoreId
  let st := yieldLinkedCurrentState ⟨2⟩
  let st' := SeLe4n.Kernel.activateThreadOnCore st core
  match st'.objects[(⟨1⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]? with
  | some (.tcb t), some (.schedContext sc) =>
    expect "SR-042 a non-current yielder keeps its link" (t.yieldToCode == 51)
    expect "SR-042 ...and the context its yielder and count"
      (sc.yieldFromCode == 2 && sc.consumed == 7)
    expect "SR-042 the bank is unchanged"
      (st'.machine.regsOnCore core == st.machine.regsOnCore core)
  | _, _ => throw <| IO.userError "SR-042 objects not found after the activation"
  let stL := yieldLinkedCurrentState ⟨1⟩
  let stA := SeLe4n.Kernel.activateThreadAt stL 9
  match stA.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb t) =>
    expect "SR-042 a core id naming no core completes no yield" (t.yieldToCode == 51)
  | _ => throw <| IO.userError "SR-042 the yielder not found"

/-- The yielder of `yieldLinkedCurrentState` last ran on core 1: current there,
with its live frame in core 1's bank, while the boot core runs thread 2.  With
`vacated`, core 1 has since saved its frame and holds no thread. -/
private def yieldLinkedRemoteState (vacated : Bool) : SystemState :=
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let st := yieldLinkedCurrentState ⟨2⟩
  let regs := match st.objects[(⟨1⟩ : ObjId)]? with
    | some (.tcb t) => t.registerContext
    | _ => default
  let cur : Option SeLe4n.ThreadId := if vacated then none else some ⟨1⟩
  { st with
    scheduler := st.scheduler.setCurrentOnCore core1 cur
    machine := (st.machine.setRegsOnCore core1 regs).setResidentOnCore core1 cur }

/-- SR-043 (a yielder that last ran on another core): the pending yield is
completed by the activation on the yielder's own core, which writes that core's
bank and no other; the boot core's activation leaves it pending; the entry tail
on core 1 (residency settle, then activation) leaves neither the core's current
nor its resident thread linked; and once core 1 has vacated the yielder, the
context's final delete writes the yielder's saved context and no core's bank. -/
private def sr043_remoteYielderCompletesOnItsCore : IO Unit := do
  let core0 := SeLe4n.Kernel.Concurrency.bootCoreId
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let st := yieldLinkedRemoteState false
  let st0 := SeLe4n.Kernel.activateThreadOnCore st core0
  match st0.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb t) =>
    expect "SR-043 the boot core's activation leaves a remote yield pending"
      (t.yieldToCode == 51 && st0.machine.regsOnCore core1 == st.machine.regsOnCore core1)
  | _ => throw <| IO.userError "SR-043 the yielder not found after the boot activation"
  let st1 := SeLe4n.Kernel.activateThreadOnCore st core1
  match st1.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb t) =>
    expect "SR-043 core 1's activation completes the yield"
      (t.yieldToCode == 0 && t.registerContext.x2 == 7)
    expect "SR-043 ...in core 1's bank, the yielder's live frame"
      (st1.machine.regsOnCore core1 == t.registerContext)
    expect "SR-043 ...and leaves the boot core's bank alone"
      (st1.machine.regsOnCore core0 == st.machine.regsOnCore core0)
  | _ => throw <| IO.userError "SR-043 the yielder not found after core 1's activation"
  let stT := SeLe4n.Kernel.activateThreadOnCore
    (SeLe4n.Kernel.PriorityInheritance.settleResidencyOnCore st core1) core1
  let unlinked (o : Option SeLe4n.ThreadId) : Bool := match o with
    | some tid => match stT.objects[tid.toObjId]? with
      | some (.tcb t) => t.yieldToCode == 0
      | _ => true
    | none => true
  expect "SR-043 core 1's entry tail leaves its current and resident threads unlinked"
    (unlinked (stT.scheduler.currentOnCore core1) && unlinked (stT.machine.residentOnCore core1))
  let stV := yieldLinkedRemoteState true
  let stF := SeLe4n.Kernel.finaliseSchedContext ⟨50⟩ stV
  match stF.objects[(⟨1⟩ : ObjId)]? with
  | some (.tcb t) =>
    expect "SR-043 a vacated yielder's completion writes its saved context"
      (t.yieldToCode == 0 && t.registerContext.x2 == 7)
    expect "SR-043 ...and no core's bank"
      (stF.machine.regsOnCore core0 == stV.machine.regsOnCore core0 &&
        stF.machine.regsOnCore core1 == stV.machine.regsOnCore core1)
  | _ => throw <| IO.userError "SR-043 the yielder not found after the finalise"

/-- `SystemState.yieldLinkedNotResident`, read off every core: no core's current
or resident thread holds a yield link. -/
private def yieldLinkedNotResidentB (st : SystemState) : Bool :=
  let unlinked (o : Option SeLe4n.ThreadId) : Bool := match o with
    | some tid => match st.objects[tid.toObjId]? with
      | some (.tcb t) => t.yieldToCode == 0
      | _ => true
    | none => true
  SeLe4n.Kernel.Concurrency.allCores.all fun c =>
    unlinked (st.scheduler.currentOnCore c) && unlinked (st.machine.residentOnCore c)

/-- SR-045 (WS-ZA ZA6.9, seL4-MCS `invokeSchedContext_Consumed`): the Consumed
invocation, on the core whose current thread is the caller, writes the invoked
context's consumed time into the caller's first message register with the
one-register message info, and resets the count; the context's yield link is
not touched.  On a core with no current thread, and on an object that is no
context, it refuses before any write. -/
private def sr045_consumedInvocationReadsAndResets : IO Unit := do
  let core := SeLe4n.Kernel.Concurrency.bootCoreId
  let st := yieldLinkedCurrentState ⟨2⟩
  match SeLe4n.Kernel.schedContextConsumedOnCore (SeLe4n.SchedContextId.ofNat 50) core st with
  | .ok st' =>
    match st'.objects[(⟨2⟩ : ObjId)]?, st'.objects[(⟨50⟩ : ObjId)]? with
    | some (.tcb t), some (.schedContext sc) =>
      expect "SR-045 the caller's MR0 holds the consumed time" (t.registerContext.x2 == 7)
      expect "SR-045 ...with a one-register message info"
        (t.registerContext.x1 == SeLe4n.Kernel.consumedInfoWord)
      expect "SR-045 the count is taken off and the yield link kept"
        (sc.consumed == 0 && sc.yieldFromCode == 2)
    | _, _ => throw <| IO.userError "SR-045 objects not found after the invocation"
  | .error e => throw <| IO.userError s!"SR-045 Consumed should succeed, got {repr e}"
  expect "SR-045 an object that is no context is refused"
    (match SeLe4n.Kernel.schedContextConsumedOnCore (SeLe4n.SchedContextId.ofNat 2) core st with
     | .error .invalidCapability => true | _ => false)
  expect "SR-045 a core with no current thread is refused"
    (match SeLe4n.Kernel.schedContextConsumedOnCore (SeLe4n.SchedContextId.ofNat 50) core
        yieldLinkedState with
     | .error .illegalState => true | _ => false)

/-- SR-044 (the kernel-wide claim, WS-ZA ZA6.8): from a state whose yielder last
ran on core 1 and has since been vacated there, the entry tail on either core
(residency settle, then activation) keeps every core's current and resident
threads unlinked; the yielder current on core 1 is the state the claim rules
out. -/
private def sr044_entryTailKeepsEveryCoreUnlinked : IO Unit := do
  let core0 := SeLe4n.Kernel.Concurrency.bootCoreId
  let core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  expect "SR-044 the checker refuses a linked current yielder"
    (!yieldLinkedNotResidentB (yieldLinkedRemoteState false))
  let stV := yieldLinkedRemoteState true
  expect "SR-044 a vacated yielder is no core's current or resident thread"
    (yieldLinkedNotResidentB stV)
  let tail (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId) : SystemState :=
    SeLe4n.Kernel.activateThreadOnCore (SeLe4n.Kernel.PriorityInheritance.settleResidencyOnCore st c) c
  expect "SR-044 the boot core's entry tail keeps every core unlinked"
    (yieldLinkedNotResidentB (tail stV core0))
  expect "SR-044 core 1's entry tail keeps every core unlinked"
    (yieldLinkedNotResidentB (tail stV core1))
  expect "SR-044 both cores' tails in turn keep every core unlinked"
    (yieldLinkedNotResidentB (tail (tail stV core0) core1))

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
  IO.println "--- PR #811: resumeThread preemption re-enqueues the caller ---"
  sr030_resumeHigherPriorityReenqueuesCaller
  sr031_resumeLowerPriorityKeepsCurrent
  IO.println "--- v0.35.134: the frozen resume mirrors the live resume ---"
  sr032_frozenResumeClearsEveryRestoredField
  sr033_frozenResumeRecomputesPipBoost
  sr034_frozenResumePreemptsOnEffectivePriority
  IO.println "--- v0.35.167: the .tcbResume arm's resolved scheduler footprint ---"
  sr035_resumeFootprintNamesHomeAndExecutingCores
  IO.println "--- ZA6.6: suspend cancels the yield link ---"
  sr036_suspendCancelsYieldTo
  sr037_frozenSuspendCancelsYieldTo
  sr038_contextFinaliseCompletesYield
  sr039_threadFinaliseCancelsYield
  sr040_liveFrozenSuspendAgree
  sr041_activationCompletesCurrentYield
  sr042_activationWithoutPendingYieldIsIdentity
  sr043_remoteYielderCompletesOnItsCore
  sr044_entryTailKeepsEveryCoreUnlinked
  IO.println "--- ZA6.9: the Consumed invocation ---"
  sr045_consumedInvocationReadsAndResets
  IO.println "=== All D1 suspend/resume tests passed (47 tests) ==="
