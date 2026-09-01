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
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState
import SeLe4n.Model.Builder

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Model

namespace SeLe4n.Testing.FrozenOpsSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"frozen-ops check passed [{label}]"
  else
    throw <| IO.userError s!"frozen-ops check failed [{label}]"

/-- Helper: construct a minimal empty FrozenSystemState. -/
private def emptyFrozenState : FrozenSystemState :=
  SeLe4n.Testing.emptyFrozenSystemState

/-- Helper: construct a test TCB. -/
private def mkTcb (tid : Nat) (prio : Nat := 0) (dom : Nat := 0) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

/-- Helper: construct a FrozenSystemState with given objects. -/
private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  SeLe4n.Testing.frozenStateOf objs

-- ============================================================================
-- Q7-T1: FrozenKernel Monad Tests (FO-001 to FO-003)
-- ============================================================================

/-- FO-001: frozenLookupObject — find existing object -/
private def fo001_lookupExisting : IO Unit := do
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1))]
  match frozenLookupObject ⟨1⟩ fst with
  | .ok (obj, _) => expect "lookup found TCB" (obj.objectType == .tcb)
  | .error _ => throw <| IO.userError "lookup should succeed"

/-- FO-002: frozenLookupObject — missing object returns error -/
private def fo002_lookupMissing : IO Unit := do
  let fst := mkFrozenState []
  match frozenLookupObject ⟨99⟩ fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "missing → objectNotFound" (e == .objectNotFound)

/-- FO-003: frozenStoreObject — update existing TCB -/
private def fo003_storeObject : IO Unit := do
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1))]
  let tcb2 := mkTcb 1 5  -- changed priority
  match frozenStoreObject ⟨1⟩ (.tcb tcb2) fst with
  | .ok ((), fst') =>
      match fst'.objects.get? ⟨1⟩ with
      | some (.tcb t) => expect "updated priority" (t.priority == ⟨5⟩)
      | _ => throw <| IO.userError "should find updated TCB"
      expect "scheduler preserved" ((fst'.scheduler.current) == (fst.scheduler.current))
      expect "machine preserved" (fst'.machine.timer == fst.machine.timer)
  | .error _ => throw <| IO.userError "store should succeed"

-- ============================================================================
-- TPH-005: Frozen IPC Send/Receive
-- ============================================================================

/-- FO-004 (PR #822 review, Codex): frozenEndpointReply requires a resolved Reply
object.  A `blockedOnReply` caller with NO `replyObject` link is rejected
`.replyCapInvalid` — the frozen mirror of the live `.reply` path, which resolves
`reply.caller` and consumes it.  (The success path with a linked Reply object is
FO-004b.) -/
private def fo004_endpointReply : IO Unit := do
  let callerTcb : TCB := { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩) }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ (⟨505⟩ : SeLe4n.ReplyId) msg fst with
  | .ok _ => throw <| IO.userError "reply to a caller with no Reply object must be rejected"
  | .error e => expect "no-reply-object frozen reply → replyCapInvalid" (e == .replyCapInvalid)

/-- FO-004b: frozenEndpointReply consumes the linked Reply object (PR #822
review): a successful reply clears the caller's `replyObject` forward link and
the Reply object's `caller` back-link, mirroring the runtime `consumeCallerReply`
single-use semantics. -/
private def fo004b_endpointReplyConsumesLink : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB := { mkTcb 2 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  -- The replier is a live TCB: the reply's provenance is read from the thread
  -- that composed it, so an unresolvable one is refused (SM9.D audit).
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨3⟩, .tcb (mkTcb 3)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ rid msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb =>
          expect "target unblocked" (tcb.ipcState == .ready)
          expect "forward reply link cleared" (tcb.replyObject == none)
      | none => throw <| IO.userError "target TCB missing"
      match fst'.objects.get? rid.toObjId with
      | some (.reply r) => expect "reply caller back-link consumed" (r.caller == none)
      | _ => throw <| IO.userError "reply object missing/retyped"
  | .error _ => throw <| IO.userError "reply should succeed"

/-- FO-005 (PR #822 review, frozen mirror of E.2 / 6J-lYm): a DELEGATED replier —
NOT the recorded `replyTarget` server (⟨3⟩), but the reply is authorized by the
linked Reply object whose `caller` names the target — now SUCCEEDS.  Authority is
the Reply object, not the recorded replier (a copied/minted reply cap is
delegatable), exactly like the live `.reply` path. -/
private def fo005_replyDelegatedReplier : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  -- ⟨99⟩ is a live thread that is simply *not* the recorded server — which is
  -- what delegation means.  It was absent from the map before, which made the
  -- reply's provenance read the empty default rather than the composer's.
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨99⟩, .tcb (mkTcb 99)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- replier ⟨99⟩ ≠ the recorded server ⟨3⟩, but presents the linked Reply cap (rid).
  match frozenEndpointReply ⟨99⟩ ⟨2⟩ rid msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb => expect "delegated replier delivers (target ready)" (tcb.ipcState == .ready)
      | none => throw <| IO.userError "target TCB missing"
  | .error _ => throw <| IO.userError "delegated replier with a valid linked Reply cap should succeed"

/-- FO-005b (PR #822 review 489): authority is the **presented** reply cap.  A replier
that presents a `replyId` which is NOT the caller's reciprocal forward link (it does
not hold the caller's reply cap) is rejected `.replyCapInvalid`, even though the caller
is `blockedOnReply` with a valid (different) linked Reply object — modelling that a
thread without the reply cap cannot deliver/consume the reply. -/
private def fo005b_replyWrongPresentedCap : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- replier presents ⟨999⟩, NOT the caller's forward link rid (⟨505⟩) → rejected.
  match frozenEndpointReply ⟨99⟩ ⟨2⟩ (⟨999⟩ : SeLe4n.ReplyId) msg fst with
  | .ok _ => throw <| IO.userError "a replier presenting a non-matching reply cap must be rejected"
  | .error e => expect "wrong presented reply cap → replyCapInvalid" (e == .replyCapInvalid)

-- ============================================================================
-- TPH-006: Frozen Scheduler Tick
-- ============================================================================

/-- FO-006: frozenTimerTick — no current thread advances timer -/
private def fo006_timerTickIdle : IO Unit := do
  let fst := { emptyFrozenState with scheduler := { emptyFrozenState.scheduler with current := none } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      expect "timer advanced" (fst'.machine.timer == fst.machine.timer + 1)
      expect "still idle" ((fst'.scheduler.current) == none)
  | .error _ => throw <| IO.userError "timer tick should succeed"

-- ============================================================================
-- TPH-007: Frozen CSpace Lookup (Radix O(1))
-- ============================================================================

/-- FO-007: frozenCspaceLookup — O(1) radix lookup -/
private def fo007_cspaceLookup : IO Unit := do
  -- Create a CNodeRadix with one slot
  let cap : Capability := {
    target := .object ⟨42⟩
    rights := .ofNat 7
    badge := none
  }
  let radix := (CNodeRadix.empty 0 0 4).insert (SeLe4n.Slot.ofNat 3) cap
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  -- Lookup slot 3 (CPtr with value 3)
  match frozenCspaceLookup fst (SeLe4n.CPtr.ofNat 3) ⟨10⟩ with
  | .ok foundCap =>
      expect "found capability" (foundCap.target == .object ⟨42⟩)
  | .error _ => throw <| IO.userError "radix lookup should succeed"

/-- FO-008: frozenCspaceLookup — missing slot returns error -/
private def fo008_cspaceLookupMissing : IO Unit := do
  let radix := CNodeRadix.empty 0 0 4
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  match frozenCspaceLookup fst (SeLe4n.CPtr.ofNat 5) ⟨10⟩ with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "empty slot → invalidCapability" (e == .invalidCapability)

-- ============================================================================
-- TPH-008: Frozen VSpace Resolve
-- ============================================================================

/-- FO-009: frozenVspaceLookup — resolve virtual address -/
private def fo009_vspaceLookup : IO Unit := do
  -- Create a frozen VSpaceRoot with one mapping
  let mappingsRt := (RHTable.empty 16 : RHTable VAddr (PAddr × PagePermissions)).insert
    (SeLe4n.VAddr.ofNat 0x1000) ((SeLe4n.PAddr.ofNat 0x2000), default)
  let vsr : FrozenVSpaceRoot := { asid := ⟨1⟩, mappings := freezeMap mappingsRt }
  let asidRt := (RHTable.empty 16 : RHTable ASID ObjId).insert ⟨1⟩ ⟨20⟩
  let fst := { mkFrozenState [(⟨20⟩, .vspaceRoot vsr)] with
    asidTable := freezeMap asidRt }
  match frozenVspaceLookup ⟨1⟩ (SeLe4n.VAddr.ofNat 0x1000) fst with
  | .ok ((paddr, _perms), _) =>
      expect "resolved paddr" (paddr == (SeLe4n.PAddr.ofNat 0x2000))
  | .error _ => throw <| IO.userError "vspace lookup should succeed"

/-- FO-010: frozenVspaceLookup — unbound ASID returns error -/
private def fo010_vspaceLookupMissing : IO Unit := do
  let fst := emptyFrozenState
  match frozenVspaceLookup ⟨99⟩ (SeLe4n.VAddr.ofNat 0x1000) fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "unbound ASID → asidNotBound" (e == .asidNotBound)

-- ============================================================================
-- TPH-009: Frozen Service Query
-- ============================================================================

/-- FO-011: frozenLookupServiceByCap — find service by endpoint -/
private def fo011_serviceLookup : IO Unit := do
  let reg : ServiceRegistration := {
    sid := ⟨1⟩
    iface := { ifaceId := ⟨1⟩, methodCount := 1, maxMessageSize := 64,
               maxResponseSize := 64, requiresGrant := false }
    endpointCap := { target := .object ⟨42⟩, rights := .ofNat 7, badge := none }
  }
  let regRt := (RHTable.empty 16 : RHTable ServiceId ServiceRegistration).insert ⟨1⟩ reg
  let fst := { emptyFrozenState with serviceRegistry := freezeMap regRt }
  match frozenLookupServiceByCap ⟨42⟩ fst with
  | .ok (found, _) => expect "found service" (found.sid == ⟨1⟩)
  | .error _ => throw <| IO.userError "service lookup should succeed"

/-- FO-012: frozenLookupServiceByCap — missing service returns error -/
private def fo012_serviceLookupMissing : IO Unit := do
  let fst := emptyFrozenState
  match frozenLookupServiceByCap ⟨99⟩ fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "missing → objectNotFound" (e == .objectNotFound)

-- ============================================================================
-- TPH-013: Delete in Frozen (CSpace)
-- ============================================================================

/-- FO-013: frozenCspaceDelete — erase slot from frozen CNode -/
private def fo013_cspaceDelete : IO Unit := do
  let cap : Capability := { target := .object ⟨42⟩, rights := .ofNat 7, badge := none }
  let radix := (CNodeRadix.empty 0 0 4).insert (SeLe4n.Slot.ofNat 3) cap
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  match frozenCspaceDelete ⟨10⟩ (SeLe4n.Slot.ofNat 3) fst with
  | .ok ((), fst') =>
      -- After delete, lookup should fail
      match frozenCspaceLookup fst' (SeLe4n.CPtr.ofNat 3) ⟨10⟩ with
      | .ok _ => throw <| IO.userError "deleted slot should be empty"
      | .error e => expect "deleted → invalidCapability" (e == .invalidCapability)
  | .error _ => throw <| IO.userError "delete should succeed"

-- ============================================================================
-- TPH-014: Notification Signal/Wait
-- ============================================================================

/-- FO-014: frozenNotificationSignal — accumulate badge on idle notification -/
private def fo014_notificationSignal : IO Unit := do
  let ntfn : Notification := { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  -- The signaller is a live TCB: the badge's provenance is read from it, so an
  -- unresolvable one is refused rather than defaulted or invented (SM9.D audit).
  let fst := mkFrozenState [(⟨5⟩, .notification ntfn), (⟨3⟩, .tcb (mkTcb 3))]
  match frozenNotificationSignal ⟨5⟩ ⟨3⟩ (Badge.ofNatMasked 0xFF) fst with
  | .ok ((), fst') =>
      match fst'.objects.get? ⟨5⟩ with
      | some (.notification ntfn') =>
          expect "state is active" (ntfn'.state == .active)
          expect "badge accumulated" (ntfn'.pendingBadge.isSome)
      | _ => throw <| IO.userError "notification should exist"
  | .error _ => throw <| IO.userError "signal should succeed"

/-- FO-015: frozenNotificationWait — consume pending badge -/
private def fo015_notificationWait : IO Unit := do
  let ntfn : Notification := { state := .active, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := some (Badge.ofNatMasked 42) }
  let waiterTcb := mkTcb 2
  let fst := mkFrozenState [(⟨5⟩, .notification ntfn), (⟨2⟩, .tcb waiterTcb)]
  match frozenNotificationWait ⟨5⟩ ⟨2⟩ fst with
  | .ok (badge, _fst') =>
      expect "badge consumed" (badge == some (Badge.ofNatMasked 42))
  | .error _ => throw <| IO.userError "wait should succeed"

-- ============================================================================
-- T7-D/F: Frozen IPC Queue Enqueue Tests (M-FRZ-1/2/3 validation, L-P01)
-- ============================================================================

/-- FO-016: frozenEndpointSend — no receiver, sender is enqueued in sendQ (M-FRZ-1) -/
private def fo016_sendEnqueuesSender : IO Unit := do
  let senderTcb := mkTcb 3
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨3⟩, .tcb senderTcb), (⟨10⟩, .endpoint ep)]
  let msg : IpcMessage := { registers := #[⟨42⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg fst with
  | .ok ((), fst') =>
      -- Verify sender TCB is now blockedOnSend
      match frozenLookupTcb fst' ⟨3⟩ with
      | some tcb =>
          expect "sender blockedOnSend" (tcb.ipcState == .blockedOnSend ⟨10⟩)
          expect "sender has pending message" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "sender TCB missing"
      -- Verify endpoint sendQ has the sender enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "sendQ head is sender" (ep'.sendQ.head == some ⟨3⟩)
          expect "sendQ tail is sender" (ep'.sendQ.tail == some ⟨3⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"send should succeed, got: {reprStr e}"

/-- FO-017: frozenEndpointReceive — no sender, receiver is enqueued in receiveQ (M-FRZ-2) -/
private def fo017_receiveEnqueuesReceiver : IO Unit := do
  let recvTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨4⟩, .tcb recvTcb), (⟨10⟩, .endpoint ep)]
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fst with
  | .ok (_, fst') =>
      -- Verify receiver TCB is now blockedOnReceive
      match frozenLookupTcb fst' ⟨4⟩ with
      | some tcb =>
          expect "receiver blockedOnReceive" (tcb.ipcState == .blockedOnReceive ⟨10⟩)
      | none => throw <| IO.userError "receiver TCB missing"
      -- Verify endpoint receiveQ has the receiver enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "receiveQ head is receiver" (ep'.receiveQ.head == some ⟨4⟩)
          expect "receiveQ tail is receiver" (ep'.receiveQ.tail == some ⟨4⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"receive should succeed, got: {reprStr e}"

/-- FO-018: frozenEndpointCall — no receiver, caller enqueued in sendQ with blockedOnCall (M-FRZ-3) -/
private def fo018_callEnqueuesCaller : IO Unit := do
  let callerTcb := mkTcb 5
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨5⟩, .tcb callerTcb), (⟨10⟩, .endpoint ep)]
  let msg : IpcMessage := { registers := #[⟨99⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointCall ⟨10⟩ ⟨5⟩ msg fst with
  | .ok ((), fst') =>
      -- Verify caller TCB is now blockedOnCall
      match frozenLookupTcb fst' ⟨5⟩ with
      | some tcb =>
          expect "caller blockedOnCall" (tcb.ipcState == .blockedOnCall ⟨10⟩)
          expect "caller has pending message" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "caller TCB missing"
      -- Verify endpoint sendQ has the caller enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "sendQ head is caller" (ep'.sendQ.head == some ⟨5⟩)
          expect "sendQ tail is caller" (ep'.sendQ.tail == some ⟨5⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"call should succeed, got: {reprStr e}"

/-- FO-019: frozenSchedule — select highest-priority thread as current (T7-D) -/
private def fo019_frozenSchedule : IO Unit := do
  let tid1 : ThreadId := ⟨1⟩
  let tid2 : ThreadId := ⟨2⟩
  let tcb1 := mkTcb 1 10  -- priority 10
  let tcb2 := mkTcb 2 50  -- priority 50 (higher)
  let objs := [(⟨1⟩, FrozenKernelObject.tcb tcb1), (⟨2⟩, FrozenKernelObject.tcb tcb2)]
  let objsMap := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  -- Set up scheduler with both threads by priority
  let byPrio := RHTable.empty 16
    |>.insert ⟨10⟩ [tid1]
    |>.insert ⟨50⟩ [tid2]
  let threadPrio := RHTable.empty 16
    |>.insert tid1 ⟨10⟩
    |>.insert tid2 ⟨50⟩
  let membership := RHTable.empty 16
    |>.insert tid1 ()
    |>.insert tid2 ()
  let st0 : FrozenSystemState := { emptyFrozenState with
    objects := freezeMap objsMap
    scheduler := { emptyFrozenState.scheduler with
      byPriority := freezeMap byPrio
      threadPriority := freezeMap threadPrio
      membership := freezeMap membership
      current := none
    }
  }
  match frozenSchedule st0 with
  | .ok (_, st1) =>
    expect "frozenSchedule selects highest priority" ((st1.scheduler.current) == some tid2)
    IO.println "frozen-ops check passed [FO-019: frozenSchedule]"
  | .error e => throw <| IO.userError s!"frozenSchedule failed: {reprStr e}"

/-- FO-020: frozenCspaceMint — insert cap into frozen CNode slot (T7-D) -/
private def fo020_frozenCspaceMint : IO Unit := do
  let cnodeId : ObjId := ⟨10⟩
  let epId : ObjId := ⟨11⟩
  -- Build a frozen CNode with an empty CNodeRadix (flat array)
  let radix := CNodeRadix.empty 0 0 4
  let frozenCNode : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let objs := [(cnodeId, FrozenKernelObject.cnode frozenCNode), (epId, FrozenKernelObject.endpoint {})]
  let objsMap := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  let st0 : FrozenSystemState := { emptyFrozenState with objects := freezeMap objsMap }
  let testCap : Capability := { target := .object epId, rights := .ofNat 7, badge := none }
  match frozenCspaceMint cnodeId (SeLe4n.Slot.ofNat 0) testCap st0 with
  | .ok ((), st1) =>
    -- Verify slot 0 now has the cap
    match frozenCspaceLookup st1 (SeLe4n.CPtr.ofNat 0) cnodeId with
    | .ok cap =>
      expect "frozenCspaceMint inserts cap" (cap.target == .object epId)
      IO.println "frozen-ops check passed [FO-020: frozenCspaceMint]"
    | .error e => throw <| IO.userError s!"lookup after mint failed: {reprStr e}"
  | .error e => throw <| IO.userError s!"frozenCspaceMint failed: {reprStr e}"

/-- FO-021: U-H01 regression — popped thread can be re-enqueued (multi-round IPC).
After frozenQueuePopHead, queuePPrev must be cleared so frozenQueuePushTail
does not reject the thread with `.illegalState`. This test exercises:
send (enqueue sender in sendQ) → receive (pop sender, deliver) → send again. -/
private def fo021_popThenPushRegression : IO Unit := do
  let senderTcb := mkTcb 3
  let receiverTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [
    (⟨3⟩, .tcb senderTcb),
    (⟨4⟩, .tcb receiverTcb),
    (⟨10⟩, .endpoint ep)
  ]
  let msg1 : IpcMessage := { registers := #[⟨42⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  -- Round 1: sender sends (no receiver waiting → enqueued in sendQ)
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg1 fst with
  | .error e => throw <| IO.userError s!"round1 send failed: {reprStr e}"
  | .ok ((), fst1) =>
  -- Round 1: receiver receives (pops sender from sendQ, delivers message)
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fst1 with
  | .error e => throw <| IO.userError s!"round1 receive failed: {reprStr e}"
  | .ok (_, fst2) =>
  -- Verify sender was popped and queue links cleared (including queuePPrev)
  match frozenLookupTcb fst2 ⟨3⟩ with
  | none => throw <| IO.userError "sender TCB missing after receive"
  | some tcb =>
      expect "sender queuePrev cleared" (tcb.queuePrev == none)
      expect "sender queueNext cleared" (tcb.queueNext == none)
      expect "sender queuePPrev cleared" (tcb.queuePPrev == none)
  -- Round 2: sender sends again (re-enqueue — must not fail with illegalState)
  let msg2 : IpcMessage := { registers := #[⟨99⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg2 fst2 with
  | .error e => throw <| IO.userError s!"round2 re-send failed (U-H01 regression): {reprStr e}"
  | .ok ((), fst3) =>
  -- Verify sender is enqueued again
  match frozenLookupTcb fst3 ⟨3⟩ with
  | none => throw <| IO.userError "sender TCB missing after re-send"
  | some tcb =>
      expect "sender re-enqueued (blockedOnSend)" (tcb.ipcState == .blockedOnSend ⟨10⟩)
      expect "sender has queuePPrev after re-enqueue" (tcb.queuePPrev.isSome)
  IO.println "frozen-ops check passed [FO-021: U-H01 pop-then-push regression]"

/-- FO-022: provenance follows content through the frozen operations.

`FrozenSystemState.declassificationTaint` is required precisely so a snapshot
can be analysed for laundering chains, and preserving it across `freeze` buys
that only for the instant of the freeze.  These assertions are the ones that
fail if the frozen operations go back to carrying the table through unchanged:
each measures a *specific* identity reaching a thread that never held it, plus
the negative that says the transport does not keep what it handed on. -/
private def frozenProvenanceFollowsContent : IO Unit := do
  let senderTcb := mkTcb 3
  let receiverTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let ntfn : Notification := { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
                               pendingBadge := none }
  let base := mkFrozenState [
    (⟨3⟩, .tcb senderTcb), (⟨4⟩, .tcb receiverTcb),
    (⟨10⟩, .endpoint ep), (⟨5⟩, .notification ntfn)
  ]
  -- Tag the sender with one identity, so the assertions below name a tag that
  -- exists nowhere else in the snapshot.
  let tagged : FrozenSystemState :=
    { base with declassificationTaint :=
        base.declassificationTaint.joinAt ⟨3⟩ (SeLe4n.Kernel.DeclassificationTaint.singleton 77) }
  expect "FO-022: the receiver starts untainted"
    (!((tagged.declassificationTaint ⟨4⟩).contains 77))
  -- A parked send followed by a receive moves the message; the provenance must
  -- move with it.
  let msg : IpcMessage := { registers := #[⟨7⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg tagged with
  | .error e => throw <| IO.userError s!"FO-022 send failed: {reprStr e}"
  | .ok ((), fstSend) =>
  expect "FO-022: a parked send leaves the message in the sender, so nothing propagates"
    (!((fstSend.declassificationTaint ⟨4⟩).contains 77))
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstSend with
  | .error e => throw <| IO.userError s!"FO-022 receive failed: {reprStr e}"
  | .ok (_, fstRecv) =>
  expect "FO-022: the receiver inherits the sender's provenance with the message"
    ((fstRecv.declassificationTaint ⟨4⟩).contains 77)
  -- A notification stores the signaller's provenance, and a wait moves it to the
  -- waiter and leaves the transport carrying none.
  match frozenNotificationSignal ⟨5⟩ ⟨3⟩ (Badge.ofNatMasked 0xFF) tagged with
  | .error e => throw <| IO.userError s!"FO-022 signal failed: {reprStr e}"
  | .ok ((), fstSig) =>
  expect "FO-022: a stored badge carries the signaller's provenance"
    ((fstSig.declassificationTaint ⟨5⟩).contains 77)
  match frozenNotificationWait ⟨5⟩ ⟨4⟩ fstSig with
  | .error e => throw <| IO.userError s!"FO-022 wait failed: {reprStr e}"
  | .ok (_, fstWait) =>
  expect "FO-022: the waiter inherits the badge's provenance"
    ((fstWait.declassificationTaint ⟨4⟩).contains 77)
  expect "FO-022: NEGATIVE — the consumed notification keeps none of it"
    (!((fstWait.declassificationTaint ⟨5⟩).contains 77))
  IO.println "frozen-ops check passed [FO-022: provenance follows frozen content]"

/-- FO-023 (PR #873 round 11): the two ways a frozen operation could claim a
delivery it had not made.

Both were surfaced by the provenance carriage rather than caused by it — the
taint flow asserts that content reached somewhere, which is only honest if the
content is actually there and its source is actually readable. -/
private def frozenDeliveryIsHonest : IO Unit := do
  -- (a) A signalled waiter receives the BADGE, not just the wake.  This branch
  -- cleared `pendingBadge` and readied the waiter while storing no message, so
  -- the badge vanished — while the flow below recorded it as delivered.
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let base := mkFrozenState
    [(⟨4⟩, .tcb (mkTcb 4)), (⟨6⟩, .tcb (mkTcb 6)), (⟨5⟩, .notification ntfn)]
  -- Wait first, so the signal below takes the *waiter* branch.
  match frozenNotificationWait ⟨5⟩ ⟨4⟩ base with
  | .error e => throw <| IO.userError s!"FO-023 wait failed: {reprStr e}"
  | .ok (_, fstWaiting) =>
  match frozenNotificationSignal ⟨5⟩ ⟨6⟩ (Badge.ofNatMasked 42) fstWaiting with
  | .error e => throw <| IO.userError s!"FO-023 signal failed: {reprStr e}"
  | .ok (_, fstSig) =>
  expect "FO-023: the signalled waiter is handed the badge, not only woken"
    (match frozenLookupTcb fstSig ⟨4⟩ with
     | some wt => match wt.pendingMessage with
                  | some m => m.badge == some (Badge.ofNatMasked 42)
                  | none => false
     | none => false)
  expect "FO-023: the notification is left holding none of it"
    (match fstSig.objects.get? ⟨5⟩ with
     | some (.notification n) => n.pendingBadge == none
     | _ => false)
  -- (b) A reply whose composing thread cannot be resolved is REFUSED rather
  -- than reading the total table's empty default and silently under-tagging.
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let fstRep := mkFrozenState [(⟨2⟩, .tcb callerTcb), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  expect "FO-023: an unresolvable reply source is refused, not defaulted"
    (match frozenEndpointReply ⟨99⟩ ⟨2⟩ rid msg fstRep with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- (c) The same for a signal's source, which has one failure mode more: an id
  -- naming a live NON-TCB object would read that object's provenance, so the
  -- snapshot could report a predecessor the badge never had.  Losing a link
  -- makes the analysis miss a chain; inventing one makes it name a false origin.
  let idle : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let other : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let fstSg := mkFrozenState [(⟨5⟩, .notification idle), (⟨8⟩, .notification other)]
  expect "FO-023: an absent signaller is refused, not defaulted"
    (match frozenNotificationSignal ⟨5⟩ ⟨7⟩ (Badge.ofNatMasked 9) fstSg with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  expect "FO-023: a signaller naming a live non-TCB object cannot invent a predecessor"
    (match frozenNotificationSignal ⟨5⟩ ⟨8⟩ (Badge.ofNatMasked 9) fstSg with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- (d) …and the send's source, on BOTH orderings.  The blocking path always
  -- resolved the sender; the rendezvous path did not, so whether a nonexistent
  -- sender was refused depended on whether a receiver happened to be waiting.
  let epEmpty : Endpoint := { sendQ := {}, receiveQ := {} }
  let fstNoRecv := mkFrozenState [(⟨10⟩, .endpoint epEmpty)]
  let sendMsg : IpcMessage :=
    { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  expect "FO-023: an absent sender is refused with no receiver waiting"
    (match frozenEndpointSend ⟨10⟩ ⟨77⟩ sendMsg fstNoRecv with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- Same sender, same endpoint, but now a receiver is queued — the ordering
  -- that used to accept it.
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none (mkFrozenState
      [(⟨10⟩, .endpoint epEmpty), (⟨4⟩, .tcb (mkTcb 4))]) with
  | .error _ =>
      -- A receive with no sender blocks the receiver; that is the state we want.
      throw <| IO.userError "FO-023: parking a receiver should succeed"
  | .ok (_, fstWithRecv) =>
    expect "FO-023: an absent sender is refused at a rendezvous too, not only when blocking"
      (match frozenEndpointSend ⟨10⟩ ⟨77⟩ sendMsg fstWithRecv with
       | .ok _ => false
       | .error e => e == .objectNotFound)
  IO.println "frozen-ops check passed [FO-023: a frozen delivery is honest]"

/-- FO-024 (PR #873 round 7): **a parked sender with no message is refused, not
dequeued.**

`frozenQueuePopHead` validated the head's blocking *state* and nothing else, so a
`.blockedOnSend` head carrying `pendingMessage := none` was accepted;
`frozenEndpointReceive` then stored that `none` in the receiver and still joined
the sender's provenance, inventing a causal predecessor for content that was
never delivered.

The state is malformed rather than reachable — the frozen send path parks with
`pendingMessage := some msg` — which is exactly why it has to be refused
structurally: a hand-built snapshot is what a frozen state IS. -/
private def frozenParkedSenderCarriesItsMessage : IO Unit := do
  let epParked : Endpoint := { sendQ := { head := some ⟨3⟩, tail := some ⟨3⟩ }, receiveQ := {} }
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- The malformed snapshot: parked to send, holding nothing.
  let fstEmpty := mkFrozenState
    [(⟨10⟩, .endpoint epParked),
     (⟨3⟩, .tcb { mkTcb 3 with ipcState := .blockedOnSend ⟨10⟩, pendingMessage := none }),
     (⟨4⟩, .tcb (mkTcb 4))]
  expect "FO-024: a message-less parked sender is refused rather than dequeued"
    (match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstEmpty with
     | .ok _ => false
     | .error e => e == .endpointStateMismatch)
  -- NEGATIVE, load-bearing: the SAME queue shape with a message succeeds and
  -- delivers, so the refusal above is about the missing message and not about
  -- the hand-built queue.
  let fstFull := mkFrozenState
    [(⟨10⟩, .endpoint epParked),
     (⟨3⟩, .tcb { mkTcb 3 with ipcState := .blockedOnSend ⟨10⟩, pendingMessage := some msg }),
     (⟨4⟩, .tcb (mkTcb 4))]
  expect "FO-024: the same shape WITH a message still delivers"
    (match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstFull with
     | .error _ => false
     | .ok (_, fst') =>
       match frozenLookupTcb fst' ⟨4⟩ with
       | some recvTcb => recvTcb.pendingMessage.isSome
       | none => false)
  IO.println "frozen-ops check passed [FO-024: a parked sender carries its message]"

/-- FO-025 (PR #873 round 8): **the frozen signal honours bound delivery.**

With no ordinary waiter and a bound TCB parked on an endpoint, the live
`notificationSignalBound` dequeues that TCB and delivers the badge into its
`pendingMessage`.  The frozen path fell through to the storage branch instead:
the bound thread stayed blocked, the badge sat on the notification, and — once
SM9.D landed — the signaller's provenance was recorded on the notification rather
than on the thread that was supposed to receive the content.

Delivery and provenance are separate ways to get this wrong, so both are
asserted, together with the negative that says the storage branch did *not*
run. -/
private def frozenBoundNotificationDelivery : IO Unit := do
  let epId      : SeLe4n.ObjId := ⟨40⟩
  let notifId   : SeLe4n.ObjId := ⟨41⟩
  let bound     : SeLe4n.ThreadId := ⟨42⟩
  let signaller : SeLe4n.ThreadId := ⟨43⟩
  let badge := Badge.ofNatMasked 77
  -- The bound TCB is parked on the endpoint's receive queue, and the
  -- notification has no ordinary waiter — the live bound-delivery shape.
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some bound, tail := some bound } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some bound }
  let boundTcb : TCB :=
    { mkTcb 42 with ipcState := .blockedOnReceive epId, queuePPrev := some .endpointHead }
  let fst := mkFrozenState
    [(epId, .endpoint ep),
     (notifId, .notification ntfn),
     (⟨42⟩, .tcb boundTcb),
     (⟨43⟩, .tcb (mkTcb 43))]
  match frozenNotificationSignal notifId signaller badge fst with
  | .error _ => throw <| IO.userError "FO-025: bound delivery should succeed"
  | .ok ((), fst') =>
    expect "FO-025: the badge is delivered into the bound thread's pendingMessage"
      (match frozenLookupTcb fst' bound with
       | some t => (t.pendingMessage.bind (·.badge)) == some badge
       | none => false)
    expect "FO-025: the bound thread is unblocked and off the endpoint queue"
      ((match frozenLookupTcb fst' bound with
        | some t => decide (t.ipcState = .ready) && t.queuePPrev.isNone
        | none => false) &&
       (match fst'.objects.get? epId with
        | some (.endpoint e) => e.receiveQ.head.isNone
        | _ => false))
    -- NEGATIVE, load-bearing: the storage branch did NOT run.  If it had, the
    -- badge would sit on the notification and the provenance with it — which is
    -- exactly the state this cut replaced.
    expect "FO-025: NEGATIVE — the badge was not stored on the notification"
      (match fst'.objects.get? notifId with
       | some (.notification n) => n.pendingBadge.isNone
       | _ => false)
    expect "FO-025: the provenance follows the badge to the bound thread"
      ((fst'.declassificationTaint bound.toObjId) ==
        (fst.declassificationTaint signaller.toObjId).join
          (fst.declassificationTaint bound.toObjId))
  IO.println "frozen-ops check passed [FO-025: frozen bound notification delivery]"

/-! ## Frozen/live differential agreement

Every scenario above this point runs the frozen operation **alone**, asserting
against what its author read in the live transition and wrote into a comment.
That is how five separate divergences reached review: the frozen operation was
green the whole time, because nothing ever ran the transition it claims to
mirror.

These scenarios run both.  One `IntermediateState` is built, the live transition
runs on `ist.state`, the frozen one on `freeze ist`, and
`frozenRunAgrees` compares the results — the same refusal, or two successes
whose object stores, taint tables and current thread agree.  Naming the wrong
counterpart fails here too, because the comparison is against the transition
actually called; `fo033` pins exactly that. -/

/-- The shared fixture: one endpoint, one notification bound to a receiver, two
threads.  Small enough to read, and containing every kind the recorded
divergences touched. -/
private def diffTcb (n : Nat) : TCB :=
  { tid := ⟨n⟩, priority := ⟨0⟩, domain := ⟨0⟩, cspaceRoot := ⟨64⟩,
    vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

private def diffEpId    : SeLe4n.ObjId := ⟨60⟩
private def diffNotifId : SeLe4n.ObjId := ⟨61⟩
private def diffA       : SeLe4n.ThreadId := ⟨62⟩
private def diffB       : SeLe4n.ThreadId := ⟨63⟩
private def diffCnId    : SeLe4n.ObjId := ⟨64⟩

/-- The actors share one CSpace root holding the operand capability at slot 0.

Without it the live side resolves no operand — `contentFlowEdges` goes through
`syscallOperandCap?`, which reads the caller's CSpace — so its taint plan is
empty and the provenance step compares as a no-op against a frozen operation
that performs one.  The scenarios would then agree only because every taint was
empty, which is agreement about nothing. -/
private def diffAddCSpace (ist : IntermediateState)
    (caps : List (SeLe4n.Slot × Capability)) : IntermediateState :=
  Builder.createObject ist diffCnId
    (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
              slots := SeLe4n.UniqueSlotMap.ofListWF caps })
    (fun _ h => by cases h; exact (SeLe4n.UniqueSlotMap.ofListWF caps).hWF)
    (fun _ h => nomatch h)

/-- The capability naming `oid`, as an actor's CSpace would hold it. -/
private def diffObjCap (oid : SeLe4n.ObjId) : Capability :=
  { target := .object oid,
    rights := AccessRightSet.ofList [.read, .write, .grant], badge := none }

/-! The three adders below take the object's *structure* rather than a
`KernelObject`, so the builder's CNode-slot and VSpace-mapping obligations are
discharged by `nomatch` on a literal constructor.  A list of `KernelObject`s
could not do that: the obligations quantify over a value the fold cannot see
into. -/

/-- Create the TCB **and** put it in the run queue.

Every thread in these scenarios is one that had been runnable and then blocked
or is about to be woken, which is the only way a live state reaches these
shapes.  Building them outside the run queue would model a state the live kernel
cannot produce — and would hide exactly what these scenarios are for, since a
wake's run-queue insert has nothing to insert into. -/
private def diffAddTcb (ist : IntermediateState) (t : TCB) : IntermediateState :=
  let withObj := Builder.createObject ist t.tid.toObjId (.tcb t)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  -- Only a `.ready` thread is in the run queue: a blocked one left it when it
  -- blocked, which is what makes the wake paths' re-insert observable.  Queuing
  -- blocked threads too would put the bucket in the state the wake wants to
  -- reach and hide whether the transition got it there.
  if t.ipcState == .ready then Builder.markRunnable withObj t.tid t.priority
  else withObj

private def diffAddEndpoint (ist : IntermediateState) (id : SeLe4n.ObjId) (e : Endpoint) :
    IntermediateState :=
  Builder.createObject ist id (.endpoint e) (fun _ h => nomatch h) (fun _ h => nomatch h)

private def diffAddNotification (ist : IntermediateState) (id : SeLe4n.ObjId)
    (n : Notification) : IntermediateState :=
  Builder.createObject ist id (.notification n) (fun _ h => nomatch h) (fun _ h => nomatch h)

private def diffAddReply (ist : IntermediateState) (rid : SeLe4n.ReplyId)
    (r : SeLe4n.Kernel.Reply) : IntermediateState :=
  Builder.createObject ist rid.toObjId (.reply r) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-! ### Comparing like layers

A frozen operation is the syscall, not the bare transition: with no dispatcher in
the frozen phase it applies the provenance step inline, while the live kernel
applies it afterwards at the seam (`applySyscallTaint` in `dispatchSyscall*`).
Comparing a frozen operation against a bare live transition therefore compares
two different layers — and passes only while every taint is empty, which is
exactly what `mkEmptyIntermediateState` gives.  It would have started failing on
the first realistic tagged input, and reported the harness rather than the
kernel.

`liveWithTaint` composes the missing half, so both sides are the syscall.  The
tagged fixture below makes the comparison non-vacuous: with the actor carrying
provenance, an omitted or misdirected taint step changes the result. -/

/-- The decoded operands the taint plan reads, for a scenario driving `sid`. -/
private def diffDecoded (sid : SyscallId) (capAddr : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 0)
    : SyscallDecodeResult :=
  { capAddr := capAddr, msgInfo := { label := 0, length := 0, extraCaps := 0 }, syscallId := sid }

/-- The live transition **plus** the provenance step the seam applies after it —
the whole of what the frozen operation does in one call. -/
private def liveWithTaint {α : Type} (sid : SyscallId) (actor : SeLe4n.ThreadId)
    (capAddr : SeLe4n.CPtr) (run : SystemState → Except KernelError (α × SystemState))
    (st : SystemState) : Except KernelError (α × SystemState) :=
  match run st with
  | .error e => .error e
  | .ok (a, post) =>
      .ok (a, SeLe4n.Kernel.applySyscallTaint
                (SeLe4n.Kernel.syscallTaintPlan st actor (diffDecoded sid capAddr)) st post)

/-- FO-026: the signal, against the live entry the `.notificationSignal` arm
runs.  A notification with no ordinary waiter and a bound TCB parked on an
endpoint — the shape whose frozen handling diverged twice. -/
private def differentialNotificationSignalAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep) diffNotifId ntfn) boundTcb) (diffTcb 63)
  -- Control (the FO-031 discipline): both sides really deliver, so the
  -- agreement below is about a delivered signal rather than a shared refusal.
  expect "FO-026 control: the live bound-aware signal succeeds (not a shared refusal)"
    (SeLe4n.Kernel.notificationSignalBound diffNotifId badge ist.state).toOption.isSome
  expect "FO-026 control: and so does the frozen one"
    (frozenNotificationSignal diffNotifId diffB badge (freeze ist)).toOption.isSome
  expect "FO-026: the frozen signal agrees with the live bound-aware signal"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))

/-- FO-027: the wait, against `notificationWait`.  A notification holding a badge
so the consuming branch runs rather than the blocking one. -/
private def differentialNotificationWaitAgrees : IO Unit := do
  let ntfn : Notification :=
    { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := some (SeLe4n.Badge.ofNatMasked 9) }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) (diffTcb 62)
  -- Control: the badge really is consumed on both sides.
  expect "FO-027 control: the live wait succeeds (not a shared refusal)"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-027 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-027: the frozen wait agrees with the live wait"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-028: the send, against `endpointSendDual`, with no receiver waiting — the
parking branch, whose frozen mirror grew the message-presence guard. -/
private def differentialEndpointSendAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨5⟩], caps := #[], badge := none }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId {}) (diffTcb 62)) (diffTcb 63)
  -- Control: the send really parks on both sides.
  expect "FO-028 control: the live send succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointSendDual diffEpId diffA msg ist.state).toOption.isSome
  expect "FO-028 control: and so does the frozen one"
    (frozenEndpointSend diffEpId diffA msg (freeze ist)).toOption.isSome
  expect "FO-028: the frozen send agrees with the live send"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId diffA msg (freeze ist))
      (liveWithTaint .send diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId diffA msg) ist.state))

/-- FO-038: the wait, against `notificationWait`, with nothing pending — the
idle park.  The waiter goes in already holding a collected `pendingMessage`,
so the scenario pins the atomic clear the live path performs at the block:
before the mirror fix the frozen side parked the waiter still holding the
message, a live/frozen divergence on the mirror's own content channel
(PR #886 review). -/
private def differentialNotificationWaitParksAgrees : IO Unit := do
  let held : IpcMessage := { registers := #[⟨11⟩], caps := #[], badge := none }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := none }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) { diffTcb 62 with pendingMessage := some held }
  -- Control: the wait really parks on both sides (no shared refusal).
  expect "FO-038 control: the live wait parks (not a shared refusal)"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-038 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-038: the frozen idle park agrees with the live one"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-029: the receive, against `endpointReceiveDual`, dequeuing a parked
sender that carries its message — the rendezvous the round-11 guard admits. -/
private def differentialEndpointReceiveAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨7⟩], caps := #[], badge := none }
  let ep : Endpoint := { sendQ := { head := some diffA, tail := some diffA }, receiveQ := {} }
  let parked : TCB := { diffTcb 62 with ipcState := .blockedOnSend diffEpId, pendingMessage := some msg, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parked) (diffTcb 63)
  -- Control: the rendezvous really completes on both sides.
  expect "FO-029 control: the live receive succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none ist.state).toOption.isSome
  expect "FO-029 control: and so does the frozen one"
    (frozenEndpointReceive diffEpId diffB none (freeze ist)).toOption.isSome
  expect "FO-029: the frozen receive agrees with the live receive"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB none (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none) ist.state))

/-- FO-030: the call, against `endpointCall`, with no receiver — the parking
branch again, on the arm that also stages a reply. -/
private def differentialEndpointCallAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨11⟩], caps := #[], badge := none }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId {}) (diffTcb 62)) (diffTcb 63)
  -- Control: the call really parks on both sides.
  expect "FO-030 control: the live call succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointCall diffEpId diffA msg ist.state).toOption.isSome
  expect "FO-030 control: and so does the frozen one"
    (frozenEndpointCall diffEpId diffA msg (freeze ist)).toOption.isSome
  expect "FO-030: the frozen call agrees with the live call"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointCall diffEpId diffA msg (freeze ist))
      (liveWithTaint .call diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointCall diffEpId diffA msg) ist.state))

/-- FO-031: the reply, against `endpointReply`, delivering to a caller parked in
`.blockedOnCall`. -/
private def differentialEndpointReplyAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨13⟩], caps := #[], badge := none }
  -- The reply's authority is the presented reply capability, so the fixture has
  -- to carry the whole link: the target parked in `.blockedOnReply` with its
  -- forward `replyObject`, and a Reply object naming it back.  Without those
  -- both sides refuse with `.replyCapInvalid` and the comparison passes without
  -- ever running a reply — a check that agrees because nothing happened.
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let caller : TCB := { diffTcb 62 with ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) (diffTcb 63))
    rid { replyId := rid, caller := some diffA }
  -- Control: the reply really happens on both sides, so the agreement below is
  -- about a delivered reply rather than a shared refusal.
  expect "FO-031 control: the live reply succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointReply diffB diffA msg ist.state).toOption.isSome
  expect "FO-031 control: and so does the frozen one"
    (frozenEndpointReply diffB diffA rid msg (freeze ist)).toOption.isSome
  expect "FO-031: the frozen reply agrees with the live reply"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReply diffB diffA rid msg (freeze ist))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReply diffB diffA msg) ist.state))

/-- FO-035: **a receive that dequeues a `.blockedOnCall` caller** (PR #873
round 17).

`frozenQueuePopHead` accepts a `.blockedOnCall` head as well as a
`.blockedOnSend` one, and the frozen receive woke both -- `.ready`, back in the
run queue.  A caller does not become runnable at rendezvous: the live
`endpointReceiveDual` moves it to `.blockedOnReply` and links it to the
server-supplied reply object.  The branch was unreachable from the suite because
FO-029's queued sender is `.blockedOnSend`, and the coverage row said `.receive`
was checked.

The control asserts both sides succeed, so the agreement is about a completed
rendezvous rather than a shared refusal. -/
private def differentialReceiveFromBlockedCallerAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨21⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨506⟩
  let ep : Endpoint := { sendQ := { head := some diffA, tail := some diffA }, receiveQ := {} }
  let parkedCaller : TCB := { diffTcb 62 with ipcState := .blockedOnCall diffEpId, pendingMessage := some msg, queuePPrev := some .endpointHead }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedCaller) (diffTcb 63))
    rid { replyId := rid, caller := none }
  expect "FO-035 control: the live receive completes the call rendezvous"
    (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB (some rid) ist.state).toOption.isSome
  expect "FO-035 control: and so does the frozen one"
    (frozenEndpointReceive diffEpId diffB (some rid) (freeze ist)).toOption.isSome
  expect "FO-035: the dequeued caller is parked for reply, not woken"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB (some rid) (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB (some rid)) ist.state))
  -- And the fail-closed half: a call rendezvous with no reply object must be
  -- refused on both sides rather than stranding the caller `.blockedOnReply`.
  expect "FO-035: both refuse a call rendezvous carrying no reply object"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB none (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none) ist.state))

/-- The same signal, from an actor that **carries provenance**.

With every taint empty the comparison above says nothing about the provenance
step: an omitted or misdirected one is invisible.  Seeding the signalling
thread's tag makes the step observable, so this is what stops the like-layer
composition from being decoration. -/
private def differentialTaintedSignalAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist0 := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
        [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep)
      diffNotifId ntfn) boundTcb) (diffTcb 63)
  -- The signaller carries a tag.  `declassificationTaint` is named by none of
  -- the four builder obligations, so seeding it leaves every proof unchanged.
  let tagged : SeLe4n.Kernel.DeclassificationTaint :=
    SeLe4n.Kernel.DeclassificationTaint.singleton 7
  let ist : IntermediateState := Builder.withTaint ist0 diffB.toObjId tagged
  expect "tagged control: the signalling thread really carries provenance"
    (!(ist.state.declassificationTaint diffB.toObjId == SeLe4n.Kernel.DeclassificationTaint.empty))
  expect "tagged: the frozen signal agrees with the live syscall, provenance included"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))
  -- …and the provenance actually moved, so the agreement is about a step that
  -- happened rather than two no-ops matching.
  expect "tagged control: the badge's recipient inherited the signaller's tag"
    (match frozenNotificationSignal diffNotifId diffB badge (freeze ist) with
     | .ok ((), fs) => !(fs.declassificationTaint diffA.toObjId == SeLe4n.Kernel.DeclassificationTaint.empty)
     | .error _ => false)

/-- FO-032: **refusals agree too.**  A frozen operation that accepts what the
live one refuses is a divergence no state comparison can see, there being no
live state to compare against — and a missing frozen guard is exactly how a
message-less parked sender reached the frozen dequeue.  Both sides are handed a
notification id that names no object. -/
private def differentialRefusalsAgree : IO Unit := do
  let missing : SeLe4n.ObjId := ⟨999⟩
  let ist := diffAddTcb mkEmptyIntermediateState (diffTcb 62)
  expect "FO-032: both refuse an absent notification, with the same error"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait missing diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait missing diffA) ist.state))

/-- FO-036: **a send naming a thread that does not exist** (PR #873 round 17).

On a rendezvous the message goes straight from the argument into the receiver's
TCB, so the live `endpointSendDual` never resolved `sender`: a caller naming a
nonexistent thread delivered anyway, and the receiver held a message attributed
to it.  Only the parking arm failed, and only because it happens to store into
the sender's own TCB.  The frozen mirror resolved the sender on both arms, so
the two disagreed on a concrete rendezvous input — and the frozen behaviour was
the correct one, which is why the live path is what changed.

The control is the same send from a sender that **does** exist: without it the
refusal below would pass against a fixture where nothing could ever be
delivered. -/
private def differentialSendFromAbsentSenderAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨31⟩], caps := #[], badge := none }
  let ghost : SeLe4n.ThreadId := ⟨9997⟩
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let parkedReceiver : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedReceiver) (diffTcb 63)
  expect "FO-036 control: the same rendezvous delivers from a sender that exists"
    (SeLe4n.Kernel.endpointSendDual diffEpId diffB msg ist.state).toOption.isSome
  expect "FO-036 control: and the ghost really is absent"
    ((ist.state.getTcb? ghost).isNone)
  expect "FO-036: both refuse a rendezvous send from a nonexistent sender"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId ghost msg (freeze ist))
      (liveWithTaint .send ghost (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId ghost msg) ist.state))
  expect "FO-036: and the live refusal leaves the receiver empty-handed"
    (match SeLe4n.Kernel.endpointSendDual diffEpId ghost msg ist.state with
     | .error _ => true
     | .ok _ => false)

/-- FO-037: **the send rendezvous actually delivering** (PR #873 audit).

FO-036 above enters the receiver-waiting arm but compares only its *refusal*
ordering, and the branch's known divergence sat on the delivery ordering: the
live `storeTcbReceiveComplete` clears the receiver's stashed reply object -- a
plain `Send` completing a server-first `Recv` moots the stash (D3/F-1) -- while
the frozen mirror kept it.  A claimed-checked branch whose substantive path is
never compared is the overstatement the branch keying exists to prevent, so this
scenario is the delivery comparison, with the stash **seeded**: the receiver
parks holding a reply object, which is exactly the field the two sides disagreed
on.  It fails against the stash-keeping frozen mirror and passes against the
field-exact one.

The run-queue halves ride along with bite of their own: the live delivery ends
in `ensureRunnable receiver` and the frozen one in `frozenEnsureRunnable`, and
`frozenStateAgrees` compares the buckets in both directions. -/
private def differentialSendRendezvousDeliversAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨37⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨507⟩
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  -- The server parked on a server-first `Recv`, reply object stashed: the state
  -- the D3/F-1 clear exists for.
  let parkedReceiver : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead, pendingReceiveReply := some rid }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedReceiver) (diffTcb 63))
    rid { replyId := rid, caller := none }
  expect "FO-037 control: the receiver really parks holding a stashed reply"
    ((ist.state.getTcb? diffA).any (fun t => t.pendingReceiveReply.isSome))
  -- The live delivery clears the stash: the field the comparison is about.
  expect "FO-037 control: the live delivery clears the stash and hands over the message"
    (match SeLe4n.Kernel.endpointSendDual diffEpId diffB msg ist.state with
     | .ok ((), st') => (st'.getTcb? diffA).any (fun t =>
         t.pendingReceiveReply.isNone && t.pendingMessage.isSome)
     | .error _ => false)
  expect "FO-037: the frozen delivery agrees with the live delivery"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId diffB msg (freeze ist))
      (liveWithTaint .send diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId diffB msg) ist.state))

/-- FO-034: **waking a thread whose priority has no bucket.**

Every actor in the scenarios above sits at priority 0, so a wake always found a
bucket already there and the frozen enqueue's missing-key branch never ran.  It
answered `.illegalState`, on the reading that a snapshot with no bucket at that
priority could not represent the thread becoming runnable -- but the live
`ensureRunnable` creates the bucket through `RunQueue.insert`, so the frozen
model refused a transition the kernel performs.  A passive server blocked at
freeze time, never runnable and therefore in no bucket, is that case.

The bound TCB is parked at a priority no runnable thread holds, so the signal's
wake has to create the bucket on both sides. -/
private def differentialWakeAtUnqueuedPriorityAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  -- Priority 5: `diffTcb 63`, the only runnable thread, is at 0, so nothing put
  -- a bucket here and the wake is the first thing that needs one.
  let parkedServer : TCB := { diffTcb 62 with priority := ⟨5⟩, ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep) diffNotifId ntfn)
    parkedServer) (diffTcb 63)
  expect "FO-034: control — the woken thread's priority has no bucket to start with"
    ((freeze ist).scheduler.byPriority.get? ⟨5⟩ |>.isNone)
  expect "FO-034: the frozen wake creates the bucket the live wake creates"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))

/-- **The registry the runner executes**, paired with the **branch** each
scenario covers.

`frozenOpDifferentiallyChecked` was a hand-maintained table nothing consumed:
setting an arm `true` satisfied all three interlock theorems whether or not a
comparison existed, and deleting a scenario left the claim standing.  A coverage
claim no execution backs is the shape this whole harness exists to remove, so the
claim is checked against this list -- which is also the list the runner runs, so
the two cannot describe different sets.

Round 17 moved the key from syscall to branch.  Tying the claim to an executed
scenario was necessary and not sufficient: one scenario satisfied a whole
syscall, so `.send` read "checked" on a fixture with no receiver waiting while
the rendezvous branch had never been compared against anything.  The unit of the
claim is now the unit of the transition. -/
private def differentialScenarios :
    List (SeLe4n.Kernel.FrozenOps.FrozenOpBranch × IO Unit) :=
  [ (.notificationSignalToBoundThread,  differentialNotificationSignalAgrees),
    (.notificationSignalToBoundThread,  differentialWakeAtUnqueuedPriorityAgrees),
    (.notificationWaitConsumesBadge,    differentialNotificationWaitAgrees),
    (.notificationWaitBlocks,           differentialNotificationWaitParksAgrees),
    (.endpointSendParks,                differentialEndpointSendAgrees),
    (.endpointSendToWaitingReceiver,    differentialSendFromAbsentSenderAgrees),
    (.endpointSendToWaitingReceiver,    differentialSendRendezvousDeliversAgrees),
    (.endpointReceiveFromBlockedSender, differentialEndpointReceiveAgrees),
    (.endpointReceiveFromBlockedCaller, differentialReceiveFromBlockedCallerAgrees),
    (.endpointCallParks,                differentialEndpointCallAgrees),
    (.endpointReplyToBlockedCaller,     differentialEndpointReplyAgrees) ]

/-- The claim and the scenarios name the same syscalls, in both directions: a
scenario for a syscall the table does not claim, or a claim with no scenario,
fails here. -/
private def differentialRegistryMatchesClaim : IO Unit := do
  let covered := differentialScenarios.map Prod.fst
  expect "registry: every differentially-checked branch has a scenario"
    (SeLe4n.Kernel.FrozenOps.FrozenOpBranch.all.all (fun b =>
      !(SeLe4n.Kernel.FrozenOps.frozenBranchDifferentiallyChecked b) || covered.contains b))
  expect "registry: every scenario covers a branch the claim names"
    (covered.all (fun b => SeLe4n.Kernel.FrozenOps.frozenBranchDifferentiallyChecked b))
  -- The per-syscall view is derived, so it must not read `true` for a syscall
  -- whose branches are not all covered -- the overstatement this replaced.
  expect "registry: a syscall reads checked only when every branch of it is"
    (SyscallId.all.all (fun sid =>
      !(SeLe4n.Kernel.FrozenOps.frozenOpDifferentiallyChecked sid)
        || SeLe4n.Kernel.FrozenOps.FrozenOpBranch.all.all (fun b =>
             b.syscall != sid || covered.contains b)))

/-- FO-033: **the comparison has bite, and the table was wrong.**

`FrozenOps/Operations.lean`'s correspondence table named `notificationSignal` as
`frozenNotificationSignal`'s counterpart.  It is not: the frozen operation
mirrors the bound-aware composition the live `.notificationSignal` arm runs, and
on the bound shape the two disagree.  Asserting that disagreement is what makes
the six scenarios above evidence rather than decoration — a comparison that
returned `true` for everything would pass them all. -/
private def differentialComparisonHasBite : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint mkEmptyIntermediateState diffEpId ep) diffNotifId ntfn) boundTcb) (diffTcb 63)
  expect "FO-033: NEGATIVE — the table-named counterpart does NOT agree"
    (!(frozenRunAgrees unitResultAgrees
        (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
        (SeLe4n.Kernel.notificationSignal diffNotifId badge ist.state)))

end SeLe4n.Testing.FrozenOpsSuite

open SeLe4n.Testing.FrozenOpsSuite in
def main : IO Unit := do
  IO.println "=== Q7 Frozen Operations Test Suite ==="
  IO.println "--- Q7-T1: FrozenKernel Monad Tests ---"
  fo001_lookupExisting
  fo002_lookupMissing
  fo003_storeObject
  IO.println "--- TPH-005: Frozen IPC ---"
  fo004_endpointReply
  fo004b_endpointReplyConsumesLink
  fo005_replyDelegatedReplier
  fo005b_replyWrongPresentedCap
  IO.println "--- TPH-006: Frozen Scheduler Tick ---"
  fo006_timerTickIdle
  IO.println "--- TPH-007: Frozen CSpace Lookup ---"
  fo007_cspaceLookup
  fo008_cspaceLookupMissing
  IO.println "--- TPH-008: Frozen VSpace Resolve ---"
  fo009_vspaceLookup
  fo010_vspaceLookupMissing
  IO.println "--- TPH-009: Frozen Service Query ---"
  fo011_serviceLookup
  fo012_serviceLookupMissing
  IO.println "--- TPH-013: Delete in Frozen ---"
  fo013_cspaceDelete
  IO.println "--- TPH-014: Notification Signal/Wait ---"
  fo014_notificationSignal
  fo015_notificationWait
  IO.println "--- T7-D/F: Frozen IPC Queue Enqueue (M-FRZ-1/2/3) ---"
  fo016_sendEnqueuesSender
  fo017_receiveEnqueuesReceiver
  fo018_callEnqueuesCaller
  IO.println "--- T7-D: Frozen Schedule & CSpace Mint ---"
  fo019_frozenSchedule
  fo020_frozenCspaceMint
  IO.println "--- U-H01: Multi-round IPC Regression ---"
  fo021_popThenPushRegression
  frozenProvenanceFollowsContent
  frozenDeliveryIsHonest
  frozenParkedSenderCarriesItsMessage
  frozenBoundNotificationDelivery
  IO.println "--- Frozen/live differential agreement ---"
  differentialRegistryMatchesClaim
  differentialScenarios.forM (fun s => s.2)
  differentialTaintedSignalAgrees
  differentialRefusalsAgree
  differentialComparisonHasBite
  IO.println "=== All Q7 frozen ops tests passed (31 scenarios) ==="
