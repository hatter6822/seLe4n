/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState

open SeLe4n.Kernel.RobinHood
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

/-- Helper: construct a test TCB. -/
private def mkTcb (tid : Nat) (prio : Nat := 0) (dom : Nat := 0) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat (0)) }

/-- Helper: construct a FrozenSystemState with given objects. -/
private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  let rt := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  { emptyFrozenState with objects := freezeMap rt }

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
      expect "scheduler preserved" (fst'.scheduler.current == fst.scheduler.current)
      expect "machine preserved" (fst'.machine.timer == fst.machine.timer)
  | .error _ => throw <| IO.userError "store should succeed"

-- ============================================================================
-- TPH-005: Frozen IPC Send/Receive
-- ============================================================================

/-- FO-004: frozenEndpointReply — reply to blocked caller -/
private def fo004_endpointReply : IO Unit := do
  let callerTcb : TCB := { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩) }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb =>
          expect "target unblocked" (tcb.ipcState == .ready)
          expect "message delivered" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "target TCB missing"
  | .error _ => throw <| IO.userError "reply should succeed"

/-- FO-005: frozenEndpointReply — wrong replier rejected -/
private def fo005_replyWrongReplier : IO Unit := do
  let callerTcb : TCB := { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩) }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨99⟩ ⟨2⟩ msg fst with
  | .ok _ => throw <| IO.userError "wrong replier should fail"
  | .error e => expect "wrong replier → replyCapInvalid" (e == .replyCapInvalid)

-- ============================================================================
-- TPH-006: Frozen Scheduler Tick
-- ============================================================================

/-- FO-006: frozenTimerTick — no current thread advances timer -/
private def fo006_timerTickIdle : IO Unit := do
  let fst := { emptyFrozenState with scheduler := { emptyFrozenState.scheduler with current := none } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      expect "timer advanced" (fst'.machine.timer == fst.machine.timer + 1)
      expect "still idle" (fst'.scheduler.current == none)
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
    (SeLe4n.VAddr.ofNat (0x1000)) ((SeLe4n.PAddr.ofNat (0x2000)), default)
  let vsr : FrozenVSpaceRoot := { asid := ⟨1⟩, mappings := freezeMap mappingsRt }
  let asidRt := (RHTable.empty 16 : RHTable ASID ObjId).insert ⟨1⟩ ⟨20⟩
  let fst := { mkFrozenState [(⟨20⟩, .vspaceRoot vsr)] with
    asidTable := freezeMap asidRt }
  match frozenVspaceLookup ⟨1⟩ (SeLe4n.VAddr.ofNat (0x1000)) fst with
  | .ok ((paddr, _perms), _) =>
      expect "resolved paddr" (paddr == (SeLe4n.PAddr.ofNat (0x2000)))
  | .error _ => throw <| IO.userError "vspace lookup should succeed"

/-- FO-010: frozenVspaceLookup — unbound ASID returns error -/
private def fo010_vspaceLookupMissing : IO Unit := do
  let fst := emptyFrozenState
  match frozenVspaceLookup ⟨99⟩ (SeLe4n.VAddr.ofNat (0x1000)) fst with
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
  let ntfn : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
  let fst := mkFrozenState [(⟨5⟩, .notification ntfn)]
  match frozenNotificationSignal ⟨5⟩ (Badge.ofNatMasked 0xFF) fst with
  | .ok ((), fst') =>
      match fst'.objects.get? ⟨5⟩ with
      | some (.notification ntfn') =>
          expect "state is active" (ntfn'.state == .active)
          expect "badge accumulated" (ntfn'.pendingBadge.isSome)
      | _ => throw <| IO.userError "notification should exist"
  | .error _ => throw <| IO.userError "signal should succeed"

/-- FO-015: frozenNotificationWait — consume pending badge -/
private def fo015_notificationWait : IO Unit := do
  let ntfn : Notification := { state := .active, waitingThreads := [], pendingBadge := some (Badge.ofNatMasked 42) }
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
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ fst with
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
    expect "frozenSchedule selects highest priority" (st1.scheduler.current == some tid2)
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
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ fst1 with
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
  fo005_replyWrongReplier
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
  IO.println "=== All Q7 frozen ops tests passed (21 scenarios) ==="
