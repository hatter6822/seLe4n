import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks

open SeLe4n.Model

namespace SeLe4n.Testing

private def endpointId : SeLe4n.ObjId := 40
private def cnodeId : SeLe4n.ObjId := 10
private def wrongTypeId : SeLe4n.ObjId := 99
private def guardedCnodeId : SeLe4n.ObjId := 55
private def sendEmptyEndpointId : SeLe4n.ObjId := 41
private def notificationId : SeLe4n.ObjId := 42
private def asidPrimary : SeLe4n.ASID := 2
private def vaddrPrimary : SeLe4n.VAddr := 4096
private def paddrPrimary : SeLe4n.PAddr := 12288

private def slot0 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := 0 }
private def slot0Path : SeLe4n.Kernel.CSpacePathAddr := { cnode := cnodeId, cptr := 0, depth := 0 }
private def guardedPathBadDepth : SeLe4n.Kernel.CSpacePathAddr := { cnode := guardedCnodeId, cptr := 0, depth := 1 }
private def badSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := wrongTypeId, slot := 0 }
private def guardedPathBadGuard : SeLe4n.Kernel.CSpacePathAddr := { cnode := guardedCnodeId, cptr := 0, depth := 3 }

private def baseState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject cnodeId (.cnode {
      guard := 0
      radix := 0
      slots := Std.HashMap.ofList [
        (0, {
          target := .object endpointId
          rights := [.read, .write]
          badge := none
        })
      ]
    })
    |>.withObject wrongTypeId (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject guardedCnodeId (.cnode {
      guard := 1
      radix := 2
      slots := Std.HashMap.ofList [
        (1, {
          target := .object endpointId
          rights := [.read]
          badge := none
        })
      ]
    })
    |>.withObject 6 (.tcb {
      tid := 6
      priority := 43
      domain := 0
      cspaceRoot := cnodeId
      vspaceRoot := 20
      ipcBuffer := 2048
      ipcState := .ready
    })
    |>.withObject 7 (.tcb {
      tid := 7
      priority := 42
      domain := 0
      cspaceRoot := cnodeId
      vspaceRoot := 20
      ipcBuffer := 4096
      ipcState := .ready
    })
    |>.withObject 8 (.tcb {
      tid := 8
      priority := 41
      domain := 0
      cspaceRoot := cnodeId
      vspaceRoot := 20
      ipcBuffer := 8192
      ipcState := .ready
    })
    |>.withObject 9 (.tcb {
      tid := 9
      priority := 40
      domain := 0
      cspaceRoot := cnodeId
      vspaceRoot := 20
      ipcBuffer := 12288
      ipcState := .ready
    })
    |>.withObject notificationId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
    |>.withObject 20 (.vspaceRoot { asid := asidPrimary, mappings := {} })
    |>.withLifecycleObjectType endpointId .endpoint
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType wrongTypeId .endpoint
    |>.withLifecycleObjectType guardedCnodeId .cnode
    |>.withLifecycleObjectType 6 .tcb
    |>.withLifecycleObjectType 7 .tcb
    |>.withLifecycleObjectType 8 .tcb
    |>.withLifecycleObjectType 9 .tcb
    |>.withLifecycleObjectType notificationId .notification
    |>.withLifecycleObjectType 20 .vspaceRoot
    |>.withLifecycleCapabilityRef slot0 (.object endpointId)
    |>.withRunnable [6, 7, 8, 9]
    |>.build)

private def invariantObjectIds : List SeLe4n.ObjId :=
  [endpointId, cnodeId, wrongTypeId, guardedCnodeId, notificationId, 20, 6, 7, 8, 9]

private def sendEmptyEndpointState : SystemState :=
  { baseState with
    objects := baseState.objects.insert sendEmptyEndpointId
      (.endpoint { state := .send, queue := [], waitingReceiver := none })
  }

private def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .ok _ =>
      throw <| IO.userError s!"{label}: expected error {reprStr expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"negative check passed [{label}]: {reprStr err}"
      else
        throw <| IO.userError s!"{label}: expected {reprStr expected}, got {reprStr err}"

private def expectOkState
    (label : String)
    (actual : Except KernelError (α × SystemState)) : IO (α × SystemState) :=
  match actual with
  | .ok result => do
      IO.println s!"positive check passed [{label}]"
      let (_, st) := result
      assertStateInvariantsFor label invariantObjectIds st
      pure result
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def expectOk
    (label : String)
    (actual : Except KernelError α) : IO α :=
  match actual with
  | .ok value => do
      IO.println s!"positive check passed [{label}]"
      pure value
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def expectThreadQueueLinks
    (label : String)
    (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (expectedPrev : Option SeLe4n.ThreadId)
    (expectedPPrev : Option QueuePPrev)
    (expectedNext : Option SeLe4n.ThreadId) : IO Unit :=
  match (st.objects[tid.toObjId]? : Option KernelObject) with
  | some (.tcb tcb) =>
      if tcb.queuePrev = expectedPrev ∧ tcb.queuePPrev = expectedPPrev ∧ tcb.queueNext = expectedNext then
        IO.println s!"positive check passed [{label}]"
      else
        throw <| IO.userError
          s!"{label}: expected queuePrev={reprStr expectedPrev} queuePPrev={reprStr expectedPPrev} queueNext={reprStr expectedNext}, got prev={reprStr tcb.queuePrev} pprev={reprStr tcb.queuePPrev} next={reprStr tcb.queueNext}"
  | _ =>
      throw <| IO.userError s!"{label}: expected TCB object"

private def corruptThreadQueueLinks
    (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  match (st.objects[tid.toObjId]? : Option KernelObject) with
  | some (.tcb tcb) =>
      .ok {
        st with
        objects := st.objects.insert tid.toObjId
          (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next })
      }
  | _ => .error .objectNotFound

-- WS-F2 untyped memory test constants and states
private def f2UntypedObjId : SeLe4n.ObjId := 80
private def f2UntypedChildId : SeLe4n.ObjId := 81
private def f2UntypedAuthCnode : SeLe4n.ObjId := 82
private def f2UntypedAuthSlot : SeLe4n.Kernel.CSpaceAddr :=
  { cnode := f2UntypedAuthCnode, slot := 0 }

private def f2UntypedState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject f2UntypedObjId (.untyped {
      regionBase := 0x10000
      regionSize := 256
      watermark := 0
      children := []
      isDevice := false
    })
    |>.withObject f2UntypedAuthCnode (.cnode {
      guard := 0
      radix := 0
      slots := Std.HashMap.ofList [
        (0, {
          target := .object f2UntypedObjId
          rights := [.read, .write, .grant]
          badge := none
        })
      ]
    })
    |>.withLifecycleObjectType f2UntypedObjId .untyped
    |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
    |>.withLifecycleCapabilityRef f2UntypedAuthSlot (.object f2UntypedObjId)
    |>.build)

private def f2DeviceUntypedId : SeLe4n.ObjId := 83

private def f2DeviceState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject f2DeviceUntypedId (.untyped {
      regionBase := 0x20000
      regionSize := 4096
      watermark := 0
      children := []
      isDevice := true
    })
    |>.withObject f2UntypedAuthCnode (.cnode {
      guard := 0
      radix := 0
      slots := Std.HashMap.ofList [
        (0, {
          target := .object f2DeviceUntypedId
          rights := [.read, .write, .grant]
          badge := none
        })
      ]
    })
    |>.withLifecycleObjectType f2DeviceUntypedId .untyped
    |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
    |>.withLifecycleCapabilityRef f2UntypedAuthSlot (.object f2DeviceUntypedId)
    |>.build)

private def runNegativeChecks : IO Unit := do
  assertStateInvariantsFor "negative suite baseState" invariantObjectIds baseState
  expectError "lookup wrong object type"
    (SeLe4n.Kernel.cspaceLookupSlot badSlot baseState)
    .objectNotFound
  let _ ← expectOk "lookup path resolved"
    (SeLe4n.Kernel.cspaceLookupPath slot0Path baseState)

  expectError "lookup path depth mismatch"
    (SeLe4n.Kernel.cspaceLookupPath guardedPathBadDepth baseState)
    .illegalState

  expectError "lookup path guard mismatch"
    (SeLe4n.Kernel.cspaceLookupPath guardedPathBadGuard baseState)
    .invalidCapability

  -- WS-E4/C-02/C-03 refinement: move updates slot↔node mappings without rewriting edges.
  let moveDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := 2 }
  let moveSrcNode : CdtNodeId := 0
  let moveParentNode : CdtNodeId := 1
  let moveChildNode : CdtNodeId := 2
  let moveSeed : SystemState :=
    { baseState with
      cdt := CapDerivationTree.empty
        |>.addEdge moveSrcNode moveChildNode .mint
        |>.addEdge moveParentNode moveSrcNode .copy
      cdtSlotNode := fun ref =>
        if ref = slot0 then some moveSrcNode else baseState.cdtSlotNode ref
      cdtNodeSlot := fun node =>
        if node = moveSrcNode then some slot0
        else if node = moveParentNode then some { cnode := cnodeId, slot := 7 }
        else if node = moveChildNode then some { cnode := cnodeId, slot := 8 }
        else baseState.cdtNodeSlot node
      cdtNextNode := 3
    }
  let (_, moveState) ← expectOkState "cspaceMove remaps slot-node pointer"
    (SeLe4n.Kernel.cspaceMove slot0 moveDst moveSeed)
  if SystemState.lookupCdtNodeOfSlot moveState slot0 = none ∧
      SystemState.lookupCdtNodeOfSlot moveState moveDst = some moveSrcNode ∧
      SystemState.lookupCdtSlotOfNode moveState moveSrcNode = some moveDst then
    IO.println "positive check passed [cspaceMove updates CDT slot-node/backpointer mappings]"
  else
    throw <| IO.userError "cspaceMove should clear src mapping and rebind node to dst"
  if moveState.cdt.edges = moveSeed.cdt.edges then
    IO.println "positive check passed [cspaceMove keeps node-level CDT edges unchanged]"
  else
    throw <| IO.userError "cspaceMove unexpectedly rewrote node-level CDT edges"

  let (_, deletedMoveDst) ← expectOkState "cspaceDeleteSlot clears stale CDT slot mapping"
    (SeLe4n.Kernel.cspaceDeleteSlot moveDst moveState)
  if SystemState.lookupCdtNodeOfSlot deletedMoveDst moveDst = none ∧
      SystemState.lookupCdtSlotOfNode deletedMoveDst moveSrcNode = none then
    IO.println "positive check passed [cspaceDeleteSlot detaches slot-node/backpointer mapping]"
  else
    throw <| IO.userError "cspaceDeleteSlot must clear stale CDT slot/node mapping"

  -- WS-E4/C-04 strict variant: surface first descendant deletion failure with context.
  let strictRootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := 5 }
  let strictChildSlotOk : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := 6 }
  let strictChildSlotBad : SeLe4n.Kernel.CSpaceAddr := { cnode := 777, slot := 0 }
  let strictRootNode : CdtNodeId := 30
  let strictChildNodeOk : CdtNodeId := 31
  let strictChildNodeBad : CdtNodeId := 32
  let strictSeed : SystemState :=
    { baseState with
      objects := baseState.objects.insert cnodeId (.cnode {
            guard := 0
            radix := 0
            slots := Std.HashMap.ofList [
              (strictRootSlot.slot, {
                target := .object endpointId
                rights := [.read, .write]
                badge := none
              }),
              (strictChildSlotOk.slot, {
                target := .object endpointId
                rights := [.read]
                badge := none
              })
            ]
          })
      cdt := CapDerivationTree.empty
        |>.addEdge strictRootNode strictChildNodeBad .mint
        |>.addEdge strictRootNode strictChildNodeOk .copy
      cdtSlotNode := fun ref =>
        if ref = strictRootSlot then some strictRootNode
        else if ref = strictChildSlotOk then some strictChildNodeOk
        else if ref = strictChildSlotBad then some strictChildNodeBad
        else baseState.cdtSlotNode ref
      cdtNodeSlot := fun node =>
        if node = strictRootNode then some strictRootSlot
        else if node = strictChildNodeOk then some strictChildSlotOk
        else if node = strictChildNodeBad then some strictChildSlotBad
        else baseState.cdtNodeSlot node
      cdtNextNode := 33
    }

  let (strictReport, strictState) ← expectOkState "cspaceRevokeCdtStrict returns report"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict strictRootSlot strictSeed)
  if strictReport.deletedSlots = [strictChildSlotOk] then
    IO.println "positive check passed [cspaceRevokeCdtStrict records deleted descendants before failure]"
  else
    throw <| IO.userError s!"cspaceRevokeCdtStrict deleted slot trace mismatch: {reprStr strictReport.deletedSlots}"

  match strictReport.firstFailure with
  | some failure =>
      if failure.offendingNode = strictChildNodeBad ∧
          failure.offendingSlot = some strictChildSlotBad ∧
          failure.error = .objectNotFound then
        IO.println "positive check passed [cspaceRevokeCdtStrict captures offending slot context]"
      else
        throw <| IO.userError s!"cspaceRevokeCdtStrict failure context mismatch: {reprStr failure}"
  | none =>
      throw <| IO.userError "cspaceRevokeCdtStrict must surface first descendant deletion failure"

  if SystemState.lookupCdtNodeOfSlot strictState strictChildSlotOk = none then
    IO.println "positive check passed [cspaceRevokeCdtStrict detaches successfully deleted descendant mapping]"
  else
    throw <| IO.userError "cspaceRevokeCdtStrict should detach successful descendant slot mapping"

  expectError "endpoint receive idle-state mismatch"
    (SeLe4n.Kernel.endpointReceive endpointId baseState)
    .endpointStateMismatch

  expectError "endpoint receive send-state empty queue"
    (SeLe4n.Kernel.endpointReceive sendEmptyEndpointId sendEmptyEndpointState)
    .endpointQueueEmpty

  expectError "vspace lookup missing asid"
    (SeLe4n.Kernel.Architecture.vspaceLookup 99 vaddrPrimary baseState)
    .asidNotBound

  -- F-03 fix: VSpace map test — verify mapping was actually created via subsequent lookup
  let (_, stMapped) ← expectOkState "vspace map initial"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary baseState)

  -- Verify the mapping was actually created by looking it up
  match SeLe4n.Kernel.Architecture.vspaceLookup asidPrimary vaddrPrimary stMapped with
  | .ok (paddr, _) =>
      if paddr = paddrPrimary then
        IO.println "positive check passed [vspace map creates retrievable mapping]"
      else
        throw <| IO.userError s!"vspace map created wrong mapping: expected paddr={reprStr paddrPrimary}, got {reprStr paddr}"
  | .error err =>
      throw <| IO.userError s!"vspace lookup after map failed: {reprStr err} — mapping was not created"

  expectError "vspace duplicate map conflict"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary stMapped)
    .mappingConflict

  let (_, stAwait) ← expectOkState "await receive handshake seed"
    (SeLe4n.Kernel.endpointAwaitReceive endpointId (SeLe4n.ThreadId.ofNat 7) baseState)

  -- F-03 fix: Notification wait — consistently check TCB ipcState across ALL variants
  let (waitBadge, stN1) ← expectOkState "notification wait blocks with none"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 7) baseState)
  if waitBadge = none then
    IO.println "positive check passed [notification wait #1 none]"
  else
    throw <| IO.userError "notification wait #1 expected none"

  match (stN1.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .blockedOnNotification notificationId then
        IO.println "positive check passed [notification wait #1 blocks thread ipcState]"
      else
        throw <| IO.userError "notification wait #1 expected blockedOnNotification ipcState"
  | _ => throw <| IO.userError "notification wait #1 expected waiter tcb"

  let (_, stN2) ← expectOkState "notification signal wakes waiter"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 55) stN1)


  match (stN2.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .ready then
        IO.println "positive check passed [notification signal wake sets waiter ipcState ready]"
      else
        throw <| IO.userError "notification signal wake expected waiter ipcState ready"
  | _ => throw <| IO.userError "notification signal wake expected waiter tcb"

  let (_, stN3) ← expectOkState "notification signal stores active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 66) stN2)

  -- F-03 fix: Badge accumulation — assert badge value BEFORE final signal
  match (stN3.objects[notificationId]? : Option KernelObject) with
  | some (.notification ntfn) =>
      if ntfn.pendingBadge = some (SeLe4n.Badge.ofNat 66) then
        IO.println "positive check passed [notification badge precondition: badge=66 before accumulation]"
      else
        throw <| IO.userError s!"notification badge precondition mismatch: expected some 66, got {reprStr ntfn.pendingBadge}"
  | _ => throw <| IO.userError "notification badge precondition expected notification object"

  let (_, stN4) ← expectOkState "notification signal accumulates active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 5) stN3)

  match (stN4.objects[notificationId]? : Option KernelObject) with
  | some (.notification ntfn) =>
      let expected := SeLe4n.Badge.ofNat (66 ||| 5)
      if ntfn.pendingBadge = some expected then
        IO.println "positive check passed [notification signal accumulates active badge via OR]"
      else
        throw <| IO.userError "notification active badge accumulation mismatch"
  | _ => throw <| IO.userError "notification signal expected notification object"

  -- F-03 fix: Notification wait #2 — check TCB ipcState after consuming badge
  let (waitBadge2, stN5) ← expectOkState "notification wait consumes active badge"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 8) stN4)
  if waitBadge2 = none then
    throw <| IO.userError "notification wait #2 expected delivered badge"
  else
    IO.println "positive check passed [notification wait #2 delivered badge]"

  -- Verify waiter TCB ipcState is ready after consuming badge (not blocked)
  match (stN5.objects[(SeLe4n.ThreadId.ofNat 8).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .ready then
        IO.println "positive check passed [notification wait #2 consumer ipcState ready]"
      else
        throw <| IO.userError s!"notification wait #2 expected consumer ipcState ready, got {reprStr tcb.ipcState}"
  | _ => throw <| IO.userError "notification wait #2 expected consumer tcb"

  expectError "notification wait wrong object type"
    (SeLe4n.Kernel.notificationWait endpointId (SeLe4n.ThreadId.ofNat 1) baseState)
    .invalidCapability

  expectError "await receive second waiter mismatch"
    (SeLe4n.Kernel.endpointAwaitReceive endpointId (SeLe4n.ThreadId.ofNat 8) stAwait)
    .endpointStateMismatch

  -- ==========================================================================
  -- WS-E4 M-01 refinement: dual-queue endpoint FIFO/handshake coverage
  -- ==========================================================================

  let (_, stDualSend1) ← expectOkState "dual queue send blocks sender"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) .empty baseState)
  match (stDualSend1.objects[endpointId]? : Option KernelObject) with
  | some (.endpoint ep) =>
      if ep.sendQ.head = some (SeLe4n.ThreadId.ofNat 7) ∧ ep.sendQ.tail = some (SeLe4n.ThreadId.ofNat 7) then
        IO.println "positive check passed [dual queue sender enqueued]"
      else
        throw <| IO.userError s!"dual queue sender enqueued expected head=tail=7, got {reprStr ep.sendQ}"
  | _ => throw <| IO.userError "dual queue sender enqueued expected endpoint object"
  expectThreadQueueLinks "dual queue sender enqueued link clear"
    stDualSend1 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none

  let (firstSender, _) ← expectOkState "dual queue receive dequeues sender"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) stDualSend1)
  if firstSender = SeLe4n.ThreadId.ofNat 7 then
    IO.println "positive check passed [dual queue first sender delivered]"
  else
    throw <| IO.userError s!"dual queue first sender expected tid 7, got {reprStr firstSender}"

  -- FIFO check across two blocked senders and one receiver consuming twice.
  let (_, stDualFifo1) ← expectOkState "dual queue fifo enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) .empty baseState)
  let (_, stDualFifo2) ← expectOkState "dual queue fifo enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) .empty stDualFifo1)
  expectThreadQueueLinks "dual queue fifo sender 7 links to sender 8"
    stDualFifo2 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 8))
  expectThreadQueueLinks "dual queue fifo sender 8 links from sender 7"
    stDualFifo2 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 7)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 7))) none
  let (fifoFirst, stDualFifo3) ← expectOkState "dual queue fifo receive #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) stDualFifo2)
  expectThreadQueueLinks "dual queue fifo dequeue #1 clears sender 7 links"
    stDualFifo3 (SeLe4n.ThreadId.ofNat 7) none none none
  expectThreadQueueLinks "dual queue fifo dequeue #1 keeps sender 8 singleton head"
    stDualFifo3 (SeLe4n.ThreadId.ofNat 8) none (some .endpointHead) none
  let (fifoSecond, stDualFifo4) ← expectOkState "dual queue fifo receive #2"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) stDualFifo3)
  expectThreadQueueLinks "dual queue fifo dequeue #2 clears sender 8 links"
    stDualFifo4 (SeLe4n.ThreadId.ofNat 8) none none none

  -- Arbitrary O(1) remove with queuePPrev metadata: remove middle waiter 8 from [7,8,9].
  let (_, stDualRm1) ← expectOkState "dual queue remove enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) .empty baseState)
  let (_, stDualRm2) ← expectOkState "dual queue remove enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) .empty stDualRm1)
  let (_, stDualRm3) ← expectOkState "dual queue remove enqueue sender 9"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 9) .empty stDualRm2)
  let (_, stDualRm4) ← expectOkState "dual queue remove middle sender 8"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8) stDualRm3)
  expectThreadQueueLinks "dual queue remove middle clears sender 8 links"
    stDualRm4 (SeLe4n.ThreadId.ofNat 8) none none none
  expectThreadQueueLinks "dual queue remove middle repairs sender 7 -> sender 9"
    stDualRm4 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 9))
  expectThreadQueueLinks "dual queue remove middle repairs sender 9 <- sender 7"
    stDualRm4 (SeLe4n.ThreadId.ofNat 9) (some (SeLe4n.ThreadId.ofNat 7)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 7))) none
  let (rmFirst, stDualRm5) ← expectOkState "dual queue remove receive #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 6) stDualRm4)
  let (rmSecond, _) ← expectOkState "dual queue remove receive #2"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 6) stDualRm5)
  if rmFirst = SeLe4n.ThreadId.ofNat 7 ∧ rmSecond = SeLe4n.ThreadId.ofNat 9 then
    IO.println "positive check passed [dual queue remove preserves remaining FIFO order]"
  else
    throw <| IO.userError s!"dual queue remove expected [7,9], got [{reprStr rmFirst},{reprStr rmSecond}]"

  let stMalformedHeadPPrev ← expectOk "dual queue malformed pprev state (head points to prev tcbNext)"
    (corruptThreadQueueLinks stDualRm3 (SeLe4n.ThreadId.ofNat 7) none (some (.tcbNext (SeLe4n.ThreadId.ofNat 8))) (some (SeLe4n.ThreadId.ofNat 8)))
  expectError "dual queue malformed pprev rejects head non-endpoint owner"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stMalformedHeadPPrev)
    .illegalState

  let stMalformedPrevNext ← expectOk "dual queue malformed pprev state (prev next mismatch)"
    (corruptThreadQueueLinks stDualRm3 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 9)))
  expectError "dual queue malformed pprev rejects stale prev pointer"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8) stMalformedPrevNext)
    .illegalState

  let stMalformedDetached ← expectOk "dual queue malformed pprev detached thread in empty queue"
    (corruptThreadQueueLinks baseState (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none)
  expectError "dual queue malformed pprev rejects detached thread marked as queued"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stMalformedDetached)
    .illegalState

  if fifoFirst = SeLe4n.ThreadId.ofNat 7 ∧ fifoSecond = SeLe4n.ThreadId.ofNat 8 then
    IO.println "positive check passed [dual queue fifo ordering preserved]"
  else
    throw <| IO.userError s!"dual queue fifo ordering expected [7,8], got [{reprStr fifoFirst},{reprStr fifoSecond}]"

  expectError "dual queue sender double-wait prevention"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) .empty stDualFifo1)
    .alreadyWaiting

  let (_, stDualRecvWait1) ← expectOkState "dual queue receiver wait #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) baseState)
  expectThreadQueueLinks "dual queue receiver wait keeps lone waiter detached"
    stDualRecvWait1 (SeLe4n.ThreadId.ofNat 9) none (some .endpointHead) none
  let (_, stDualRecvWait2) ← expectOkState "dual queue receiver fifo enqueue receiver 8"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) stDualRecvWait1)
  expectThreadQueueLinks "dual queue receiver fifo receiver 9 links to receiver 8"
    stDualRecvWait2 (SeLe4n.ThreadId.ofNat 9) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 8))
  expectThreadQueueLinks "dual queue receiver fifo receiver 8 links from receiver 9"
    stDualRecvWait2 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 9)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 9))) none
  let (_, stDualRecvWake) ← expectOkState "dual queue sender wakes first waiting receiver"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) .empty stDualRecvWait2)
  expectThreadQueueLinks "dual queue sender wake clears first receiver links"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 9) none none none
  expectThreadQueueLinks "dual queue sender wake keeps second receiver singleton head"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 8) none (some .endpointHead) none
  expectError "dual queue receiver double-wait prevention"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) stDualRecvWait1)
    .alreadyWaiting

  match (stDualFifo4.objects[endpointId]? : Option KernelObject) with
  | some (.endpoint ep) =>
      if ep.sendQ.head = none ∧ ep.sendQ.tail = none then
        IO.println "positive check passed [dual queue fifo drains send queue]"
      else
        throw <| IO.userError s!"dual queue fifo expected empty intrusive sendQ, got {reprStr ep.sendQ}"
  | _ => throw <| IO.userError "dual queue fifo expected endpoint object"

  let schedPriorityState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject 7 (.tcb {
        tid := 7
        priority := 10
        domain := 0
        cspaceRoot := cnodeId
        vspaceRoot := 20
        ipcBuffer := 4096
        ipcState := .ready
      })
      |>.withObject 8 (.tcb {
        tid := 8
        priority := 42
        domain := 0
        cspaceRoot := cnodeId
        vspaceRoot := 20
        ipcBuffer := 8192
        ipcState := .ready
      })
      |>.withRunnable [7, 8]
      |>.withCurrent (some (SeLe4n.ThreadId.ofNat 7))
      |>.build)
  let (_, stPriorityScheduled) ← expectOkState "schedule chooses highest-priority runnable"
    (SeLe4n.Kernel.schedule schedPriorityState)
  if stPriorityScheduled.scheduler.current = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [schedule priority order]: current = tid 8"
  else
    throw <| IO.userError "schedule priority order expected current = tid 8"

  let crossDomainState : SystemState :=
    { schedPriorityState with
      objects := schedPriorityState.objects.insert (SeLe4n.ThreadId.ofNat 7).toObjId (.tcb {
            tid := 7
            priority := 80
            domain := 1
            cspaceRoot := cnodeId
            vspaceRoot := 20
            ipcBuffer := 4096
            ipcState := .ready
          })
      scheduler := { schedPriorityState.scheduler with activeDomain := 0, current := none } }
  let (_, stCrossDomainScheduled) ← expectOkState "schedule filters runnable set to active domain"
    (SeLe4n.Kernel.schedule crossDomainState)
  if stCrossDomainScheduled.scheduler.current = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [schedule domain filter]: active domain thread selected"
  else
    throw <| IO.userError "schedule domain filter expected current = tid 8"

  let noActiveDomainRunnableState : SystemState :=
    { crossDomainState with scheduler := { crossDomainState.scheduler with activeDomain := 2 } }
  let (_, stNoActiveDomainRunnable) ← expectOkState "schedule returns idle when no active-domain runnable threads"
    (SeLe4n.Kernel.schedule noActiveDomainRunnableState)
  if stNoActiveDomainRunnable.scheduler.current = none then
    IO.println "positive check passed [schedule domain isolation]: no cross-domain fallback"
  else
    throw <| IO.userError "schedule domain isolation expected current = none"

  let mixedDomainFifoState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject 10 (.tcb {
        tid := 10
        priority := 20
        deadline := 2
        domain := 1
        cspaceRoot := cnodeId
        vspaceRoot := 20
        ipcBuffer := 12288
        ipcState := .ready
      })
      |>.withObject 11 (.tcb {
        tid := 11
        priority := 20
        deadline := 4
        domain := 1
        cspaceRoot := cnodeId
        vspaceRoot := 20
        ipcBuffer := 16384
        ipcState := .ready
      })
      |>.withObject 12 (.tcb {
        tid := 12
        priority := 80
        deadline := 1
        domain := 0
        cspaceRoot := cnodeId
        vspaceRoot := 20
        ipcBuffer := 20480
        ipcState := .ready
      })
      |>.withRunnable [12, 10, 11]
      |>.withCurrent none
      |>.build)
      |> fun st => { st with scheduler := { st.scheduler with activeDomain := 1 } }
  let (_, stMixedDomainScheduled) ← expectOkState "schedule ignores higher-priority cross-domain runnable"
    (SeLe4n.Kernel.schedule mixedDomainFifoState)
  if stMixedDomainScheduled.scheduler.current = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [schedule mixed domain priority]: active-domain runnable wins"
  else
    throw <| IO.userError "schedule mixed domain priority expected current = tid 10"

  let (_, stMixedDomainScheduledFifo) ← expectOkState "schedule keeps FIFO stability for equal prio/deadline in active domain"
    (SeLe4n.Kernel.schedule {
      mixedDomainFifoState with
      objects := mixedDomainFifoState.objects.insert (SeLe4n.ThreadId.ofNat 10).toObjId (.tcb {
            tid := 10
            priority := 20
            deadline := 4
            domain := 1
            cspaceRoot := cnodeId
            vspaceRoot := 20
            ipcBuffer := 12288
            ipcState := .ready
          }) })
  if stMixedDomainScheduledFifo.scheduler.current = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [schedule mixed domain FIFO]: earlier queue element retained"
  else
    throw <| IO.userError "schedule mixed domain FIFO expected current = tid 10"

  let scheduleDomainSwitchState : SystemState :=
    { mixedDomainFifoState with
      scheduler := { mixedDomainFifoState.scheduler with
        activeDomain := 0
        current := some (SeLe4n.ThreadId.ofNat 12)
        domainTimeRemaining := 1
        domainSchedule := [
          { domain := 0, length := 3 },
          { domain := 1, length := 2 }
        ]
        domainScheduleIndex := 0
      } }
  let (_, stScheduleDomainSwitched) ← expectOkState "scheduleDomain switches domain and reschedules"
    (SeLe4n.Kernel.scheduleDomain scheduleDomainSwitchState)
  if stScheduleDomainSwitched.scheduler.activeDomain = 1 then
    IO.println "positive check passed [scheduleDomain active domain advance]: activeDomain = 1"
  else
    throw <| IO.userError "scheduleDomain active domain advance expected activeDomain = 1"
  if stScheduleDomainSwitched.scheduler.domainScheduleIndex = 1 then
    IO.println "positive check passed [scheduleDomain index advance]: index = 1"
  else
    throw <| IO.userError "scheduleDomain index advance expected index = 1"
  if stScheduleDomainSwitched.scheduler.domainTimeRemaining = 2 then
    IO.println "positive check passed [scheduleDomain refresh domain budget]: remaining = 2"
  else
    throw <| IO.userError "scheduleDomain refresh domain budget expected remaining = 2"
  if stScheduleDomainSwitched.scheduler.current = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [scheduleDomain reschedule respects new active domain]: current = tid 10"
  else
    throw <| IO.userError "scheduleDomain reschedule expected current = tid 10"

  let scheduleDomainTickOnlyState : SystemState :=
    { scheduleDomainSwitchState with
      scheduler := { scheduleDomainSwitchState.scheduler with
        activeDomain := 1
        current := some (SeLe4n.ThreadId.ofNat 10)
        domainTimeRemaining := 3
        domainScheduleIndex := 1
      } }
  let (_, stScheduleDomainTickOnly) ← expectOkState "scheduleDomain decrements budget without switching"
    (SeLe4n.Kernel.scheduleDomain scheduleDomainTickOnlyState)
  if stScheduleDomainTickOnly.scheduler.activeDomain = 1 ∧ stScheduleDomainTickOnly.scheduler.domainScheduleIndex = 1 then
    IO.println "positive check passed [scheduleDomain no switch]: domain/index unchanged"
  else
    throw <| IO.userError "scheduleDomain no switch expected domain/index unchanged"
  if stScheduleDomainTickOnly.scheduler.domainTimeRemaining = 2 then
    IO.println "positive check passed [scheduleDomain no switch budget decrement]: remaining = 2"
  else
    throw <| IO.userError "scheduleDomain no switch budget expected remaining = 2"
  if stScheduleDomainTickOnly.scheduler.current = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [scheduleDomain no switch current consistency]: current preserved"
  else
    throw <| IO.userError "scheduleDomain no switch current consistency expected current = tid 10"

  -- F-03 fix: Yield test — verify which thread is current after rotation, not just queue membership
  let (_, stYielded) ← expectOkState "yield rotates current within runnable queue"
    (SeLe4n.Kernel.handleYield schedPriorityState)
  if stYielded.scheduler.runnable = [SeLe4n.ThreadId.ofNat 8, SeLe4n.ThreadId.ofNat 7] then
    IO.println "positive check passed [yield runnable rotation]: [8,7]"
  else
    throw <| IO.userError "yield runnable rotation expected [8,7]"

  -- Verify which thread is current after yield (should be tid 8, the highest priority)
  if stYielded.scheduler.current = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [yield current thread]: current = tid 8 (highest priority after rotation)"
  else
    throw <| IO.userError s!"yield current thread expected tid 8, got {reprStr stYielded.scheduler.current}"

  let malformedSched : SystemState :=
    (BootstrapBuilder.empty
      |>.withRunnable [SeLe4n.ThreadId.ofNat 77]
      |>.withCurrent none
      |>.build)
  expectError "schedule malformed runnable target"
    (SeLe4n.Kernel.schedule malformedSched)
    .schedulerInvariantViolation

  let malformedOffDomain : SystemState :=
    { malformedSched with scheduler := { malformedSched.scheduler with activeDomain := 1 } }
  expectError "schedule malformed runnable target in non-active domain still rejected"
    (SeLe4n.Kernel.schedule malformedOffDomain)
    .schedulerInvariantViolation

  -- ==========================================================================
  -- WS-D4 F-12: Double-wait prevention in notificationWait
  -- ==========================================================================

  -- stN1 already has thread 7 in the waiting list (from "notification wait blocks with none")
  expectError "notification double-wait prevention"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 7) stN1)
    .alreadyWaiting

  -- ==========================================================================
  -- WS-D4 F-07: Service dependency cycle detection
  -- ==========================================================================

  let svcIdA : ServiceId := ⟨100⟩
  let svcIdB : ServiceId := ⟨101⟩
  let svcEntryA : ServiceGraphEntry := {
    identity := { sid := svcIdA, backingObject := 200, owner := 300 }
    status := .stopped
    dependencies := []
    isolatedFrom := []
  }
  let svcEntryB : ServiceGraphEntry := {
    identity := { sid := svcIdB, backingObject := 201, owner := 301 }
    status := .stopped
    dependencies := []
    isolatedFrom := []
  }
  let svcState : SystemState :=
    (BootstrapBuilder.empty
      |>.withService svcIdA svcEntryA
      |>.withService svcIdB svcEntryB
      |>.build)

  -- Self-dependency should be rejected
  expectError "service dependency self-loop rejection"
    (SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdA svcState)
    .cyclicDependency

  -- Non-existent dependency target should be rejected
  let svcIdMissing : ServiceId := ⟨999⟩
  expectError "service dependency missing target rejection"
    (SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdMissing svcState)
    .objectNotFound

  -- Register A → B (should succeed)
  let regResult := SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdB svcState
  match regResult with
  | .ok (_, svcStateAB) => do
    IO.println "positive check passed [service dependency A→B registration]"
    -- Now registering B → A should create a cycle and be rejected
    expectError "service dependency cycle detection B→A"
      (SeLe4n.Kernel.serviceRegisterDependency svcIdB svcIdA svcStateAB)
      .cyclicDependency
    -- Idempotent re-registration of A → B should succeed
    let _ ← expectOk "service dependency idempotent re-registration"
      (SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdB svcStateAB)
  | .error err =>
    throw <| IO.userError s!"service dependency A→B registration failed: {reprStr err}"

  -- ── WS-F2: Untyped memory negative tests ──────────────────────────
  -- F2-NEG-01: retype from non-existent object
  expectError "F2 retype from non-existent object"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot 999 f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-02: retype from non-untyped object (type mismatch)
  expectError "F2 retype from cnode (type mismatch)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedAuthCnode f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 64 f2UntypedState)
    .untypedTypeMismatch

  -- F2-NEG-03: retype exhausts region
  expectError "F2 retype region exhausted (oversized)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 512 f2UntypedState)
    .untypedRegionExhausted

  -- F2-NEG-04: device restriction (non-untyped child from device untyped)
  expectError "F2 device untyped restricts non-untyped child"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2DeviceUntypedId f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 64 f2DeviceState)
    .untypedDeviceRestriction

  -- F2-NEG-05: wrong authority (lookup from bad slot)
  expectError "F2 retype wrong authority"
    (SeLe4n.Kernel.retypeFromUntyped { cnode := 999, slot := 0 } f2UntypedObjId f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-06: allocSize too small for object type (endpoint needs 64, giving 1)
  expectError "F2 retype allocSize too small"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) 1 f2UntypedState)
    .untypedAllocSizeTooSmall

  IO.println "WS-F2 untyped memory negative checks passed"

/-- Audit coverage: endpointReplyRecv and cspaceMutate tests.
    Split into a separate function to avoid maxRecDepth limits in the main do block. -/
private def runAuditCoverageChecks : IO Unit := do
  -- ── Audit: endpointReplyRecv coverage ────────────────────────────────
  -- NEG-REPLYRECV-01: replyRecv with non-existent reply target
  expectError "endpointReplyRecv non-existent reply target"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 6) (SeLe4n.ThreadId.ofNat 999)
      .empty baseState)
    .objectNotFound

  -- NEG-REPLYRECV-02: replyRecv when reply target is not in blockedOnReply state
  expectError "endpointReplyRecv target not blocked on reply"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 6) (SeLe4n.ThreadId.ofNat 7)
      .empty baseState)
    .replyCapInvalid

  -- POS-REPLYRECV: Set up a valid blockedOnReply scenario via endpointCall, then replyRecv
  -- First, enqueue receiver in the dual-queue receiveQ (not legacy waitingReceiver)
  let (_, stCallSetup1) ← expectOkState "replyRecv setup: receiver blocks on receive"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) baseState)
  -- Caller calls endpoint (handshakes with queued receiver, caller blocks for reply)
  let (_, stCallSetup2) ← expectOkState "replyRecv setup: caller calls endpoint"
    (SeLe4n.Kernel.endpointCall endpointId (SeLe4n.ThreadId.ofNat 7) .empty stCallSetup1)
  -- Verify caller is now blocked on reply
  match (stCallSetup2.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb callerTcb) =>
      -- WS-H1: blockedOnReply now carries replyTarget = some receiverId (ThreadId 8)
      if callerTcb.ipcState = .blockedOnReply endpointId (some (SeLe4n.ThreadId.ofNat 8)) then
        IO.println "positive check passed [replyRecv setup: caller blockedOnReply]"
      else
        throw <| IO.userError s!"replyRecv setup: expected caller blockedOnReply, got {reprStr callerTcb.ipcState}"
  | _ => throw <| IO.userError "replyRecv setup: expected caller TCB"
  -- Now execute replyRecv: receiver replies to caller and waits on endpoint
  let (_, stReplyRecv) ← expectOkState "replyRecv success"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 8) (SeLe4n.ThreadId.ofNat 7)
      .empty stCallSetup2)
  -- Verify caller is unblocked (ready)
  match (stReplyRecv.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb unblocked) =>
      if unblocked.ipcState = .ready then
        IO.println "positive check passed [replyRecv: caller unblocked after reply]"
      else
        throw <| IO.userError s!"replyRecv: expected caller ready, got {reprStr unblocked.ipcState}"
  | _ => throw <| IO.userError "replyRecv: expected caller TCB after reply"
  IO.println "endpointReplyRecv coverage checks passed"

  -- ── Audit: cspaceMutate coverage ─────────────────────────────────────
  -- NEG-MUTATE-01: mutate on non-existent CNode
  expectError "cspaceMutate non-existent CNode"
    (SeLe4n.Kernel.cspaceMutate { cnode := 999, slot := 0 } [.read] none baseState)
    .objectNotFound

  -- NEG-MUTATE-02: mutate with rights not a subset (escalation attempt)
  expectError "cspaceMutate rights escalation denied"
    (SeLe4n.Kernel.cspaceMutate slot0 [.read, .write, .grant] none baseState)
    .invalidCapability

  -- POS-MUTATE: attenuate rights successfully
  let (_, stMutated) ← expectOkState "cspaceMutate attenuate to read-only"
    (SeLe4n.Kernel.cspaceMutate slot0 [.read] none baseState)
  -- Verify rights were attenuated
  match SeLe4n.Kernel.cspaceLookupSlot slot0 stMutated with
  | .ok (cap, _) =>
      if cap.rights = [.read] then
        IO.println "positive check passed [cspaceMutate: rights attenuated to read-only]"
      else
        throw <| IO.userError s!"cspaceMutate: expected [read], got {reprStr cap.rights}"
  | .error err =>
      throw <| IO.userError s!"cspaceMutate: lookup after mutate failed: {reprStr err}"

  -- POS-MUTATE-BADGE: mutate with badge override
  let (_, stBadgeMutate) ← expectOkState "cspaceMutate with badge override"
    (SeLe4n.Kernel.cspaceMutate slot0 [.read] (some (SeLe4n.Badge.ofNat 77)) baseState)
  match SeLe4n.Kernel.cspaceLookupSlot slot0 stBadgeMutate with
  | .ok (cap, _) =>
      if cap.badge = some 77 then
        IO.println "positive check passed [cspaceMutate: badge override applied]"
      else
        throw <| IO.userError s!"cspaceMutate: expected badge 77, got {reprStr cap.badge}"
  | .error err =>
      throw <| IO.userError s!"cspaceMutate: lookup after badge mutate failed: {reprStr err}"
  IO.println "cspaceMutate coverage checks passed"

end SeLe4n.Testing

def main : IO Unit := do
  SeLe4n.Testing.runNegativeChecks
  SeLe4n.Testing.runAuditCoverageChecks
