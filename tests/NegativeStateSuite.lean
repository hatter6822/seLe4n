import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks

set_option maxRecDepth 1024

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
    |>.withObject endpointId (.endpoint {})
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
    |>.withObject wrongTypeId (.endpoint {})
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
      (.endpoint {})
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
      cdtSlotNode := baseState.cdtSlotNode.insert slot0 moveSrcNode
      cdtNodeSlot := (((baseState.cdtNodeSlot
        |>.insert moveSrcNode slot0)
        |>.insert moveParentNode { cnode := cnodeId, slot := 7 })
        |>.insert moveChildNode { cnode := cnodeId, slot := 8 })
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
      cdtSlotNode := ((((baseState.cdtSlotNode
        |>.insert strictRootSlot strictRootNode)
        |>.insert strictChildSlotOk strictChildNodeOk)
        |>.insert strictChildSlotBad strictChildNodeBad))
      cdtNodeSlot := (((baseState.cdtNodeSlot
        |>.insert strictRootNode strictRootSlot)
        |>.insert strictChildNodeOk strictChildSlotOk)
        |>.insert strictChildNodeBad strictChildSlotBad)
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

  expectError "dual-queue receive on non-endpoint object"
    (SeLe4n.Kernel.endpointReceiveDual cnodeId (SeLe4n.ThreadId.ofNat 1) baseState)
    .invalidCapability

  expectError "dual-queue receive on missing object"
    (SeLe4n.Kernel.endpointReceiveDual (SeLe4n.ObjId.ofNat 9999) (SeLe4n.ThreadId.ofNat 1) baseState)
    .objectNotFound

  expectError "vspace lookup missing asid"
    (SeLe4n.Kernel.Architecture.vspaceLookup 99 vaddrPrimary baseState)
    .asidNotBound

  -- F-03 fix: VSpace map test — verify mapping was actually created via subsequent lookup
  let (_, stMapped) ← expectOkState "vspace map initial"
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary) baseState)

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
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary) stMapped)
    .mappingConflict

  let (_, _stAwait) ← expectOkState "dual-queue receive enqueue seed"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 7) baseState)

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

  expectError "dual-queue send on missing object"
    (SeLe4n.Kernel.endpointSendDual (SeLe4n.ObjId.ofNat 9998) (SeLe4n.ThreadId.ofNat 8)
      { registers := #[], caps := #[], badge := none } baseState)
    .objectNotFound

  -- ==========================================================================
  -- WS-H12d/A-09: IPC message payload bounds enforcement
  -- ==========================================================================

  -- Oversized registers (> 120) rejected
  expectError "endpointSendDual rejects oversized registers"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 1)
      { registers := Array.mk (List.replicate 121 0), caps := #[], badge := none } baseState)
    .ipcMessageTooLarge

  -- Oversized caps (> 3) rejected
  expectError "endpointSendDual rejects oversized caps"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 1)
      { registers := #[],
        caps := #[{ target := .object 1, rights := [] },
                  { target := .object 2, rights := [] },
                  { target := .object 3, rights := [] },
                  { target := .object 4, rights := [] }],
        badge := none } baseState)
    .ipcMessageTooManyCaps

  -- endpointCall rejects oversized registers
  expectError "endpointCall rejects oversized registers"
    (SeLe4n.Kernel.endpointCall endpointId (SeLe4n.ThreadId.ofNat 1)
      { registers := Array.mk (List.replicate 121 0), caps := #[], badge := none } baseState)
    .ipcMessageTooLarge

  -- endpointCall rejects oversized caps
  expectError "endpointCall rejects oversized caps"
    (SeLe4n.Kernel.endpointCall endpointId (SeLe4n.ThreadId.ofNat 1)
      { registers := #[],
        caps := #[{ target := .object 1, rights := [] },
                  { target := .object 2, rights := [] },
                  { target := .object 3, rights := [] },
                  { target := .object 4, rights := [] }],
        badge := none } baseState)
    .ipcMessageTooManyCaps

  -- endpointReply rejects oversized registers
  expectError "endpointReply rejects oversized registers"
    (SeLe4n.Kernel.endpointReply (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := Array.mk (List.replicate 121 0), caps := #[], badge := none } baseState)
    .ipcMessageTooLarge

  -- endpointReply rejects oversized caps
  expectError "endpointReply rejects oversized caps"
    (SeLe4n.Kernel.endpointReply (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := #[],
        caps := #[{ target := .object 1, rights := [] },
                  { target := .object 2, rights := [] },
                  { target := .object 3, rights := [] },
                  { target := .object 4, rights := [] }],
        badge := none } baseState)
    .ipcMessageTooManyCaps

  -- endpointReplyRecv rejects oversized registers
  expectError "endpointReplyRecv rejects oversized registers"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := Array.mk (List.replicate 121 0), caps := #[], badge := none } baseState)
    .ipcMessageTooLarge

  -- endpointReplyRecv rejects oversized caps
  expectError "endpointReplyRecv rejects oversized caps"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := #[],
        caps := #[{ target := .object 1, rights := [] },
                  { target := .object 2, rights := [] },
                  { target := .object 3, rights := [] },
                  { target := .object 4, rights := [] }],
        badge := none } baseState)
    .ipcMessageTooManyCaps

  -- Boundary message (exactly 120 regs, 3 caps) should NOT be rejected by bounds check
  -- (may still fail due to other reasons like endpoint state)
  let boundaryMsg : SeLe4n.Model.IpcMessage := {
    registers := Array.mk (List.replicate 120 42),
    caps := #[{ target := .object 1, rights := [] },
              { target := .object 2, rights := [] },
              { target := .object 3, rights := [] }],
    badge := none }
  let boundaryResult := SeLe4n.Kernel.endpointSendDual endpointId
    (SeLe4n.ThreadId.ofNat 1) boundaryMsg baseState
  match boundaryResult with
  | .error .ipcMessageTooLarge =>
    throw <| IO.userError "boundary message (120 regs, 3 caps) incorrectly rejected as too large"
  | .error .ipcMessageTooManyCaps =>
    throw <| IO.userError "boundary message (120 regs, 3 caps) incorrectly rejected as too many caps"
  | _ => IO.println "positive check passed [boundary message not rejected by bounds]"

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

  -- WS-H12b: dequeue-on-dispatch — current thread 7 is NOT in the runnable queue
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
      |>.withRunnable [8]
      |>.withCurrent (some (SeLe4n.ThreadId.ofNat 7))
      |>.build)
  let (_, stPriorityScheduled) ← expectOkState "schedule chooses highest-priority runnable"
    (SeLe4n.Kernel.schedule schedPriorityState)
  if stPriorityScheduled.scheduler.current = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [schedule priority order]: current = tid 8"
  else
    throw <| IO.userError "schedule priority order expected current = tid 8"

  -- WS-H12b: current=none so both threads can be in runnable; re-add thread 7
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
      scheduler := { schedPriorityState.scheduler with
        runQueue := schedPriorityState.scheduler.runQueue.insert (SeLe4n.ThreadId.ofNat 7) 80
        activeDomain := 0
        current := none } }
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

  -- WS-H12b: dequeue-on-dispatch — current thread must NOT be in runnable queue
  let scheduleDomainTickOnlyState : SystemState :=
    { scheduleDomainSwitchState with
      scheduler := { scheduleDomainSwitchState.scheduler with
        activeDomain := 1
        current := some (SeLe4n.ThreadId.ofNat 10)
        runQueue := scheduleDomainSwitchState.scheduler.runQueue.remove (SeLe4n.ThreadId.ofNat 10)
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
  -- WS-H12b: after yield, schedule dequeues the dispatched thread (8) from runnable
  if stYielded.scheduler.runnable = [SeLe4n.ThreadId.ofNat 7] then
    IO.println "positive check passed [yield runnable rotation]: [7] (8 dequeued as current)"
  else
    throw <| IO.userError s!"yield runnable rotation expected [7], got {reprStr stYielded.scheduler.runnable}"

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
      (.endpoint {}) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-02: retype from non-untyped object (type mismatch)
  expectError "F2 retype from cnode (type mismatch)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedAuthCnode f2UntypedChildId
      (.endpoint {}) 64 f2UntypedState)
    .untypedTypeMismatch

  -- F2-NEG-03: retype exhausts region
  expectError "F2 retype region exhausted (oversized)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 512 f2UntypedState)
    .untypedRegionExhausted

  -- F2-NEG-04: device restriction (non-untyped child from device untyped)
  expectError "F2 device untyped restricts non-untyped child"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2DeviceUntypedId f2UntypedChildId
      (.endpoint {}) 64 f2DeviceState)
    .untypedDeviceRestriction

  -- F2-NEG-05: wrong authority (lookup from bad slot)
  expectError "F2 retype wrong authority"
    (SeLe4n.Kernel.retypeFromUntyped { cnode := 999, slot := 0 } f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-06: allocSize too small for object type (endpoint needs 64, giving 1)
  expectError "F2 retype allocSize too small"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 1 f2UntypedState)
    .untypedAllocSizeTooSmall

  IO.println "WS-F2 untyped memory negative checks passed"

/-- WS-H2: Lifecycle safety guards negative tests.
    Split into a separate function to avoid maxRecDepth limits in the main do block. -/
private def runH2NegativeChecks : IO Unit := do
  -- H2-NEG-01: childId self-overwrite — childId = untypedId
  expectError "H2 childId self-overwrite guard"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedObjId
      (.endpoint {}) 64 f2UntypedState)
    .childIdSelfOverwrite

  -- H2-NEG-02: childId collision with existing object
  expectError "H2 childId collision with existing object"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedAuthCnode
      (.endpoint {}) 64 f2UntypedState)
    .childIdCollision

  -- H2-NEG-03: childId collision with existing untyped child
  let h2UntypedWithChild : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject f2UntypedObjId (.untyped {
        regionBase := 0x10000
        regionSize := 256
        watermark := 64
        children := [{ objId := 60, offset := 0, size := 64 }]
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
  expectError "H2 childId collision with untyped child"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId 60
      (.endpoint {}) 64 h2UntypedWithChild)
    .childIdCollision

  IO.println "WS-H2 lifecycle safety guards negative checks passed"

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


/-- WS-H7 regression checks: HashMap BEq order-independence and capabilityRef metadata sync. -/
private def runWSH7Checks : IO Unit := do
  let vr1 : VSpaceRoot :=
    { asid := 77
      mappings := (({} : Std.HashMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)).insert 4096 (8192, default)).insert 12288 (16384, default) }
  let vr2 : VSpaceRoot :=
    { asid := 77
      mappings := (({} : Std.HashMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)).insert 12288 (16384, default)).insert 4096 (8192, default) }
  if vr1 == vr2 then
    IO.println "positive check passed [WS-H7 VSpaceRoot BEq ignores insertion order]"
  else
    throw <| IO.userError "WS-H7 VSpaceRoot BEq ignores insertion order: expected true"

  let capA : Capability := { target := .object endpointId, rights := [.read], badge := none }
  let capB : Capability := { target := .object notificationId, rights := [.read, .write], badge := none }
  let cn1 : CNode :=
    { depth := 2, guardWidth := 0, guardValue := 0, radixWidth := 2
      slots := (({} : Std.HashMap SeLe4n.Slot Capability).insert 1 capA).insert 2 capB }
  let cn2 : CNode :=
    { depth := 2, guardWidth := 0, guardValue := 0, radixWidth := 2
      slots := (({} : Std.HashMap SeLe4n.Slot Capability).insert 2 capB).insert 1 capA }
  if cn1 == cn2 then
    IO.println "positive check passed [WS-H7 CNode BEq ignores insertion order]"
  else
    throw <| IO.userError "WS-H7 CNode BEq ignores insertion order: expected true"

  let lifecycleCnode : KernelObject := .cnode { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 1, slots := Std.HashMap.ofList [(0, capA)] }
  let lifecycleEndpoint : KernelObject := .endpoint {}

  let stAfterCnode :=
    match storeObject 500 lifecycleCnode baseState with
    | .ok ((), st') => st'
    | .error err =>
        panic! s!"unexpected storeObject failure in WS-H7 check (cnode phase): {reprStr err}"

  if SystemState.lookupCapabilityRefMeta stAfterCnode { cnode := 500, slot := 0 } = some capA.target then
    IO.println "positive check passed [WS-H7 storeObject syncs capabilityRef metadata for stored CNode slot]"
  else
    throw <| IO.userError "WS-H7 storeObject syncs capabilityRef metadata for stored CNode slot: expected some target"

  let stAfterOverwrite :=
    match storeObject 500 lifecycleEndpoint stAfterCnode with
    | .ok ((), st') => st'
    | .error err =>
        panic! s!"unexpected storeObject failure in WS-H7 check (overwrite phase): {reprStr err}"

  if SystemState.lookupCapabilityRefMeta stAfterOverwrite { cnode := 500, slot := 0 } = none then
    IO.println "positive check passed [WS-H7 storeObject clears capabilityRef metadata when overwriting CNode]"
  else
    throw <| IO.userError "WS-H7 storeObject clears capabilityRef metadata when overwriting CNode: expected none"

  IO.println "WS-H7 regression checks passed"

-- ============================================================================
-- WS-H11: VSpace & Architecture Enrichment negative tests
-- ============================================================================

/-- WS-H11 negative tests: VSpace page permissions, address bounds, ASID, and TLB. -/
def runWSH11Checks : IO Unit := do
  IO.println "\n--- WS-H11: VSpace & Architecture Enrichment ---"

  -- Build a state with a VSpaceRoot
  let asid : SeLe4n.ASID := 1
  let vspaceOid : SeLe4n.ObjId := 20
  let st := (BootstrapBuilder.empty
    |>.withObject vspaceOid (.vspaceRoot { asid := asid, mappings := {} })
    |>.withLifecycleObjectType vspaceOid .vspaceRoot).build

  -- H-02: W^X violation must be rejected
  let wxPerms : PagePermissions := { write := true, execute := true }
  expectError "WS-H11 W^X violation rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 8192 wxPerms) st)
    .policyDenied
  IO.println "negative check passed [WS-H11 W^X violation correctly rejected]"

  -- A-05: Address bounds violation must be rejected (vspaceMapPageChecked)
  let hugeAddr : SeLe4n.PAddr := ⟨2^52 + 1⟩
  expectError "WS-H11 address out of bounds rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid 4096 hugeAddr) st)
    .addressOutOfBounds
  IO.println "negative check passed [WS-H11 address out of bounds correctly rejected]"

  -- Boundary: address exactly at bound is also rejected
  let boundaryAddr : SeLe4n.PAddr := ⟨2^52⟩
  expectError "WS-H11 address at boundary rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid 4096 boundaryAddr) st)
    .addressOutOfBounds
  IO.println "negative check passed [WS-H11 address at boundary correctly rejected]"

  -- A-05: Address just below bound should succeed via checked path
  let validAddr : SeLe4n.PAddr := ⟨2^52 - 1⟩
  match (SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid 4096 validAddr) st with
  | .ok _ => IO.println "positive check passed [WS-H11 valid address accepted by checked map]"
  | .error err => throw <| IO.userError s!"WS-H11 valid address rejected: {reprStr err}"

  -- Mapping conflict: duplicate vaddr should fail
  let (_, stMapped) ← expectOkState "WS-H11 map initial"
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 8192) st)
  expectError "WS-H11 duplicate mapping conflict"
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 16384) stMapped)
    .mappingConflict
  IO.println "negative check passed [WS-H11 duplicate mapping correctly rejected]"

  -- ASID not bound: lookup on unregistered ASID
  expectError "WS-H11 unbound ASID lookup"
    (SeLe4n.Kernel.Architecture.vspaceLookup 99 4096 st)
    .asidNotBound
  IO.println "negative check passed [WS-H11 unbound ASID correctly rejected]"

  -- Translation fault: lookup on unmapped vaddr
  expectError "WS-H11 unmapped vaddr lookup"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid 9999 st)
    .translationFault
  IO.println "negative check passed [WS-H11 unmapped vaddr returns translation fault]"

  -- Unmap non-existent mapping returns error
  expectError "WS-H11 unmap non-existent"
    ((SeLe4n.Kernel.Architecture.vspaceUnmapPage asid 9999) st)
    .translationFault
  IO.println "negative check passed [WS-H11 unmap non-existent returns translation fault]"

  -- Read-only permissions (write=false, execute=false) should be W^X compliant
  let roPerms : PagePermissions := { read := true, write := false, execute := false }
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 8192 16384 roPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 read-only permissions accepted]"
  | .error err => throw <| IO.userError s!"WS-H11 read-only rejected: {reprStr err}"

  -- Write-only (no execute) should be W^X compliant
  let woPerms : PagePermissions := { read := false, write := true, execute := false }
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 12288 20480 woPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 write-only permissions accepted]"
  | .error err => throw <| IO.userError s!"WS-H11 write-only rejected: {reprStr err}"

  -- Execute-only (no write) should be W^X compliant
  let xoPerms : PagePermissions := { read := false, write := false, execute := true }
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 16384 24576 xoPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 execute-only permissions accepted]"
  | .error err => throw <| IO.userError s!"WS-H11 execute-only rejected: {reprStr err}"

  -- TLB model: empty TLB is consistent
  let tlb := SeLe4n.Kernel.Architecture.TlbState.empty
  -- Full flush produces empty TLB
  let flushed := SeLe4n.Kernel.Architecture.adapterFlushTlb tlb
  if flushed.entries.length = 0 then
    IO.println "positive check passed [WS-H11 full TLB flush clears all entries]"
  else
    throw <| IO.userError "WS-H11 full TLB flush should clear entries"

  -- Per-ASID flush removes only matching ASID entries
  let entry1 : SeLe4n.Kernel.Architecture.TlbEntry :=
    { asid := 1, vaddr := 4096, paddr := 8192, perms := default }
  let entry2 : SeLe4n.Kernel.Architecture.TlbEntry :=
    { asid := 2, vaddr := 8192, paddr := 16384, perms := default }
  let tlb2 : SeLe4n.Kernel.Architecture.TlbState := { entries := [entry1, entry2] }
  let flushedAsid := SeLe4n.Kernel.Architecture.adapterFlushTlbByAsid tlb2 1
  if flushedAsid.entries.length = 1 then
    IO.println "positive check passed [WS-H11 per-ASID TLB flush removes only matching]"
  else
    throw <| IO.userError s!"WS-H11 per-ASID flush: expected 1 entry, got {flushedAsid.entries.length}"

  -- Per-VAddr flush removes only matching (ASID, VAddr) entries
  let entry3 : SeLe4n.Kernel.Architecture.TlbEntry :=
    { asid := 1, vaddr := 4096, paddr := 8192, perms := default }
  let entry4 : SeLe4n.Kernel.Architecture.TlbEntry :=
    { asid := 1, vaddr := 8192, paddr := 16384, perms := default }
  let entry5 : SeLe4n.Kernel.Architecture.TlbEntry :=
    { asid := 2, vaddr := 4096, paddr := 24576, perms := default }
  let tlb3 : SeLe4n.Kernel.Architecture.TlbState := { entries := [entry3, entry4, entry5] }
  let flushedVAddr := SeLe4n.Kernel.Architecture.adapterFlushTlbByVAddr tlb3 1 4096
  if flushedVAddr.entries.length = 2 then
    IO.println "positive check passed [WS-H11 per-VAddr TLB flush removes only matching (ASID,VAddr)]"
  else
    throw <| IO.userError s!"WS-H11 per-VAddr flush: expected 2 entries, got {flushedVAddr.entries.length}"

  -- vspaceLookupFull returns permissions
  let permsCheck : PagePermissions := { read := true, write := false, execute := false, user := true }
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 20480 32768 permsCheck) st with
  | .error err => throw <| IO.userError s!"WS-H11 lookupFull map error: {reprStr err}"
  | .ok (_, stPerm) =>
      match SeLe4n.Kernel.Architecture.vspaceLookupFull asid 20480 stPerm with
      | .error err => throw <| IO.userError s!"WS-H11 lookupFull error: {reprStr err}"
      | .ok ((paddr, perms), _) =>
          if paddr = ⟨32768⟩ && perms.read == true && perms.write == false &&
             perms.execute == false && perms.user == true then
            IO.println "positive check passed [WS-H11 vspaceLookupFull returns correct permissions]"
          else
            throw <| IO.userError s!"WS-H11 lookupFull wrong result"

  -- Cross-ASID isolation: mapping in ASID 1 must not be visible in ASID 2
  let asid2 : SeLe4n.ASID := 2
  let vspaceOid2 : SeLe4n.ObjId := 21
  let st2Asid := (BootstrapBuilder.empty
    |>.withObject vspaceOid (.vspaceRoot { asid := asid, mappings := {} })
    |>.withLifecycleObjectType vspaceOid .vspaceRoot
    |>.withObject vspaceOid2 (.vspaceRoot { asid := asid2, mappings := {} })
    |>.withLifecycleObjectType vspaceOid2 .vspaceRoot).build
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 8192) st2Asid with
  | .error err => throw <| IO.userError s!"WS-H11 cross-ASID map failed: {reprStr err}"
  | .ok (_, stCross) =>
      expectError "WS-H11 cross-ASID isolation"
        (SeLe4n.Kernel.Architecture.vspaceLookup asid2 4096 stCross)
        .translationFault
  IO.println "negative check passed [WS-H11 cross-ASID isolation enforced]"

  -- Multiple concurrent mappings: map 3 different vaddrs, verify all retrievable
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 8192) st with
  | .error err => throw <| IO.userError s!"WS-H11 multi-map step 1 failed: {reprStr err}"
  | .ok (_, stM1) =>
      match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 8192 16384) stM1 with
      | .error err => throw <| IO.userError s!"WS-H11 multi-map step 2 failed: {reprStr err}"
      | .ok (_, stM2) =>
          match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 12288 24576) stM2 with
          | .error err => throw <| IO.userError s!"WS-H11 multi-map step 3 failed: {reprStr err}"
          | .ok (_, stM3) =>
              match SeLe4n.Kernel.Architecture.vspaceLookup asid 4096 stM3,
                    SeLe4n.Kernel.Architecture.vspaceLookup asid 8192 stM3,
                    SeLe4n.Kernel.Architecture.vspaceLookup asid 12288 stM3 with
              | .ok (p1, _), .ok (p2, _), .ok (p3, _) =>
                  if p1 = ⟨8192⟩ && p2 = ⟨16384⟩ && p3 = ⟨24576⟩ then
                    IO.println "positive check passed [WS-H11 multiple concurrent mappings all retrievable]"
                  else
                    throw <| IO.userError "WS-H11 multi-map: wrong addresses returned"
              | _, _, _ => throw <| IO.userError "WS-H11 multi-map: lookup failed"

  -- Sequential map-unmap-map cycle: verify remapping works after unmap
  match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 8192) st with
  | .error err => throw <| IO.userError s!"WS-H11 cycle map1 failed: {reprStr err}"
  | .ok (_, stC1) =>
      match (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid 4096) stC1 with
      | .error err => throw <| IO.userError s!"WS-H11 cycle unmap failed: {reprStr err}"
      | .ok (_, stC2) =>
          match (SeLe4n.Kernel.Architecture.vspaceMapPage asid 4096 16384) stC2 with
          | .error err => throw <| IO.userError s!"WS-H11 cycle remap failed: {reprStr err}"
          | .ok (_, stC3) =>
              match SeLe4n.Kernel.Architecture.vspaceLookup asid 4096 stC3 with
              | .ok (pa, _) =>
                  if pa = ⟨16384⟩ then
                    IO.println "positive check passed [WS-H11 map-unmap-remap cycle works correctly]"
                  else
                    throw <| IO.userError s!"WS-H11 cycle: expected 16384, got {pa.toNat}"
              | .error err => throw <| IO.userError s!"WS-H11 cycle lookup failed: {reprStr err}"

  IO.println "all WS-H11 VSpace & Architecture checks passed"

end SeLe4n.Testing

def main : IO Unit := do
  SeLe4n.Testing.runNegativeChecks
  SeLe4n.Testing.runH2NegativeChecks
  SeLe4n.Testing.runAuditCoverageChecks
  SeLe4n.Testing.runWSH7Checks
  SeLe4n.Testing.runWSH11Checks
