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
      slots := [
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
      slots := [
        (1, {
          target := .object endpointId
          rights := [.read]
          badge := none
        })
      ]
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
    |>.withObject 20 (.vspaceRoot { asid := asidPrimary, mappings := [] })
    |>.withLifecycleObjectType endpointId .endpoint
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType wrongTypeId .endpoint
    |>.withLifecycleObjectType guardedCnodeId .cnode
    |>.withLifecycleObjectType 7 .tcb
    |>.withLifecycleObjectType 8 .tcb
    |>.withLifecycleObjectType 9 .tcb
    |>.withLifecycleObjectType notificationId .notification
    |>.withLifecycleObjectType 20 .vspaceRoot
    |>.withLifecycleCapabilityRef slot0 (.object endpointId)
    |>.withRunnable [7, 8, 9]
    |>.build)

private def invariantObjectIds : List SeLe4n.ObjId :=
  [endpointId, cnodeId, wrongTypeId, guardedCnodeId, notificationId, 20, 7, 8, 9]

private def sendEmptyEndpointState : SystemState :=
  { baseState with
    objects := fun oid =>
      if oid = sendEmptyEndpointId then
        some (.endpoint { state := .send, queue := [], waitingReceiver := none })
      else
        baseState.objects oid
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
  match st.objects tid.toObjId with
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
  match st.objects tid.toObjId with
  | some (.tcb tcb) =>
      .ok {
        st with
        objects := fun oid =>
          if oid = tid.toObjId then
            some (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next })
          else
            st.objects oid
      }
  | _ => .error .objectNotFound

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

  match stN1.objects (SeLe4n.ThreadId.ofNat 7).toObjId with
  | some (.tcb tcb) =>
      if tcb.ipcState = .blockedOnNotification notificationId then
        IO.println "positive check passed [notification wait #1 blocks thread ipcState]"
      else
        throw <| IO.userError "notification wait #1 expected blockedOnNotification ipcState"
  | _ => throw <| IO.userError "notification wait #1 expected waiter tcb"

  let (_, stN2) ← expectOkState "notification signal wakes waiter"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 55) stN1)


  match stN2.objects (SeLe4n.ThreadId.ofNat 7).toObjId with
  | some (.tcb tcb) =>
      if tcb.ipcState = .ready then
        IO.println "positive check passed [notification signal wake sets waiter ipcState ready]"
      else
        throw <| IO.userError "notification signal wake expected waiter ipcState ready"
  | _ => throw <| IO.userError "notification signal wake expected waiter tcb"

  let (_, stN3) ← expectOkState "notification signal stores active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 66) stN2)

  -- F-03 fix: Badge accumulation — assert badge value BEFORE final signal
  match stN3.objects notificationId with
  | some (.notification ntfn) =>
      if ntfn.pendingBadge = some (SeLe4n.Badge.ofNat 66) then
        IO.println "positive check passed [notification badge precondition: badge=66 before accumulation]"
      else
        throw <| IO.userError s!"notification badge precondition mismatch: expected some 66, got {reprStr ntfn.pendingBadge}"
  | _ => throw <| IO.userError "notification badge precondition expected notification object"

  let (_, stN4) ← expectOkState "notification signal accumulates active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNat 5) stN3)

  match stN4.objects notificationId with
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
  match stN5.objects (SeLe4n.ThreadId.ofNat 8).toObjId with
  | some (.tcb tcb) =>
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
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) baseState)
  match stDualSend1.objects endpointId with
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
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) baseState)
  let (_, stDualFifo2) ← expectOkState "dual queue fifo enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) stDualFifo1)
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
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) baseState)
  let (_, stDualRm2) ← expectOkState "dual queue remove enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) stDualRm1)
  let (_, stDualRm3) ← expectOkState "dual queue remove enqueue sender 9"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 9) stDualRm2)
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
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) stDualFifo1)
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
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) stDualRecvWait2)
  expectThreadQueueLinks "dual queue sender wake clears first receiver links"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 9) none none none
  expectThreadQueueLinks "dual queue sender wake keeps second receiver singleton head"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 8) none (some .endpointHead) none
  expectError "dual queue receiver double-wait prevention"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) stDualRecvWait1)
    .alreadyWaiting

  match stDualFifo4.objects endpointId with
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

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runNegativeChecks
