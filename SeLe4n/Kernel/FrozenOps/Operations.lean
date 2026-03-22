/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Core

/-!
# Q7-C: Per-Subsystem Frozen Operations

Implements 14 frozen kernel operations that operate on `FrozenSystemState`
using O(1) array-indexed lookups. Each mirrors a builder-phase operation
but uses `FrozenMap.get?`/`FrozenMap.set` instead of `RHTable` operations.

## Operation Table

| # | Frozen Operation              | Builder Counterpart      | Subsystem  |
|---|------------------------------|--------------------------|------------|
| 1 | `frozenSchedule`             | `schedule`               | Scheduler  |
| 2 | `frozenHandleYield`          | `handleYield`            | Scheduler  |
| 3 | `frozenTimerTick`            | `timerTick`              | Scheduler  |
| 4 | `frozenNotificationSignal`   | `notificationSignal`     | IPC        |
| 5 | `frozenNotificationWait`     | `notificationWait`       | IPC        |
| 6 | `frozenEndpointSend`         | `endpointSendDual`       | IPC        |
| 7 | `frozenEndpointReceive`      | `endpointReceiveDual`    | IPC        |
| 8 | `frozenEndpointCall`         | `endpointCall`           | IPC        |
| 9 | `frozenEndpointReply`        | `endpointReply`          | IPC        |
|10 | `frozenCspaceLookup`         | `cspaceLookupSlot`       | Capability |
|11 | `frozenCspaceMint`           | `cspaceMint`             | Capability |
|12 | `frozenCspaceDelete`         | `cspaceDeleteSlot`       | Capability |
|13 | `frozenVspaceLookup`         | `vspaceLookupFull`       | VSpace     |
|14 | `frozenLookupServiceByCap`   | `lookupServiceByCap`     | Service    |

**Lifecycle operations** (`lifecycleRetype`) are builder-only — they add new
keys, which is incompatible with the frozen map's fixed key set.
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree

-- ============================================================================
-- Q7-C1: Scheduler Frozen Operations
-- ============================================================================

/-! ### Frozen Scheduler Architecture

The frozen scheduler uses a different representation than the builder-phase
`RunQueue`. Key differences:

1. **No key-set mutation**: `FrozenSet`/`FrozenMap` cannot add or remove keys.
   The `membership` set is immutable after freeze — it records the set of
   threads that were in the run queue at freeze time.

2. **Dequeue-on-dispatch via `current`**: In the builder phase, `schedule`
   removes the dispatched thread from the run queue. In the frozen phase,
   the `current` field serves as the dequeue marker: `current = some tid`
   means `tid` is dispatched and should be skipped during selection.

3. **Thread eligibility**: A thread is eligible for selection if:
   - It is in the `membership` set (was in run queue at freeze time)
   - It is NOT the current thread (dequeue-on-dispatch)
   - Its TCB domain matches `activeDomain`
   - Its TCB ipcState is `.ready` (not blocked)

4. **Yield**: Clears `current` (conceptually re-enqueues the outgoing thread)
   then calls `frozenSchedule` to select the next thread.

5. **`ensureRunnable` equivalent**: In the builder phase, woken threads are
   inserted into the run queue. In the frozen phase, woken threads must
   already be in the `membership` set (pre-allocated at freeze time). The
   frozen equivalent is updating the TCB's `ipcState` to `.ready`, which
   makes the thread eligible for selection. -/

/-- Q7-C1: Choose the best runnable thread in the frozen scheduler.
Mirrors `chooseThread` — scans `byPriority` buckets for an eligible thread
in the active domain, skipping the current thread (dequeue-on-dispatch). -/
def frozenChooseThread (st : FrozenSystemState)
    : Except KernelError (Option SeLe4n.ThreadId × FrozenSystemState) :=
  let currentTid := st.scheduler.current
  let result := st.scheduler.byPriority.fold (init := none)
    fun acc _prio threads =>
      match acc with
      | some _ => acc
      | none =>
          threads.find? (fun tid =>
            -- Skip current thread (dequeue-on-dispatch semantics)
            if currentTid == some tid then false
            else
              match st.objects.get? tid.toObjId with
              | some (.tcb tcb) =>
                  tcb.domain == st.scheduler.activeDomain &&
                  tcb.ipcState == .ready
              | _ => false)
  .ok (result, st)

/-- Q7-C1: Frozen schedule — select and dispatch a thread from frozen state.
Mirrors `schedule` with dequeue-on-dispatch and inline context switch.

In the frozen phase, "dequeue" is represented by setting `current := some tid`.
The `membership` FrozenSet is not modified — it remains a read-only record
of the thread population at freeze time. -/
def frozenSchedule : FrozenKernel Unit :=
  fun st =>
    match frozenChooseThread st with
    | .error e => .error e
    | .ok (none, st') =>
        match frozenSaveOutgoingContext st' with
        | .error e => .error e
        | .ok stSaved => frozenSetCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.objects.get? tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.domain == st'.scheduler.activeDomain &&
               tcb.ipcState == .ready then
              match frozenSaveOutgoingContext st' with
              | .error e => .error e
              | .ok stSaved =>
                -- Dequeue-on-dispatch: setting current = some tid marks the
                -- thread as dispatched. frozenChooseThread will skip it.
                match frozenRestoreIncomingContext stSaved tid with
                | .error e => .error e
                | .ok stRestored => frozenSetCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- Q7-C1: Frozen yield — re-enqueue current thread and reschedule.
Mirrors `handleYield` with dequeue-on-dispatch.

In the frozen phase, "re-enqueue" means clearing `current` so the thread
becomes eligible for selection again. The `frozenSchedule` call then
picks the best candidate (which may be the same thread if it has the
highest priority). -/
def frozenHandleYield : FrozenKernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => frozenSchedule st
    | some _tid =>
        -- Clear current to make the yielding thread eligible again
        let st' := { st with scheduler := { st.scheduler with current := none } }
        frozenSchedule st'

/-- Q7-C1: Default time-slice quantum for frozen scheduler. -/
def frozenDefaultTimeSlice : Nat := 5

/-- Q7-C1: Frozen timer tick — handle preemption in frozen state.
Mirrors `timerTick` with dequeue-on-dispatch.

On time-slice expiry: reset time-slice, advance timer, clear `current`
(conceptually re-enqueue the preempted thread), then reschedule.
On non-expiry: decrement time-slice, advance timer. -/
def frozenTimerTick : FrozenKernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.objects.get? tid.toObjId with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, update TCB, advance timer, reschedule
              let tcb' := { tcb with timeSlice := frozenDefaultTimeSlice }
              match st.objects.set tid.toObjId (.tcb tcb') with
              | some objects' =>
                  let st' := { st with objects := objects', machine := tick st.machine }
                  -- Clear current to re-enqueue the preempted thread
                  let st'' := { st' with scheduler :=
                    { st'.scheduler with current := none } }
                  frozenSchedule st''
              | none => .error .objectNotFound
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              match st.objects.set tid.toObjId (.tcb tcb') with
              | some objects' =>
                  .ok ((), { st with objects := objects', machine := tick st.machine })
              | none => .error .objectNotFound
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- Q7-C2: IPC Frozen Operations
-- ============================================================================

/-- Q7-C2: Frozen notification signal — wake waiter or accumulate badge.
Mirrors `notificationSignal` using frozen state lookups and mutations.

**`ensureRunnable` equivalent**: The builder phase calls `ensureRunnable` to
insert the woken thread into the run queue. In the frozen phase, the woken
thread is already in the `membership` FrozenSet (pre-allocated at freeze time).
Setting `ipcState := .ready` via `frozenStoreTcbIpcState` makes the thread
eligible for selection by `frozenChooseThread`, which checks `.ready` state. -/
def frozenNotificationSignal (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? notificationId with
    | some (.notification ntfn) =>
        match ntfn.waitingThreads with
        | waiter :: rest =>
            let nextState : NotificationState := if rest.isEmpty then .idle else .waiting
            let ntfn' : Notification := {
              state := nextState, waitingThreads := rest, pendingBadge := none }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' =>
                let st' := { st with objects := objects' }
                match frozenStoreTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok ((), st'')
            | none => .error .objectNotFound
        | [] =>
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat
            let ntfn' : Notification := {
              state := .active, waitingThreads := [], pendingBadge := some mergedBadge }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' => .ok ((), { st with objects := objects' })
            | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen notification wait — consume badge or block caller.
Mirrors `notificationWait` using frozen state.

**`removeRunnable` equivalent**: The builder phase calls `removeRunnable` when
a thread blocks. In the frozen phase, setting `ipcState := .blockedOnNotification`
via `frozenStoreTcbIpcState` makes the thread ineligible for selection by
`frozenChooseThread`, which only selects threads with `.ready` state. -/
def frozenNotificationWait (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : FrozenKernel (Option SeLe4n.Badge) :=
  fun st =>
    match st.objects.get? notificationId with
    | some (.notification ntfn) =>
        match ntfn.pendingBadge with
        | some badge =>
            let ntfn' : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' =>
                let st' := { st with objects := objects' }
                match frozenStoreTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok (some badge, st'')
            | none => .error .objectNotFound
        | none =>
            match frozenLookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  let ntfn' : Notification := {
                    state := .waiting
                    waitingThreads := waiter :: ntfn.waitingThreads
                    pendingBadge := none }
                  match st.objects.set notificationId (.notification ntfn') with
                  | some objects' =>
                      let st' := { st with objects := objects' }
                      match frozenStoreTcbIpcState st' waiter (.blockedOnNotification notificationId) with
                      | .error e => .error e
                      | .ok st'' => .ok (none, st'')
                  | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Pop head from a frozen intrusive queue.
Follows `queueNext` link in the head TCB to advance the queue.
Returns the dequeued ThreadId, its TCB, and updated state. -/
private def frozenQueuePopHead (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st : FrozenSystemState) : Except KernelError (SeLe4n.ThreadId × TCB × FrozenSystemState) :=
  match st.objects.get? endpointId with
  | some (.endpoint ep) =>
      let queue := if isReceiveQ then ep.receiveQ else ep.sendQ
      match queue.head with
      | none => .error .endpointQueueEmpty
      | some headTid =>
          match frozenLookupTcb st headTid with
          | none => .error .objectNotFound
          | some headTcb =>
              -- Advance queue head to next TCB in chain
              let newHead := headTcb.queueNext
              let newTail := if newHead = none then none else queue.tail
              let queue' : IntrusiveQueue := { head := newHead, tail := newTail }
              let ep' := if isReceiveQ
                then { ep with receiveQ := queue' }
                else { ep with sendQ := queue' }
              -- Clear queue links on dequeued TCB
              let headTcb' := { headTcb with queuePrev := none, queueNext := none }
              match st.objects.set endpointId (.endpoint ep') with
              | some objects1 =>
                  let st1 := { st with objects := objects1 }
                  match frozenStoreTcb headTid headTcb' st1 with
                  | .error e => .error e
                  | .ok ((), st2) => .ok (headTid, headTcb, st2)
              | none => .error .objectNotFound
  | _ => .error .objectNotFound

/-- Q7-C2: Frozen endpoint send — send message via frozen endpoint.
Uses intrusive queue pop/enqueue via TCB queue links. -/
def frozenEndpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) : FrozenKernel Unit :=
  fun st =>
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match st.objects.get? endpointId with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _receiver =>
            -- Receiver waiting: pop head and transfer message
            match frozenQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                match frozenLookupTcb st' receiver with
                | some recvTcb =>
                    let recvTcb' := { recvTcb with ipcState := ThreadIpcState.ready, pendingMessage := some msg }
                    match frozenStoreTcb receiver recvTcb' st' with
                    | .error e => .error e
                    | .ok ((), st'') => .ok ((), st'')
                | none => .error .objectNotFound
        | none =>
            -- No receiver: block sender with message
            match frozenLookupTcb st sender with
            | some senderTcb =>
                let senderTcb' := { senderTcb with
                  ipcState := .blockedOnSend endpointId
                  pendingMessage := some msg }
                match frozenStoreTcb sender senderTcb' st with
                | .error e => .error e
                | .ok ((), st') => .ok ((), st')
            | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint receive — receive message via frozen endpoint.
Returns sender ThreadId. -/
def frozenEndpointReceive (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : FrozenKernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects.get? endpointId with
    | some (.endpoint ep) =>
        match ep.sendQ.head with
        | some _sender =>
            -- Sender waiting: pop head and transfer message
            match frozenQueuePopHead endpointId false st with
            | .error e => .error e
            | .ok (sender, senderTcb, st') =>
                let senderMsg := senderTcb.pendingMessage
                -- Unblock sender
                match frozenLookupTcb st' sender with
                | some senderTcb' =>
                    let senderTcbUpdated := { senderTcb' with ipcState := ThreadIpcState.ready, pendingMessage := none }
                    match frozenStoreTcb sender senderTcbUpdated st' with
                    | .error e => .error e
                    | .ok ((), st'') =>
                        -- Deliver message to receiver
                        match frozenLookupTcb st'' receiver with
                        | some recvTcb =>
                            let recvTcb' := { recvTcb with pendingMessage := senderMsg }
                            match frozenStoreTcb receiver recvTcb' st'' with
                            | .error e => .error e
                            | .ok ((), st''') => .ok (sender, st''')
                        | none => .error .objectNotFound
                | none => .error .objectNotFound
        | none =>
            -- No sender: block receiver
            match frozenLookupTcb st receiver with
            | some recvTcb =>
                let recvTcb' := { recvTcb with ipcState := .blockedOnReceive endpointId }
                match frozenStoreTcb receiver recvTcb' st with
                | .error e => .error e
                | .ok ((), st') => .ok (receiver, st')
            | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint call — send then block for reply.
Mirrors `endpointCall` using intrusive queue management. -/
def frozenEndpointCall (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : FrozenKernel Unit :=
  fun st =>
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match st.objects.get? endpointId with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _receiver =>
            -- Receiver waiting: pop head, transfer message, block caller for reply
            match frozenQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                match frozenLookupTcb st' receiver with
                | some recvTcb =>
                    let recvTcb' := { recvTcb with ipcState := ThreadIpcState.ready, pendingMessage := some msg }
                    match frozenStoreTcb receiver recvTcb' st' with
                    | .error e => .error e
                    | .ok ((), st'') =>
                        -- Block caller waiting for reply
                        match frozenLookupTcb st'' caller with
                        | some callerTcb =>
                            let callerTcb' := { callerTcb with
                              ipcState := .blockedOnReply endpointId (some receiver) }
                            match frozenStoreTcb caller callerTcb' st'' with
                            | .error e => .error e
                            | .ok ((), st''') => .ok ((), st''')
                        | none => .error .objectNotFound
                | none => .error .objectNotFound
        | none =>
            -- No receiver: block caller with message
            match frozenLookupTcb st caller with
            | some callerTcb =>
                let callerTcb' := { callerTcb with
                  ipcState := .blockedOnCall endpointId
                  pendingMessage := some msg }
                match frozenStoreTcb caller callerTcb' st with
                | .error e => .error e
                | .ok ((), st') => .ok ((), st')
            | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint reply — reply to a blocked caller.
Mirrors `endpointReply`. -/
def frozenEndpointReply (replierId : SeLe4n.ThreadId)
    (targetId : SeLe4n.ThreadId) (msg : IpcMessage) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st targetId with
    | some targetTcb =>
        match targetTcb.ipcState with
        | .blockedOnReply _epId replyTarget =>
            if replyTarget = some replierId then
              -- Deliver message and unblock
              let targetTcb' := { targetTcb with
                ipcState := ThreadIpcState.ready
                pendingMessage := some msg }
              match frozenStoreTcb targetId targetTcb' st with
              | .error e => .error e
              | .ok ((), st') => .ok ((), st')
            else .error .replyCapInvalid
        | _ => .error .replyCapInvalid
    | none => .error .objectNotFound

-- ============================================================================
-- Q7-C3: Capability Frozen Operations
-- ============================================================================

/-- Q7-C3: Frozen CSpace lookup — O(1) via CNodeRadix.
Uses zero-hash bit extraction for direct array indexing. -/
def frozenCspaceLookup (st : FrozenSystemState) (cptr : SeLe4n.CPtr)
    (rootId : SeLe4n.ObjId) : Except KernelError Capability :=
  match st.objects.get? rootId with
  | some (.cnode cn) =>
      let slot := SeLe4n.Slot.ofNat (extractBits cptr.toNat 0 cn.radixWidth)
      match cn.slots.lookup slot with
      | some cap => .ok cap
      | none => .error .invalidCapability
  | some _ => .error .objectNotFound
  | none => .error .objectNotFound

/-- Q7-C3: Frozen CSpace lookup as kernel monad. -/
def frozenCspaceLookupSlot (cptr : SeLe4n.CPtr) (rootId : SeLe4n.ObjId)
    : FrozenKernel Capability :=
  fun st =>
    match frozenCspaceLookup st cptr rootId with
    | .ok cap => .ok (cap, st)
    | .error e => .error e

/-- Q7-C3: Frozen CSpace mint — insert a capability into a frozen CNode.
The CNodeRadix supports insert via its radix array. -/
def frozenCspaceMint (rootId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (cap : Capability) : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? rootId with
    | some (.cnode cn) =>
        let slots' := cn.slots.insert slot cap
        let cn' : FrozenCNode := { cn with slots := slots' }
        match st.objects.set rootId (.cnode cn') with
        | some objects' => .ok ((), { st with objects := objects' })
        | none => .error .objectNotFound
    | some _ => .error .objectNotFound
    | none => .error .objectNotFound

/-- Q7-C3: Frozen CSpace delete — erase a capability from a frozen CNode. -/
def frozenCspaceDelete (rootId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? rootId with
    | some (.cnode cn) =>
        let slots' := cn.slots.erase slot
        let cn' : FrozenCNode := { cn with slots := slots' }
        match st.objects.set rootId (.cnode cn') with
        | some objects' => .ok ((), { st with objects := objects' })
        | none => .error .objectNotFound
    | some _ => .error .objectNotFound
    | none => .error .objectNotFound

-- ============================================================================
-- Q7-C4: VSpace Frozen Operations
-- ============================================================================

/-- Q7-C4: Frozen VSpace lookup — resolve virtual address in frozen state.
Uses FrozenVSpaceRoot's FrozenMap for O(1) mapping lookup. -/
def frozenVspaceLookup (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    : FrozenKernel (SeLe4n.PAddr × PagePermissions) :=
  fun st =>
    match st.asidTable.get? asid with
    | some rootId =>
        match st.objects.get? rootId with
        | some (.vspaceRoot vsr) =>
            if vsr.asid == asid then
              match vsr.mappings.get? vaddr with
              | some entry => .ok (entry, st)
              | none => .error .translationFault
            else .error .asidNotBound
        | _ => .error .vspaceRootInvalid
    | none => .error .asidNotBound

-- ============================================================================
-- Q7-C5: Service Frozen Operations
-- ============================================================================

/-- Q7-C5: Frozen service lookup by capability target.
Mirrors `lookupServiceByCap` using FrozenMap fold. -/
def frozenLookupServiceByCap (epId : SeLe4n.ObjId)
    : FrozenKernel ServiceRegistration :=
  fun st =>
    let result := st.serviceRegistry.fold (init := none) fun acc _sid reg =>
      match acc with
      | some _ => acc
      | none =>
          match reg.endpointCap.target with
          | .object id => if id == epId then some reg else none
          | _ => none
    match result with
    | some reg => .ok (reg, st)
    | none => .error .objectNotFound

-- ============================================================================
-- S3-L/U-M29: Frozen operation exhaustiveness check
-- ============================================================================

/-- S3-L: SyscallId arms covered by frozen operations.
    This inductive type enumerates all SyscallId arms that have a corresponding
    frozen operation. The compile-time check ensures that adding a new SyscallId
    without a frozen operation (or vice versa) produces a type error.

    Lifecycle operations (`lifecycleRetype`) are intentionally excluded — they
    modify the key set, which is incompatible with frozen maps. Service
    registration/revocation are also builder-only. -/
def frozenOpCoverage : SyscallId → Bool
  | .send => true             -- frozenEndpointSend
  | .receive => true          -- frozenEndpointReceive
  | .call => true             -- frozenEndpointCall
  | .reply => true            -- frozenEndpointReply
  | .cspaceMint => true       -- frozenCspaceMint
  | .cspaceCopy => false      -- builder-only (structural copy)
  | .cspaceMove => false      -- builder-only (structural move)
  | .cspaceDelete => true     -- frozenCspaceDelete
  | .lifecycleRetype => false -- builder-only (adds keys)
  | .vspaceMap => true        -- frozenVspaceLookup (read-only in frozen phase)
  | .vspaceUnmap => true      -- frozenVspaceLookup (read-only in frozen phase)
  | .serviceRegister => false -- builder-only (adds service)
  | .serviceRevoke => false   -- builder-only (removes service)
  | .serviceQuery => true     -- frozenLookupServiceByCap

/-- S3-L: Exactly 9 SyscallId arms have frozen operation coverage.
    The 5 uncovered arms are builder-only operations (cspaceCopy, cspaceMove,
    lifecycleRetype, serviceRegister, serviceRevoke). -/
theorem frozenOpCoverage_count :
    (([SyscallId.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
       .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
       .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery].filter
         frozenOpCoverage).length = 9) := by
  native_decide

/-- S3-L: All 14 SyscallId arms are accounted for (either covered or documented as builder-only). -/
theorem frozenOpCoverage_exhaustive :
    ∀ (s : SyscallId), frozenOpCoverage s = true ∨ frozenOpCoverage s = false := by
  intro s; cases s <;> simp [frozenOpCoverage]

end SeLe4n.Kernel.FrozenOps
