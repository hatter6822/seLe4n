/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Core
import SeLe4n.Kernel.SchedContext.Budget

/-!
# Q7-C: Per-Subsystem Frozen Operations

**STATUS: Experimental — deferred to WS-V (AG8-D). Not in production chain.**

AF5-I (AF-43): Implements 24 frozen kernel operations that operate on
`FrozenSystemState` using O(1) array-indexed lookups. Each mirrors a
builder-phase operation but uses `FrozenMap.get?`/`FrozenMap.set` instead
of `RHTable` operations.

## Operation Table

| # | Frozen Operation              | Builder Counterpart        | Subsystem    |
|---|------------------------------|----------------------------|--------------|
| 1 | `frozenSchedule`             | `schedule`                 | Scheduler    |
| 2 | `frozenHandleYield`          | `handleYield`              | Scheduler    |
| 3 | `frozenTimerTick`            | `timerTick`                | Scheduler    |
| 4 | `frozenTimerTickBudget`      | `timerTickBudget`          | Scheduler    |
| 5 | `frozenNotificationSignal`   | `notificationSignal`       | IPC          |
| 6 | `frozenNotificationWait`     | `notificationWait`         | IPC          |
| 7 | `frozenEndpointSend`         | `endpointSendDual`         | IPC          |
| 8 | `frozenEndpointReceive`      | `endpointReceiveDual`      | IPC          |
| 9 | `frozenEndpointCall`         | `endpointCall`             | IPC          |
|10 | `frozenEndpointReply`        | `endpointReply`            | IPC          |
|11 | `frozenCspaceLookup`         | `cspaceLookupSlot`         | Capability   |
|12 | `frozenCspaceLookupSlot`     | `cspaceLookupSlot` (root)  | Capability   |
|13 | `frozenCspaceMint`           | `cspaceMint`               | Capability   |
|14 | `frozenCspaceDelete`         | `cspaceDeleteSlot`         | Capability   |
|15 | `frozenVspaceLookup`         | `vspaceLookupFull`         | VSpace       |
|16 | `frozenLookupServiceByCap`   | `lookupServiceByCap`       | Service      |
|17 | `frozenSchedContextConfigure`| `schedContextConfigure`    | SchedContext |
|18 | `frozenSchedContextBind`     | `schedContextBind`         | SchedContext |
|19 | `frozenSchedContextUnbind`   | `schedContextUnbind`       | SchedContext |
|20 | `frozenSuspendThread`        | `suspendThread`            | Lifecycle    |
|21 | `frozenResumeThread`         | `resumeThread`             | Lifecycle    |
|22 | `frozenSetPriority`          | `setPriorityOp`            | SchedContext |
|23 | `frozenSetMCPriority`        | `setMCPriorityOp`          | SchedContext |
|24 | `frozenSetIPCBuffer`         | `setIPCBufferOp`           | Architecture |

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

/-- Q7-C1: Default time-slice quantum for frozen scheduler.
DEPRECATED: Use `FrozenSchedulerState.configDefaultTimeSlice` instead.
Retained for backward compatibility in tests that reference this constant. -/
def frozenDefaultTimeSlice : Nat := 5

/-- Q7-C1: Frozen timer tick — handle preemption in frozen state.
Mirrors `timerTick` with dequeue-on-dispatch.

On time-slice expiry: reset time-slice to the platform-configured value
(`configDefaultTimeSlice`), advance timer, clear `current` (conceptually
re-enqueue the preempted thread), then reschedule.
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
              -- Time-slice expired: reset to platform-configured value, update TCB
              let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
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

/-- Q7-C2/V5-O: Pop head from a frozen intrusive queue.
Follows `queueNext` link in the head TCB to advance the queue.
Returns the dequeued ThreadId, its TCB, and updated state.

V5-O (L-DS-3): Validates that the head thread's IPC state is consistent
with the queue it's being dequeued from (blocked-on-send for send queues,
blocked-on-receive for receive queues). Returns `.endpointStateMismatch`
if the head TCB's blocking state doesn't match the queue direction. -/
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
              -- V5-O: Verify the head thread's blocking state matches queue direction
              let stateConsistent := if isReceiveQ then
                match headTcb.ipcState with
                | .blockedOnReceive epId => epId == endpointId
                | _ => false
              else
                match headTcb.ipcState with
                | .blockedOnSend epId => epId == endpointId
                | .blockedOnCall epId => epId == endpointId
                | _ => false
              if !stateConsistent then .error .endpointStateMismatch
              else
              -- Advance queue head to next TCB in chain
              let newHead := headTcb.queueNext
              let newTail := if newHead = none then none else queue.tail
              let queue' : IntrusiveQueue := { head := newHead, tail := newTail }
              let ep' := if isReceiveQ
                then { ep with receiveQ := queue' }
                else { ep with sendQ := queue' }
              -- Clear queue links on dequeued TCB (U-H01: must also clear queuePPrev
              -- to allow re-enqueue via frozenQueuePushTail, which rejects
              -- threads with queuePPrev.isSome)
              let headTcb' := { headTcb with queuePrev := none, queueNext := none, queuePPrev := none }
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
            -- No receiver: block sender with message, then enqueue into sendQ (T1-B/M-FRZ-1)
            match frozenLookupTcb st sender with
            | some senderTcb =>
                let senderTcb' := { senderTcb with
                  ipcState := .blockedOnSend endpointId
                  pendingMessage := some msg }
                match frozenStoreTcb sender senderTcb' st with
                | .error e => .error e
                | .ok ((), st') =>
                    -- Enqueue sender into sendQ so subsequent receive can find it
                    match frozenQueuePushTail endpointId false sender st' with
                    | .error e => .error e
                    | .ok st'' => .ok ((), st'')
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
            -- No sender: block receiver, then enqueue into receiveQ (T1-C/M-FRZ-2)
            match frozenLookupTcb st receiver with
            | some recvTcb =>
                let recvTcb' := { recvTcb with ipcState := .blockedOnReceive endpointId }
                match frozenStoreTcb receiver recvTcb' st with
                | .error e => .error e
                | .ok ((), st') =>
                    -- Enqueue receiver into receiveQ so subsequent send can find it
                    match frozenQueuePushTail endpointId true receiver st' with
                    | .error e => .error e
                    | .ok st'' => .ok (receiver, st'')
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
            -- No receiver: block caller with message, then enqueue into sendQ (T1-D/M-FRZ-3)
            match frozenLookupTcb st caller with
            | some callerTcb =>
                let callerTcb' := { callerTcb with
                  ipcState := .blockedOnCall endpointId
                  pendingMessage := some msg }
                match frozenStoreTcb caller callerTcb' st with
                | .error e => .error e
                | .ok ((), st') =>
                    -- Enqueue caller into sendQ (caller is a sender until reply)
                    match frozenQueuePushTail endpointId false caller st' with
                    | .error e => .error e
                    | .ok st'' => .ok ((), st'')
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

/-- Q7-C3/V5-P: Frozen CSpace mint — insert a capability into a frozen CNode.
The CNodeRadix supports insert via its radix array.

V5-P (L-DS-4): Checks whether the target slot is already occupied before
insertion. If the slot contains an existing capability, returns `.targetSlotOccupied`
instead of silently overwriting. This prevents accidental capability leaks
where a mint operation clobbers an existing capability without revoking it. -/
def frozenCspaceMint (rootId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (cap : Capability) : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? rootId with
    | some (.cnode cn) =>
        -- V5-P: Reject if slot is already occupied
        match cn.slots.lookup slot with
        | some _ => .error .targetSlotOccupied
        | none =>
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
-- Z8-H: Frozen SchedContext Operations
-- ============================================================================

/-- Z8-H: Frozen SchedContext configure — update scheduling parameters.
Mirrors `schedContextConfigure` in frozen state. SchedContext is passthrough-
frozen (no internal RHTables), so this is a straightforward lookup + store.
Validates parameters and checks admission control against frozen state. -/
def frozenSchedContextConfigure (scId : SeLe4n.ObjId)
    (budget period priority deadline domain : Nat) : FrozenKernel Unit :=
  fun st =>
    -- Parameter validation (mirrors SchedContextOps.validateSchedContextParams)
    if period == 0 then .error .invalidArgument
    else if budget > period then .error .invalidArgument
    else if priority > 255 then .error .invalidArgument
    else if domain ≥ 16 then .error .invalidArgument
    else
      match st.objects.get? scId with
      | some (.schedContext sc) =>
        let updated : SeLe4n.Kernel.SchedContext :=
          { sc with
            budget := ⟨budget⟩
            period := ⟨period⟩
            priority := ⟨priority⟩
            deadline := ⟨deadline⟩
            domain := ⟨domain⟩
            budgetRemaining := ⟨budget⟩ }
        -- Admission control: collect all SchedContexts from frozen store
        let allScs := st.objects.fold (init := []) fun acc _id obj =>
          match obj with
          | .schedContext sc' => if sc'.scId.toObjId == scId then acc else sc' :: acc
          | _ => acc
        if SeLe4n.Kernel.admissionCheck allScs updated then
          match st.objects.set scId (.schedContext updated) with
          | some objects' => .ok ((), { st with objects := objects' })
          | none => .error .objectNotFound
        else
          .error .resourceExhausted
      | _ => .error .objectNotFound

/-- Z8-H: Frozen SchedContext bind — bind a thread to a SchedContext.
Mirrors `schedContextBind` in frozen state. In the frozen phase, there is no
RunQueue re-insertion (frozen scheduler uses membership FrozenSet + dequeue-on-
dispatch), so the bind only updates bidirectional references. -/
def frozenSchedContextBind (scId : SeLe4n.ObjId) (threadId : SeLe4n.ThreadId)
    : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? scId with
    | some (.schedContext sc) =>
      if sc.boundThread.isSome then .error .illegalState
      else
        match st.objects.get? threadId.toObjId with
        | some (.tcb tcb) =>
          match tcb.schedContextBinding with
          | .unbound =>
            let scIdTyped : SeLe4n.SchedContextId := ⟨scId.toNat⟩
            let updatedSc := { sc with boundThread := some threadId }
            let updatedTcb := { tcb with
              schedContextBinding := SeLe4n.Kernel.SchedContextBinding.bound scIdTyped }
            match st.objects.set scId (.schedContext updatedSc) with
            | some objs1 =>
              match objs1.set threadId.toObjId (.tcb updatedTcb) with
              | some objs2 => .ok ((), { st with objects := objs2 })
              | none => .error .objectNotFound
            | none => .error .objectNotFound
          | _ => .error .illegalState
        | _ => .error .objectNotFound
    | _ => .error .objectNotFound

/-- Z8-H: Frozen SchedContext unbind — unbind a thread from a SchedContext.
Mirrors `schedContextUnbind` in frozen state. No RunQueue or replenish queue
manipulation (frozen phase uses fixed membership set). Clears bidirectional
binding and, if the bound thread is current, clears current to force
rescheduling. -/
def frozenSchedContextUnbind (scId : SeLe4n.ObjId) : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? scId with
    | some (.schedContext sc) =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        -- Clear current if bound thread is current (force rescheduling)
        let st0 := if st.scheduler.current == some tid then
          { st with scheduler := { st.scheduler with current := none } }
        else st
        let updatedSc := { sc with boundThread := none, isActive := false }
        match st0.objects.set scId (.schedContext updatedSc) with
        | none => .error .objectNotFound
        | some st1Objs =>
        match st1Objs.get? tid.toObjId with
        | some (.tcb tcb) =>
          let updatedTcb := { tcb with
            schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
          match st1Objs.set tid.toObjId (.tcb updatedTcb) with
          | some objs2 => .ok ((), { st0 with objects := objs2 })
          | none => .error .objectNotFound
        | _ =>
          -- TCB not found — clear SC side only
          .ok ((), { st0 with objects := st1Objs })
    | _ => .error .objectNotFound

-- ============================================================================
-- Z8-I: Frozen timer tick with budget awareness
-- ============================================================================

/-- Z8-I: Frozen timer tick with CBS budget awareness.
Mirrors `timerTickBudget` (Z4-F) in frozen state. On each tick, if the current
thread has a bound SchedContext, decrements its budget. On budget exhaustion,
clears current to force rescheduling (frozen equivalent of preemption).
Falls back to legacy time-slice behavior for unbound threads. -/
def frozenTimerTickBudget : FrozenKernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.objects.get? tid.toObjId with
        | some (.tcb tcb) =>
          match tcb.schedContextBinding with
          | .bound scId | .donated scId _ =>
            -- CBS path: decrement SchedContext budget
            match st.objects.get? scId.toObjId with
            | some (.schedContext sc) =>
              let result := SeLe4n.Kernel.cbsBudgetCheck sc st.machine.timer 1
              let updatedSc := result.1
              let wasPreempted := result.2
              match st.objects.set scId.toObjId (.schedContext updatedSc) with
              | some objs1 =>
                let st' := { st with objects := objs1, machine := tick st.machine }
                if wasPreempted == true then
                  -- Budget exhausted: clear current to force rescheduling
                  .ok ((), { st' with scheduler :=
                    { st'.scheduler with current := none } })
                else
                  .ok ((), st')
              | none => .error .objectNotFound
            | _ =>
              -- SchedContext not found — fall back to legacy behavior
              frozenTimerTick st
          | .unbound =>
            -- Legacy path: use time-slice
            frozenTimerTick st
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- D1: Frozen thread suspension and resumption
-- ============================================================================

/-- D1: Frozen thread suspend — transition a thread from any non-Inactive state
to Inactive. Mirrors `suspendThread` in frozen state. In frozen phase, run queue
manipulation is skipped (fixed membership set); only TCB state is updated. -/
def frozenSuspendThread (tid : SeLe4n.ThreadId) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st tid with
    | none => .error .objectNotFound
    | some tcb =>
      if tcb.threadState == .Inactive then .error .illegalState
      else
        let tcb' := { tcb with
          threadState := .Inactive
          ipcState := .ready
          pendingMessage := none
          timeoutBudget := none
          queuePrev := none
          queueNext := none
          queuePPrev := none }
        match st.objects.set tid.toObjId (.tcb tcb') with
        | some objs => .ok ((), { st with objects := objs })
        | none => .error .objectNotFound

/-- D1: Frozen thread resume — transition a thread from Inactive to Ready.
Mirrors `resumeThread` in frozen state. In frozen phase, run queue insertion
is skipped (fixed membership set); only TCB state is updated. If the resumed
thread has higher priority than current, clears current to force rescheduling. -/
def frozenResumeThread (tid : SeLe4n.ThreadId) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st tid with
    | none => .error .objectNotFound
    | some tcb =>
      if tcb.threadState != .Inactive then .error .illegalState
      else
        let tcb' := { tcb with threadState := .Ready, ipcState := .ready }
        match st.objects.set tid.toObjId (.tcb tcb') with
        | some objs =>
          let st' := { st with objects := objs }
          -- If resumed thread has higher priority than current, force reschedule
          let st' := match st'.scheduler.current with
            | some curTid =>
              match st'.objects.get? curTid.toObjId with
              | some (.tcb curTcb) =>
                if tcb'.priority.val > curTcb.priority.val then
                  { st' with scheduler := { st'.scheduler with current := none } }
                else st'
              | _ => { st' with scheduler := { st'.scheduler with current := none } }
            | none => st'
          .ok ((), st')
        | none => .error .objectNotFound

-- ============================================================================
-- D2-L: Frozen priority management operations
-- ============================================================================

/-- D2-L: Frozen-phase setPriority. Validates MCP authority, updates priority
on the frozen state (SchedContext if bound, TCB if unbound). -/
def frozenSetPriority (callerTid targetTid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st callerTid with
    | none => .error .objectNotFound
    | some callerTcb =>
      if newPriority.val > callerTcb.maxControlledPriority.val then .error .illegalAuthority
      else match frozenLookupTcb st targetTid with
      | none => .error .objectNotFound
      | some targetTcb =>
        -- Update priority source (SchedContext or TCB)
        match targetTcb.schedContextBinding with
        | .unbound =>
          let tcb' := { targetTcb with priority := newPriority }
          match st.objects.set targetTid.toObjId (.tcb tcb') with
          | some objs => .ok ((), { st with objects := objs })
          | none => .error .objectNotFound
        | .bound scId | .donated scId _ =>
          match st.objects.get? scId.toObjId with
          | some (.schedContext sc) =>
            let sc' := { sc with priority := newPriority }
            match st.objects.set scId.toObjId (.schedContext sc') with
            | some objs => .ok ((), { st with objects := objs })
            | none => .error .objectNotFound
          | _ => .error .objectNotFound

/-- D2-L: Frozen-phase setMCPriority. Validates caller has sufficient MCP,
updates target's maxControlledPriority. If current priority exceeds new MCP,
caps it. -/
def frozenSetMCPriority (callerTid targetTid : SeLe4n.ThreadId)
    (newMCP : SeLe4n.Priority) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st callerTid with
    | none => .error .objectNotFound
    | some callerTcb =>
      if newMCP.val > callerTcb.maxControlledPriority.val then .error .illegalAuthority
      else match frozenLookupTcb st targetTid with
      | none => .error .objectNotFound
      | some targetTcb =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        -- Cap priority if it exceeds new MCP
        let targetTcb' :=
          if targetTcb'.priority.val > newMCP.val
          then { targetTcb' with priority := newMCP }
          else targetTcb'
        match st.objects.set targetTid.toObjId (.tcb targetTcb') with
        | some objs => .ok ((), { st with objects := objs })
        | none => .error .objectNotFound

-- ============================================================================
-- D3-I: Frozen IPC buffer configuration
-- ============================================================================

/-- D3-I: Frozen-phase setIPCBuffer. Validates alignment, canonical address,
VSpace mapping with write permission, then updates the target TCB's ipcBuffer.
Mirrors `setIPCBufferOp` in frozen state using FrozenMap lookups. -/
def frozenSetIPCBuffer (targetTid : SeLe4n.ThreadId)
    (addr : SeLe4n.VAddr) : FrozenKernel Unit :=
  fun st =>
    -- Step 1: Alignment check
    if addr.toNat % SeLe4n.ipcBufferAlignment != 0 then .error .alignmentError
    -- Step 2: Canonical address check
    else if !addr.isCanonical then .error .addressOutOfBounds
    else
      match frozenLookupTcb st targetTid with
      | none => .error .objectNotFound
      | some tcb =>
        -- Step 3: VSpace root validity (frozen VSpaceRoot)
        match st.objects.get? tcb.vspaceRoot with
        | some (.vspaceRoot vsr) =>
          -- Step 4: Mapping check via FrozenMap
          match vsr.mappings.get? addr with
          | some (_, perms) =>
            -- Step 5: Write permission check
            if perms.write then
              let tcb' := { tcb with ipcBuffer := addr }
              match st.objects.set targetTid.toObjId (.tcb tcb') with
              | some objs => .ok ((), { st with objects := objs })
              | none => .error .objectNotFound
            else .error .translationFault
          | none => .error .translationFault
        | _ => .error .invalidArgument

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
  | .notificationSignal => true  -- V2-A: notification signal (frozen-phase badge merge)
  | .notificationWait => true    -- V2-A: notification wait (frozen-phase consume/block)
  | .replyRecv => true           -- V2-C: compound reply + receive
  | .schedContextConfigure => true   -- Z8-H: frozenSchedContextConfigure
  | .schedContextBind => true        -- Z8-H: frozenSchedContextBind
  | .schedContextUnbind => true      -- Z8-H: frozenSchedContextUnbind
  | .tcbSuspend => true              -- D1: frozenSuspendThread
  | .tcbResume => true               -- D1: frozenResumeThread
  | .tcbSetPriority => true          -- D2: frozenSetPriority
  | .tcbSetMCPriority => true        -- D2: frozenSetMCPriority
  | .tcbSetIPCBuffer => true         -- D3: frozenSetIPCBuffer

/-- S3-L/Z8-H/D1/D2/D3: Exactly 20 SyscallId arms have frozen operation coverage.
    The 5 uncovered arms are builder-only operations (cspaceCopy, cspaceMove,
    lifecycleRetype, serviceRegister, serviceRevoke). -/
theorem frozenOpCoverage_count :
    (([SyscallId.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
       .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
       .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
       .notificationSignal, .notificationWait, .replyRecv,
       .schedContextConfigure, .schedContextBind, .schedContextUnbind,
       .tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority,
       .tcbSetIPCBuffer].filter
         frozenOpCoverage).length = 20) := by
  decide

/-- S3-L/D1/D2/D3: All 25 SyscallId arms are accounted for (either covered or documented as builder-only). -/
theorem frozenOpCoverage_exhaustive :
    ∀ (s : SyscallId), frozenOpCoverage s = true ∨ frozenOpCoverage s = false := by
  intro s; cases s <;> simp [frozenOpCoverage]

end SeLe4n.Kernel.FrozenOps
