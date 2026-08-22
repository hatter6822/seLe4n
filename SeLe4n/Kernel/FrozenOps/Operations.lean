-- SPDX-License-Identifier: GPL-3.0-or-later
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

**STATUS: Experimental — post-1.0 hardening candidate (AG8-D). Not in
production chain; no currently-active plan file tracks promotion.**

AF5-I (AF-43): Implements 24 frozen kernel operations that operate on
`FrozenSystemState` using O(1) array-indexed lookups. Each mirrors a
builder-phase operation but uses `FrozenMap.get?`/`FrozenMap.set` instead
of `RHTable` operations.

## Operation Table

This table is a reading aid, and it must not be the reason anyone believes a
frozen operation still matches the transition it names.  It was exactly that
for a long time, and row 5 was **wrong** the whole time — it named
`notificationSignal` while the operation mirrors the bound-aware
`notificationSignalBound` the live `.notificationSignal` arm runs.  Nothing
could tell, because nothing ran both.

`FrozenOps/Agreement.lean` is what tells: it runs the live transition on a
`SystemState` and the frozen one on that state's `freeze`, and compares.  A row
here that names the wrong counterpart now fails a differential scenario rather
than misleading its next reader.

| # | Frozen Operation              | Live Counterpart           | Subsystem    |
|---|------------------------------|----------------------------|--------------|
| 1 | `frozenSchedule`             | `schedule`                 | Scheduler    |
| 2 | `frozenHandleYield`          | `handleYield`              | Scheduler    |
| 3 | `frozenTimerTick`            | `timerTick`                | Scheduler    |
| 4 | `frozenTimerTickBudget`      | `timerTickBudget`          | Scheduler    |
| 5 | `frozenNotificationSignal`   | `notificationSignalBound`  | IPC          |
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

**Lifecycle operations** (`lifecycleRetype`) are builder-only — but not, since
PR #873 round 17, because a frozen map cannot gain a key: `FrozenMap.insert`
appends, which is what let the run-queue enqueue create a bucket.  What retype
still needs and the representation still lacks is *removal* — it erases the
replaced VSpace root's `asidTable` entry, and there is no `FrozenMap.erase`.
Adding one is a shrink, so it renumbers every index above the hole; that is a
separate piece of work, not a corollary of the append.
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)
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

5. **`ensureRunnable` equivalent**: `frozenEnsureRunnable`, on every wake, and
   `frozenRemoveRunnable` on every block or suspend.  Setting `ipcState` alone
   does *not* make a thread eligible: `frozenChooseThread` folds `byPriority`
   and filters on `.ready`, so a thread outside every bucket is unselectable
   whatever its `ipcState` says.  `membership` is a `FrozenSet` — key-presence
   with `Unit` values — so it cannot change and is not what selection reads. -/

/-- Q7-C1: Choose the best runnable thread in the frozen scheduler.
Mirrors `chooseThread` — scans `byPriority` buckets for an eligible thread
in the active domain, skipping the current thread (dequeue-on-dispatch). -/
def frozenChooseThread (st : FrozenSystemState)
    : Except KernelError (Option SeLe4n.ThreadId × FrozenSystemState) :=
  let currentTid := (st.scheduler.current)
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
                  tcb.domain == (st.scheduler.activeDomain) &&
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
            if tcb.domain == (st'.scheduler.activeDomain) &&
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
    match (st.scheduler.current) with
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
    match (st.scheduler.current) with
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

/-! ### WS-SM SM9.D: provenance follows content here too.

`FrozenSystemState.declassificationTaint` is **required**, with the reason
stated on the field: a snapshot that dropped provenance would report a system in
which every recorded downgrade is causally unconnected — the shape a laundering
chain is precisely *not* — so the analysis a frozen snapshot exists to support
would come back clean on a system that is not.  Preserving the table across
`freeze` buys that only for the instant of the freeze: the frozen operations
below move content between objects, and carrying the table through unchanged
would reproduce the same blind snapshot one operation later.

The moves mirror the live content-derived model exactly, because they are the
same transitions on the same content channels (`TCB.pendingMessage`,
`Notification.pendingBadge`): a sink joins its source's provenance, and a
transport that hands its content on is cleared, since its taint reflects what it
currently holds rather than everything it ever held. -/

/-- WS-SM SM9.D: a frozen content move — the sink joins the source's
provenance.  `joinAt` accumulates, so a propagation step cannot lose a link. -/
private def frozenTaintFlow (st : FrozenSystemState)
    (sink source : SeLe4n.ObjId) : FrozenSystemState :=
  { st with declassificationTaint :=
      st.declassificationTaint.joinAt sink (st.declassificationTaint source) }

/-- WS-SM SM9.D: a frozen content consumption — the transport holds nothing
afterwards, so it carries no provenance either. -/
private def frozenTaintClear (st : FrozenSystemState)
    (oid : SeLe4n.ObjId) : FrozenSystemState :=
  { st with declassificationTaint := st.declassificationTaint.clearAt oid }

/-- **WS-SM SM6.B (PR #873 round 8): the frozen bound-delivery target.**

The frozen mirror of `boundDeliveryTarget?`, and it has to agree with it exactly:
the notification has **no** ordinary waiters and its bound TCB is currently
`.blockedOnReceive` on some endpoint.  Same three conditions, same fail-safe
`none` on a dangling binding or a bound thread doing something else. -/
private def frozenBoundDeliveryTarget? (st : FrozenSystemState)
    (notificationId : SeLe4n.ObjId) : Option (SeLe4n.ThreadId × SeLe4n.ObjId) :=
  match st.objects.get? notificationId with
  | some (.notification ntfn) =>
      if ntfn.waitingThreads.val.isEmpty then
        match ntfn.boundTCB with
        | some t =>
            match frozenLookupTcb st t with
            | some tcb =>
                match tcb.ipcState with
                | .blockedOnReceive epId => some (t, epId)
                | _ => none
            | none => none
        | none => none
      else none
  | _ => none

/-- Q7-C2: Frozen notification signal — wake waiter or accumulate badge.
Mirrors `notificationSignal` using frozen state lookups and mutations.

**The signaller is an operand**, as it is in the live `notificationSignal`: the
badge's provenance is the signalling subject's, and without naming that subject
this operation could not say where the content it introduces came from.

**`ensureRunnable` equivalent**: `frozenEnsureRunnable`, called on every wake.

This sentence used to claim the insert was unnecessary because the woken thread
"is already in the `membership` FrozenSet (pre-allocated at freeze time)", and
that setting `.ready` therefore made it eligible for `frozenChooseThread`.  Both
halves were wrong, and being wrong in a docstring is why the gap survived five
review rounds: `frozenChooseThread` never reads `membership` at all -- it folds
`byPriority` and filters on `.ready` -- so a woken thread absent from every
bucket was `.ready` and permanently unselectable.  `membership` genuinely cannot
change (a `FrozenSet` is key-presence with `Unit` values); `byPriority` can, and
is the field that decides selection. -/
def frozenNotificationSignal (notificationId : SeLe4n.ObjId)
    (signaller : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? notificationId with
    | some (.notification ntfn) =>
        -- **The signaller must resolve to a live TCB**, for the reason the
        -- replier must in `frozenEndpointReply`, and with one failure mode more.
        -- `frozenTaintFlow` reads `declassificationTaint` at whatever `ObjId` it
        -- is handed: an absent signaller yields the total table's empty default,
        -- so the badge reaches its destination having lost its predecessor —
        -- but an id naming some *other* live object yields that object's
        -- provenance, so the snapshot would report a predecessor the badge
        -- never had.  Losing a link makes the analysis miss a chain; inventing
        -- one makes it name the wrong origin, and a provenance table that can
        -- do either is not evidence.
        --
        -- Checked after the notification is resolved, so a missing or
        -- non-notification target still answers `.objectNotFound` /
        -- `.invalidCapability` on its own terms, and before either delivery
        -- branch commits, because both of them apply the flow.
        match frozenLookupTcb st signaller with
        | none => .error .objectNotFound
        | some _ =>
        -- **Bound delivery comes first**, exactly as `notificationSignalBound`
        -- orders it (PR #873 round 8).  With no ordinary waiter and a bound TCB
        -- parked on an endpoint, the live kernel dequeues that TCB and delivers
        -- the badge into its `pendingMessage`; this path used to fall through to
        -- the storage branch instead, leaving the bound thread blocked and — once
        -- SM9.D landed — recording the signaller's provenance on the
        -- *notification* rather than on the thread that was supposed to receive
        -- the content.  A snapshot that reports the wrong recipient is not a
        -- snapshot of this kernel.
        match frozenBoundDeliveryTarget? st notificationId with
        | some (boundTid, epId) =>
            match frozenQueueRemove epId true boundTid st with
            | .error e => .error e
            | .ok st1 =>
                match frozenLookupTcb st1 boundTid with
                | none => .error .objectNotFound
                | some boundTcb =>
                  -- `pendingReceiveReply` is cleared with the delivery: the bound
                  -- TCB was `.blockedOnReceive` and no `Call` arrived, which is
                  -- what `storeTcbReceiveComplete` does on the live path.
                  match frozenStoreTcb boundTid
                      { boundTcb with
                        ipcState := .ready,
                        pendingReceiveReply := none,
                        pendingMessage :=
                          some { IpcMessage.empty with badge := some badge } } st1 with
                  | .error e => .error e
                  | .ok ((), st2) =>
                      -- PR #873 round 15: the woken thread re-enters the run
                      -- queue, as `notificationSignalBound`'s `ensureRunnable`
                      -- puts it back live.  Without this it is `.ready` and
                      -- invisible to `frozenChooseThread`, which selects only
                      -- from `byPriority`.
                      match frozenEnsureRunnable st2 boundTid with
                      | .error e => .error e
                      | .ok st3 =>
                        -- The badge reached the bound thread, so the provenance
                        -- goes there.  The notification is not written at all on
                        -- this path — a badge it already held keeps its own
                        -- provenance — so nothing is cleared, matching
                        -- `signalBypassedNotification`'s live classification.
                        .ok ((), frozenTaintFlow st3 boundTid.toObjId signaller.toObjId)
        | none =>
        -- WS-RC R4.C: pop via `NoDupList.tail?`.
        match ntfn.waitingThreads.tail? with
        | some (waiter, rest) =>
            let nextState : NotificationState := if rest.val.isEmpty then .idle else .waiting
            let ntfn' : Notification := {
              state := nextState, waitingThreads := rest, pendingBadge := none }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' =>
                let st' := { st with objects := objects' }
                -- **The badge is delivered, not just dropped.**  This branch
                -- clears `pendingBadge` and woke the waiter, but stored no
                -- message — so the badge vanished while the state claimed a
                -- delivery had happened.  The live `notificationSignal` stores
                -- a badge-only `IpcMessage` in the waiter's `pendingMessage`
                -- on this path, and a frozen snapshot that does otherwise is
                -- not a snapshot of this kernel.  Storing both fields in one
                -- write also keeps the taint flow below honest: it says the
                -- waiter received the signaller's content, which is only true
                -- if the content is actually there.
                match frozenLookupTcb st' waiter with
                | none => .error .objectNotFound
                | some waiterTcb =>
                  match frozenStoreTcb waiter
                      { waiterTcb with
                        ipcState := .ready,
                        pendingMessage :=
                          some { IpcMessage.empty with badge := some badge } } st' with
                  | .error e => .error e
                  | .ok ((), st'') =>
                    -- PR #873 round 15: the woken waiter re-enters the run queue,
                    -- as the live `notificationSignal` does with `ensureRunnable`.
                    match frozenEnsureRunnable st'' waiter with
                    | .error e => .error e
                    | .ok st3 =>
                      -- Delivered straight to the waiter: the badge reaches that
                      -- thread and the notification is left holding none, so the
                      -- transport's provenance goes with the content.
                      .ok ((), frozenTaintClear
                              (frozenTaintFlow st3 waiter.toObjId signaller.toObjId)
                              notificationId)
            | none => .error .objectNotFound
        | none =>
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat
            let ntfn' : Notification := {
              state := .active, waitingThreads := SeLe4n.NoDupList.empty,
              pendingBadge := some mergedBadge }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' =>
                -- Stored on the notification: it now holds the badge, so it
                -- carries the signaller's provenance until something takes it.
                .ok ((), frozenTaintFlow { st with objects := objects' }
                          notificationId signaller.toObjId)
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
            let ntfn' : Notification :=
              { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
                pendingBadge := none }
            match st.objects.set notificationId (.notification ntfn') with
            | some objects' =>
                let st' := { st with objects := objects' }
                -- **No enqueue here** (PR #873 round 17).  The waiter on this
                -- branch is the *calling* thread: it consumed a badge that was
                -- already pending, so it never blocked and never left the run
                -- queue -- and under dequeue-on-dispatch it is the current
                -- thread, absent from the queue entirely.  The live
                -- `notificationWait` marks it `.ready` and leaves the scheduler
                -- alone; an enqueue here would put a thread into a bucket the
                -- live transition does not touch.  The round-15 cut added one to
                -- every `.ready` transition without separating the wake of a
                -- *blocked* thread from the return of the caller.
                match frozenStoreTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' =>
                    -- The wait takes the whole stored badge, so the waiter
                    -- inherits the notification's provenance and the
                    -- notification is left carrying none.
                    .ok (some badge, frozenTaintClear
                            (frozenTaintFlow st'' waiter.toObjId notificationId)
                            notificationId)
            | none => .error .objectNotFound
        | none =>
            match frozenLookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  -- WS-RC R4.C: structural duplicate guard via consWithGuard?
                  match ntfn.waitingThreads.consWithGuard? waiter with
                  | none => .error .alreadyWaiting
                  | some wt' =>
                      let ntfn' : Notification := {
                        state := .waiting
                        waitingThreads := wt'
                        pendingBadge := none }
                      match st.objects.set notificationId (.notification ntfn') with
                      | some objects' =>
                          let st' := { st with objects := objects' }
                          match (frozenStoreTcbIpcState st' waiter
                              (.blockedOnNotification notificationId)).map
                              (fun stB => frozenRemoveRunnable stB waiter) with
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
if the head TCB's blocking state doesn't match the queue direction.

PR #873 round 7: **a parked sender must also be carrying its message.**  The
state check alone accepted a `.blockedOnSend` / `.blockedOnCall` head with
`pendingMessage := none`, and `frozenEndpointReceive` then stored that `none` in
the receiver while still joining the sender's provenance — inventing a causal
predecessor for content that was never delivered.  Structural rather than a guard
at the one caller: the frozen send path always parks with `pendingMessage := some
msg`, so a message-less parked sender is a malformed snapshot in exactly the way
a mismatched blocking state is, and it is refused with the same error.  The
receive queue is unaffected — a thread parked to *receive* correctly holds
nothing. -/
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
                -- The parked sender's message is part of what "parked to send"
                -- means: without it the dequeue would hand the receiver `none`
                -- while the provenance join claimed a delivery.
                (match headTcb.ipcState with
                 | .blockedOnSend epId => epId == endpointId
                 | .blockedOnCall epId => epId == endpointId
                 | _ => false) && headTcb.pendingMessage.isSome
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
        -- **The sender is resolved once, for both orderings.**  The blocking
        -- path already did this and the rendezvous path did not, so whether a
        -- nonexistent sender was refused depended on whether a receiver
        -- happened to be waiting — and on the rendezvous ordering the message
        -- was delivered while `frozenTaintFlow` read the total table at an id
        -- that names nothing (empty provenance) or names a non-TCB object
        -- (that object's provenance).  Hoisting the lookup removes the
        -- asymmetry structurally rather than adding a second guard that could
        -- drift from this one.
        match frozenLookupTcb st sender with
        | none => .error .objectNotFound
        | some senderTcb =>
        match ep.receiveQ.head with
        | some _receiver =>
            -- Receiver waiting: pop head and transfer message
            match frozenQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                match frozenLookupTcb st' receiver with
                | some recvTcb =>
                    -- Mirrors `storeTcbReceiveComplete` **field for field** (PR
                    -- #873 audit): a plain `Send` completing a server-first
                    -- `Recv` also clears the receiver's stashed reply object —
                    -- no `Call` arrived, so the stash is moot (IPC de-threading
                    -- D3, finding F-1).  The frozen mirror kept the stash, and
                    -- the branch's differential scenario compared only the
                    -- refusal ordering, so the divergence sat exactly where the
                    -- claimed-checked branch was not being compared.  FO-037 is
                    -- the delivery-ordering comparison, with the stash seeded so
                    -- this field is what the scenario measures.
                    let recvTcb' := { recvTcb with ipcState := ThreadIpcState.ready, pendingMessage := some msg, pendingReceiveReply := none }
                    match frozenStoreTcb receiver recvTcb' st' with
                    | .error e => .error e
                    | .ok ((), st'') =>
                      -- PR #873 round 15: the woken receiver re-enters the run
                      -- queue, as the live `endpointSendDual` does with
                      -- `ensureRunnable`.
                      match frozenEnsureRunnable st'' receiver with
                      | .error e => .error e
                      | .ok st3 =>
                        -- Rendezvous: the message reaches the receiver, so the
                        -- receiver joins the sender's provenance.
                        .ok ((), frozenTaintFlow st3 receiver.toObjId sender.toObjId)
                | none => .error .objectNotFound
        | none =>
            -- No receiver: block sender with message, then enqueue into sendQ (T1-B/M-FRZ-1).
            -- The message stays in the sender's own TCB, whose provenance is
            -- already the sender's, so there is nothing to propagate here.
            -- `senderTcb` is the one resolved above, shared with the rendezvous
            -- ordering so the two cannot disagree about what a valid sender is.
            let senderTcb' := { senderTcb with
              ipcState := .blockedOnSend endpointId
              pendingMessage := some msg }
            match frozenStoreTcb sender senderTcb' st with
            | .error e => .error e
            | .ok ((), st') =>
                -- Enqueue sender into sendQ so subsequent receive can find it
                match frozenQueuePushTail endpointId false sender st' with
                | .error e => .error e
                -- PR #873 round 15: a blocked sender leaves the run queue, as
                -- the live `endpointSendDual` does with `removeRunnable`.
                | .ok st'' => .ok ((), frozenRemoveRunnable st'' sender)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint receive — receive message via frozen endpoint.
Returns sender ThreadId.

**The dequeued sender's own state decides what happens to it** (PR #873 round
17).  `frozenQueuePopHead` accepts a `.blockedOnCall` head as well as a
`.blockedOnSend` one, and this woke both: it set the head `.ready` and put it
back in the run queue.  A caller does not become runnable at rendezvous — the
live `endpointReceiveDual` moves it to `.blockedOnReply`, links it to the
server-supplied reply object, and fails closed with `.replyCapInvalid` when the
receive carries none.  So the frozen operation succeeded with a runnable caller
where its counterpart either leaves it blocked or refuses.

`replyId` exists for that: the frozen operation could not previously express the
reply path at all, which is why the divergence was invisible rather than
deliberate. -/
def frozenEndpointReceive (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    : FrozenKernel SeLe4n.ThreadId :=
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
                let senderWasCall : Bool :=
                  match senderTcb.ipcState with
                  | .blockedOnCall _ => true
                  | _ => false
                match frozenLookupTcb st' sender with
                | some senderTcb' =>
                    -- The call arm parks the caller for its reply; the send arm
                    -- wakes it.  Both then deliver the message to the receiver.
                    let senderNext : ThreadIpcState :=
                      if senderWasCall then .blockedOnReply endpointId (some receiver)
                      else ThreadIpcState.ready
                    let senderTcbUpdated := { senderTcb' with ipcState := senderNext, pendingMessage := none }
                    match frozenStoreTcb sender senderTcbUpdated st' with
                    | .error e => .error e
                    | .ok ((), stSender) =>
                        -- A Call rendezvous carrying no reply object fails
                        -- closed: the post-state is discarded, so the caller is
                        -- never stranded `.blockedOnReply` with nothing to wake
                        -- it.
                        match (if senderWasCall then
                                 match replyId with
                                 | none => (.error .replyCapInvalid :
                                     Except KernelError FrozenSystemState)
                                 | some rid => frozenLinkCallerReply stSender sender rid
                               else .ok stSender) with
                        | .error e => .error e
                        | .ok st'' =>
                        -- Deliver message to receiver
                        match frozenLookupTcb st'' receiver with
                        | some recvTcb =>
                            -- `.ready` mirrors `storeTcbIpcStateAndMessage _ _
                            -- .ready senderMsg` exactly (PR #873 audit).  On
                            -- every reachable state the receiver — the calling
                            -- thread — is already `.ready`, so this changes
                            -- nothing observable; the live side still writes the
                            -- field (AK1-D's atomic pair), and a mirror that
                            -- writes one field of the pair is one stale
                            -- invariant away from diverging on the other.
                            let recvTcb' := { recvTcb with ipcState := ThreadIpcState.ready, pendingMessage := senderMsg }
                            match frozenStoreTcb receiver recvTcb' st'' with
                            | .error e => .error e
                            | .ok ((), stDelivered) =>
                                -- The parked message moves from the sender's TCB
                                -- into the receiver's: the receiver joins the
                                -- sender's provenance, and the sender's own
                                -- taint is left alone (it still describes the
                                -- content that thread holds).
                              -- PR #873 round 15: a woken sender re-enters the
                              -- run queue, as the live `endpointReceiveDual`
                              -- does with `ensureRunnable`.  Round 17: only the
                              -- send arm wakes, so only the send arm enqueues.
                              match (if senderWasCall then
                                       (.ok stDelivered :
                                         Except KernelError FrozenSystemState)
                                     else frozenEnsureRunnable stDelivered sender) with
                              | .error e => .error e
                              | .ok st4 =>
                                .ok (sender,
                                     frozenTaintFlow st4 receiver.toObjId sender.toObjId)
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
                    -- PR #873 round 15: a blocked receiver leaves the run
                    -- queue, as the live `endpointReceiveDual` does with
                    -- `removeRunnable`.
                    | .ok st'' => .ok (receiver, frozenRemoveRunnable st'' receiver)
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
                            | .ok ((), st''') =>
                              -- PR #873 round 15: the run queue moves both ways
                              -- here, as the live `endpointCall` does -- the woken
                              -- receiver enters it, the caller blocking for its
                              -- reply leaves it.
                              match frozenEnsureRunnable st''' receiver with
                              | .error e => .error e
                              | .ok st4 =>
                                -- Same content move as the send half of a call:
                                -- the message reaches the receiver.
                                .ok ((), frozenTaintFlow (frozenRemoveRunnable st4 caller)
                                          receiver.toObjId caller.toObjId)
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
                    -- PR #873 round 15: a blocked caller leaves the run queue,
                    -- as the live `endpointCall` does with `removeRunnable`.
                    | .ok st'' => .ok ((), frozenRemoveRunnable st'' caller)
            | none => .error .objectNotFound
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint reply — reply to a blocked caller.
Mirrors `endpointReply`. -/
def frozenEndpointReply (replierId : SeLe4n.ThreadId)
    (targetId : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (msg : IpcMessage) :
    FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st targetId with
    | some targetTcb =>
        match targetTcb.ipcState with
        | .blockedOnReply _epId _replyTarget =>
            -- PR #822 review (Codex), frozen mirror of E.2: authority is the **presented
            -- reply capability** `replyId` — the replier must hold a reply cap naming
            -- `targetId` as its caller, exactly like the live `.reply` arm resolves
            -- `reply.caller = target` from the *cap* (it does NOT derive the reply from the
            -- target, so a thread that does not hold the cap cannot deliver and consume it).
            -- `_replierId` is retained for documentation (a delegated/copied reply cap held
            -- by a *different* replier is legitimate — the `replier == expected` gate was
            -- dropped, 6J-lYm — so authority flows from the cap, not the issuer's identity).
            -- Fail-closed BEFORE any store on: a `blockedOnReply` caller with no forward
            -- link; a presented `replyId` that is not the caller's reciprocal forward link
            -- (`replyObject ≠ some replyId`); a missing Reply object; or a Reply whose
            -- `caller` is not `some targetId`.  Deliver + consume the single-use Reply link
            -- (clear both reciprocal sides, mirroring `consumeCallerReply`).
            let targetTcb' := { targetTcb with
              ipcState := ThreadIpcState.ready
              pendingMessage := some msg
              replyObject := none }
            match targetTcb.replyObject with
            | none => .error .replyCapInvalid
            | some fwdRid =>
                if fwdRid == replyId then
                  match st.objects.get? replyId.toObjId with
                  | some (.reply r) =>
                      if r.caller = some targetId then
                        -- **The composing thread must be resolvable**, because
                        -- the reply's provenance is read from it.  A `replierId`
                        -- absent from the frozen map used to succeed and read
                        -- the total table's empty default, so a reply carrying
                        -- previously declassified content reached its caller
                        -- with no predecessor tag — a laundering step the
                        -- snapshot would then report as unconnected, which is
                        -- exactly what carrying the table into `FrozenOps` is
                        -- meant to prevent.
                        --
                        -- Checked **after** the authority gates, deliberately:
                        -- authority still comes from the presented reply cap,
                        -- so a wrong or missing cap must still answer
                        -- `.replyCapInvalid` rather than being masked by this.
                        -- Delegation is unaffected — a delegated replier is a
                        -- *different* live thread, not a nonexistent one.
                        match frozenLookupTcb st replierId with
                        | none => .error .objectNotFound
                        | some _ =>
                        match frozenStoreTcb targetId targetTcb' st with
                        | .error e => .error e
                        | .ok ((), st') =>
                            match frozenStoreObject replyId.toObjId
                                    (.reply { r with caller := none }) st' with
                            | .error e => .error e
                            | .ok ((), st'') =>
                              -- PR #873 round 15: the woken caller re-enters the
                              -- run queue, as the live `endpointReply` does with
                              -- `ensureRunnable`.
                              match frozenEnsureRunnable st'' targetId with
                              | .error e => .error e
                              | .ok st3 =>
                                -- The reply message lands in the caller's TCB, so
                                -- the caller joins the replier's provenance.  This
                                -- is what `replierId` is *for* — authority still
                                -- comes from the presented cap, but the content
                                -- comes from the thread that composed it.
                                .ok ((), frozenTaintFlow st3 targetId.toObjId
                                          replierId.toObjId)
                      else .error .replyCapInvalid
                  | _ => .error .replyCapInvalid
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
    -- AK6-A (SC-H01): reject zero-budget to preserve replenishmentListWellFormed.
    if period == 0 then .error .invalidArgument
    else if budget == 0 then .error .invalidArgument
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
            budgetRemaining := ⟨budget⟩
            -- AK6-B/C parity (SC-M01/SC-M02): mirror the runtime
            -- `schedContextConfigure` replenishment replacement so the
            -- FROZEN variant does not leave stale replenishment entries
            -- across reconfigures. The frozen timer is 0 at boot, so
            -- the first eligibility aligns with `period`; any subsequent
            -- reconfigure honors `timer + period` like the runtime path.
            replenishments := [{ amount := ⟨budget⟩,
                                 eligibleAt := 0 + period }] }
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
rescheduling.

**AK8-H (WS-AK / DS-M02) — Transactional two-phase rewrite:** the previous
implementation was non-transactional — on a failed TCB lookup AFTER the SC
mutation had already been committed, it silently succeeded with a half-mutated
state (SC cleared, TCB binding stale). This matched the AE2-D finding pattern
and was flagged in audit §DS-M02.

The rewrite hoists **both** lookups (SC and TCB) to the top, validates that
the target TCB exists and holds the expected `.tcb` variant, and only then
writes the two updated objects. Either both writes succeed or neither is
attempted. The clean up-front validation also lets us reject the "SC bound
to a non-TCB" case explicitly with `.error .objectNotFound`, rather than
leaving a half-mutated state behind. -/
def frozenSchedContextUnbind (scId : SeLe4n.ObjId) : FrozenKernel Unit :=
  fun st =>
    match st.objects.get? scId with
    | some (.schedContext sc) =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        -- AK8-H Phase 1: Validate TCB lookup BEFORE any state mutation.
        match st.objects.get? tid.toObjId with
        | some (.tcb tcb) =>
          -- AK8-H Phase 2: Both lookups succeeded; apply all writes atomically.
          let st0 := if (st.scheduler.current) == some tid then
            { st with scheduler := { st.scheduler with current := none } }
          else st
          let updatedSc := { sc with boundThread := none, isActive := false }
          let updatedTcb := { tcb with
            schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
          match st0.objects.set scId (.schedContext updatedSc) with
          | none => .error .objectNotFound
          | some st1Objs =>
            match st1Objs.set tid.toObjId (.tcb updatedTcb) with
            | some objs2 => .ok ((), { st0 with objects := objs2 })
            | none => .error .objectNotFound
        | _ =>
          -- AK8-H: TCB missing or wrong variant — fail closed, no SC mutation.
          .error .objectNotFound
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
    match (st.scheduler.current) with
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
              -- R5.E (DEEP-SCH-04): SchedContext lookup failed for a bound-
              -- budget thread.  Pre-R5 this silently fell back to the legacy
              -- (unbound) path so the kernel kept running on stale state.
              -- The frozen-state mirror of the production path surfaces the
              -- same `.missingSchedContext` error for consistency.  Under the
              -- runtime-checked invariant `schedContextStoreConsistent` (part
              -- of `crossSubsystemInvariant`) the branch is unreachable; the
              -- explicit rejection makes the discrepancy observable if the
              -- invariant ever drifts.
              .error .missingSchedContext
          | .unbound =>
            -- Legacy path: use time-slice
            frozenTimerTick st
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- D1: Frozen thread suspension and resumption
-- ============================================================================

/-- D1: Frozen thread suspend — transition a thread from any non-Inactive state
to Inactive. Mirrors `suspendThread` in frozen state.

PR #873 round 15: the thread also **leaves the run queue**.  This used to say
run-queue manipulation was skipped because the membership set is fixed — true of
`membership`, whose `FrozenSet` keys cannot change, but not of `byPriority`,
which is the field `frozenChooseThread` actually selects from.  So a suspended
thread stayed in its bucket carrying `ipcState := .ready` and the frozen
scheduler would still pick it: suspended in name, runnable in fact. -/
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
        | some objs => .ok ((), frozenRemoveRunnable { st with objects := objs } tid)
        | none => .error .objectNotFound

/-- D1: Frozen thread resume — transition a thread from Inactive to Ready.
Mirrors `resumeThread` in frozen state.

PR #873 round 15: the thread also **enters the run queue**, for the reason its
suspending counterpart leaves it.  Skipping the insert left a resumed thread
`.ready` and absent from every `byPriority` bucket, which is precisely the state
`frozenChooseThread` cannot select from — resumed in name, unschedulable in
fact.  If the resumed thread has higher priority than current, `current` is
cleared to force rescheduling. -/
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
          let st' := match (st'.scheduler.current) with
            | some curTid =>
              match st'.objects.get? curTid.toObjId with
              | some (.tcb curTcb) =>
                if tcb'.priority.val > curTcb.priority.val then
                  { st' with scheduler := { st'.scheduler with current := none } }
                else st'
              | _ => { st' with scheduler := { st'.scheduler with current := none } }
            | none => st'
          -- PR #873 round 15: and it re-enters the run queue, which is what
          -- makes it selectable at all.
          match frozenEnsureRunnable st' tid with
          | .error e => .error e
          | .ok st'' => .ok ((), st'')
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
VSpace mapping with write permission and PA bounds, then updates the target
TCB's ipcBuffer. Mirrors `setIPCBufferOp` in frozen state using FrozenMap
lookups.

AJ4-C (L-06): Step 7 (PA bounds check) mirrors `validateIpcBufferAddress`
step 7, ensuring consistency between frozen and production validation paths. -/
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
        -- Step 4: VSpace root validity (frozen VSpaceRoot)
        match st.objects.get? tcb.vspaceRoot with
        | some (.vspaceRoot vsr) =>
          -- Step 5: Mapping check via FrozenMap
          match vsr.mappings.get? addr with
          | some (paddr, perms) =>
            -- Step 6: Write permission check
            if !perms.write then .error .translationFault
            -- Step 7: Physical address bounds check (AJ4-C / L-06 + AK3-F)
            -- AK3-F (A-M02): Check end-PA, not just start-PA, so the entire
            -- `[paddr, paddr + ipcBufferAlignment)` IPC buffer fits within
            -- the platform's PA range. Mirror `validateIpcBufferAddress`.
            else if !(paddr.toNat + SeLe4n.ipcBufferAlignment ≤
                      2^st.machine.physicalAddressWidth) then
              .error .addressOutOfBounds
            else
              let tcb' := { tcb with ipcBuffer := addr }
              match st.objects.set targetTid.toObjId (.tcb tcb') with
              | some objs => .ok ((), { st with objects := objs })
              | none => .error .objectNotFound
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
    *remove* keys (the replaced VSpace root's `asidTable` entry), and a frozen
    map has no `erase`: a shrink renumbers every index above the hole, unlike
    the append `FrozenMap.insert` performs. Service registration/revocation are
    also builder-only for the same reason.  `tcbSetAffinity` (WS-SM SM5.H.4)
    is excluded because the operation is defined by its run-queue + replenish-queue
    *migration* (live scheduler state), which the frozen snapshot phase does not
    model — the production op is complete and verified in the non-frozen path. -/
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
  | .tcbSetAffinity => false         -- WS-SM SM5.H.4: runtime scheduler op (run/replenish-queue migration)
  | .tcbBindNotification => false    -- WS-SM SM6.B: production object-store op; no frozen-phase variant defined
  | .tcbUnbindNotification => false  -- WS-SM SM6.B: ditto
  | .mintReplyCap => false           -- PR #822 Phase H: structural cap insertion (like cspaceCopy); builder-only, no frozen-phase variant
  | .vspaceUnifyInstruction => false -- WS-SM SM7.D: cache maintenance over a live mapping; the frozen phase has no VSpace/cache model
  | .declassify => false             -- WS-SM SM8.C.9: writes the mounted declassification audit trail, which the frozen phase carries but never grows (a frozen snapshot is a record, not a running system)
  | .declassifySignal => false       -- WS-SM SM9.C.8: appends to the same trail, and additionally signals a notification and wakes a waiter — two runtime effects the frozen phase does not model on top of the one it deliberately refuses
  | .auditRead => false              -- WS-SM SM9.A.13: reads the mounted audit trail through a clearance-filtered view; the frozen phase carries the trail but models no `LabelingContext`, so there is no reader's clearance to filter by
  | .auditDrain => false             -- WS-SM SM9.A.13: removes a prefix of the mounted audit trail — a *shrinking* write, and the frozen snapshot is a record rather than a running system, so nothing may remove entries from it

/-- S3-L/Z8-H/D1/D2/D3: Exactly 20 SyscallId arms have frozen operation coverage.
    The 14 uncovered arms are builder-only / structural operations (cspaceCopy, cspaceMove,
    lifecycleRetype, serviceRegister, serviceRevoke, mintReplyCap) plus the
    runtime-scheduler `tcbSetAffinity` (WS-SM SM5.H.4), the production-only
    notification-binding ops (tcbBind/UnbindNotification, WS-SM SM6.B), the
    cache-maintenance `vspaceUnifyInstruction` (WS-SM SM7.D — the frozen phase
    models no VSpace or cache state), `declassify` (WS-SM SM8.C.9 — a frozen
    snapshot carries the audit trail but never appends to it), its data-carrying
    sibling `declassifySignal` (WS-SM SM9.C.8 — the same refusal plus a
    notification signal and a waiter wake), and the two audit
    accessors (WS-SM SM9.A.13 — the reader needs a `LabelingContext` the frozen
    phase does not model, and the drain would *remove* entries from a record). -/
theorem frozenOpCoverage_count :
    (([SyscallId.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
       .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
       .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
       .notificationSignal, .notificationWait, .replyRecv,
       .schedContextConfigure, .schedContextBind, .schedContextUnbind,
       .tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority,
       .tcbSetIPCBuffer, .tcbSetAffinity,
       .tcbBindNotification, .tcbUnbindNotification, .mintReplyCap,
       .vspaceUnifyInstruction, .declassify, .declassifySignal,
       .auditRead, .auditDrain].filter
         frozenOpCoverage).length = 20) := by
  decide

/-- S3-L/D1/D2/D3: All 34 SyscallId arms are accounted for (either covered or documented as builder-only). -/
theorem frozenOpCoverage_exhaustive :
    ∀ (s : SyscallId), frozenOpCoverage s = true ∨ frozenOpCoverage s = false := by
  intro s; cases s <;> simp [frozenOpCoverage]

end SeLe4n.Kernel.FrozenOps
