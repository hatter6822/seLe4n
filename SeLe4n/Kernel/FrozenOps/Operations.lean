-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Core
import SeLe4n.Kernel.FrozenOps.ReleaseQueue
import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.Architecture.PageTableInstall
import SeLe4n.Kernel.IPC.DualQueue.SenderMessage

/-!
# Q7-C: Per-Subsystem Frozen Operations

**STATUS: in the production import chain since `v0.35.60`** (`SeLe4n.lean` imports
`FrozenOps.Agreement` and `FrozenOps.Invariant`), so the Tier 1 censuses and the
production/staging partition gate reach this module by derivation rather than
because someone remembered to widen them.  What remains deferred is the
*architectural* switch — `API.lean` running syscalls over frozen snapshots — which
AG8-D gated on RPi5 freeze→operate→thaw benchmarks that do not exist yet
(`docs/REGISTERED_DEBT.md`, Registered debt index C.1 row 14).  Being in the chain
is not being the dispatch path.

AF5-I (AF-43): Implements 23 frozen kernel operations that operate on
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
|10 | `frozenEndpointReply`        | `endpointReplyOnCore`      | IPC          |
|10a| `frozenEndpointReplyWithDonationReturn` | `endpointReplyCrossCoreDispatch` | IPC |
|11 | `frozenCspaceLookup`         | `cspaceLookupSlot`         | Capability   |
|12 | `frozenCspaceLookupSlot`     | `cspaceLookupSlot` (root)  | Capability   |
|13 | `frozenCspaceMint`           | `cspaceMint`               | Capability   |
|14 | `frozenCspaceDelete`         | `cspaceDeleteSlot`         | Capability   |
|15 | `frozenVspaceLookup`         | `vspaceLookupFull`         | VSpace       |
|16 | `frozenLookupServiceByCap`   | `lookupServiceByRecordedRegistration` | Service   |
|17 | `frozenSchedContextConfigure`| `schedContextConfigure`    | SchedContext |
|18 | `frozenSchedContextBind`     | `schedContextBind`         | SchedContext |
|19 | `frozenSchedContextUnbind`   | `schedContextUnbind`       | SchedContext |
|20 | `frozenSuspendThread`        | `suspendThreadOnCore`      | Lifecycle    |
|21 | `frozenResumeThread`         | `restartThreadOnCore`      | Lifecycle    |
|22 | `frozenSetPriority`          | `setPriorityOp`            | SchedContext |
|23 | `frozenSetMCPriority`        | `setMCPriorityOp`          | SchedContext |

**Lifecycle operations** (`untypedRetype`, `untypedReset`) are builder-only.
The carve adds an object and a CDT node, which a frozen map's fixed key set
cannot; the reset writes the invoked capability's free index, and its refusal
reads the untyped's child list and the derivation tree, which the frozen
phase has no operation for.
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
              match st.getTcb? tid with
              | some tcb =>
                  tcb.domain == (st.scheduler.activeDomain) &&
                  decide (tcb.ipcState = .ready)
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
        match st'.getTcb? tid with
        | some tcb =>
            if tcb.domain == (st'.scheduler.activeDomain) &&
               decide (tcb.ipcState = .ready) then
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

-- `frozenDefaultTimeSlice : Nat := 5` stood here and is **deleted** at
-- `v0.35.103`, together with the live `defaultTimeSlice` it mirrored.  Its own
-- docstring marked it DEPRECATED in favour of
-- `FrozenSchedulerState.configDefaultTimeSlice` and justified keeping it as
-- *"backward compatibility in tests that reference this constant"* — and no test
-- referenced it, nor did anything else in the tree.  A retention justification
-- that names a consumer which does not exist is the stale-claim shape this
-- project retires on sight; `frozenTimerTick` below reads
-- `st.scheduler.configDefaultTimeSlice`.

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
        match st.getTcb? tid with
        | some tcb =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset to platform-configured value, update TCB
              let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
              match frozenWithObjectStored st tid.toObjId (.tcb tcb') with
              | .ok stored =>
                  let st' := { stored with machine := tick st.machine }
                  -- Clear current to re-enqueue the preempted thread
                  let st'' := { st' with scheduler :=
                    { st'.scheduler with current := none } }
                  frozenSchedule st''
              | .error e => .error e
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              match frozenWithObjectStored st tid.toObjId (.tcb tcb') with
              | .ok stored => .ok ((), { stored with machine := tick st.machine })
              | .error e => .error e
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- Q7-C2: IPC Frozen Operations
-- ============================================================================

/-! ### WS-SM SM9.D: provenance follows content here too.

A snapshot that dropped provenance would report a system in which every
recorded downgrade is causally unconnected — the shape a laundering chain is
precisely *not* — so the analysis a frozen snapshot exists to support would come
back clean on a system that is not.  The taint lives in the frozen threads and
notifications it describes (`FrozenSystemState.declassificationTaint`), so
`freeze` carries it (`freeze_preserves_declassificationTaint`); that buys it only
for the instant of the freeze: the frozen operations below move content between
objects, and leaving the words unchanged would reproduce the same blind snapshot
one operation later.

The moves mirror the live content-derived model exactly, because they are the
same transitions on the same content channels (`TCB.pendingMessage`,
`Notification.pendingBadge`): a sink joins its source's provenance, and a
transport that hands its content on is cleared, since its taint reflects what it
currently holds rather than everything it ever held. -/

/-- WS-ZA ZA5.12: the frozen mirror of the live slot write: the taint words of
the thread or the notification at `k` become `f` of its own; any other key is
left as it is. -/
private def frozenMapTaintWords (st : FrozenSystemState) (k : SeLe4n.ObjId)
    (f : SeLe4n.Kernel.TaintWords → SeLe4n.Kernel.TaintWords) : FrozenSystemState :=
  match st.getObject? k with
  | some (.tcb t) => frozenRewriteObject st k (.tcb (t.withTaintWords (f t.taintWords)))
  | some (.notification n) =>
    frozenRewriteObject st k (.notification (n.withTaintWords (f n.taintWords)))
  | _ => st

/-- WS-SM SM9.D: a frozen content move — the sink joins the source's
provenance.  The join accumulates, so a propagation step cannot lose a link.
WS-ZA ZA5.12: the live step's mirror (`joinTaintAt`) — the source's words join
the sink's, only at a thread or a notification, and words naming no provenance
write nothing. -/
private def frozenTaintFlow (st : FrozenSystemState)
    (sink source : SeLe4n.ObjId) : FrozenSystemState :=
  let w := st.taintWordsAt source
  if w.isEmpty then st
  else frozenMapTaintWords st sink (SeLe4n.Kernel.TaintWords.join · w)

/-- WS-SM SM9.D: a frozen content consumption — the transport holds nothing
afterwards, so it carries no provenance either.  WS-ZA ZA5.12: the words are
carved clean (`clearTaintAt`'s mirror). -/
private def frozenTaintClear (st : FrozenSystemState)
    (oid : SeLe4n.ObjId) : FrozenSystemState :=
  if (st.taintWordsAt oid).isEmpty then st
  else frozenMapTaintWords st oid (fun _ => {})

/-- **WS-SM SM6.B (PR #873 round 8): the frozen bound-delivery target.**

The frozen mirror of `boundDeliveryTarget?`, and it has to agree with it exactly:
the notification has **no** ordinary waiters and its bound TCB is currently
`.blockedOnReceive` on some endpoint.  Same three conditions, same fail-safe
`none` on a dangling binding or a bound thread doing something else. -/
private def frozenBoundDeliveryTarget? (st : FrozenSystemState)
    (notificationId : SeLe4n.ObjId) : Option (SeLe4n.ThreadId × SeLe4n.ObjId) :=
  match st.getNotification? notificationId with
  | some ntfn =>
      if ntfn.waitHeadCode = 0 then
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

/-- WS-ZA ZA4.4: the frozen mirror of `modifyTcbOpt` — a TCB field write at an
optional thread; no thread, no write. -/
def frozenModifyTcbOpt (st : FrozenSystemState) (target? : Option SeLe4n.ThreadId)
    (f : TCB → TCB) : Except KernelError FrozenSystemState :=
  match target? with
  | none => .ok st
  | some t =>
      match frozenLookupTcb st t with
      | none => .error .objectNotFound
      | some tcb =>
          match frozenStoreTcb t (f tcb) st with
          | .error e => .error e
          | .ok ((), st') => .ok st'

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
    match st.getObject? notificationId with
    | some (.notification ntfn) =>
        -- **The signaller must resolve to a live TCB**, for the reason the
        -- replier must in `frozenEndpointReply`, and with one failure mode more.
        -- `frozenTaintFlow` reads the taint words at whatever `ObjId` it
        -- is handed: an absent signaller yields the carved words' empty taint,
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
                      (TCB.setIpcState { boundTcb with
                        pendingReceiveReplyCode := 0,
                        pendingMessage :=
                          some { IpcMessage.empty with badge := some badge } } .ready) st1 with
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
        -- WS-ZA ZA4.4: wake the head; its successor heads the queue (the live
        -- `notificationSignal`).
        match ntfn.waitHead with
        | some waiter =>
            let next := match frozenLookupTcb st waiter with
              | some t => t.ntfnNext
              | none => none
            let ntfn' : Notification := ntfn.withHeadPopped next
            match frozenWithObjectStored st notificationId (.notification ntfn') with
            | .ok st' =>
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
                  -- WS-ZA ZA4.4: the woken waiter leaves the queue holding no
                  -- links, and its successor heads it with no predecessor
                  -- (the live `detachNtfnHead`).
                  match (frozenStoreTcb waiter
                      (TCB.setIpcState { waiterTcb with
                        pendingMessage :=
                          some { IpcMessage.empty with badge := some badge },
                        ntfnPrevCode := SeLe4n.ThreadId.optCode none,
                        ntfnNextCode := SeLe4n.ThreadId.optCode none } .ready) st').bind
                      (fun r => (frozenModifyTcbOpt r.2 next
                        (fun t => { t with ntfnPrevCode := SeLe4n.ThreadId.optCode none })).map
                        (fun s => ((), s))) with
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
            | .error e => .error e
        | none =>
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat
            let ntfn' : Notification := {
              state := .active, 
              hasPendingBadge := true, pendingWord := mergedBadge, boundTCBCode := ntfn.boundTCBCode, taintTag0 := ntfn.taintTag0, taintTag1 := ntfn.taintTag1, taintTag2 := ntfn.taintTag2, taintTag3 := ntfn.taintTag3, taintTag4 := ntfn.taintTag4, taintTag5 := ntfn.taintTag5, taintTag6 := ntfn.taintTag6, taintTag7 := ntfn.taintTag7, taintCount := ntfn.taintCount, taintSaturated := ntfn.taintSaturated }
            match frozenWithObjectStored st notificationId (.notification ntfn') with
            | .ok stored =>
                -- Stored on the notification: it now holds the badge, so it
                -- carries the signaller's provenance until something takes it.
                .ok ((), frozenTaintFlow stored notificationId signaller.toObjId)
            | .error e => .error e
    | some _ => .error (.invalidCapability 0)
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
    match st.getObject? notificationId with
    | some (.notification ntfn) =>
        match ntfn.pendingBadge with
        | some badge =>
            let ntfn' : Notification :=
              { state := .idle, 
                hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero, boundTCBCode := ntfn.boundTCBCode, taintTag0 := ntfn.taintTag0, taintTag1 := ntfn.taintTag1, taintTag2 := ntfn.taintTag2, taintTag3 := ntfn.taintTag3, taintTag4 := ntfn.taintTag4, taintTag5 := ntfn.taintTag5, taintTag6 := ntfn.taintTag6, taintTag7 := ntfn.taintTag7, taintCount := ntfn.taintCount, taintSaturated := ntfn.taintSaturated }
            match frozenWithObjectStored st notificationId (.notification ntfn') with
            | .ok st' =>
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
            | .error e => .error e
        | none =>
            match frozenLookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  let tail := ntfn.waitTail
                  let ntfn' : Notification := ntfn.withWaiterAppended waiter
                  match frozenWithObjectStored st notificationId (.notification ntfn') with
                  | .ok st' =>
                      -- PR #886 review: clear `pendingMessage` atomically
                      -- with the block, exactly as the live idle-wait path
                      -- does since the RR3.5 fix -- storing state alone
                      -- carried a consumed message into
                      -- `.blockedOnNotification` on this side only, a
                      -- live/frozen divergence on the mirror's own
                      -- `TCB.pendingMessage` content channel.
                      --
                      -- WS-ZA ZA4.4: then linked in behind the old tail.
                      match ((frozenStoreTcbIpcStateAndMessage st' waiter
                          (.blockedOnNotification notificationId) none).bind
                          (fun stB => frozenModifyTcbOpt stB (some waiter)
                            (fun t => { t with
                              ntfnPrevCode := SeLe4n.ThreadId.optCode tail,
                              ntfnNextCode := SeLe4n.ThreadId.optCode none })) |>.bind
                          (fun stL => frozenModifyTcbOpt stL tail
                            (fun t => { t with
                              ntfnNextCode := SeLe4n.ThreadId.optCode (some waiter) }))).map
                          (fun stB => frozenRemoveRunnable stB waiter) with
                      | .error e => .error e
                      | .ok st'' => .ok (none, st'')
                  | .error e => .error e
    | some _ => .error (.invalidCapability 0)
    | none => .error .objectNotFound

/-- WS-ZA ZA4.7: an overflow word of a frozen thread's IPC buffer, read as the
live `ipcBufferReadMr` reads it (slot bound, the frame the thread's buffer slot
names as `lookupIPCBuffer` finds it, then the synced word or memory), every
failure the live decode's `.invalidMessageInfo`. -/
private def frozenReadOverflowWord (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (idx : Nat) : Except KernelError UInt64 :=
  if idx ≥ Architecture.IpcBufferRead.maxOverflowSlots then .error .invalidMessageInfo else
  match frozenLookupTcb st tid with
  | none => .error .invalidMessageInfo
  | some tcb =>
    match tcb.spaceCells[2] with
    | some cap =>
      match cap.target with
      | .object id =>
        match st.getObject? id with
        | some (.frame f) =>
          if !f.isDevice && cap.rights.mem .read then
            .ok (Architecture.IpcBufferRead.userWordAt st.machine
              (Architecture.IpcBufferRead.ipcBufferWordAt
                (SeLe4n.PAddr.ofNat (f.base.toNat + tcb.ipcBuffer.pageOffset)) idx))
          else .error .invalidMessageInfo
        | _ => .error .invalidMessageInfo
      | _ => .error .invalidMessageInfo
    | none => .error .invalidMessageInfo

/-- WS-ZA ZA4.7: the frozen decode of a sender's saved frame -- the live
decoder (`decodeSyscallArgsWith`) with the overflow words read from the frozen
IPC buffer. -/
def frozenSenderDecode (st : FrozenSystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    Except KernelError SyscallDecodeResult :=
  Architecture.RegisterDecode.decodeSyscallArgsWith (frozenReadOverflowWord st sender)
    SeLe4n.arm64DefaultLayout tcb.registerContext 32

/-- WS-ZA ZA4.7: **the message a frozen blocked sender holds** — the live
reader's definition (`blockedSenderMessageOf`) over the frozen decode of the
sender's saved frame, whose overflow words come from the frozen IPC buffer. -/
def frozenBlockedSenderMessage (st : FrozenSystemState) (sender : SeLe4n.ThreadId)
    (tcb : TCB) : IpcMessage :=
  blockedSenderMessageOf tcb (frozenSenderDecode st sender tcb)

/-- WS-ZA ZA4.7: **the message a frozen send delivers** to a waiting receiver --
the live `sendPayloadMessage` over the frozen decode of the sender's frame: a
fault's message, or the frame under the capability's badge.  A
sender that does not exist has no frame, so its decode is a refusal.  The
blocked-sender read above makes the same read under the recorded badge, so the two frozen arrival orders deliver one message, with no
capabilities on either. -/
def frozenSendPayloadMessage (st : FrozenSystemState) (sender : SeLe4n.ThreadId) :
    SendPayload → IpcMessage
  | .frame b _ =>
      senderFrameMessage
        (match frozenLookupTcb st sender with
         | some tcb => frozenSenderDecode st sender tcb
         | none => .error .objectNotFound) b
  | .fault f ctx b => faultMessage f ctx b

/-- Q7-C2/V5-O: Pop head from a frozen intrusive queue.
Follows `queueNext` link in the head TCB to advance the queue.
Returns the dequeued ThreadId, its TCB, and updated state.

V5-O (L-DS-3): Validates that the head thread's IPC state is consistent
with the queue it's being dequeued from (blocked-on-send for send queues,
blocked-on-receive for receive queues). Returns `.endpointStateMismatch`
if the head TCB's blocking state doesn't match the queue direction.

WS-ZA ZA4.7: a parked sender holds no message object -- its message is in its
saved frame and TCB (`frozenBlockedSenderMessage`), as on the live surface -- so
the blocking state is the whole of what "parked to send" means here. -/
private def frozenQueuePopHead (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st : FrozenSystemState) : Except KernelError (SeLe4n.ThreadId × TCB × FrozenSystemState) :=
  match st.getEndpoint? endpointId with
  | some ep =>
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
                then (ep.withReceiveQ queue')
                else (ep.withSendQ queue')
              -- Clear queue links on dequeued TCB (U-H01: must also clear queuePPrev
              -- to allow re-enqueue via frozenQueuePushTail, which rejects
              -- threads with queuePPrev.isSome)
              let headTcb' := { headTcb with queuePrevCode := 0, queueNextCode := 0, queuePPrevCode := 0 }
              match frozenWithObjectStored st endpointId (.endpoint ep') with
              | .ok st1 =>
                  -- **PR #897 review, swept: THE SUCCESSOR IS PROMOTED.**  The
                  -- live `endpointQueuePopHead` writes
                  -- `storeTcbQueueLinks st1 nextTid none (some .endpointHead)
                  -- nextTcb.queueNext` here; this mirror wrote **nothing**, so
                  -- the thread the pop makes the head went on naming the popped
                  -- thread as its predecessor.
                  --
                  -- That is not a refusal-set divergence but a *structural* one,
                  -- and it is the worse of the two: the new head then fails
                  -- `intrusiveQueueWellFormed`'s P2 (`queuePrev = none` and
                  -- `queuePPrev = some .endpointHead`) and, because
                  -- `dualQueueRemovalEnabled`'s `queuePPrevHeadPositionAgrees`
                  -- factor reads exactly that pair, **every later
                  -- `frozenQueueRemove` of it is refused `.illegalState`** -- the
                  -- thread is stranded in the queue for good.  Measured on the
                  -- surface's own operations, with no hand-built state: one
                  -- `frozenEndpointSend` rendezvous into a two-deep receive queue
                  -- leaves the promoted head undequeueable where the live
                  -- `endpointSendDual` leaves it removable.  It is the
                  -- OD1.1 / OD3.9 stranding class -- *a removal that writes one
                  -- of a node's two back-pointers and not the other* -- arriving
                  -- on the surface that had no theorems to catch it.
                  --
                  -- Every existing scenario popped from a **one**-deep queue,
                  -- where there is no successor and the two programs agree by
                  -- construction.  That is FO-043's lesson on a different
                  -- primitive: *a sweep for fixtures that would break is not a
                  -- sweep for fixtures that would exercise.*
                  --
                  -- The read is `frozenLookupTcb`, so an unresolvable or
                  -- reserved successor is `.objectNotFound` as it is live, and
                  -- the order is the live order -- endpoint, successor, then the
                  -- head's own clear -- so a self-linked head resolves the same
                  -- way on both surfaces.
                  let afterSuccessor : Except KernelError FrozenSystemState :=
                    match newHead with
                    | none => .ok st1
                    | some nextTid =>
                      match frozenLookupTcb st1 nextTid with
                      | none => .error .objectNotFound
                      | some nextTcb =>
                          frozenWithObjectStored st1 nextTid.toObjId (.tcb { nextTcb with
                            queuePrevCode := 0, queuePPrevCode := 1 })
                  match afterSuccessor with
                  | .error e => .error e
                  | .ok st2 =>
                    match frozenStoreTcb headTid headTcb' st2 with
                    | .error e => .error e
                    | .ok ((), st3) => .ok (headTid, headTcb, st3)
              | .error e => .error e
  | _ => .error .objectNotFound

/-- Q7-C2: Frozen endpoint send — send message via frozen endpoint.
Uses intrusive queue pop/enqueue via TCB queue links. -/
def frozenEndpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload) : FrozenKernel Unit :=
  fun st =>
    match st.getObject? endpointId with
    | some (.endpoint ep) =>
        -- **The sender is resolved once, for both orderings.**  The blocking
        -- path already did this and the rendezvous path did not, so whether a
        -- nonexistent sender was refused depended on whether a receiver
        -- happened to be waiting — and on the rendezvous ordering the message
        -- was delivered while `frozenTaintFlow` read the taint words at an id
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
                    -- WS-ZA ZA4.7: the words are read from the sender's frame,
                    -- where the receive that takes a blocked sender reads them.
                    let recvTcb' := (TCB.setIpcState { recvTcb with
                      pendingMessage := some (frozenSendPayloadMessage st sender payload),
                      pendingReceiveReplyCode := 0 } ThreadIpcState.ready)
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
            -- No receiver: block sender, then enqueue into sendQ (T1-B/M-FRZ-1).
            -- WS-ZA ZA4.7: the message stays in the sender's own frame, with its
            -- badge and grant right in its TCB (`TCB.setSendCap`), as on the
            -- live surface; the sender's provenance already covers it, so there
            -- is nothing to propagate here.
            -- `senderTcb` is the one resolved above, shared with the rendezvous
            -- ordering so the two cannot disagree about what a valid sender is.
            let senderTcb' := (TCB.setIpcState { senderTcb.setSendCap payload.badge payload.grant with
              pendingMessage := none } (.blockedOnSend endpointId))
            match frozenStoreTcb sender senderTcb' st with
            | .error e => .error e
            | .ok ((), st') =>
                -- Enqueue sender into sendQ so subsequent receive can find it
                match frozenQueuePushTail endpointId false sender st' with
                | .error e => .error e
                -- PR #873 round 15: a blocked sender leaves the run queue, as
                -- the live `endpointSendDual` does with `removeRunnable`.
                | .ok st'' => .ok ((), frozenRemoveRunnable st'' sender)
    | some _ => .error (.invalidCapability 0)
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
    match st.getObject? endpointId with
    | some (.endpoint ep) =>
        match ep.sendQ.head with
        | some _sender =>
            -- Sender waiting: pop head and transfer message
            match frozenQueuePopHead endpointId false st with
            | .error e => .error e
            | .ok (sender, senderTcb, st') =>
                -- WS-ZA ZA4.7: the parked sender's message is read from its
                -- frame and TCB, as the live receive reads it.
                let senderMsg := some (frozenBlockedSenderMessage st sender senderTcb)
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
                    let senderTcbUpdated := (TCB.setIpcState { senderTcb' with pendingMessage := none } senderNext)
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
                            let recvTcb' := (TCB.setIpcState { recvTcb with pendingMessage := senderMsg } ThreadIpcState.ready)
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
                let recvTcb' := (recvTcb.setIpcState (.blockedOnReceive endpointId))
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
    | some _ => .error (.invalidCapability 0)
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint call — send then block for reply.
Mirrors `endpointCall` using intrusive queue management. -/
def frozenEndpointCall (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) : FrozenKernel Unit :=
  fun st =>
    match st.getObject? endpointId with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _receiver =>
            -- Receiver waiting: pop head, transfer message, block caller for reply
            match frozenQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                match frozenLookupTcb st' receiver with
                | some recvTcb =>
                    -- WS-ZA ZA4.7: the words are read from the caller's frame,
                    -- in the state the call began in, as the live call reads them.
                    let recvTcb' := (TCB.setIpcState { recvTcb with
                      pendingMessage := some (frozenSendPayloadMessage st caller payload) }
                      ThreadIpcState.ready)
                    match frozenStoreTcb receiver recvTcb' st' with
                    | .error e => .error e
                    | .ok ((), st'') =>
                        -- Block caller waiting for reply
                        match frozenLookupTcb st'' caller with
                        | some callerTcb =>
                            let callerTcb' := (callerTcb.setIpcState (.blockedOnReply endpointId (some receiver)))
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
            -- No receiver: block caller, then enqueue into sendQ (T1-D/M-FRZ-3); the
            -- message stays in its frame, as for a blocked send (WS-ZA ZA4.7)
            match frozenLookupTcb st caller with
            | some callerTcb =>
                let callerTcb' := (TCB.setIpcState { callerTcb.setSendCap payload.badge payload.grant with
                  pendingMessage := none } (.blockedOnCall endpointId))
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
    | some _ => .error (.invalidCapability 0)
    | none => .error .objectNotFound

/-- Q7-C2: Frozen endpoint reply — reply to a blocked caller.

Mirrors **`endpointReplyOnCore`** (`IPC/CrossCore/EndpointReply.lean`), the leg
the live `.reply` arm dispatches, and *not* the bare single-core `endpointReply`
this docstring used to name (PR #895 review round 22).  The two differ on exactly
the authority question the body below decides: the cross-core leg's `_replier` is
unused, because the 6J-lYm gate removal made authority the presented reply
capability, while the bare leg keeps `replier == expected` and so refuses a
delegated cap holder.  This mirror accepts one, as the comments in the body say
and as `endpointReplyOnCore` does — so naming the bare leg made the claim false
on every delegated input, and `FrozenOpsSuite`'s FO-031 differential compared
against it.  `frozenBranchLiveLeg` (`FrozenOps/Agreement.lean`) now carries the
counterpart as data rather than as this sentence. -/
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
            -- **A caller with no recorded server is answered** (WS-ZA ZA6.34),
            -- as both live spellings answer it -- `endpointReplyOnCore`
            -- (`IPC/CrossCore/EndpointReply.lean`) and the bare `endpointReply`
            -- (`IPC/DualQueue/Transport.lean`) -- and as seL4-MCS's
            -- `doReplyTransfer` does: a server's finalisation forgets the
            -- callers blocked on it, so `.blockedOnReply _ none` is a reachable
            -- state, and the reply capability the replier presents is the
            -- authority to answer it.  PR #895 review round 15 made this
            -- mirror refuse the shape because the live legs then did (AK1-B /
            -- I-H02, which rated the retired `none => true` a confused-deputy
            -- risk): that refusal was fail-closed under the assumption that no
            -- reachable state records no server, an assumption the server
            -- finalisation retires.  The authority gates below -- the
            -- presented reply cap is the caller's forward link and the Reply
            -- names the caller -- are what close the confused-deputy path, and
            -- they run on this arm as on the recorded one.
            --
            -- The recorded server is read nowhere here, exactly as in
            -- `endpointReplyOnCore`: authority is the presented reply
            -- capability, so a *delegated* replier is legitimate.
            let targetTcb' := (TCB.setIpcState { targetTcb with
              pendingMessage := some msg
              replyObjectCode := 0 } ThreadIpcState.ready)
            match targetTcb.replyObject with
            | none => .error .replyCapInvalid
            | some fwdRid =>
                if fwdRid == replyId then
                  match st.getReply? replyId with
                  | some r =>
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
                        | .ok ((), st'') =>
                            -- **WS-RM, frozen mirror**: the frame above comes off
                            -- the stack BEFORE its caller link is consumed — the
                            -- removal reads the link the consume clears, so the
                            -- order is the content, exactly as it is live.
                            --
                            -- **WS-HP HP8.2**: and it **splices** rather than
                            -- severing.  The frame above takes the cut frame's
                            -- own downward link and the frame below links back up
                            -- at it, so a middle removal leaves the stack
                            -- connected and the reservation travelling outward.
                            -- HP6.3 made the live removal do this; leaving the
                            -- mirror severing would be one question answered in
                            -- two places with the answers already known to
                            -- differ, which is what `frozenBranchOperationChecked
                            -- .endpointReplyToBlockedCaller = true` forbids.
                            -- Where the cut frame is the *bottom* of its stack
                            -- the two write the same value at the frame above
                            -- (`frozenCutReplyFrameStores_eq_sever_of_no_frame_below`),
                            -- which is why every scenario this surface carried
                            -- before HP8 answers as it did.
                            let st' := frozenCutReplyFrameOutOrSelf st'' replyId
                            -- ...and the record stored is **`Reply.consumed`**, the
                            -- live function, not an inline caller clear.  It is a
                            -- pure function on a `Reply`, and this surface stores
                            -- the live `Reply`, so there is no reason to spell the
                            -- question twice — and spelling it twice got it wrong:
                            -- `consumed` keeps the links only on a frame that
                            -- **heads** a context (the pop that follows clears
                            -- them) and clears `prev` and `next` on every other,
                            -- where a bare `caller := none` leaves the frame with
                            -- no caller and links intact.  That falsifies
                            -- `Reply.wellFormed` at the frame, makes it fail
                            -- `Reply.isFree` forever — so it can never be relinked
                            -- or retyped — and diverges from the live transition
                            -- under `frozenStateAgrees`.
                            match frozenStoreObject replyId.toObjId
                                    (.reply r.consumed) st' with
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

/-- **WS-RM, frozen mirror**: the server a blocked caller's reply is recorded
against -- `recordedReplyServer?`'s counterpart. -/
def frozenRecordedReplyServer? (st : FrozenSystemState) (target : SeLe4n.ThreadId) :
    Option SeLe4n.ThreadId :=
  match st.getTcb? target with
  | some tcb =>
      match tcb.ipcState with
      | .blockedOnReply _ (some expected) => some expected
      | _                                 => none
  | none => none

/-- **WS-RM, frozen mirror of `applyReplyDonation`** — the return **and** the
deschedule, as one step.

The live function is `returnDonatedSchedContextResolved … ` followed by
`removeRunnable replier` (`IPC/Operations/Donation/Primitives.lean`), and the two
are a pair: the server has just handed its reservation back, so leaving it on a
run queue lets the scheduler select a thread that is `.unbound` and charged to
nobody -- the temporal-isolation defect PR #895 rounds 9-11 closed on the live
`.replyRecv` arm.

**This exists so the pairing cannot be forgotten again** (PR #895 review round
14).  Round 13 mirrored the *inner* call and not the live caller that pairs it
with the deschedule, and reproduced the defect on this surface -- that round's
own rule, *sharing an implementation transfers its preconditions*, failing inside
the fix that recorded it.  A frozen mirror of a live step therefore names the
live function that **completes** it, never the one nested inside.

**The sentinel holder is refused here, as the live twin refuses it** (WS-HP
HP4.7).  `applyReplyDonation` promotes the holder through `ThreadId.toValid?` and
answers `.invalidArgument` when it will not promote; that promotion is the live
step's, not `returnDonatedSchedContext`'s, so it belongs at this unit.  It is
spelled `holder.isReserved` rather than with `toValid?` because this surface uses
`toValid?` nowhere -- `frozenLookupTcb` is how it asks whether an id is usable,
and that predicate *is* `isReserved`, which in turn is exactly `= sentinel`
(`Prelude.lean`).  So the condition is the live one and the vocabulary is this
surface's, which is what keeps "is this id usable" one question here rather than
two.  Reachable only on a malformed frozen state -- a SchedContext bound to the
sentinel thread, which no live invariant admits and which `Model.freeze` would
copy verbatim if one existed -- and that is precisely the class this surface's
guards exist for. -/
def frozenApplyReplyDonation (st : FrozenSystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) :
    Except KernelError FrozenSystemState :=
  if holder.isReserved then .error (.invalidArgument 0)
  else
    match frozenReturnDonatedSchedContextResolved st holder scId originalOwner with
    | .error e => .error e
    | .ok st' => .ok (frozenRemoveRunnable st' holder)

/-- **WS-RM, frozen mirror of the whole `.reply` operation** (PR #895 review
round 13).

`frozenEndpointReply` above is the mirror of the reply **leg**
(`endpointReplyOnCore`; not the bare `endpointReply`, whose authority gate this
surface does not carry — PR #895 review round 22), and that is exactly what
`FrozenOpsSuite`'s FO-031 differential compares it against.
But the live `.reply` *operation* is that reply **followed by the donation
return**, and this surface had only the first half -- so `Reply.consumed`, which
deliberately keeps a stack head's links because "the pop that follows clears
them", was storing a record whose contract nothing here met.  A frozen state
captured mid-donation-chain (`freeze` copies Reply objects verbatim, links and
all) therefore left the answered Reply failing `Reply.isFree` forever: it could
never be re-linked to a new caller and never retyped, so a passive server could
not complete a second call/reply cycle on it.

The pop belongs **here and not inside `frozenEndpointReply`** for a reason worth
keeping: the bare live reply leaves a head linked too, so moving the pop into the
mirror would make it diverge from the very function it refines -- the refinement
that currently holds is what tells this surface apart from a guess.

The donation is resolved on the **pre**-state, because the reply clears both
things a resolver could key on: the `ipcState` that records the server, and the
`replyObject` that names the answered frame.

**...and it is resolved from the FRAME** (WS-HP HP8.1).  HP4 made the live
`.reply` operation head-driven — `endpointReplyCrossCoreDispatch` reads
`replyFrameHeadHolder?` and pops the context the answered frame **heads** — and
this mirror read the recorded server's `.donated` binding.  The two coincide on
every state `severAtCut` leaves, which is why nothing here failed, and part
company on the states HP6's splice creates: that is this project's *one question
answered in two places will diverge*, with the divergence already on the
schedule.  The frame needs no resolving here, because `replyId` **is** the
presented reply capability and `frozenEndpointReply` refuses it unless the
target's own `replyObject` names it — so this surface asks the head question of
exactly the frame the live operation recovers through `answeredReplyObject?`.

Two consequences worth stating.  The pop's subject is the frame's **holder**
(the context's `boundThread`), which on a delegated reply capability is neither
the replier nor, since HP6's splice (`v0.35.45`), necessarily the recorded
server.  And the
recipient is `targetId` — the caller being answered — rather than the binding's
recorded `originalOwner`; the two agree wherever `donationOwnerValid` holds, and
the frame reading is the one that stays true when a middle frame has been
spliced out.

**...and priority inheritance is reverted on every successful reply** (PR #895
review round 15), donation or none.  The answered caller was blocked *on* the
recorded server, so it was one of that server's waiters and contributed to its
`TCB.pipBoost`; the reply makes it `.ready`, so the boost has to be recomputed
from whoever is left.  Both live compositions do this -- the **live** spine
`endpointReplyCrossCoreDispatch` with `propagatePipChainCrossCore`
(`IPC/CrossCore/EndpointReplyDispatch.lean`), which is what the `.reply` arm
dispatches and what this composite is compared against, and the superseded
single-core `endpointReplyWithDonation` with `revertPriorityInheritance`
(`IPC/Operations/Donation.lean`, no production caller and a reply leg that
refuses a delegated cap holder -- PR #895 review round 22) -- and this surface
did not, so a stale boost survived.  That is not inert here: `frozenEnsureRunnable` buckets by
`frozenEffectivePriority`, which reads `pipBoost`, so the next time the server is
made runnable it enters the run queue at a priority it inherited from a client
it has already answered.

It runs **after** the donation return, as both live compositions do, and takes
the **recorded server** as its subject -- not the (possibly delegated) cap
holder, which is nobody's blocking target.  Like the pop, it belongs in this
composite and not in `frozenEndpointReply`: neither bare live reply reverts, and
the mirror is refined against the bare one.

**...and a frame heading a context no thread holds is popped too** (WS-ZA
ZA6.34), as the live unheld arm pops it (`frozenPopUnheldReplyHead`): the
context donated to the answered caller, or the head popped off alone where that
caller holds a context of its own (seL4-MCS's `reply_pop`).  A caller recording
no server — its server's finalisation forgot it — is answered with no
reversion, as the live spine answers it. -/
def frozenEndpointReplyWithDonationReturn (replierId : SeLe4n.ThreadId)
    (targetId : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (msg : IpcMessage) :
    FrozenKernel Unit :=
  fun st =>
    -- **WS-HP HP8.1**: the head-driven trigger, read on the pre-state.
    let headHolder? := frozenReplyFrameHeadHolder? st replyId
    let server? := frozenRecordedReplyServer? st targetId
    match frozenEndpointReply replierId targetId replyId msg st with
    | .error e => .error e
    | .ok ((), st') =>
      match headHolder?, server? with
      | some (scId, holder), some server =>
          -- **WS-HP HP10.8**: the recipient at the BOTTOM of the stack is the
          -- reservation's recorded origin, exactly as the live arm has read it
          -- since HP10.7.  The resolver is read on the PRE-state `st`, because
          -- `frozenEndpointReply` has already consumed the answered caller's
          -- reply link by the time `st'` exists -- the same reason the live
          -- trigger takes its frame as an argument.  A window in which the live
          -- arm redirects and this one does not makes
          -- `frozenBranchOperationChecked .endpointReplyToBlockedCaller = true`
          -- an over-claim, which is HP4.7's situation verbatim.
          match frozenApplyReplyDonation st' holder scId
                  (frozenReplyDonationRecipient st scId targetId) with
          | .error e => .error e
          | .ok st'' => .ok ((), frozenRevertPriorityInheritance st'' server)
      -- **WS-ZA ZA6.34**: a frame heading a context no thread holds -- its
      -- server was finalised and returned the context to no one -- is popped
      -- as the live unheld arm pops it (`frozenPopUnheldReplyHead`, read on the
      -- state the pop runs on, as `applyReplyDonationOnCore` reads it): the
      -- context donated to the answered caller, or, where that caller holds a
      -- context of its own, the head popped off alone; a frame heading nothing
      -- pops nothing.
      | none, some server =>
          match frozenPopUnheldReplyHead st' replyId targetId with
          | .error e => .error e
          | .ok st'' => .ok ((), frozenRevertPriorityInheritance st'' server)
      -- **WS-ZA ZA6.34**: a caller recording no server -- its server was
      -- finalised, which forgot it -- is answered as the live spine answers it:
      -- the reply leg, then the pop at the answered frame, and no reversion,
      -- since the walk starts at a server and none is recorded.
      | some (scId, holder), none =>
          match frozenApplyReplyDonation st' holder scId
                  (frozenReplyDonationRecipient st scId targetId) with
          | .error e => .error e
          | .ok st'' => .ok ((), st'')
      | none, none =>
          match frozenPopUnheldReplyHead st' replyId targetId with
          | .error e => .error e
          | .ok st'' => .ok ((), st'')

-- ============================================================================
-- Q7-C3: Capability Frozen Operations
-- ============================================================================

/-- Q7-C3: Frozen CSpace lookup — O(1) via CNodeRadix.
Uses zero-hash bit extraction for direct array indexing. -/
def frozenCspaceLookup (st : FrozenSystemState) (cptr : SeLe4n.CPtr)
    (rootId : SeLe4n.ObjId) : Except KernelError Capability :=
  match st.getObject? rootId with
  | some (.cnode cn) =>
      let slot := SeLe4n.Slot.ofNat (cptr.slotBits 0 cn.radixWidth)
      match cn.slots.lookup slot with
      | some cap => .ok cap
      | none => .error (.invalidCapability 0)
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
where a mint operation clobbers an existing capability without revoking it.

WS-BP BP7.1 (`v0.36.38`): the inserted capability carries **no mapping
record** (`Capability.withoutMapping`), as every live derivation's does
(seL4's `deriveCap`).  A record says *this* capability made a mapping, and a
new capability made none; inserting one verbatim would let the finalising
delete of the copy remove a mapping another capability owns. -/
def frozenCspaceMint (rootId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (cap : Capability) : FrozenKernel Unit :=
  fun st =>
    match st.getObject? rootId with
    | some (.cnode cn) =>
        -- V5-P: Reject if slot is already occupied
        match cn.slots.lookup slot with
        | some _ => .error .targetSlotOccupied
        | none =>
            let slots' := cn.slots.insert slot cap.withoutMapping
            let cn' : FrozenCNode := { cn with slots := slots' }
            match frozenWithObjectStored st rootId (.cnode cn') with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | some _ => .error .objectNotFound
    | none => .error .objectNotFound

/-- WS-BP BP7.1 (`v0.36.12`): the frozen mirror of
`Architecture.pageTableInstallLive` — the table's record names a root, and that
root holds the slot the record names, for this table. -/
def frozenPageTableInstallLive (st : FrozenSystemState) (id : SeLe4n.ObjId) : Bool :=
  match st.getObject? id with
  | some (.pageTable p) =>
    match p.installedIn with
    | some inst =>
      match st.getObject? inst.root with
      | some (.vspaceRoot root) => root.tables.contains (inst.slotFor id)
      | _ => false
    | none => false
  | _ => false

/-- WS-BP BP7.1 (`v0.36.12`): does the capability name an installed page table? -/
def frozenCapNamesInstalledPageTable (st : FrozenSystemState) (cap : Capability) : Bool :=
  match cap.target with
  | .object id => frozenPageTableInstallLive st id
  | _ => false

/-- Q7-C3: Frozen CSpace delete — erase a capability from a frozen CNode.

WS-BP BP7.1 (`v0.36.7`): a capability carrying a **mapping record** is refused
with `.revocationRequired`.  The live delete (`cspaceDeleteSlotFinalising`)
removes the recorded mapping before it returns — seL4's `finaliseCap` →
`unmapPage` — and this surface has no VSpace unmap to perform it with, so
erasing the slot here would leave a mapping whose frame capability is gone:
the defect the live cut closes.  Refusing is the one sound mirror of a step
the surface cannot model, and it can only refuse what the live kernel
performs, never admit what it refuses.

WS-BP BP7.1 (`v0.36.12`): a capability naming an **installed page table** is
refused for the same reason.  The live delete takes the table out of its address
space when the capability is the table's last (`finaliseDestroyedCapabilities`),
which this surface cannot model either; it cannot even decide *last* cheaply, so
it refuses every such capability — a subset of what the live kernel performs. -/
def frozenCspaceDelete (rootId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    : FrozenKernel Unit :=
  fun st =>
    match st.getObject? rootId with
    | some (.cnode cn) =>
      if (cn.slots.lookup slot).any
          (fun cap => cap.mapping.isSome || frozenCapNamesInstalledPageTable st cap) then
        .error .revocationRequired
      else
        let slots' := cn.slots.erase slot
        let cn' : FrozenCNode := { cn with slots := slots' }
        match frozenWithObjectStored st rootId (.cnode cn') with
        | .ok st' => .ok ((), st')
        | .error e => .error e
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
        match st.getVSpaceRoot? rootId with
        | some vsr =>
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
Mirrors `lookupServiceByRecordedRegistration`, the O(1) lookup the live kernel runs:
the endpoint records whether a registration names it and the registration's
words (`Endpoint.service`, WS-ZA ZA5.8), and a service's identity is its
endpoint's, so the lookup reads that endpoint and no table. -/
def frozenLookupServiceByCap (epId : SeLe4n.ObjId)
    : FrozenKernel ServiceRegistration :=
  fun st =>
    match frozenLookupEndpoint st epId with
    | some ep =>
      match ep.serviceRegistered with
      | false => .error .objectNotFound
      | true => .ok (ep.service.registrationAt epId, st)
    | none => .error .objectNotFound

-- ============================================================================
-- Z8-H: Frozen SchedContext Operations
-- ============================================================================

/-- **WS-ZA ZA6.4: the frozen mirror of configure's resume tail**
(`SchedContextOps.configureResumeBound`, seL4-MCS's `schedContext_resume` then
`possibleSwitchTo` at the end of `invokeSchedControl_ConfigureFlags`), on the
configured context `sc` and its bound thread `t`, over the state the
propagation halves left.  Arm for arm, in this surface's vocabulary:

* the **current** thread is left where it is.  Live, a current thread is on no
  run queue (`queueCurrentConsistent`, dequeue-on-dispatch), so the live tail's
  queued arm cannot see it and its current arm writes only the reschedule flag,
  which the frozen surface does not carry (frozen dispatch also leaves a current
  thread in its bucket, so it must be asked about before the bucket is);
* a **queued** thread stays queued while the context can run it now
  (`budgetRemaining` positive) and is taken out of its bucket otherwise
  (`frozenRemoveRunnable`, the live `runRemoveOnCore`);
* a **parked** runnable thread (`frozenBindPlacesParkedThread`, the mirror of the
  guard the live tail reads) is placed in the bucket its effective priority
  names (`frozenRebucketRunnable`, which only appends when the thread is in no
  bucket).  The live insert priority is `resolveInsertPriority`, which for a
  thread bound to the context it was just configured from is
  `TCB.boostedPriority` — the key the frozen bind places at, for the same
  reason;
* anything else is left as it is.

Without it a runnable bound thread parked off every bucket stayed outside every
bucket after a configure that gave its context budget, so `frozenChooseThread`
could never select it while the live scheduler could. -/
def frozenConfigureResumeBound (st : FrozenSystemState) (t : SeLe4n.ThreadId)
    (sc : SeLe4n.Kernel.SchedContext) : FrozenSystemState :=
  if st.scheduler.current == some t then st
  else if frozenQueuedAnywhere st t then
    if sc.budgetRemaining.isPositive then st else frozenRemoveRunnable st t
  else
    match frozenLookupTcb st t with
    | some tcb =>
      if frozenBindPlacesParkedThread st t tcb sc then
        frozenRebucketRunnable st t tcb.boostedPriority
      else st
    | none => st

/-- Z8-H: Frozen SchedContext configure — update scheduling parameters.
Mirrors `schedContextConfigure` in frozen state. SchedContext is passthrough-
frozen (no internal RHTables), so this is a straightforward lookup + store.
Validates parameters and checks admission control against frozen state.

WS-SX SX6.4: the context carries no priority, deadline or domain — those are
the bound thread's own, as in seL4-MCS — so, like the live configure, this writes
the context alone and propagates nothing to the bound thread. -/
def frozenSchedContextConfigure (scId : SeLe4n.ObjId)
    (budget period : Nat) (extraRefills badge flags : UInt64) : FrozenKernel Unit :=
  fun st =>
    -- Parameter validation: the live operation's own
    -- (`SchedContextOps.validateSchedContextParams`), so the two answer every
    -- refusal with one error and payload.  AK6-A (SC-H01): a zero budget is
    -- refused, preserving replenishmentListWellFormed.
    match SeLe4n.Kernel.SchedContextOps.validateSchedContextParams budget period with
    | .error e => .error e
    | .ok () =>
      match st.getObject? scId with
      | some (.schedContext sc) =>
        -- WS-ZA ZA6.4: the live configure's refills (`configuredSchedContext`):
        -- seL4-MCS's `refill_update` for a context in use, `refill_new`
        -- otherwise, so the frozen mirror hands out the new budget once, as the
        -- live operation does.  The keep decision is `configureKeepsHead`'s,
        -- read over the frozen store.
        let keep : Bool := budget != period && sc.budget.val != 0 &&
          match sc.boundThread with
          | some t => (frozenLookupTcb st t).any TCB.isRunnable
          | none => false
        let updated : SeLe4n.Kernel.SchedContext :=
          SeLe4n.Kernel.SchedContextOps.configuredSchedContext budget period extraRefills badge flags
             st.machine.timer keep sc
        -- Admission control: collect all SchedContexts from frozen store
        let allScs := st.objects.fold (init := []) fun acc _id obj =>
          match obj with
          | .schedContext sc' => if sc'.scId.toObjId == scId then acc else sc' :: acc
          | _ => acc
        if SeLe4n.Kernel.admissionCheck allScs updated then
          -- WS-ZA ZA6.37: the live configure's release-queue writes, mirrored:
          -- the context off the queue its own link names
          -- (`frozenPurgeReplenishment`, the live `purgeReplenishment`) before
          -- the record is stored, and a bound context placed on its thread's
          -- home core's queue by its refills (`frozenReleasePlace`, the live
          -- `releasePlace`) before the propagation reads the stored state.
          let scIdTyped : SeLe4n.SchedContextId := ⟨scId.toNat⟩
          match frozenWithObjectStored (frozenPurgeReplenishment st scIdTyped) scId
              (.schedContext updated) with
          | .ok stStored =>
            -- WS-ZA ZA6.4: then the live resume tail (`frozenConfigureResumeBound`)
            -- over the stored state, as the live `configureResumeBound` runs
            -- whenever the bound thread exists.
            match sc.boundThread with
            | none => .ok ((), stStored)
            | some boundTid =>
              let st' := frozenReleasePlace stStored (frozenDetermineTargetCore st boundTid) scIdTyped
              match frozenLookupTcb st' boundTid with
              | none => .ok ((), st')
              | some _ => .ok ((), frozenConfigureResumeBound st' boundTid updated)
          | .error e => .error e
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
    match st.getObject? scId with
    | some (.schedContext sc) =>
      if sc.boundThread.isSome then .error .illegalState
      -- **PR #897 review, the sweep the origin fix owed.**  The live bind refuses
      -- four things and this mirror refused one, so it **succeeded where the
      -- kernel refuses** -- the direction that matters on a differential surface,
      -- and the `v0.35.59` shape one operation over (*a named condition beside
      -- unnamed ones is a subset*).  The three below are the live guards in the
      -- live order, so the two agree on the error code as well as on the verdict.
      --
      -- WS-OD (`v0.35.4`): a context that heads a reply stack is on loan down a
      -- call chain and owed back along it; binding it elsewhere would give it a
      -- second claimant the pop then displaces.
      else if sc.scReply.isSome then .error .illegalState
      else
        match st.getTcb? threadId with
        | some tcb =>
          -- WS-SX SX6.4: no domain check, as the live bind has none (seL4-MCS's
          -- `decodeSchedContext_Bind`): a context carries no domain.
          --
          -- WS-OD (`v0.35.4`): a thread blocked on a reply whose frame is on a
          -- live stack is owed a context by the pop that reaches that frame, and
          -- that pop writes its binding; a second context now would be
          -- overwritten by it and orphaned.
          if frozenReplyFrameOnLiveStack st tcb then .error .illegalState
          else
          match tcb.schedContextBinding with
          | .unbound =>
            let scIdTyped : SeLe4n.SchedContextId := ⟨scId.toNat⟩
            -- **WS-HP HP10.4, frozen mirror (PR #897 review).**  A bind ends any
            -- loan, so the recorded origin clears — the live clause, which this
            -- mirror did not carry.  `FrozenSystemState` holds the **live**
            -- `SchedContext` record and `Model.freeze` copies it verbatim, so a
            -- frozen state taken mid-chain really does carry an origin; leaving it
            -- here would let `frozenDonationOriginRecipient?` hand a later
            -- bottom-of-stack return to a thread this bind has nothing to do with,
            -- which is the thread-id-reuse hazard the field's own docstring names.
            -- A field added to a shared record is a sweep of **both** surfaces,
            -- not of the one whose transition motivated it.
            let updatedSc := { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some threadId),
                                       donationOrigin := none }
            let updatedTcb := { tcb with
              scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SeLe4n.Kernel.SchedContextBinding.bound scIdTyped), scBindingOwnerCode := 0 }
            match frozenWithObjectStored st scId (.schedContext updatedSc) with
            | .ok st1 =>
              -- **WS-RR RR8.12 Cut B2 (`v0.35.182`)**: the bind **places** a parked
              -- runnable thread, which is the live bind's own new arm and
              -- seL4-MCS's `SCHED_ENQUEUE` tail.  `frozenWriteTcbBoundPlaced` is
              -- the bind-specific writer rather than a widening of
              -- `frozenWriteTcbRebucketed`: the other callers of that one are
              -- priority writes, and a priority write must not make a parked
              -- thread schedulable — only a bind, which hands it a reservation,
              -- may.
              match frozenWriteTcbBoundPlaced st1 threadId updatedTcb sc with
              | .ok st2 => .ok ((), st2)
              | .error e => .error e
            | .error e => .error e
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
    match st.getObject? scId with
    | some (.schedContext sc) =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        -- AK8-H Phase 1: Validate TCB lookup BEFORE any state mutation.
        match st.getTcb? tid with
        | some tcb =>
          -- WS-OD (PR #894 review): **the donated-holder rejection this path
          -- claims to mirror.**  `schedContextUnbind` refuses to unbind a holder
          -- that received the context by donation, because erasing that binding
          -- while the context's stack still names the caller leaves the caller's
          -- frame dead on the stack — the Reply and the context can then never be
          -- retyped.  This operation's own docstring says it mirrors that one,
          -- and it cleared both sides unconditionally, so the frozen path could
          -- construct exactly the dead stack the live guard exists to prevent.
          -- `freezeObject` preserves TCBs and SchedContexts verbatim, so the
          -- shape reaches here intact; one question must not have two answers.
          if tcb.schedContextBinding.isDonated then .error .illegalState else
          -- AK8-H Phase 2: Both lookups succeeded; apply all writes atomically.
          let st0 := if (st.scheduler.current) == some tid then
            { st with scheduler := { st.scheduler with current := none } }
          else st
          -- **WS-HP HP10.4, frozen mirror (PR #897 review)**: and the origin,
          -- for the bind's reason in the other direction — the reservation stops
          -- being owned at all, so a recorded departure from ownership has no
          -- subject.  Both live arms of `schedContextUnbind` clear it; a mirror
          -- that keeps history the kernel erases is a mirror that answers a later
          -- pop differently.
          let updatedSc := { sc with boundThreadCode := 0, isActive := false,
                                     donationOrigin := none }
          let updatedTcb := { tcb with
            scBindingScCode := 0, scBindingOwnerCode := 0 }
          match frozenWithObjectStored st0 scId (.schedContext updatedSc) with
          | .error e => .error e
          | .ok st1 =>
            match frozenWithObjectStored st1 tid.toObjId (.tcb updatedTcb) with
            | .ok st2 => .ok ((), st2)
            | .error e => .error e
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
        match st.getTcb? tid with
        | some tcb =>
          match tcb.schedContextBinding with
          | .bound scId | .donated scId _ =>
            -- CBS path: decrement SchedContext budget
            match st.getSchedContext? scId with
            | some sc =>
              -- WS-ZA ZA6.4: the live charge of the unit run from `timer`
              -- (`chargeBudget`), and its exhaustion test (`tickExhausts`).
              let updatedSc := sc.chargeBudget st.machine.timer 1 (st.machine.timer + 1)
              let wasPreempted := sc.tickExhausts st.machine.timer
              match frozenWithObjectStored st scId.toObjId (.schedContext updatedSc) with
              | .ok stored =>
                let st' := { stored with machine := tick st.machine }
                if wasPreempted == true then
                  -- Budget exhausted: the context waits on the release queue
                  -- for its first pending refill (WS-ZA ZA6.37: the live
                  -- `replenishOnCore`, `releasePlace` on the core the tick runs
                  -- on, which on this single-core surface is the boot core),
                  -- and current is cleared to force rescheduling.
                  let stPlaced := frozenReleasePlace st' bootCoreId scId
                  .ok ((), { stPlaced with scheduler :=
                    { stPlaced.scheduler with current := none } })
                else
                  .ok ((), st')
              | .error e => .error e
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

/-- A TCB field write at `t` that writes nothing when `t` names no TCB, as the
live `SystemState.updateTcb` and `mapTcbInPlace` write nothing there. -/
def frozenMapTcbAt (st : FrozenSystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    FrozenSystemState :=
  match st.getTcb? t with
  | some tcb => frozenRewriteObject st t.toObjId (.tcb (g tcb))
  | none => st

/-- WS-SX SX4: **`w` leaves server `s`'s reply-waiter queue** — the frozen
mirror of `SystemState.unlinkReplyWaiter`, write for write: the predecessor and
successor link past `w`, `s`'s head moves past it when it headed the queue,
`s`'s count drops, and `w` keeps no links. -/
def frozenUnlinkReplyWaiter (st : FrozenSystemState) (w s : SeLe4n.ThreadId) :
    FrozenSystemState :=
  let pv := match st.getTcb? w with | some t => t.replyWaiterPrevCode | none => 0
  let nx := match st.getTcb? w with | some t => t.replyWaiterNextCode | none => 0
  let st1 := match SeLe4n.ThreadId.ofOptCode pv with
    | some p => frozenMapTcbAt st p fun x => { x with replyWaiterNextCode := nx }
    | none => st
  let st2 := match SeLe4n.ThreadId.ofOptCode nx with
    | some n => frozenMapTcbAt st1 n fun x => { x with replyWaiterPrevCode := pv }
    | none => st1
  let st3 := frozenMapTcbAt st2 s fun x => { x with
    replyWaitersHeadCode := if pv = 0 then nx else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }
  frozenMapTcbAt st3 w fun x => { x with replyWaiterPrevCode := 0, replyWaiterNextCode := 0 }

/-- WS-SX SX4: **a thread leaves the notification wait queue it is blocked on** —
the frozen mirror of `removeFromNotificationWaitQueue`, write for write: the
notification's head and tail move past it (and a `.waiting` notification left
with no waiter goes `.idle`), it keeps no queue links, and its neighbours link
past it. -/
def frozenRemoveFromNotificationWaitQueue (st : FrozenSystemState) (tid : SeLe4n.ThreadId) :
    FrozenSystemState :=
  match st.getTcb? tid with
  | some tcb =>
    match tcb.ipcState with
    | .blockedOnNotification oid =>
      match st.getNotification? oid with
      | some notif =>
        let prev := tcb.ntfnPrev
        let next := tcb.ntfnNext
        let isHead := notif.waitHead = some tid
        let head' := if isHead then next else notif.waitHead
        let tail' := if next.isSome then notif.waitTail
          else if isHead then none else prev
        let notif' : Notification := { notif with
          waitHeadCode := SeLe4n.ThreadId.optCode head'
          waitTailCode := SeLe4n.ThreadId.optCode tail'
          state := if notif.state = .waiting ∧ head'.isNone then .idle else notif.state }
        let st1 := frozenRewriteObject st oid (.notification notif')
        let st2 := frozenMapTcbAt st1 tid fun t => { t with
          ntfnPrevCode := SeLe4n.ThreadId.optCode none,
          ntfnNextCode := SeLe4n.ThreadId.optCode none }
        let prev' := if isHead then none else prev
        let st3 := match prev' with
          | some p => frozenMapTcbAt st2 p fun t => { t with
              ntfnNextCode := SeLe4n.ThreadId.optCode next }
          | none => st2
        match next with
        | some n => frozenMapTcbAt st3 n fun t => { t with
            ntfnPrevCode := SeLe4n.ThreadId.optCode prev' }
        | none => st3
      | none => st
    | _ => st
  | none => st

/-- WS-SX SX4: **a cancelled caller's frame cut off the context it heads, the
context staying with its holder** — the frozen mirror of
`cutHeadFrameKeepingContext` (seL4-MCS `reply_remove_tcb`'s head branch): the
frame's upward link cleared, the context's head and origin cleared, and a holder
holding the context on loan made its owner.  (The live cut also raises the
holder's reschedule-pending flags, which the frozen surface does not keep.) -/
def frozenCutHeadFrameKeepingContext (st : FrozenSystemState) (rid : SeLe4n.ReplyId) :
    FrozenSystemState :=
  match frozenReplyFrameHeadContext? st rid with
  | none => st
  | some scId =>
    match st.getReply? rid with
    | none => st
    | some r =>
      let st1 := frozenRewriteObject st rid.toObjId (.reply { r with next := none })
      let st2 := match st1.getSchedContext? scId with
        | some sc => frozenRewriteObject st1 scId.toObjId
            (.schedContext { sc with scReply := none, donationOrigin := none })
        | none => st1
      match (st2.getSchedContext? scId).bind (·.boundThread) with
      | none => st2
      | some holder =>
        match st2.getTcb? holder with
        | none => st2
        | some ht =>
          match ht.schedContextBinding with
          | .donated s _ =>
            if s = scId then frozenMapTcbAt st2 holder fun t => { t with scBindingOwnerCode := 0 }
            else st2
          | _ => st2

/-- WS-SX SX4: **the caller's reply link consumed** — the frozen mirror of
`SystemState.consumeCallerReplyLink`: the reply's consumed record
(`Reply.consumed`), and the caller holding no reply object. -/
def frozenConsumeCallerReplyLink (st : FrozenSystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : FrozenSystemState :=
  let st1 := match st.getReply? rid with
    | some r => frozenRewriteObject st rid.toObjId (.reply r.consumed)
    | none => st
  frozenMapTcbAt st1 caller fun t => { t with replyObjectCode := 0 }

/-- WS-SX SX4: **the cancelled thread's reply frame cut out of its stack** — the
frozen mirror of `cutThreadReplyFrameOut`: the removal under the thread's own
`replyObject`, and nothing for a thread holding none. -/
def frozenCutThreadReplyFrameOut (st : FrozenSystemState) (tcb : TCB) : FrozenSystemState :=
  match tcb.replyObject with
  | none => st
  | some rid => frozenCutReplyFrameOutOrSelf st rid

/-- WS-SX SX4: **a cancelled thread leaves the endpoint queue it waits on** — the
frozen mirror of `removeFromBlockingEndpoint`, and total as it is.  First the
interior splice (`spliceOutMidQueueNode`): the predecessor skips the thread
(`queueUnlinkPredecessor`) and the successor inherits its back links
(`queueUnlinkSuccessor`), the successor read after the predecessor's patch.
Then, when an end of either queue names the thread, both queues' boundaries
move past it (`removeThreadFromQueue`, through the shared `queueRemoveBoundary`).
A missing endpoint leaves the splice alone, as on the live path: a cancel does
not refuse. -/
def frozenRemoveFromBlockingEndpoint (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : FrozenSystemState :=
  let stSpliced := match frozenLookupTcb st tid with
    | none => st
    | some tcb =>
      let s1 := match tcb.queuePrev with
        | some p => frozenMapTcbAt st p (queueUnlinkPredecessor tcb)
        | none => st
      match tcb.queueNext with
      | some n => frozenMapTcbAt s1 n (queueUnlinkSuccessor tcb)
      | none => s1
  let boundary (q : IntrusiveQueue) : IntrusiveQueue :=
    match frozenLookupTcb stSpliced tid with
    | some tcb => queueRemoveBoundary q tid tcb
    | none => { head := if q.head = some tid then none else q.head,
                tail := if q.tail = some tid then none else q.tail }
  match stSpliced.getEndpoint? epId with
  | some ep =>
    if ep.sendQ.head == some tid || ep.sendQ.tail == some tid
        || ep.receiveQ.head == some tid || ep.receiveQ.tail == some tid then
      frozenRewriteObject stSpliced epId
        (.endpoint ((ep.withSendQ (boundary ep.sendQ)).withReceiveQ (boundary ep.receiveQ)))
    else stSpliced
  | none => stSpliced

/-- WS-SX SX4: **seL4-MCS's `cancelIPC`, as the suspend runs it, on the frozen
store** — the mirror of `cancelIpcKeepingContexts`, arm for arm, for every
object other than the cancelled thread's own record, which the suspend then
writes through the live record step (`TCB.restoredToRestart`).

* **Endpoint** (send, call, receive): the thread leaves the endpoint queue its
  state names (`frozenRemoveFromBlockingEndpoint`, the frozen
  `removeFromBlockingEndpoint`).
* **Notification**: it leaves the notification's wait queue
  (`frozenRemoveFromNotificationWaitQueue`).
* **Reply**: its frame is cut off the context it heads, which stays with its
  holder (`frozenCutHeadFrameKeepingContext`); then, as
  `cancelIpcKeepingContexts_reply_arm` states the live arm, there is no donation
  left to return, so the frame is cut out of its stack
  (`frozenCutThreadReplyFrameOut`), the reply link is consumed
  (`frozenConsumeCallerReplyLink`) and the caller leaves its server's
  reply-waiter queue (`frozenUnlinkReplyWaiter`).

Total, as the live cancel is: every arm writes what it can and none refuses, so
a suspend never fails on the state of the queue its thread waited on. -/
def frozenCancelIpcBlocking (st : FrozenSystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    FrozenSystemState :=
  match tcb.ipcState with
  | .ready => st
  | .blockedOnSend ep | .blockedOnCall ep | .blockedOnReceive ep =>
    frozenRemoveFromBlockingEndpoint st tid ep
  | .blockedOnNotification _ => frozenRemoveFromNotificationWaitQueue st tid
  | .blockedOnReply _ _ =>
    let st1 := match tcb.replyObject with
      | some rid => frozenCutThreadReplyFrameOut (frozenCutHeadFrameKeepingContext st rid) tcb
      | none => st
    let st2 := match tcb.replyObject with
      | some rid => frozenConsumeCallerReplyLink st1 tid rid
      | none => st1
    match tcb.blockingServer? with
    | some s => frozenUnlinkReplyWaiter st2 tid s
    | none => st2

/-- D1: Frozen thread suspend — transition a thread to Inactive (a thread
already Inactive is left as it is). Mirrors `suspendThread` in frozen state.

PR #873 round 15: the thread also **leaves the run queue**.  This used to say
run-queue manipulation was skipped because the membership set is fixed — true of
`membership`, whose `FrozenSet` keys cannot change, but not of `byPriority`,
which is the field `frozenChooseThread` actually selects from.  So a suspended
thread stayed in its bucket carrying `ipcState := .ready` and the frozen
scheduler would still pick it: suspended in name, runnable in fact.

WS-ZA ZA6.6: **and its yield link goes as the live suspend's does**: the
suspend ends as seL4-MCS's `suspend` ends, with the thread's yield cancelled
(`schedContext_cancelYieldTo`, the live `cancelYieldTo`): the context it names
forgets its yielder and the thread its context.  WS-ZA ZA6.33: **no reservation
ends**: a context bound to the thread stays bound and one it holds on loan stays
with it, as seL4-MCS's `suspend` keeps `tcbSchedContext`; the frozen surface
keeps no release queue, so `tcbReleaseRemove` has nothing to write here.

WS-SX SX4: **a blocked thread's cancel is the live one's record step**
(`TCB.restoredToRestart`, which the live `cancelIpcBlocking` reaches through
`restoreToReadyCancelled`).  Its IPC fields are cleared, its fault record is
retired, and its saved program counter is moved to its restart PC, so the
suspended thread is `Inactive` at the `SVC` it was blocked in, and the frozen
resume (`frozenResumeThread`, which suspends a blocked thread first) restarts it
there, as the live `restartThreadOnCore` does.

WS-SX SX4 (PR #1084 review): **and the blocking itself is cancelled, in every
arm**, before that record step (`frozenCancelIpcBlocking`, the mirror of the
live `cancelIpcKeepingContexts`): the thread is spliced out of its endpoint
queue at any position, out of its notification's wait queue, and, blocked on a
reply, cut off a donated context's reply stack, its reply link consumed and its
server's reply-waiter entry unlinked, after which the server's inherited boost
is reverted (`frozenRevertPriorityInheritance`).  Clearing the TCB's own fields
alone left the endpoint naming a thread that no longer waited.  Each arm, and
the runnable and `Inactive` suspends, is compared whole against
`suspendThreadOnCore` by `FrozenOpsSuite`'s registered `.tcbSuspend` branches. -/
def frozenSuspendThread (tid : SeLe4n.ThreadId) : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st tid with
    | none => .error .objectNotFound
    | some tcb =>
      -- WS-SX SX4: an already-`Inactive` thread is suspended with nothing
      -- written, as the live `suspendThreadOnCore` and seL4's `suspend` leave it.
      if tcb.threadState == .Inactive then .ok ((), st)
      else
        -- WS-SX SX4: the IPC cancelled as the live suspend cancels it
        -- (`frozenCancelIpcBlocking`, the mirror of `cancelIpcKeepingContexts`),
        -- so no endpoint, notification or reply-waiter queue names the thread
        -- afterwards and its reply link is consumed.
        let stC := frozenCancelIpcBlocking st tid tcb
        -- Then its own record, read again (the cancel cleared its links and
        -- its reply object), through the live record step
        -- (`TCB.restoredToRestart`): its saved program counter moves to its
        -- restart PC (the `SVC`, or its fault's restart PC, read before the
        -- fault record is cleared), so a later resume re-issues the call.  A
        -- thread not blocked keeps its program counter, as on the live path.
        let cur := (frozenLookupTcb stC tid).getD tcb
        let base := if tcb.ipcState != .ready then cur.restoredToRestart else cur
        let tcb' := (TCB.setIpcState { base with
          threadState := .Inactive
          pendingMessage := none
          timeoutBudget := none
          queuePrevCode := 0
          queueNextCode := 0
          queuePPrevCode := 0
          yieldToCode := 0 } .ready)
        match frozenWithObjectStored stC tid.toObjId (.tcb tcb') with
        | .error e => .error e
        | .ok stR =>
        -- The server a reply-blocked thread waited on has its inheritance
        -- reverted, as the live suspend's `suspendCancelRevert` reverts it
        -- (`frozenRevertPriorityInheritance`, the counterpart the frozen reply
        -- uses for the same live step).
        let stP := match tcb.blockingServer? with
          | some s => frozenRevertPriorityInheritance stR s
          | none => stR
        let cleared : Except KernelError FrozenSystemState :=
          match tcb.yieldToCode with
          | 0 => .ok stP
          | k + 1 =>
            let scId : SeLe4n.SchedContextId := ⟨k⟩
            match stP.getObject? scId.toObjId with
            | some (.schedContext sc) =>
              frozenWithObjectStored stP scId.toObjId
                (.schedContext { sc with yieldFromCode := 0 })
            | _ => .ok stP
        match cleared with
        | .error e => .error e
        | .ok st1 => .ok ((), frozenRemoveRunnable st1 tid)

/-- WS-ZA ZA6.33: **the frozen mirror of the resume's context step**
(`Lifecycle.Suspend.resumeContext`, seL4-MCS's `refill_unblock_check` then
`schedContext_resume`), on the resumed thread's record `t`, with the live
`resumeSchedulable` answer beside it.  The context the thread runs on has its
ready head moved to now (`SchedContext.refillUnblockCheck`); the frozen surface
keeps no release queue, so the placement has nothing to write.  An unbound
thread is schedulable on its own time slice; one on a context is schedulable when
the context's head has budget now, and one naming a context the store does not
hold is not. -/
def frozenResumeContext (st : FrozenSystemState) (t : TCB) :
    Except KernelError (Bool × FrozenSystemState) :=
  match t.schedContextBinding.scId? with
  | none => .ok (true, st)
  | some s =>
    match st.getSchedContext? s with
    | none => .ok (false, st)
    | some sc =>
      let sc' := sc.refillUnblockCheck st.machine.timer
      match frozenWithObjectStored st s.toObjId (.schedContext sc') with
      | .ok st' => .ok (sc'.budgetRemaining.isPositive, st')
      | .error e => .error e

/-- D1: Frozen thread resume — transition a thread from Inactive to Restart (seL4's `restart`), as the live `resumeThread` does.
Mirrors `resumeThread` in frozen state.

PR #873 round 15: the thread also **enters the run queue**, for the reason its
suspending counterpart leaves it.  Skipping the insert left a resumed thread
`.ready` and absent from every `byPriority` bucket, which is precisely the state
`frozenChooseThread` cannot select from — resumed in name, unschedulable in
fact.

**And it mirrors the live resume's three scheduling steps** (`v0.35.134`).  All
three were absent, and each is a divergence from `resumeThread` on a state the
frozen surface reaches.  They were found by sweeping the question PR #897's
review asked of `frozenComputeMaxWaiterPriority` — *which priority does this
surface read* — one function over, which is why they are one cut with it.

1. **The field clear is `TCB.restoredToReady`** (`Model/Object/Types.lean`), the
   live `restoreToReady`'s own function rather than a second list of fields.
   This set `ipcState := .ready` and stopped, so the three intrusive-queue links
   and the stashed receive Reply survived the resume.  The stashed Reply is the
   sharper half: `replyIsStashed` stays true, so lifecycle cleanup of that Reply
   answers `revocationRequired` with no receive pending — the defect PR #822's
   review added the live clear for, alive here because the clear had no name to
   call.

2. **`pipBoost` is recomputed from the blocking graph** (live H3b).  While the
   thread was `.Inactive`, threads may have blocked on it or stopped blocking on
   it, so a carried-over boost is stale in both directions: too high and the
   thread runs at an inherited band nobody is waiting for, too low and the
   inversion priority inheritance exists to prevent is live.  It is computed on
   the **cleared** state, as live computes it after `restoreToReady`, so a thread
   whose own `ipcState` recorded it as blocked on itself does not count itself.

3. **The preemption comparison reads `TCB.boostedPriority`**, which is what the
   live comparison's `resolveEffectivePrioDeadline` resolves to
   (`resolveEffectivePrioDeadline_fst_eq_boostedPriority`).  It compared
   `tcb'.priority` against `curTcb.priority` — the **bases** — so the two
   surfaces disagreed in both directions whenever either thread carried a boost:
   a boosted resumed thread failed to preempt the lower-priority thread its boost
   exists to get ahead of, and an unboosted resumed thread preempted a boosted
   current one.  No fixture could see it (none of the three frozen resume
   scenarios set `current` at all, so the branch was unexecuted) and no
   differential could reach it (`.tcbResume` has no `FrozenOpBranch`: its
   scenarios compare objects only, since the live restart dispatches at its
   scheduling point and this resume leaves selection to `frozenSchedule`).

Clearing `current` **is** the frozen spelling of the live re-enqueue-then-
schedule: dispatch here is `current := some tid` with the thread left in its
bucket, so clearing it makes the outgoing thread selectable again, exactly as
`frozenHandleYield` documents.  The enqueue runs after the comparison where live
runs it before; the order is immaterial, because the enqueue touches only
`byPriority` and the comparison reads only the two TCBs.

WS-ZA ZA6.33: **and the context is resumed before either** (`frozenResumeContext`):
the live resume runs `resumeContext` and then enqueues only a schedulable thread,
so a thread whose context has no budget now is left out of every bucket, with
neither a comparison nor an enqueue.

**And it is seL4's `restart`, as the live `.tcbResume` is**
(`Lifecycle.Suspend.restartThreadOnCore`): a thread that is not stopped is
left as it is, with no error, and one blocked in an IPC is suspended first, which
cancels the IPC and leaves it `Inactive` with its saved program counter at its
restart PC (`TCB.restoredToRestart`, as on the live path), and then resumed, so
it runs at the `SVC` it was blocked in and re-issues the call. -/
def frozenResumeThread (tid : SeLe4n.ThreadId) : FrozenKernel Unit :=
  fun st0 =>
    match frozenLookupTcb st0 tid with
    | none => .error .objectNotFound
    | some tcb0 =>
      -- seL4's `restart` acts only on a stopped thread (`isStopped`): one that
      -- is neither `Inactive` nor blocked in an IPC is left as it is.
      if tcb0.threadState != .Inactive && tcb0.ipcState == .ready then .ok ((), st0)
      else
      -- A thread blocked in an IPC has the IPC cancelled first, as the live
      -- restart cancels it through the suspend (`frozenSuspendThread`), which
      -- leaves it `Inactive`.
      let stopped : Except KernelError FrozenSystemState :=
        if tcb0.threadState == .Inactive then .ok st0
        else
          match frozenSuspendThread tid st0 with
          | .ok ((), st1) => .ok st1
          | .error e => .error e
      match stopped with
      | .error e => .error e
      | .ok st =>
      match frozenLookupTcb st tid with
      | none => .error .objectNotFound
      | some tcb =>
        -- (1) the shared restore, committed first so (2) reads a state in which
        -- the resumed thread is no longer recorded as blocked on anything.
        match frozenWithObjectStored st tid.toObjId (.tcb tcb.restoredToReady) with
        | .error e => .error e
        | .ok stCleared =>
          -- (2) the boost re-derived from the post-restore blocking graph.
          let tcb' := { tcb.restoredToReady with
                          threadState := .Restart
                          pipBoostCode := SeLe4n.Priority.optCode (frozenComputeMaxWaiterPriority stCleared tid) }
          match frozenWithObjectStored stCleared tid.toObjId (.tcb tcb') with
          | .ok stored =>
            -- (3) WS-ZA ZA6.33: the context resumed (`frozenResumeContext`, the
            -- live `resumeContext`'s refill-unblock check); only a schedulable
            -- thread goes on, as the live resume's `resumeSchedulable` gate.
            match frozenResumeContext stored tcb' with
            | .error e => .error e
            | .ok (false, stCtx) => .ok ((), stCtx)
            | .ok (true, stored) =>
            -- (4) preemption on the EFFECTIVE priority, off the record just
            -- stored, so the refreshed boost is the one compared.
            let st' := match (stored.scheduler.current) with
              | some curTid =>
                match stored.getTcb? curTid with
                | some curTcb =>
                  if tcb'.boostedPriority.val > curTcb.boostedPriority.val then
                    { stored with scheduler := { stored.scheduler with current := none } }
                  else stored
                | _ => { stored with scheduler := { stored.scheduler with current := none } }
              | none => stored
            -- PR #873 round 15: and it re-enters the run queue, which is what
            -- makes it selectable at all -- at the bucket `tcb'.boostedPriority`
            -- names, which (2) may have moved.
            match frozenEnsureRunnable st' tid with
            | .error e => .error e
            | .ok st'' => .ok ((), st'')
          | .error e => .error e

-- ============================================================================
-- D2-L: Frozen priority management operations
-- ============================================================================

/-- **The frozen mirror of `updatePrioritySource`**: the thread's base priority
has one home, its TCB (WS-SX SX6.4: a scheduling context carries no priority, as
in seL4-MCS), and this writes it.

Both frozen operations that move a base priority call this, so the surface has
one answer: `frozenSetPriority` directly, and `frozenSetMCPriority` when its
ceiling bites.

**And the write re-buckets** (`v0.35.101`, reported on PR #897).  The frozen run
queue is keyed by `TCB.boostedPriority`, which is `priority.raisedBy pipBoost` --
so a base-priority write moves a queued thread's bucket exactly as a boost write
does, and this wrote the field and stopped.  `frozenChooseThread` folds
`byPriority`, so the frozen kernel went on ordering the thread by the band this
write had just removed, where the live `applyPriorityChangeOnCore` composes
`migrateRunQueueBucketOnCore` onto `updatePrioritySource` for precisely that
reason; worse, a later `frozenEnsureRunnable` appends when the thread is absent
from the bucket for its *new* priority, so the thread would have ended in **two**.
`frozenWriteTcbRebucketed` is the shared answer -- the mechanics were spelled
inline in `frozenUpdatePipBoost` and so answered the boost half only, which is
this project's *one question answered in two places* shape with one of the places
never answering. -/
def frozenWriteBasePriority (st : FrozenSystemState) (targetTid : SeLe4n.ThreadId)
    (targetTcb : TCB) (newPriority : SeLe4n.Priority) :
    Except KernelError FrozenSystemState :=
  frozenWriteTcbRebucketed st targetTid { targetTcb with priority := newPriority }

/-- D2-L: Frozen-phase setPriority. Validates MCP authority, then writes the
target thread's own TCB priority (`frozenWriteBasePriority`), at every binding.

WS-SX SX6.4: a scheduling context carries no priority, so the thread's TCB is
the priority's only home, as in seL4-MCS's `setPriority`; the frozen mirror and
the live `updatePrioritySource` write the same field. -/
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
        -- Write the thread's own priority (its only home).
        match frozenWriteBasePriority st targetTid targetTcb newPriority with
        | .ok st' => .ok ((), st')
        | .error e => .error e

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
        -- `v0.35.99`: the ceiling on the TCB, then the capped base priority
        -- through the shared writer -- the live `setMCPriorityOnCore`'s own
        -- control flow (rewrite the ceiling, then `applyPriorityChangeOnCore`).
        -- Two divergences closed here, mirror images of each other: the cap is
        -- compared against `threadBasePriority`, which reads the *reservation*
        -- for a `.bound` thread and which this arm read off the TCB; and the
        -- capped value was written to the TCB alone, where the live path writes
        -- both homes.
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        match frozenWithObjectStored st targetTid.toObjId (.tcb targetTcb') with
        | .error e => .error e
        | .ok st1 =>
          if (st1.threadBasePriority targetTcb').val > newMCP.val then
            match frozenWriteBasePriority st1 targetTid targetTcb' newMCP with
            | .ok st' => .ok ((), st')
            | .error e => .error e
          else .ok ((), st1)

-- ============================================================================
-- S3-L/U-M29: Frozen operation exhaustiveness check
-- ============================================================================

/-- S3-L: SyscallId arms covered by frozen operations.
    This inductive type enumerates all SyscallId arms that have a corresponding
    frozen operation. The compile-time check ensures that adding a new SyscallId
    without a frozen operation (or vice versa) produces a type error.

    Lifecycle operations (`untypedRetype`, `untypedReset`) are intentionally
    excluded — the carve adds keys a frozen map's fixed key set cannot hold,
    and the reset is its companion: it writes back the free index the carve
    advanced. Service registration/revocation are builder-only too.  `tcbSetAffinity` (WS-SM SM5.H.4)
    is excluded because the operation is defined by its run-queue + replenish-queue
    *migration* (live scheduler state), which the frozen snapshot phase does not
    model — the production op is complete and verified in the non-frozen path. -/
def frozenOpCoverage : SyscallId → Bool
  | .send => true             -- frozenEndpointSend
  | .receive => true          -- frozenEndpointReceive
  | .call => true             -- frozenEndpointCall
  | .reply => true            -- frozenEndpointReplyWithDonationReturn:
                             -- the reply leg then the donation return, as the
                             -- live `.reply` operation does.  `frozenEndpointReply`
                             -- alone is the mirror of the LEG `endpointReplyOnCore`
                             -- -- not the bare `endpointReply`, which keeps the
                             -- `replier == expected` gate this surface does not
                             -- (PR #895 review round 22).
  | .cspaceMint => true       -- frozenCspaceMint
  | .cspaceCopy => false      -- builder-only (structural copy)
  | .cspaceMove => false      -- builder-only (structural move)
  | .cspaceDelete => true     -- frozenCspaceDelete
  | .cspaceRevoke => false    -- WS-RR RR8.16 (`v0.35.190`): builder-only.  Since
                             -- WS-ZA ZA5.3 part 8 the arm is `cteRevoke`'s loop
                             -- of finalising deletes
                             -- (`cspaceRevokeCdtFinalising`), which tears down
                             -- each destroyed frame's mapping; the frozen phase
                             -- has no form of it.
  | .untypedRetype => false   -- WS-BP BP7.1 (`v0.36.5`): adds a key (the carved
                             -- object) and a CDT node, which the frozen phase's
                             -- fixed key set cannot.
  | .untypedReset => false    -- WS-BP BP7.1 (`v0.36.6`): the carve's companion,
                             -- writing back the free index the carve advanced;
                             -- the frozen phase carves nothing.
  | .vspaceMap => false       -- WS-BP BP7.1 (`v0.36.38`): a map WRITES a mapping,
                             -- a frame-capability record and a physical-write
                             -- ledger entry; the frozen phase has only
                             -- `frozenVspaceLookup`, a read, and a read is not a
                             -- mirror of a write.  It was `true` on the strength
                             -- of that lookup.
  | .vspaceUnmap => false     -- WS-BP BP7.1 (`v0.36.38`): ditto — an unmap writes
                             -- the mapping, the ledger and a shootdown round.
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
  | .tcbSetIPCBuffer => false        -- WS-SX SX6.6: deletes the buffer slot and inserts the derived frame cap with a CDT copy edge; the frozen phase models no CDT write
  | .tcbSetAffinity => false         -- WS-SM SM5.H.4: runtime scheduler op (run/replenish-queue migration)
  | .tcbSetSpace => false            -- WS-BP BP7.1 (`v0.36.11`): production object-store op; no frozen-phase variant defined
  | .pageTableMap => false           -- WS-BP BP7.1 (`v0.36.12`): translation-table install; the frozen phase models no page-table objects' installs
  | .pageTableUnmap => false         -- WS-BP BP7.1 (`v0.36.12`): ditto
  | .yield => false                  -- WS-ZA ZA4.3: per-core scheduler op (charges the executing core's
                                     -- caller, replenish and run queues), like `.tcbSetAffinity`
  | .schedContextConsumed => false   -- WS-ZA ZA6.9: writes the executing core's caller's registers; no frozen-phase variant defined
  | .schedContextYieldTo => false    -- WS-ZA ZA6.29: per-core scheduler op (the executing core's caller and run queue); no frozen-phase variant defined
  | .irqHandlerAck => false          -- WS-ZA ZA6.32: writes the interrupt controller's mask (a machine write); no frozen-phase variant defined
  | .irqControlGet => false          -- WS-ZA ZA6.32: writes the line's state and mask (machine writes); no frozen-phase variant defined
  | .irqHandlerSetNotification => false -- WS-ZA ZA6.32: a finalising delete and a copy into the line's node; no frozen-phase variant defined
  | .irqHandlerClear => false        -- WS-ZA ZA6.32: a finalising delete of the line's node slot; no frozen-phase variant defined
  | .tcbBindNotification => false    -- WS-SM SM6.B: production object-store op; no frozen-phase variant defined
  | .tcbUnbindNotification => false  -- WS-SM SM6.B: ditto
  | .mintReplyCap => false           -- PR #822 Phase H: structural cap insertion (like cspaceCopy); builder-only, no frozen-phase variant
  | .vspaceUnifyInstruction => false -- WS-SM SM7.D: cache maintenance over a live mapping; the frozen phase has no VSpace/cache model
  | .declassify => false             -- WS-SM SM8.C.9: writes the mounted declassification audit trail, which the frozen phase carries but never grows (a frozen snapshot is a record, not a running system)
  | .declassifySignal => false       -- WS-SM SM9.C.8: appends to the same trail, and additionally signals a notification and wakes a waiter — two runtime effects the frozen phase does not model on top of the one it deliberately refuses
  | .auditRead => false              -- WS-SM SM9.A.13: reads the mounted audit trail through a clearance-filtered view; the frozen phase carries the trail but models no `LabelingContext`, so there is no reader's clearance to filter by
  | .auditDrain => false             -- WS-SM SM9.A.13: removes a prefix of the mounted audit trail — a *shrinking* write, and the frozen snapshot is a record rather than a running system, so nothing may remove entries from it

/-- S3-L/Z8-H/D1/D2/D3: exactly **17** `SyscallId` arms have frozen operation
coverage; the other 24 carry the reason beside their own `frozenOpCoverage` row.

The count is taken over `SyscallId.all`, the derived constructor list, not a
hand-written one: the enumeration this replaced named every constructor by hand
and its docstring still said "18 uncovered" when 21 were, and "20 covered"
included two arms (`vspaceMap`, `vspaceUnmap`) whose only frozen operation was a
read (`v0.36.38`). -/
theorem frozenOpCoverage_count :
    (SyscallId.all.filter frozenOpCoverage).length = 17 := by
  decide

/-- S3-L/D1/D2/D3: All 38 SyscallId arms are accounted for (either covered or documented as builder-only). -/
theorem frozenOpCoverage_exhaustive :
    ∀ (s : SyscallId), frozenOpCoverage s = true ∨ frozenOpCoverage s = false := by
  intro s; cases s <;> simp [frozenOpCoverage]

end SeLe4n.Kernel.FrozenOps
