-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.IPC.CrossCore.NotificationBindDispatch
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.F.2 — Aggregate SMP cross-core notification suite

The acceptance-gate aggregate notification suite for WS-SM Phase SM6
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §SM6.F): end-to-end cross-core
signal/wait flows on a **4-core** deterministic fixture, composing the SM6.B
transitions with the SM5 per-core scheduler (SGI handler dispatch) into full
signal round trips.

Where the per-phase suite (`SmpCrossCoreNotificationSuite`) exercises each
transition in isolation, this suite drives **multi-step pipelines** threaded
through the evolving state:

* **§3.1** wait blocks the waiter on its own core (per-core descheduling);
* **§3.2** the wait → cross-core signal → `.reschedule` SGI → target-core
  handler-dispatch round trip (the woken waiter runs on its home core);
* **§3.3** multi-waiter drain: successive signals wake head waiters one at a
  time, each to its **own** home core, with per-waiter badge isolation;
* **§3.4** badge accumulation: waiterless signals merge badges (`Badge.bor`);
  a later wait consumes the merged badge without blocking;
* **§3.5** the **remote bound-TCB delivery** round trip: a signal to a bound
  notification dequeues the `BlockedOnReceive` bound TCB from its endpoint and
  wakes it on its home core with an SGI, completed by the handler dispatch;
* **§3.6** the bind/unbind lifecycle (both binding directions, fall-through
  signal preservation, double-bind rejection);
* **§3.7** fail-closed error paths (absent/wrong-kind objects, double wait) —
  every error returns the pre-state;
* **§3.8** cross-core independence framing + the state-resolved 2PL lock-set
  footprints.

`lake exe smp_notification_suite` runs all scenarios; a notification-logic
regression flips a decidable check.
-/

namespace SeLe4n.Testing.SmpNotification

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (elaboration-time: rename/removal breaks this suite)
-- ============================================================================

-- The cross-core notification transitions (SM6.B, production):
#check @notificationSignalOnCore
#check @notificationWaitOnCore
#check @notificationSignalBoundOnCore
#check @notificationSignalBoundCrossCoreDispatch
#check @notificationSignalBoundCrossCoreDispatchChecked
#check @notificationWaitCrossCoreDispatch
#check @notificationWaitCrossCoreDispatchChecked
#check @bindNotification
#check @unbindNotification
#check @boundDeliveryTarget?
-- Pre-resolution + state-resolved lock-sets (SM3.B.3 / SM6.B.1):
#check @notificationSignalWaiter?
#check @lockSet_notificationSignalOnCore
#check @lockSet_notificationWaitOnCore
-- Acceptance-gate theorems (SGI emission, multi-waiter discipline, blocking):
#check @notificationSignalOnCore_remote_wake
#check @notificationSignalOnCore_remote_wake_preState
#check @notificationSignalOnCore_no_sgi_if_local_waiter
#check @notificationSignalOnCore_noWaiter_no_sgi
#check @notificationSignalOnCore_wakes_head
#check @notificationSignalOnCore_remaining_waiters
#check @notificationSignalOnCore_perCore_consistent
#check @notificationSignalOnCore_atomic_under_lockSet
#check @notificationWaitOnCore_perCore_blocking
#check @notificationWaitOnCore_atomic_under_lockSet
#check @notificationSignalWaiter?_eq_wake_head
-- Bound delivery (SM6.B v0.31.70+, production):
#check @notificationSignalBoundOnCore_delivery_remote_wake
#check @notificationSignalBoundOnCore_delivery_no_sgi_if_local
#check @notificationSignalBoundOnCore_fallthrough_eq
#check @lockSet_notificationSignalOnCore_bound_endpoint_write_mem
#check @lockSet_notificationSignalOnCore_bound_tcb_write_mem
-- Whole-bundle preservation (SM6.D completion, production):
#check @notificationSignalOnCore_preserves_ipcInvariantFull
#check @notificationWaitOnCore_preserves_ipcInvariantFull
#check @notificationSignalOnCore_preserves_ipcInvariantFull_perCore
#check @notificationWaitOnCore_preserves_ipcInvariantFull_perCore

-- ============================================================================
-- §2  Elaboration-time witnesses (headline theorems applied to typed inputs)
-- ============================================================================

/-- SM6.B.1 no-waiter reduction: a waiterless signal merges its badge into the
notification (word-bounded `bor`), preserving the binding; no SGI. -/
example (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (st' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = none)
    (hStore : storeObject notificationId (.notification
        { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := some (match ntfn.pendingBadge with
            | some existing => SeLe4n.Badge.bor existing badge
            | none => SeLe4n.Badge.ofNatMasked badge.toNat), boundTCB := ntfn.boundTCB }) st = .ok ((), st')) :
    notificationSignalOnCore notificationId badge executingCore st = (st', .ok none) :=
  notificationSignalOnCore_noWaiter_eq notificationId badge executingCore st ntfn st'
    hObj hWaiters hStore

/-- SM6.B.1 waiter reduction: a signal on a waiting head is the badge delivery
+ cross-core wake, surfacing exactly the wake's SGI. -/
example (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'') :
    notificationSignalOnCore notificationId badge executingCore st
      = ((wakeThread st'' waiter executingCore).1,
         .ok (wakeThread st'' waiter executingCore).2) :=
  notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn waiter rest
    st' st'' hObj hWaiters hStore hMsg

-- ============================================================================
-- §3  Runtime scenarios — the deterministic 4-core notification fixture
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩
private def c3 : CoreId := ⟨3, by decide⟩

-- Fixture OIDs (range 900–999 — see the range table in SeLe4n/Testing/Helpers.lean).
private def cnRoot : SeLe4n.ObjId := ⟨900⟩
private def vsRoot : SeLe4n.ObjId := ⟨905⟩
private def nId : SeLe4n.ObjId := ⟨910⟩
private def epId : SeLe4n.ObjId := ⟨920⟩
private def signallerT : SeLe4n.ThreadId := ⟨921⟩
private def waiter2 : SeLe4n.ThreadId := ⟨922⟩
private def waiter3 : SeLe4n.ThreadId := ⟨923⟩
private def boundT : SeLe4n.ThreadId := ⟨924⟩

-- Distinct pinned badges (per-waiter badge isolation is asserted on the values).
private def badge1 : SeLe4n.Badge := SeLe4n.Badge.ofNatMasked 3
private def badge2 : SeLe4n.Badge := SeLe4n.Badge.ofNatMasked 5

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := vsRoot, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- The 4-core notification workload: an idle notification + an endpoint (for the
bound-delivery flow) + a signaller on core 0, two waiters homed on cores 2/3, and
a to-be-bound TCB homed on core 1 — each runnable on its **own** core's run
queue.  The signaller is unbound (home = boot core 0). -/
private def stFourCore : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
      |>.withObject epId (.endpoint {})
      |>.withObject signallerT.toObjId (.tcb (mkTcb 921 40 none))
      |>.withObject waiter2.toObjId (.tcb (mkTcb 922 30 (some c2)))
      |>.withObject waiter3.toObjId (.tcb (mkTcb 923 30 (some c3)))
      |>.withObject boundT.toObjId (.tcb (mkTcb 924 35 (some c1)))
      |>.build)
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0 (RunQueue.ofList [(signallerT, ⟨40⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(boundT, ⟨35⟩)])).setRunQueueOnCore
        c2 (RunQueue.ofList [(waiter2, ⟨30⟩)])).setRunQueueOnCore
        c3 (RunQueue.ofList [(waiter3, ⟨30⟩)])) }

-- Fail-closed Option plumbing for the multi-step pipelines.
private def okPair {α : Type} (r : SystemState × Except KernelError α) :
    Option (SystemState × α) :=
  match r with
  | (st, .ok a) => some (st, a)
  | (_, .error _) => none

private def okExcept {α : Type} (r : Except KernelError α) : Option α :=
  match r with
  | .ok a => some a
  | .error _ => none

/-- Read the notification's waiter list from a state (empty on absence). -/
private def waiterList (st : SystemState) : List SeLe4n.ThreadId :=
  match st.objects[nId]? with
  | some (.notification ntfn) => ntfn.waitingThreads.val
  | _ => []

/-- Decidable predicate: `tid`'s ipcState in `st` equals `expected`. -/
private def ipcStateIs (st : SystemState) (tid : SeLe4n.ThreadId)
    (expected : ThreadIpcState) : Bool :=
  match st.getTcb? tid with
  | some t => decide (t.ipcState = expected)
  | none => false

/-- Decidable predicate: `tid`'s delivered badge in `st` equals `expected`. -/
private def deliveredBadgeIs (st : SystemState) (tid : SeLe4n.ThreadId)
    (expected : SeLe4n.Badge) : Bool :=
  match st.getTcb? tid with
  | some t => t.pendingMessage.bind (·.badge) == some expected
  | none => false

/-- The full wait/signal/handle round-trip pipeline (every intermediate state +
every surfaced SGI).  Both waiters block from their own cores (waiter 2 first,
so waiter 3 is the list head — `notificationWait` prepends); two signals from
core 0 then drain the list head-first, each handled on its target core. -/
private structure NtfnRoundTrip where
  afterWait2 : SystemState
  waitRes2   : Option SeLe4n.Badge
  afterWait3 : SystemState
  afterSig1  : SystemState
  sgiSig1    : Option (CoreId × SgiKind)
  afterH3    : SystemState
  afterSig2  : SystemState
  sgiSig2    : Option (CoreId × SgiKind)
  afterH2    : SystemState

private def ntfnRoundTrip? : Option NtfnRoundTrip := do
  let (afterWait2, waitRes2) ← okPair (notificationWaitOnCore nId waiter2 c2 stFourCore)
  let (afterWait3, _) ← okPair (notificationWaitOnCore nId waiter3 c3 afterWait2)
  let (afterSig1, sgiSig1) ← okPair (notificationSignalOnCore nId badge1 c0 afterWait3)
  let afterH3 ← okExcept (handleRescheduleSgiOnCore afterSig1 c3)
  let (afterSig2, sgiSig2) ← okPair (notificationSignalOnCore nId badge2 c0 afterH3)
  let afterH2 ← okExcept (handleRescheduleSgiOnCore afterSig2 c2)
  pure { afterWait2 := afterWait2, waitRes2 := waitRes2, afterWait3 := afterWait3,
         afterSig1 := afterSig1, sgiSig1 := sgiSig1, afterH3 := afterH3,
         afterSig2 := afterSig2, sgiSig2 := sgiSig2, afterH2 := afterH2 }

-- ============================================================================
-- §3.1  Wait blocks the waiter on its own core (per-core descheduling)
-- ============================================================================

private def runWaitBlockChecks : IO Unit := do
  IO.println "--- §3.1 wait blocks the waiter on its own core ---"
  match ntfnRoundTrip? with
  | none => assertBool "notification round-trip pipeline succeeded" false
  | some rt =>
    assertBool "the block-path wait returns no badge"
      (rt.waitRes2 == none)
    assertBool "wait blocks waiter 2 as blockedOnNotification"
      (ipcStateIs rt.afterWait2 waiter2 (.blockedOnNotification nId))
    assertBool "wait deschedules waiter 2 from core 2's run queue"
      (!(rt.afterWait2.scheduler.runQueueOnCore c2).contains waiter2)
    assertBool "waiter 2's wait frames core 3's run queue"
      ((rt.afterWait2.scheduler.runQueueOnCore c3).toList
        == (stFourCore.scheduler.runQueueOnCore c3).toList)
    assertBool "the notification records the single waiter"
      (waiterList rt.afterWait2 == [waiter2])
    assertBool "the second wait prepends: waiter 3 becomes the list head"
      (waiterList rt.afterWait3 == [waiter3, waiter2])
    assertBool "wait deschedules waiter 3 from core 3's run queue"
      (!(rt.afterWait3.scheduler.runQueueOnCore c3).contains waiter3)

-- ============================================================================
-- §3.2  The wait → signal → SGI → handler-dispatch round trip
-- ============================================================================

private def runSignalRoundTripChecks : IO Unit := do
  IO.println "--- §3.2 cross-core signal round trip (signal from core 0, waiter homed core 3) ---"
  match ntfnRoundTrip? with
  | none => assertBool "notification round-trip pipeline succeeded" false
  | some rt =>
    assertBool "the signal wakes the list head (waiter 3) with a reschedule SGI to core 3"
      (match rt.sgiSig1 with
       | some (tgt, kind) => decide (tgt = c3 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "the woken waiter is .ready with the signal's badge delivered"
      (ipcStateIs rt.afterSig1 waiter3 .ready && deliveredBadgeIs rt.afterSig1 waiter3 badge1)
    assertBool "the woken waiter is enqueued on core 3 (its home core)"
      ((rt.afterSig1.scheduler.runQueueOnCore c3).contains waiter3)
    assertBool "the woken waiter is NOT enqueued on core 0 (the signalling core)"
      (!(rt.afterSig1.scheduler.runQueueOnCore c0).contains waiter3)
    assertBool "core 3's reschedule handler dispatches the woken waiter (current = waiter 3)"
      (rt.afterH3.scheduler.currentOnCore c3 == some waiter3)
    assertBool "one wake per signal: waiter 2 remains blocked after the first signal"
      (ipcStateIs rt.afterSig1 waiter2 (.blockedOnNotification nId))
    assertBool "the notification retains the remaining waiter list"
      (waiterList rt.afterSig1 == [waiter2])
    assertBool "the signaller stays runnable on core 0 (signal is non-blocking)"
      ((rt.afterSig1.scheduler.runQueueOnCore c0).contains signallerT)

-- ============================================================================
-- §3.3  Multi-waiter drain (each waiter woken to its OWN home core)
-- ============================================================================

private def runMultiWaiterDrainChecks : IO Unit := do
  IO.println "--- §3.3 multi-waiter drain (successive signals, per-waiter home cores + badges) ---"
  match ntfnRoundTrip? with
  | none => assertBool "notification round-trip pipeline succeeded" false
  | some rt =>
    assertBool "the second signal wakes the remaining waiter with a reschedule SGI to core 2"
      (match rt.sgiSig2 with
       | some (tgt, kind) => decide (tgt = c2 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "the drained notification is idle with no waiters"
      (match rt.afterSig2.objects[nId]? with
       | some (.notification ntfn) =>
           decide (ntfn.state = .idle) && ntfn.waitingThreads.val.isEmpty
       | _ => false)
    assertBool "per-waiter badge isolation: waiter 3 holds badge 1, waiter 2 holds badge 2"
      (deliveredBadgeIs rt.afterSig2 waiter3 badge1 && deliveredBadgeIs rt.afterSig2 waiter2 badge2)
    assertBool "the second woken waiter is enqueued on core 2 (its home core)"
      ((rt.afterSig2.scheduler.runQueueOnCore c2).contains waiter2)
    assertBool "core 2's reschedule handler dispatches the second waiter (current = waiter 2)"
      (rt.afterH2.scheduler.currentOnCore c2 == some waiter2)
    assertBool "the first waiter's dispatch survives the second wake (current core 3 = waiter 3)"
      (rt.afterH2.scheduler.currentOnCore c3 == some waiter3)

-- ============================================================================
-- §3.4  Badge accumulation (waiterless bor merge + non-blocking consume)
-- ============================================================================

private def runBadgeAccumulationChecks : IO Unit := do
  IO.println "--- §3.4 badge accumulation (bor merge) + non-blocking consume ---"
  let pipeline : Option (SystemState × SystemState × SystemState × Option SeLe4n.Badge) := do
    let (st1, sgi1) ← okPair (notificationSignalOnCore nId badge1 c0 stFourCore)
    if sgi1 != none then none else
    let (st2, sgi2) ← okPair (notificationSignalOnCore nId badge2 c0 st1)
    if sgi2 != none then none else
    let (st3, consumed) ← okPair (notificationWaitOnCore nId waiter2 c2 st2)
    pure (st1, st2, st3, consumed)
  match pipeline with
  | none => assertBool "badge-accumulation pipeline succeeded (no spurious SGI)" false
  | some (st1, st2, st3, consumed) =>
    assertBool "a waiterless signal activates the notification with its badge pending"
      (match st1.objects[nId]? with
       | some (.notification ntfn) =>
           decide (ntfn.state = .active ∧ ntfn.pendingBadge = some badge1)
       | _ => false)
    assertBool "a second waiterless signal merges the badges (word-bounded bor)"
      (match st2.objects[nId]? with
       | some (.notification ntfn) =>
           decide (ntfn.pendingBadge = some (SeLe4n.Badge.bor badge1 badge2))
       | _ => false)
    assertBool "a wait on the active notification consumes the merged badge"
      (consumed == some (SeLe4n.Badge.bor badge1 badge2))
    assertBool "the badge-path wait does NOT block the waiter (stays runnable on core 2)"
      (ipcStateIs st3 waiter2 .ready
        && (st3.scheduler.runQueueOnCore c2).contains waiter2)
    assertBool "the consumed notification returns to idle with no pending badge"
      (match st3.objects[nId]? with
       | some (.notification ntfn) =>
           decide (ntfn.state = .idle ∧ ntfn.pendingBadge = none)
       | _ => false)

-- ============================================================================
-- §3.5  Remote bound-TCB delivery round trip (SM6.B bound notifications)
-- ============================================================================

private def runBoundDeliveryChecks : IO Unit := do
  IO.println "--- §3.5 remote bound-TCB delivery (bind, signal-bound, SGI to core 1, dispatch) ---"
  let pipeline : Option (SystemState × SystemState × Option (CoreId × SgiKind) × SystemState) := do
    let (stRecv, _) ← okPair (endpointReceiveDualOnCore epId boundT none c1 stFourCore)
    let stBound ← okExcept (bindNotification nId boundT stRecv) |>.map (·.2)
    let (stSig, sgi) ← okPair (notificationSignalBoundOnCore nId badge1 c0 stBound)
    let stH1 ← okExcept (handleRescheduleSgiOnCore stSig c1)
    pure (stBound, stSig, sgi, stH1)
  match pipeline with
  | none => assertBool "bound-delivery pipeline succeeded" false
  | some (stBound, stSig, sgi, stH1) =>
    assertBool "the bound TCB is BlockedOnReceive on its endpoint before the signal"
      (ipcStateIs stBound boundT (.blockedOnReceive epId))
    assertBool "boundDeliveryTarget? resolves the bound TCB + its endpoint"
      (decide (boundDeliveryTarget? stBound nId = some (boundT, epId)))
    assertBool "the bound signal fires a reschedule SGI to core 1 (the bound TCB's home core)"
      (match sgi with
       | some (tgt, kind) => decide (tgt = c1 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "the bound delivery makes the bound TCB .ready with the badge (value pinned)"
      (ipcStateIs stSig boundT .ready && deliveredBadgeIs stSig boundT badge1)
    assertBool "the bound delivery dequeues the bound TCB from its endpoint"
      (match stSig.objects[epId]? with
       | some (.endpoint ep) => ep.receiveQ.head == none
       | _ => false)
    assertBool "the woken bound TCB is enqueued on core 1 (its home core)"
      ((stSig.scheduler.runQueueOnCore c1).contains boundT)
    assertBool "core 1's reschedule handler dispatches the bound TCB (current = boundT)"
      (stH1.scheduler.currentOnCore c1 == some boundT)
    assertBool "the binding survives the delivery (boundTCB retained)"
      (match stSig.objects[nId]? with
       | some (.notification ntfn) => ntfn.boundTCB == some boundT
       | _ => false)

-- ============================================================================
-- §3.6  Bind/unbind lifecycle
-- ============================================================================

private def runBindLifecycleChecks : IO Unit := do
  IO.println "--- §3.6 bind/unbind lifecycle (both directions, fall-through, double-bind) ---"
  match okExcept (bindNotification nId boundT stFourCore) with
  | none => assertBool "bindNotification succeeded" false
  | some ((), stB) =>
    assertBool "bind sets both directions (Notification.boundTCB + TCB.boundNotification)"
      ((match stB.objects[nId]? with
        | some (.notification n) => n.boundTCB == some boundT
        | _ => false)
       && (match stB.getTcb? boundT with
           | some t => t.boundNotification == some nId
           | none => false))
    assertBool "a runnable bound TCB is no bound-delivery target (fall-through)"
      (decide (boundDeliveryTarget? stB nId = none))
    -- The fall-through signal (bound TCB not BlockedOnReceive) merges the badge
    -- and PRESERVES the binding.
    let (stSig, _) := notificationSignalOnCore nId badge1 c0 stB
    assertBool "a fall-through signal preserves the binding and merges the badge"
      (match stSig.objects[nId]? with
       | some (.notification n) =>
           n.boundTCB == some boundT && decide (n.pendingBadge = some badge1)
       | _ => false)
    assertBool "re-binding an already-bound notification fails with illegalState"
      (match bindNotification nId boundT stB with
       | .error .illegalState => true | _ => false)
    match okExcept (unbindNotification boundT stB) with
    | none => assertBool "unbindNotification succeeded" false
    | some ((), stU) =>
      assertBool "unbind clears both directions"
        ((match stU.objects[nId]? with
          | some (.notification n) => n.boundTCB == none
          | _ => false)
         && (match stU.getTcb? boundT with
             | some t => t.boundNotification == none
             | none => false))
      assertBool "re-binding after unbind succeeds"
        (match bindNotification nId boundT stU with
         | .ok _ => true | .error _ => false)

-- ============================================================================
-- §3.7  Fail-closed error paths (pre-state returned on every error)
-- ============================================================================

private def runErrorPathChecks : IO Unit := do
  IO.println "--- §3.7 fail-closed error paths (absent / wrong-kind / double wait) ---"
  -- A blocked waiter re-waiting fails closed and leaves the waiter list intact.
  match okPair (notificationWaitOnCore nId waiter2 c2 stFourCore) with
  | none => assertBool "double-wait setup succeeded" false
  | some (stW, _) =>
    let (stW2, res2) := notificationWaitOnCore nId waiter2 c2 stW
    assertBool "a double wait fails with alreadyWaiting"
      (match res2 with | .error .alreadyWaiting => true | _ => false)
    assertBool "the failed double wait returns the pre-state (waiter list unchanged)"
      (waiterList stW2 == [waiter2])
  -- Absent / wrong-kind objects, wait side.
  assertBool "wait on an absent object fails with objectNotFound"
    (match (notificationWaitOnCore ⟨999⟩ waiter2 c2 stFourCore).2 with
     | .error .objectNotFound => true | _ => false)
  assertBool "wait on a wrong-kind object (an endpoint) fails with invalidCapability"
    (match (notificationWaitOnCore epId waiter2 c2 stFourCore).2 with
     | .error .invalidCapability => true | _ => false)
  -- Absent / wrong-kind objects, signal side.
  assertBool "signal on an absent object fails with objectNotFound"
    (match (notificationSignalOnCore ⟨999⟩ badge1 c0 stFourCore).2 with
     | .error .objectNotFound => true | _ => false)
  assertBool "signal on a wrong-kind object (a TCB) fails with invalidCapability"
    (match (notificationSignalOnCore waiter2.toObjId badge1 c0 stFourCore).2 with
     | .error .invalidCapability => true | _ => false)
  -- Pre-state on a failed signal: the fixture notification is untouched.
  let (stErr, _) := notificationSignalOnCore ⟨999⟩ badge1 c0 stFourCore
  assertBool "the failed signal returns the pre-state (notification untouched)"
    (stErr.objects[nId]? == stFourCore.objects[nId]?)

-- ============================================================================
-- §3.8  Cross-core independence framing + 2PL lock-set discipline
-- ============================================================================

private def runIndependenceAndLockChecks : IO Unit := do
  IO.println "--- §3.8 cross-core independence + state-resolved lock-set footprints ---"
  match ntfnRoundTrip? with
  | none => assertBool "notification round-trip pipeline succeeded" false
  | some rt =>
    -- The head wake (to core 3) frames every other core's run queue.
    assertBool "the head wake frames core 0's run queue"
      ((rt.afterSig1.scheduler.runQueueOnCore c0).toList
        == (rt.afterWait3.scheduler.runQueueOnCore c0).toList)
    assertBool "the head wake frames core 1's run queue"
      ((rt.afterSig1.scheduler.runQueueOnCore c1).toList
        == (rt.afterWait3.scheduler.runQueueOnCore c1).toList)
    assertBool "the head wake frames core 2's run queue"
      ((rt.afterSig1.scheduler.runQueueOnCore c2).toList
        == (rt.afterWait3.scheduler.runQueueOnCore c2).toList)
    -- The pre-resolution helper sees the waiting head; the state-resolved
    -- footprint covers it with a write lock, hierarchically correct.
    assertBool "notificationSignalWaiter? resolves the waiting head (waiter 3)"
      (decide (notificationSignalWaiter? rt.afterWait3 nId = some waiter3))
    let sigLs := lockSet_notificationSignalOnCore rt.afterWait3 nId signallerT cnRoot
    assertBool "state-resolved signal lock-set kinds all permitted"
      (decide (∀ p ∈ sigLs.pairs, p.fst.kind ∈ permittedKinds .notificationSignal))
    assertBool "state-resolved signal lock-set keys are duplicate-free"
      (decide (sigLs.pairs.map (·.fst)).Nodup)
    assertBool "the head waiter's TCB write lock is in the signal footprint"
      (decide ((tcbLock waiter3, AccessMode.write) ∈ sigLs.pairs))
    assertBool "the notification write lock is in the signal footprint"
      (decide ((notificationLock nId, AccessMode.write) ∈ sigLs.pairs))
    assertBool "signal lock-set size within maxLockSetSize"
      (decide (sigLs.pairs.length ≤ maxLockSetSize))
    let waitLs := lockSet_notificationWaitOnCore nId waiter2 cnRoot
    assertBool "wait lock-set kinds all permitted"
      (decide (∀ p ∈ waitLs.pairs, p.fst.kind ∈ permittedKinds .notificationWait))
    assertBool "the waiter's TCB write lock is in the wait footprint"
      (decide ((tcbLock waiter2, AccessMode.write) ∈ waitLs.pairs))

def runSmpNotificationChecks : IO Unit := do
  IO.println "WS-SM SM6.F.2 — Aggregate SMP cross-core notification suite (4 cores)"
  IO.println "===================================="
  runWaitBlockChecks
  runSignalRoundTripChecks
  runMultiWaiterDrainChecks
  runBadgeAccumulationChecks
  runBoundDeliveryChecks
  runBindLifecycleChecks
  runErrorPathChecks
  runIndependenceAndLockChecks
  IO.println "===================================="
  IO.println "All SM6.F cross-core notification checks PASS."

end SeLe4n.Testing.SmpNotification

def main : IO Unit :=
  SeLe4n.Testing.SmpNotification.runSmpNotificationChecks
