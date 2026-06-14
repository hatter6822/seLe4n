-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignalNI
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.IPC.CrossCore.NotificationBindDispatch
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.B — Cross-core notification test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM6.B
"Notification across cores" deliverable
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).

* **§1 Surface anchors** — every public SM6.B symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (SGI emission,
  2PL atomicity, per-core / ∀-core non-interference) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cross_core_notification_suite`
  exercises the actual `notificationSignalOnCore` / `notificationWaitOnCore` /
  `lockSet_notificationSignal` computations on the SM6.B cross-core notification
  scenarios: the lock-set footprint and binding membership, the no-waiter badge
  merge, the local vs remote signal SGI emission, the multi-waiter discipline,
  and the per-core caller blocking on `notificationWait`.
-/

namespace SeLe4n.Testing.SmpCrossCoreNotification

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM6.B public symbol resolves
-- ============================================================================

-- SM6.B.1 production transitions + lock-set helpers:
#check @notificationSignalOnCore
#check @notificationWaitOnCore
#check @notificationSignalWaiter?
#check @lockSet_notificationSignalOnCore
#check @lockSet_notificationWaitOnCore

-- SM6.B.1 path-reduction lemmas:
#check @notificationSignalOnCore_waiter_eq
#check @notificationSignalOnCore_noWaiter_eq

-- SM6.B.2 cross-core wake (notificationSignal_remote_wake):
#check @notificationSignalOnCore_remote_wake
#check @notificationSignalOnCore_no_sgi_if_local_waiter
#check @notificationSignalOnCore_noWaiter_no_sgi

-- SM6.B.1 lock-set hierarchical correctness:
#check @notificationSignalOnCore_lockSet_correct
#check @lockSet_notificationSignalOnCore_correct
#check @notificationWaitOnCore_lockSet_correct

-- SM6.B.6 notification ↔ TCB binding under lock-set (both ends write-locked):
#check @self_write_mem_insertOrMerge
#check @lockSet_notificationSignal_notification_write_mem
#check @lockSet_notificationSignal_waiter_tcb_write_mem

-- SM6.B.5 per-core wake locality:
#check @notificationSignalOnCore_perCore_consistent

-- SM6.B.4 2PL atomicity of wait + signal:
#check @notificationWaitOnCore_atomic_under_lockSet
#check @notificationSignalOnCore_atomic_under_lockSet

-- SM6.B.3 multi-waiter discipline:
#check @notificationSignalOnCore_wakes_head
#check @notificationSignalOnCore_remaining_waiters

-- SM6.B.7 non-interference (boot-core projectState + per-core / ∀-core smp):
#check @notificationSignalOnCore_signal_path_NI
#check @notificationSignalOnCore_signal_path_NI_smp
#check @storeObject_preserves_projectionOnCore

-- SM6.B.7 (wait) non-interference (boot-core + per-core/∀-core smp) + helper:
#check @notificationWaitOnCore_block_path_NI
#check @notificationWaitOnCore_block_path_NI_smp
#check @storeTcbIpcState_preserves_projectionOnCore

-- SM6.B.1 IPC-invariant preservation (objects.invExt + ipcInvariant, both ops):
#check @notificationSignalOnCore_preserves_objects_invExt
#check @notificationSignalOnCore_preserves_ipcInvariant
#check @notificationWaitOnCore_preserves_objects_invExt
#check @notificationWaitOnCore_preserves_ipcInvariant

-- SM6.B.1 wait path reductions + per-core caller blocking:
#check @notificationWaitOnCore_badge_eq
#check @notificationWaitOnCore_block_eq
#check @notificationWaitOnCore_perCore_blocking

-- SM6.B.2 (strengthening) honest pre-state SGI target + affinity-frame congruence:
#check @notificationSignalOnCore_remote_wake_preState
#check @determineTargetCore_congr
#check @storeTcbIpcStateAndMessage_determineTargetCore_eq

-- SM6.B (coherence) lock-set pre-resolution names the woken thread:
#check @notificationSignalWaiter?_eq_wake_head

-- SM6.B (bound notification) — bind/unbind ops + bound-delivery + the live dispatch:
#check @bindNotification
#check @unbindNotification
#check @boundDeliveryTarget?
#check @notificationSignalBound
#check @notificationSignalBoundOnCore
#check @notificationSignalBoundCrossCoreDispatch
#check @notificationSignalBoundCrossCoreDispatchChecked
#check @notificationSignalBoundCrossCoreDispatchChecked_flow_denied
#check @notificationSignalBoundCrossCoreDispatchChecked_flow_denied_to_receiver
#check @notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_no_delivery
#check @notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_to_receiver
-- SM6.B audit closure (codex review #4 wait wiring, #5 bound lock-set):
#check @notificationWaitCrossCoreDispatch
#check @notificationWaitCrossCoreDispatchChecked
#check @lockSet_notificationSignalBoundOnCore_correct
-- SM6.B bound-delivery semantics + invariant preservation:
#check @notificationSignalBoundOnCore_fallthrough_eq
#check @notificationSignalBoundOnCore_delivery_eq
#check @notificationSignalBoundOnCore_delivery_remote_wake
#check @notificationSignalBoundOnCore_preserves_objects_invExt
#check @notificationSignalBoundOnCore_preserves_ipcInvariant
#check @bindNotification_preserves_ipcInvariant
#check @unbindNotification_preserves_ipcInvariant
#check @endpointQueueRemoveDual_preserves_objects_invExt

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): theorems apply to typed inputs
-- ============================================================================

/-- SM6.B.2: a signal unblocking a remote waiter emits the reschedule SGI. -/
example (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (waiterTcb'' : TCB) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hTcb'' : st''.getTcb? waiter = some waiterTcb'')
    (hRemote : determineTargetCore st'' waiter ≠ executingCore) :
    (notificationSignalOnCore notificationId badge executingCore st).2
      = .ok (some (determineTargetCore st'' waiter, SgiKind.reschedule)) :=
  notificationSignalOnCore_remote_wake notificationId badge executingCore st ntfn waiter rest
    waiterTcb'' st' st'' hObj hWaiters hStore hMsg hTcb'' hRemote

/-- SM6.B.4: the signal is a single 2PL-atomic step under its lock-set. -/
example (notificationId cnRoot : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (signaller : SeLe4n.ThreadId) (executingCore : CoreId)
    (waiter? : Option SeLe4n.ThreadId) (s : SystemState) :
    (withLockSet (lockSet_notificationSignal signaller cnRoot notificationId waiter?)
        executingCore (notificationSignalOnCore notificationId badge executingCore) s).2
      = (notificationSignalOnCore notificationId badge executingCore
          (acquireAll executingCore
            (lockSet_notificationSignal signaller cnRoot notificationId waiter?).lockAcquireSequence s)).2 := by
  rw [notificationSignalOnCore_atomic_under_lockSet]

/-- SM6.B.7: a cross-core signal between high principals is invisible on every core. -/
example (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hObjInv : st.objects.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false) :
    lowEquivalent_smp ctx observer
      (notificationSignalOnCore notificationId badge executingCore st).1 st :=
  notificationSignalOnCore_signal_path_NI_smp ctx observer notificationId badge executingCore st
    ntfn waiter rest st' st'' hObj hWaiters hStore hMsg hObjInv hNtfnHigh hWaiterHigh hWaiterObjHigh

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM6.B cross-core notification scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def core1 : CoreId := ⟨1, by decide⟩

private def nId : SeLe4n.ObjId := ⟨500⟩
private def cnRoot : SeLe4n.ObjId := ⟨300⟩
private def signallerTid : SeLe4n.ThreadId := ⟨501⟩
private def waiterLocalTid : SeLe4n.ThreadId := ⟨502⟩
private def waiterRemoteTid : SeLe4n.ThreadId := ⟨503⟩
private def badge : SeLe4n.Badge := SeLe4n.Badge.ofNatMasked 7

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- Notification (idle, no waiters) + unbound signaller + unbound (local) waiter
+ core1-bound (remote) waiter; all three runnable on the boot core. -/
private def stBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
    |>.withObject signallerTid.toObjId (.tcb (mkTcb 501 40 none))
    |>.withObject waiterLocalTid.toObjId (.tcb (mkTcb 502 30 none))
    |>.withObject waiterRemoteTid.toObjId (.tcb (mkTcb 503 30 (some core1)))
    |>.withRunnable [signallerTid, waiterLocalTid, waiterRemoteTid]
    |>.build)

/-- Drive `w` onto the notification's waiter list (it blocks, no pending badge). -/
private def stWithWaiter (w : SeLe4n.ThreadId) : Option SystemState :=
  match notificationWaitOnCore nId w bootCoreId stBase with
  | (st, .ok _) => some st
  | (_, .error _) => none

/-- Drive both waiters onto the list (local first, so the core1-bound remote
waiter becomes the head — `notificationWait` prepends). -/
private def stTwoWaiters : Option SystemState :=
  match notificationWaitOnCore nId waiterLocalTid bootCoreId stBase with
  | (st1, .ok _) =>
      match notificationWaitOnCore nId waiterRemoteTid bootCoreId st1 with
      | (st2, .ok _) => some st2
      | (_, .error _) => none
  | (_, .error _) => none

/-- The optional SGI surfaced by a cross-core signal (`none` on a kernel error). -/
private def signalSgi (st : SystemState) (ec : CoreId) : Option (CoreId × SgiKind) :=
  match (notificationSignalOnCore nId badge ec st).2 with
  | .ok sgi => sgi
  | .error _ => none

/-- Read the notification's current waiter list from a state (empty on absence). -/
private def waiterList (st : SystemState) : List SeLe4n.ThreadId :=
  match st.objects[nId]? with
  | some (.notification ntfn) => ntfn.waitingThreads.val
  | _ => []

-- Bound-notification fixture: an endpoint + a TCB to bind to the notification.
private def epId : SeLe4n.ObjId := ⟨600⟩
private def boundTid : SeLe4n.ThreadId := ⟨504⟩

/-- Notification (idle, no waiters) + an endpoint + a TCB (to be bound), all on the
boot core. -/
private def stBoundBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
    |>.withObject epId (.endpoint {})
    |>.withObject signallerTid.toObjId (.tcb (mkTcb 501 40 none))
    |>.withObject boundTid.toObjId (.tcb (mkTcb 504 30 none))
    |>.withRunnable [signallerTid, boundTid]
    |>.build)

private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.1 SM6.B.1/.6 lock-set footprint + binding ---"
  -- SM6.B.1: every declared lock has a kind permitted for `.notificationSignal`.
  assertBool "notificationSignal lock-set kinds all permitted (signaller R, cnode R, ntfn W, waiter W)"
    (decide (∀ p ∈ (lockSet_notificationSignal signallerTid cnRoot nId (some waiterRemoteTid)).pairs,
        p.fst.kind ∈ permittedKinds .notificationSignal))
  -- SM6.B.1: keys are duplicate-free.
  assertBool "notificationSignal lock-set keys are duplicate-free"
    (decide ((lockSet_notificationSignal signallerTid cnRoot nId (some waiterRemoteTid)).pairs.map
        (·.fst)).Nodup)
  -- SM6.B.1: the wait lock-set is hierarchically correct (caller W, cnode R, ntfn W).
  assertBool "notificationWait lock-set kinds all permitted"
    (decide (∀ p ∈ (lockSet_notificationWait waiterLocalTid cnRoot nId).pairs,
        p.fst.kind ∈ permittedKinds .notificationWait))
  -- SM6.B.6: the notification *write* lock — both ends of the binding — is declared.
  assertBool "notification write lock is in the signal footprint (binding, notification end)"
    (decide ((notificationLock nId, AccessMode.write) ∈
      (lockSet_notificationSignal signallerTid cnRoot nId (some waiterRemoteTid)).pairs))
  -- SM6.B.6: the woken waiter's TCB *write* lock is declared (binding, TCB end).
  assertBool "woken-waiter TCB write lock is in the signal footprint (binding, TCB end)"
    (decide ((tcbLock waiterRemoteTid, AccessMode.write) ∈
      (lockSet_notificationSignal signallerTid cnRoot nId (some waiterRemoteTid)).pairs))
  -- SM6.B.1: the state-resolved signal lock-set picks up the waiting head.
  assertBool "notificationSignalWaiter? resolves none on a notification with no waiter"
    (decide (notificationSignalWaiter? stBase nId = none))
  assertBool "state-resolved signal lock-set kinds all permitted"
    (decide (∀ p ∈ (lockSet_notificationSignalOnCore stBase nId signallerTid cnRoot).pairs,
        p.fst.kind ∈ permittedKinds .notificationSignal))

private def runNoWaiterChecks : IO Unit := do
  IO.println "--- §3.2 SM6.B.2 no-waiter path (badge merge, no SGI) ---"
  let (st', res) := notificationSignalOnCore nId badge bootCoreId stBase
  -- No waiter ⇒ no cross-core wake ⇒ no SGI.
  assertBool "no-waiter signal surfaces no SGI"
    (match res with | .ok none => true | _ => false)
  -- The notification transitions to `.active` carrying the merged pending badge.
  assertBool "no-waiter signal merges the badge into the notification (state .active)"
    (match st'.objects[nId]? with
     | some (.notification ntfn) => decide (ntfn.state = .active ∧ ntfn.pendingBadge = some badge)
     | _ => false)

private def runSignalWakeChecks : IO Unit := do
  IO.println "--- §3.3 SM6.B.2 signal wake (local vs remote SGI) ---"
  -- Local waiter (unbound ⇒ home = boot core = executing core): no SGI.
  match stWithWaiter waiterLocalTid with
  | some st =>
      assertBool "notificationSignalWaiter? resolves the waiting (local) head"
        (decide (notificationSignalWaiter? st nId = some waiterLocalTid))
      assertBool "signal waking a local (unbound) waiter surfaces no SGI"
        (match signalSgi st bootCoreId with | none => true | _ => false)
      -- The woken waiter is delivered the badge and made ready.
      let (st', _) := notificationSignalOnCore nId badge bootCoreId st
      assertBool "signal delivers the badge to the woken local waiter (.ready + badge value)"
        (match st'.getTcb? waiterLocalTid with
         | some t => decide (t.ipcState = .ready ∧ t.pendingMessage.bind (·.badge) = some badge)
         | none => false)
  | none => assertBool "signal setup (local waiter) succeeded" false
  -- Remote waiter (core1-bound): a reschedule SGI is fired to core 1.
  match stWithWaiter waiterRemoteTid with
  | some st =>
      assertBool "signal waking a core1-bound (remote) waiter fires a reschedule SGI to core 1"
        (match signalSgi st bootCoreId with
         | some (tgt, kind) => decide (tgt = core1 ∧ kind = SgiKind.reschedule)
         | none => false)
  | none => assertBool "signal setup (remote waiter) succeeded" false

private def runMultiWaiterChecks : IO Unit := do
  IO.println "--- §3.4 SM6.B.3 multi-waiter discipline ---"
  match stTwoWaiters with
  | some st =>
      -- Both waiters are queued (remote is the head after the local-then-remote waits).
      assertBool "both waiters are queued before signal"
        (((waiterList st).contains waiterLocalTid) && ((waiterList st).contains waiterRemoteTid))
      assertBool "the remote waiter is the wake head (notificationSignalWaiter?)"
        (decide (notificationSignalWaiter? st nId = some waiterRemoteTid))
      let (st', _) := notificationSignalOnCore nId badge bootCoreId st
      -- Exactly one wake: the head (remote) is removed; the local waiter remains.
      assertBool "signal wakes exactly the head — remote waiter removed from the list"
        (!(waiterList st').contains waiterRemoteTid)
      assertBool "signal preserves the remaining waiter — local waiter still queued"
        ((waiterList st').contains waiterLocalTid)
      -- The remaining list stays duplicate-free (the multi-waiter NoDup discipline).
      assertBool "remaining waiter list is duplicate-free"
        (decide (waiterList st').Nodup)
      -- Waking the head crosses to its home core: reschedule SGI to core 1.
      assertBool "multi-waiter signal fires the reschedule SGI to the head's home core"
        (match signalSgi st bootCoreId with
         | some (tgt, _) => decide (tgt = core1)
         | none => false)
  | none => assertBool "multi-waiter setup succeeded" false

private def runWaitChecks : IO Unit := do
  IO.println "--- §3.5 SM6.B.1/.4 wait blocks the caller on its own core ---"
  let (st', res) := notificationWaitOnCore nId waiterLocalTid bootCoreId stBase
  -- No pending badge ⇒ the caller blocks (returns none), with no SGI surfaced.
  assertBool "wait with no pending badge blocks the caller (returns none)"
    (match res with | .ok none => true | _ => false)
  -- The caller is removed from its own core's run queue (per-core deschedule).
  assertBool "wait removes the caller from its own core's run queue"
    (!(st'.scheduler.runQueueOnCore bootCoreId).contains waiterLocalTid)
  -- The caller's TCB records the blocked-on-notification state.
  assertBool "wait records blockedOnNotification on the caller"
    (match st'.getTcb? waiterLocalTid with
     | some t => decide (t.ipcState = .blockedOnNotification nId)
     | none => false)
  -- A sibling core's run queue is untouched (per-core locality of the deschedule).
  let (st'', _) := notificationWaitOnCore nId waiterLocalTid core1 stBase
  assertBool "wait on core 1 leaves the boot core's run queue intact"
    ((st''.scheduler.runQueueOnCore bootCoreId).contains waiterLocalTid)

private def runBadgeWaitChecks : IO Unit := do
  IO.println "--- §3.6 SM6.B.1 wait consumes a pending badge (caller stays runnable) ---"
  -- Prepare a notification carrying a pending badge (a no-waiter signal merges it in).
  let stActive := (notificationSignalOnCore nId badge bootCoreId stBase).1
  let (st', res) := notificationWaitOnCore nId waiterLocalTid bootCoreId stActive
  assertBool "wait on a notification with a pending badge returns the badge (value pinned)"
    (match res with | .ok (some b) => decide (b = badge) | _ => false)
  -- The badge-consume path makes no scheduler change — the caller stays runnable.
  assertBool "badge-consume wait leaves the caller runnable on the boot core"
    ((st'.scheduler.runQueueOnCore bootCoreId).contains waiterLocalTid)
  assertBool "badge-consume wait clears the notification to idle (badge consumed)"
    (match st'.objects[nId]? with
     | some (.notification ntfn) => decide (ntfn.state = .idle ∧ ntfn.pendingBadge = none)
     | _ => false)

private def runErrorChecks : IO Unit := do
  IO.println "--- §3.7 SM6.B.1 error paths (wrong-kind / absent object) ---"
  -- Wrong-kind object (a TCB id) ⇒ invalidCapability; absent id ⇒ objectNotFound.
  assertBool "signal on a non-notification object fails with invalidCapability"
    (match (notificationSignalOnCore signallerTid.toObjId badge bootCoreId stBase).2 with
     | .error .invalidCapability => true | _ => false)
  assertBool "signal on an absent object fails with objectNotFound"
    (match (notificationSignalOnCore ⟨9999⟩ badge bootCoreId stBase).2 with
     | .error .objectNotFound => true | _ => false)
  assertBool "wait on a non-notification object fails with invalidCapability"
    (match (notificationWaitOnCore signallerTid.toObjId waiterLocalTid bootCoreId stBase).2 with
     | .error .invalidCapability => true | _ => false)
  assertBool "wait on an absent object fails with objectNotFound"
    (match (notificationWaitOnCore ⟨9999⟩ waiterLocalTid bootCoreId stBase).2 with
     | .error .objectNotFound => true | _ => false)

private def runBoundChecks : IO Unit := do
  IO.println "--- §3.8 SM6.B bound notification (bind / deliver / unbind) ---"
  -- Block the to-be-bound TCB on receive (it joins the endpoint's receive queue).
  match endpointReceiveDual epId boundTid stBoundBase with
  | .ok (_, stRecv) =>
      match bindNotification nId boundTid stRecv with
      | .ok ((), stBound) =>
          -- Both directions of the binding are established.
          assertBool "bindNotification sets Notification.boundTCB"
            (match stBound.objects[nId]? with
             | some (.notification n) => decide (n.boundTCB = some boundTid)
             | _ => false)
          assertBool "bindNotification sets TCB.boundNotification"
            (match stBound.getTcb? boundTid with
             | some t => decide (t.boundNotification = some nId)
             | none => false)
          -- The bound-delivery target resolves to the BlockedOnReceive bound TCB.
          assertBool "boundDeliveryTarget? resolves the bound TCB + its endpoint"
            (decide (boundDeliveryTarget? stBound nId = some (boundTid, epId)))
          -- A signal delivers the badge directly to the bound TCB.
          let (stSig, res) := notificationSignalBoundOnCore nId badge bootCoreId stBound
          assertBool "bound signal succeeds with no SGI for a local bound TCB"
            (match res with | .ok none => true | _ => false)
          assertBool "bound signal makes the bound TCB ready with the badge delivered (value pinned)"
            (match stSig.getTcb? boundTid with
             | some t => decide (t.ipcState = .ready ∧ t.pendingMessage.bind (·.badge) = some badge)
             | none => false)
          -- The bound TCB is dequeued from the endpoint's receive queue.
          assertBool "bound signal dequeues the bound TCB from its endpoint"
            (match stSig.objects[epId]? with
             | some (.endpoint ep) => decide (ep.receiveQ.head = none)
             | _ => false)
          -- Unbind clears both directions.
          match unbindNotification boundTid stBound with
          | .ok ((), stUnbound) =>
              assertBool "unbindNotification clears Notification.boundTCB"
                (match stUnbound.objects[nId]? with
                 | some (.notification n) => decide (n.boundTCB = none)
                 | _ => false)
              assertBool "unbindNotification clears TCB.boundNotification"
                (match stUnbound.getTcb? boundTid with
                 | some t => decide (t.boundNotification = none)
                 | none => false)
          | .error _ => assertBool "unbindNotification succeeded" false
      | .error _ => assertBool "bindNotification succeeded" false
  | .error _ => assertBool "endpointReceiveDual (bound-TCB setup) succeeded" false
  -- Fall-through: a signal to an UNBOUND notification takes the normal path.
  assertBool "unbound notification has no bound-delivery target"
    (decide (boundDeliveryTarget? stBoundBase nId = none))
  assertBool "fall-through bound signal matches the plain cross-core signal"
    (((notificationSignalBoundOnCore nId badge bootCoreId stBoundBase).1.objects[nId]?) ==
     ((notificationSignalOnCore nId badge bootCoreId stBoundBase).1.objects[nId]?))
  -- Bind precondition: binding an already-bound notification fails (illegalState).
  match endpointReceiveDual epId boundTid stBoundBase with
  | .ok (_, stRecv) =>
      match bindNotification nId boundTid stRecv with
      | .ok ((), stBound) =>
          assertBool "re-binding an already-bound notification fails with illegalState"
            (match bindNotification nId boundTid stBound with
             | .error .illegalState => true | _ => false)
      | .error _ => assertBool "bind setup for precondition check succeeded" false
  | .error _ => assertBool "receive setup for precondition check succeeded" false

/-- §3.9: WS-SM SM6.B audit closure (codex review #2 binding preservation + #5
bound-delivery lock-set footprint). -/
private def runReviewFixChecks : IO Unit := do
  IO.println "--- §3.9 SM6.B audit closure (binding preservation + bound lock-set) ---"
  -- review #2: an ordinary signal must PRESERVE the notification ↔ TCB binding.
  -- Bind without making the bound TCB BlockedOnReceive ⇒ no bound-delivery target ⇒
  -- the signal takes the no-waiter merge path; a fresh record would drop boundTCB.
  match bindNotification nId boundTid stBoundBase with
  | .ok ((), stB) =>
      assertBool "review #2 precond: no bound-delivery target (bound TCB not BlockedOnReceive)"
        (decide (boundDeliveryTarget? stB nId = none))
      let (stSig, _) := notificationSignalOnCore nId badge bootCoreId stB
      assertBool "review #2: an ordinary (fall-through) signal preserves the binding"
        (match stSig.objects[nId]? with
         | some (.notification n) => decide (n.boundTCB = some boundTid ∧ n.pendingBadge = some badge)
         | _ => false)
  | .error _ => assertBool "review #2 bind setup succeeded" false
  -- review #5: on the bound-delivery path the lock-set covers the endpoint + bound TCB
  -- (the writes `notificationSignalBoundOnCore` performs), all with permitted kinds.
  match endpointReceiveDual epId boundTid stBoundBase with
  | .ok (_, stRecv) =>
      match bindNotification nId boundTid stRecv with
      | .ok ((), stBnd) =>
          assertBool "review #5 precond: bound-delivery target resolves"
            (decide (boundDeliveryTarget? stBnd nId = some (boundTid, epId)))
          let ls := lockSet_notificationSignalBoundOnCore stBnd nId signallerTid cnRoot
          assertBool "review #5: bound lock-set includes the endpoint write lock"
            (ls.pairs.any (fun p => p.fst == endpointLock epId && p.snd == AccessMode.write))
          assertBool "review #5: bound lock-set includes the bound-TCB write lock"
            (ls.pairs.any (fun p => p.fst == tcbLock boundTid && p.snd == AccessMode.write))
          assertBool "review #5: bound lock-set is hierarchically correct (all kinds permitted)"
            (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .notificationSignal))
      | .error _ => assertBool "review #5 bind setup succeeded" false
  | .error _ => assertBool "review #5 receive setup succeeded" false

def runSmpCrossCoreNotificationChecks : IO Unit := do
  IO.println "WS-SM SM6.B — Cross-core notification suite"
  IO.println "===================================="
  runLockSetChecks
  runNoWaiterChecks
  runSignalWakeChecks
  runMultiWaiterChecks
  runWaitChecks
  runBadgeWaitChecks
  runErrorChecks
  runBoundChecks
  runReviewFixChecks
  IO.println "===================================="
  IO.println "All SM6.B cross-core notification checks PASS."

end SeLe4n.Testing.SmpCrossCoreNotification

def main : IO Unit :=
  SeLe4n.Testing.SmpCrossCoreNotification.runSmpCrossCoreNotificationChecks
