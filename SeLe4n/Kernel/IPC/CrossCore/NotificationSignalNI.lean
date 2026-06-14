-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.B.7 cross-core IPC (per-core / ∀-core
-- non-interference for the notification signal; see
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore

/-!
# WS-SM SM6.B.7 — Cross-core notification-signal non-interference

The information-flow slice of SM6.B: a cross-core `notificationSignalOnCore` at a
**non-observable** notification, waking a **non-observable** waiter, is invisible
to a low observer.

* **`notificationSignalOnCore_signal_path_NI`** — the boot-core `projectState`
  form (the cross-core variant of the single-core
  `notificationSignal_projection_preserved`).
* **`notificationSignalOnCore_signal_path_NI_smp`** — the per-core / ∀-core
  `lowEquivalent_smp` strengthening: a high signal is invisible on *every* core,
  including the remote core the waiter is woken onto, not just the boot core.

The new content over the single-core proof is the projection preservation of the
cross-core wake step — `wakeThread` (the waiter wake routed to its home core) —
for a high thread on an *arbitrary* core.  It composes with the existing
single-core `storeObject` / `storeTcbIpcStateAndMessage` projection lemmas (boot
core) and the SM6.A per-core projection family (the `*_preserves_projectionOnCore`
lemmas), plus the new per-core `storeObject_preserves_projectionOnCore` (§1).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Per-core projection preservation for the object-store write
-- ============================================================================

/-- SM6.B.7: the per-core form of `storeObject_preserves_projection`.  A
`storeObject` at a **high** id preserves every core's per-core observer
projection: the object-store base projection is preserved (single-core lemma),
and the scheduler / machine registers are untouched (object-store frame), so the
per-core congruence applies on every core.  The notification-object analogue of
the SM6.A `storeTcbIpcStateAndMessage_preserves_projectionOnCore`. -/
theorem storeObject_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (c : CoreId)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := storeObject_scheduler_eq st st' oid obj hStore
  have hMach := storeObject_machine_eq st st' oid obj hStore
  exact projectStateOnCore_congr ctx observer
    (storeObject_preserves_projection ctx observer st st' oid obj hOidHigh hObjInv hStore)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hMach])

-- ============================================================================
-- §2  SM6.B.7 — boot-core non-interference (`projectState`)
-- ============================================================================

/-- WS-SM SM6.B.7 (`notificationSignal_perCore_NI`, boot-core form): a cross-core
notification signal at a **non-observable** notification, waking a non-observable
waiter, is invisible to a low observer — `projectState` of the post-state equals
that of the pre-state.  No covert channel is opened: the notification-object write
(badge / waiter-list mutation), the waiter's `ipcState := .ready` write, and the
cross-core waiter wake all touch only high state. -/
theorem notificationSignalOnCore_signal_path_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hObjInv : st.objects.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false) :
    projectState ctx observer (notificationSignalOnCore notificationId badge executingCore st).1
      = projectState ctx observer st := by
  have hInv' : st'.objects.invExt :=
    storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' waiter _ _ hInv' hMsg
  rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
        waiter rest st' st'' hObj hWaiters hStore hMsg]
  show projectState ctx observer (wakeThread st'' waiter executingCore).1
    = projectState ctx observer st
  rw [wakeThread_preserves_projection ctx observer st'' waiter executingCore
        hWaiterHigh hWaiterObjHigh hInv'',
      storeTcbIpcStateAndMessage_preserves_projection ctx observer st' st'' waiter _ _
        hWaiterObjHigh hInv' hMsg,
      storeObject_preserves_projection ctx observer st st' notificationId _ hNtfnHigh hObjInv hStore]

-- ============================================================================
-- §3  SM6.B.7 — per-core / ∀-core non-interference (`lowEquivalent_smp`)
-- ============================================================================

/-- WS-SM SM6.B.7 (`notificationSignal_perCore_NI`, ∀-core form): a high
cross-core notification signal is invisible to a low observer on *every* core —
the post-state is `lowEquivalent_smp` to the pre-state.  This is the SMP-faithful
strengthening of `notificationSignalOnCore_signal_path_NI` (which covers only the
boot core): no covert channel is opened on the *remote* core the waiter is woken
onto, nor on any bystander core.  Proof: the same single-step chain as the
boot-core theorem, discharged at an arbitrary observer core `c` — the object
writes are high (object-store frame), the waiter wake's run-queue insert edits
only a *high* thread the observer filters out, and no step touches any core's
current-thread / domain slots or machine registers. -/
theorem notificationSignalOnCore_signal_path_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hObjInv : st.objects.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false) :
    lowEquivalent_smp ctx observer
      (notificationSignalOnCore notificationId badge executingCore st).1 st := by
  intro c
  have hInv' : st'.objects.invExt :=
    storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' waiter _ _ hInv' hMsg
  show projectStateOnCore ctx observer
      (notificationSignalOnCore notificationId badge executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
        waiter rest st' st'' hObj hWaiters hStore hMsg]
  show projectStateOnCore ctx observer (wakeThread st'' waiter executingCore).1 c
    = projectStateOnCore ctx observer st c
  rw [wakeThread_preserves_projectionOnCore ctx observer st'' waiter executingCore c
        hWaiterHigh hWaiterObjHigh hInv'',
      storeTcbIpcStateAndMessage_preserves_projectionOnCore ctx observer st' st'' waiter .ready _ c
        hWaiterObjHigh hInv' hMsg,
      storeObject_preserves_projectionOnCore ctx observer st st' notificationId _ c
        hNtfnHigh hObjInv hStore]

end SeLe4n.Kernel
