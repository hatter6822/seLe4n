-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.B cross-core IPC (notification IPC-invariant
-- preservation; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.Invariant

/-!
# WS-SM SM6.B — Cross-core notification IPC-invariant preservation

`notificationSignalOnCore` / `notificationWaitOnCore` preserve the kernel's
object-store integrity (`objects.invExt`) and the IPC `ipcInvariant`
(notification well-formedness).  Each cross-core operation differs from its
single-core form only in the *scheduler* placement of the woken waiter / blocked
caller; `ipcInvariant` is **lookup-only** (it reads the state solely through
`objects[·]?`), so the cross-core receiver wake (`wakeThread`, object-invisible
on the already-`.ready` waiter — the §2 keystone of `EndpointCallInvariant`) and
the per-core deschedule (`removeRunnableOnCore`, an object-store frame) cannot
disturb it.  The notification-store / TCB-store steps reuse the single-core
per-step preservation lemmas verbatim.

(The full fifteen-conjunct `ipcInvariantFull_perCore` preservation for every IPC
operation is the SM6.D aggregate; this module establishes the two load-bearing
conjuncts for the two notification operations, matching SM6.A's
`EndpointCallInvariant`.)
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  `objects.invExt` preservation
-- ============================================================================

/-- WS-SM SM6.B.1: the cross-core notification signal preserves object-store
integrity (`invExt`) on every control path. -/
theorem notificationSignalOnCore_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationSignalOnCore notificationId badge executingCore st).1.objects.invExt := by
  unfold notificationSignalOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact hObjInv
  | some ntfn =>
    simp only
    cases hWaiters : ntfn.waitingThreads.tail? with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hObjInv
      | ok pair => simp only; exact storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hObjInv
      | ok pair =>
        simp only
        have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => simp only; exact hObjInv
        | ok st'' =>
          simp only
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st'' waiter _ _ hObj1 hTcb
          show (wakeThread st'' waiter executingCore).1.objects.invExt
          exact wakeThread_preserves_objects_invExt st'' waiter executingCore hObj2

/-- WS-SM SM6.B.1: the cross-core notification wait preserves object-store
integrity (`invExt`) on every control path. -/
theorem notificationWaitOnCore_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationWaitOnCore notificationId waiter executingCore st).1.objects.invExt := by
  unfold notificationWaitOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact hObjInv
  | some ntfn =>
    simp only
    cases hBadge : ntfn.pendingBadge with
    | some badge =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hObjInv
      | ok pair =>
        simp only
        have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcState pair.2 waiter .ready with
        | error e => simp only; exact hObjInv
        | ok st'' => simp only; exact storeTcbIpcState_preserves_objects_invExt pair.2 st'' waiter _ hObj1 hTcb
    | none =>
      simp only
      cases hLk : lookupTcb st waiter with
      | none => simp only; exact hObjInv
      | some tcb =>
        simp only
        split
        · exact hObjInv
        · cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
          | none => simp only; exact hObjInv
          | some wt' =>
            simp only
            cases hStore : storeObject notificationId _ st with
            | error e => simp only; exact hObjInv
            | ok pair =>
              simp only
              have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              cases hTcb : storeTcbIpcState_fromTcb pair.2 waiter tcb (.blockedOnNotification notificationId) with
              | error e => simp only; exact hObjInv
              | ok st'' =>
                simp only
                have hObj2 : st''.objects.invExt := by
                  unfold storeTcbIpcState_fromTcb at hTcb
                  cases hSO : storeObject waiter.toObjId
                      (.tcb { tcb with ipcState := .blockedOnNotification notificationId }) pair.2 with
                  | error e => simp [hSO] at hTcb
                  | ok p =>
                    simp only [hSO] at hTcb
                    have hE := Except.ok.inj hTcb; subst hE
                    exact storeObject_preserves_objects_invExt' pair.2 waiter.toObjId _ p hObj1 hSO
                show (removeRunnableOnCore st'' waiter executingCore).objects.invExt
                rw [removeRunnableOnCore_preserves_objects]; exact hObj2

-- ============================================================================
-- §2  `ipcInvariant` (notification well-formedness) preservation
-- ============================================================================

/-- WS-SM SM6.B.1: the cross-core notification signal preserves the IPC
`ipcInvariant`.  Mirrors `notificationSignal_preserves_ipcInvariant`, with the
cross-core waiter wake discharged through the object-invisibility keystone (the
waiter is already `.ready` after the message store, so `wakeThread` does not
disturb any object lookup). -/
theorem notificationSignalOnCore_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationSignalOnCore notificationId badge executingCore st).1 := by
  unfold notificationSignalOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact hInv
  | some ntfn =>
    simp only
    cases hWaiters : ntfn.waitingThreads.tail? with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        exact storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv hObjInv
          hStore (notificationSignal_result_wellFormed_merge _)
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv
          hObjInv hStore (notificationSignal_result_wellFormed_wake rest)
        have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st'' waiter _ _ hInv1 hObjInv1 hTcb
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st'' waiter _ _ hObjInv1 hTcb
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2 st'' waiter .ready _ hObjInv1 hTcb
          show ipcInvariant (wakeThread st'' waiter executingCore).1
          exact fun oid ntfn' h => hInv2 oid ntfn'
            (by rwa [wakeThread_objects_getElem_eq_of_ready st'' waiter executingCore tr hTrGet hTrReady hObj2 oid] at h)

/-- WS-SM SM6.B.1: the cross-core notification wait preserves the IPC
`ipcInvariant`.  Mirrors `notificationWait_preserves_ipcInvariant`, with the
per-core deschedule (`removeRunnableOnCore`) carried through its object-store
frame. -/
theorem notificationWaitOnCore_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationWaitOnCore notificationId waiter executingCore st).1 := by
  unfold notificationWaitOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact hInv
  | some ntfn =>
    simp only
    cases hBadge : ntfn.pendingBadge with
    | some badge =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv
          hObjInv hStore notificationWait_result_wellFormed_badge
        cases hTcb : storeTcbIpcState pair.2 waiter .ready with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          exact storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter .ready hInv1 hObjInv1 hTcb
    | none =>
      simp only
      cases hLk : lookupTcb st waiter with
      | none => simp only; exact hInv
      | some tcb =>
        simp only
        split
        · exact hInv
        · cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
          | none => simp only; exact hInv
          | some wt' =>
            simp only
            have hConsEq : wt'.val = waiter :: ntfn.waitingThreads.val :=
              ((SeLe4n.NoDupList.consWithGuard?_eq_some_iff waiter ntfn.waitingThreads wt').mp hCons).2
            cases hStore : storeObject notificationId _ st with
            | error e => simp only; exact hInv
            | ok pair =>
              simp only
              have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
                (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObjRaw hObjInv hStore
              have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv
                hObjInv hStore (notificationWait_result_wellFormed_wait waiter ntfn.waitingThreads wt' hConsEq)
              cases hTcb : storeTcbIpcState_fromTcb pair.2 waiter tcb (.blockedOnNotification notificationId) with
              | error e => simp only; exact hInv
              | ok st'' =>
                simp only
                rw [storeTcbIpcState_fromTcb_eq hLk'] at hTcb
                have hInv2 := storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter
                  (.blockedOnNotification notificationId) hInv1 hObjInv1 hTcb
                show ipcInvariant (removeRunnableOnCore st'' waiter executingCore)
                exact fun oid ntfn' h => hInv2 oid ntfn'
                  (by rwa [removeRunnableOnCore_preserves_objects] at h)

end SeLe4n.Kernel
