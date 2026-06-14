-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.IPC.Operations.NotificationBind

/-!
# WS-SM SM6.B — Bound-notification delivery across cores

`notificationSignalBoundOnCore` is the cross-core canonical notification signal:
when a notification with a `BlockedOnReceive` bound TCB and no waiters is
signalled, the badge is delivered directly to the bound TCB — dequeued from its
endpoint, woken on its *home* core via the SM5.C `wakeThread` (surfacing the
`.reschedule` SGI for a remote bound TCB) — otherwise it falls through to the
cross-core `notificationSignalOnCore`.

This module proves the bound-delivery semantics (path reductions + cross-core SGI
emission) and the IPC-invariant preservation of the bound-aware signal and the
bind / unbind operations.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The cross-core bound-aware signal transition
-- ============================================================================

/-- WS-SM SM6.B: the canonical cross-core notification signal.  On the
bound-delivery path the bound TCB is dequeued from its endpoint
(`endpointQueueRemoveDual`), delivered the badge, and woken cross-core
(`wakeThread`, surfacing the optional `.reschedule` SGI); otherwise the unchanged
cross-core `notificationSignalOnCore` runs. -/
def notificationSignalBoundOnCore (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match boundDeliveryTarget? st notificationId with
  | some (t, epId) =>
      let badgeMsg : IpcMessage := { IpcMessage.empty with badge := some badge }
      match endpointQueueRemoveDual epId true t st with
      | .error e => (st, .error e)
      | .ok ((), st1) =>
          match storeTcbIpcStateAndMessage st1 t .ready (some badgeMsg) with
          | .error e => (st, .error e)
          | .ok st2 =>
              ((wakeThread st2 t executingCore).1, .ok (wakeThread st2 t executingCore).2)
  | none => notificationSignalOnCore notificationId badge executingCore st

-- ============================================================================
-- §2  Path reductions
-- ============================================================================

/-- WS-SM SM6.B: the **fall-through** path — no bound-delivery target — is exactly
the cross-core `notificationSignalOnCore`.  (So every `notificationSignalOnCore`
theorem applies verbatim to the unbound / non-receiving case.) -/
theorem notificationSignalBoundOnCore_fallthrough_eq
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hNone : boundDeliveryTarget? st notificationId = none) :
    notificationSignalBoundOnCore notificationId badge executingCore st
      = notificationSignalOnCore notificationId badge executingCore st := by
  unfold notificationSignalBoundOnCore; rw [hNone]

/-- WS-SM SM6.B: the **bound-delivery** path reduction — the badge is delivered to
the bound TCB, which is dequeued from its endpoint and woken cross-core; the
surfaced SGI is exactly the wake's. -/
theorem notificationSignalBoundOnCore_delivery_eq
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (st1 st2 : SystemState)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId))
    (hRemove : endpointQueueRemoveDual epId true t st = .ok ((), st1))
    (hStore : storeTcbIpcStateAndMessage st1 t .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st2) :
    notificationSignalBoundOnCore notificationId badge executingCore st
      = ((wakeThread st2 t executingCore).1, .ok (wakeThread st2 t executingCore).2) := by
  unfold notificationSignalBoundOnCore
  rw [hTarget]; simp only [hRemove, hStore]

-- ============================================================================
-- §3  Cross-core SGI emission on bound delivery
-- ============================================================================

/-- WS-SM SM6.B: a bound delivery that wakes the bound TCB on a *remote* core
surfaces a `.reschedule` SGI to that core — the cross-core poke for the
directly-delivered notification. -/
theorem notificationSignalBoundOnCore_delivery_remote_wake
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (tTcb2 : TCB) (st1 st2 : SystemState)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId))
    (hRemove : endpointQueueRemoveDual epId true t st = .ok ((), st1))
    (hStore : storeTcbIpcStateAndMessage st1 t .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st2)
    (hTcb2 : st2.getTcb? t = some tTcb2)
    (hRemote : determineTargetCore st2 t ≠ executingCore) :
    (notificationSignalBoundOnCore notificationId badge executingCore st).2
      = .ok (some (determineTargetCore st2 t, SgiKind.reschedule)) := by
  rw [notificationSignalBoundOnCore_delivery_eq notificationId badge executingCore st t epId
        st1 st2 hTarget hRemove hStore]
  show Except.ok (wakeThread st2 t executingCore).2
      = Except.ok (some (determineTargetCore st2 t, SgiKind.reschedule))
  rw [wakeThread_emits_sgi_if_remote st2 t executingCore tTcb2 hTcb2 hRemote]

/-- WS-SM SM6.B: a bound delivery whose bound TCB is *local* surfaces no SGI. -/
theorem notificationSignalBoundOnCore_delivery_no_sgi_if_local
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (st1 st2 : SystemState)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId))
    (hRemove : endpointQueueRemoveDual epId true t st = .ok ((), st1))
    (hStore : storeTcbIpcStateAndMessage st1 t .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st2)
    (hLocal : determineTargetCore st2 t = executingCore) :
    (notificationSignalBoundOnCore notificationId badge executingCore st).2 = .ok none := by
  rw [notificationSignalBoundOnCore_delivery_eq notificationId badge executingCore st t epId
        st1 st2 hTarget hRemove hStore]
  show Except.ok (wakeThread st2 t executingCore).2 = Except.ok none
  rw [wakeThread_no_sgi_if_local st2 t executingCore hLocal]

-- ============================================================================
-- §4  IPC-invariant preservation of the bound-aware signal
-- ============================================================================

/-- WS-SM SM6.B: the bound-aware cross-core signal preserves `objects.invExt`.
Fall-through reuses `notificationSignalOnCore_preserves_objects_invExt`; the
delivery path chains the (new) `endpointQueueRemoveDual` / TCB-store / wake invExt
frames. -/
theorem notificationSignalBoundOnCore_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationSignalBoundOnCore notificationId badge executingCore st).1.objects.invExt := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only
    exact notificationSignalOnCore_preserves_objects_invExt notificationId badge executingCore st hObjInv
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => simp only; exact hObjInv
    | ok p =>
      simp only
      have hInv1 := endpointQueueRemoveDual_preserves_objects_invExt st p.2 epId true t hObjInv hRemove
      cases hStore : storeTcbIpcStateAndMessage p.2 t .ready
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact hObjInv
      | ok st2 =>
        simp only
        have hInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt p.2 st2 t _ _ hInv1 hStore
        show (wakeThread st2 t executingCore).1.objects.invExt
        exact wakeThread_preserves_objects_invExt st2 t executingCore hInv2

/-- WS-SM SM6.B: the bound-aware cross-core signal preserves the `ipcInvariant`
notification well-formedness.  Delivery path: `endpointQueueRemoveDual` preserves
it (queue links only), the TCB store does not write a notification, and the wake
is object-invisible on the just-`.ready` bound TCB. -/
theorem notificationSignalBoundOnCore_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationSignalBoundOnCore notificationId badge executingCore st).1 := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only
    exact notificationSignalOnCore_preserves_ipcInvariant notificationId badge executingCore st hInv hObjInv
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => simp only; exact hInv
    | ok p =>
      simp only
      have hInv1 := endpointQueueRemoveDual_preserves_ipcInvariant st p.2 epId true t hInv hObjInv hRemove
      have hObj1 := endpointQueueRemoveDual_preserves_objects_invExt st p.2 epId true t hObjInv hRemove
      cases hStore : storeTcbIpcStateAndMessage p.2 t .ready
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact hInv
      | ok st2 =>
        simp only
        have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant p.2 st2 t _ _ hInv1 hObj1 hStore
        have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt p.2 st2 t _ _ hObj1 hStore
        obtain ⟨tr, hTrGet, hTrReady⟩ :=
          storeTcbIpcStateAndMessage_getTcb?_ipcState p.2 st2 t .ready _ hObj1 hStore
        show ipcInvariant (wakeThread st2 t executingCore).1
        exact fun oid ntfn' h => hInv2 oid ntfn'
          (by rwa [wakeThread_objects_getElem_eq_of_ready st2 t executingCore tr hTrGet hTrReady hObj2 oid] at h)

-- ============================================================================
-- §5  Bind / unbind invariant preservation
-- ============================================================================

/-- Storing a **TCB** preserves `ipcInvariant` — the write touches only
`tcbId.toObjId`, which post-store holds a `.tcb` (never a `.notification`), so
every notification lookup is unchanged. -/
theorem storeObject_tcb_preserves_ipcInvariant
    (st st' : SystemState) (tcbId : SeLe4n.ThreadId) (newTcb : TCB)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStore : storeObject tcbId.toObjId (.tcb newTcb) st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ntfn hObj
  by_cases hNe : oid = tcbId.toObjId
  · rw [hNe, storeObject_objects_eq st st' tcbId.toObjId (.tcb newTcb) hObjInv hStore] at hObj
    simp at hObj
  · exact hInv oid ntfn (by rwa [storeObject_objects_ne st st' tcbId.toObjId oid _ hNe hObjInv hStore] at hObj)

/-- WS-SM SM6.B: `bindNotification` preserves `objects.invExt` (two `storeObject`
steps). -/
theorem bindNotification_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (tcbId : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : bindNotification notificationId tcbId st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold bindNotification at hStep
  cases hObjN : st.getNotification? notificationId with
  | none => simp only [hObjN] at hStep; split at hStep <;> simp at hStep
  | some ntfn =>
    simp only [hObjN] at hStep
    cases hLk : lookupTcb st tcbId with
    | none => simp [hLk] at hStep
    | some tcb =>
      simp only [hLk] at hStep; revert hStep
      split
      · simp
      · cases hS1 : storeObject notificationId _ st with
        | error e => simp
        | ok p1 =>
          simp only []
          have hInv1 := storeObject_preserves_objects_invExt' st notificationId _ p1 hObjInv hS1
          cases hS2 : storeObject tcbId.toObjId _ p1.2 with
          | error e => simp
          | ok p2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeObject_preserves_objects_invExt' p1.2 tcbId.toObjId _ p2 hInv1 hS2

/-- WS-SM SM6.B: `bindNotification` preserves `ipcInvariant` — the notification
write changes only `boundTCB` (not the queue/badge `notificationQueueWellFormed`
reads), and the TCB write touches no notification. -/
theorem bindNotification_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (tcbId : SeLe4n.ThreadId) (st st' : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : bindNotification notificationId tcbId st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold bindNotification at hStep
  cases hObjN : st.getNotification? notificationId with
  | none => simp only [hObjN] at hStep; split at hStep <;> simp at hStep
  | some ntfn =>
    simp only [hObjN] at hStep
    have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
      (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
    cases hLk : lookupTcb st tcbId with
    | none => simp [hLk] at hStep
    | some tcb =>
      simp only [hLk] at hStep; revert hStep
      split
      · simp
      · cases hS1 : storeObject notificationId _ st with
        | error e => simp
        | ok p1 =>
          simp only []
          have hInv1 : ipcInvariant p1.2 :=
            storeObject_notification_preserves_ipcInvariant st p1.2 notificationId _ hInv hObjInv hS1
              (hInv notificationId ntfn hObjRaw)
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ p1 hObjInv hS1
          cases hS2 : storeObject tcbId.toObjId _ p1.2 with
          | error e => simp
          | ok p2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeObject_tcb_preserves_ipcInvariant p1.2 p2.2 tcbId _ hInv1 hObjInv1 hS2

/-- WS-SM SM6.B: `unbindNotification` preserves `objects.invExt`. -/
theorem unbindNotification_preserves_objects_invExt
    (tcbId : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : unbindNotification tcbId st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold unbindNotification at hStep
  cases hLk : lookupTcb st tcbId with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep
    cases hBound : tcb.boundNotification with
    | none => simp [hBound] at hStep
    | some notificationId =>
      simp only [hBound] at hStep; revert hStep
      cases hS1 : storeObject tcbId.toObjId _ st with
      | error e => simp
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt' st tcbId.toObjId _ p1 hObjInv hS1
        cases hObjN : p1.2.getNotification? notificationId with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro ⟨_, hEq⟩; subst hEq; exact hInv1
        | some ntfn =>
          simp only []
          cases hS2 : storeObject notificationId _ p1.2 with
          | error e => simp
          | ok p2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeObject_preserves_objects_invExt' p1.2 notificationId _ p2 hInv1 hS2

/-- WS-SM SM6.B: `unbindNotification` preserves `ipcInvariant`. -/
theorem unbindNotification_preserves_ipcInvariant
    (tcbId : SeLe4n.ThreadId) (st st' : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : unbindNotification tcbId st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold unbindNotification at hStep
  cases hLk : lookupTcb st tcbId with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep
    cases hBound : tcb.boundNotification with
    | none => simp [hBound] at hStep
    | some notificationId =>
      simp only [hBound] at hStep; revert hStep
      cases hS1 : storeObject tcbId.toObjId _ st with
      | error e => simp
      | ok p1 =>
        simp only []
        have hInv1 : ipcInvariant p1.2 := storeObject_tcb_preserves_ipcInvariant st p1.2 tcbId _ hInv hObjInv hS1
        have hObjInv1 := storeObject_preserves_objects_invExt' st tcbId.toObjId _ p1 hObjInv hS1
        cases hObjN : p1.2.getNotification? notificationId with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro ⟨_, hEq⟩; subst hEq; exact hInv1
        | some ntfn =>
          simp only []
          have hObjRaw : p1.2.objects[notificationId]? = some (.notification ntfn) :=
            (SystemState.getNotification?_eq_some_iff p1.2 notificationId ntfn).mp hObjN
          cases hS2 : storeObject notificationId _ p1.2 with
          | error e => simp
          | ok p2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeObject_notification_preserves_ipcInvariant p1.2 p2.2 notificationId _ hInv1 hObjInv1 hS2
              (hInv1 notificationId ntfn hObjRaw)

-- ============================================================================
-- §6  Bound-delivery lock-set footprint (codex review #5)
-- ============================================================================

/-- WS-SM SM6.B: the lock-set footprint a cross-core **bound** notification signal
acquires.  On the bound-delivery path (`boundDeliveryTarget? = some (t, ep)`) the
signal additionally dequeues the bound TCB `t` from its endpoint `ep`
(`endpointQueueRemoveDual`) and writes `t` (badge + `.ready`), so the footprint
extends the base signal lock-set — signaller TCB (read), CNode (read), notification
(write); there is no notification waiter on this path — with the **endpoint write**
and the **bound-TCB write** locks.  Off the bound path it is exactly
`lockSet_notificationSignalOnCore`.  This is the footprint the runtime `withLockSet`
bracket must acquire so the bound-delivery endpoint/TCB writes fall inside the 2PL
footprint (codex review #5); the prior `lockSet_notificationSignalOnCore` declared
only signaller/CNode/notification, leaving those writes unprotected. -/
def lockSet_notificationSignalBoundOnCore (st : SystemState) (notificationId : SeLe4n.ObjId)
    (signaller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) : LockSet :=
  match boundDeliveryTarget? st notificationId with
  | some (boundTcb, epId) =>
      lockSetOfList
        [(tcbLock signaller, .read),
         (cnodeLock cnodeRootObjId, .read),
         (notificationLock notificationId, .write),
         (endpointLock epId, .write),
         (tcbLock boundTcb, .write)]
  | none =>
      lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId

/-- WS-SM SM6.B: the bound-signal lock-set is **hierarchically correct** — every
declared lock has a kind in `permittedKinds .notificationSignal` (which SM6.B
extends with `.endpoint` for the bound-delivery dequeue).  Off the bound path this
is `lockSet_notificationSignalOnCore_correct`; on it, each of the five footprint
locks (signaller / bound TCB, CNode, notification, endpoint) has a permitted kind. -/
theorem lockSet_notificationSignalBoundOnCore_correct
    (st : SystemState) (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    ∀ p ∈ (lockSet_notificationSignalBoundOnCore st notificationId signaller cnodeRootObjId).pairs,
      p.fst.kind ∈ permittedKinds .notificationSignal := by
  unfold lockSet_notificationSignalBoundOnCore
  cases hT : boundDeliveryTarget? st notificationId with
  | none =>
      exact lockSet_notificationSignalOnCore_correct st notificationId signaller cnodeRootObjId
  | some pair =>
      obtain ⟨boundTcb, epId⟩ := pair
      refine lockSet_consistent_of_extended_base _ (permittedKinds .notificationSignal) ?_
      intro p hMem
      rcases List.mem_cons.mp hMem with h | hMem
      · rw [h]; simp; decide
      rcases List.mem_cons.mp hMem with h | hMem
      · rw [h]; simp; decide
      rcases List.mem_cons.mp hMem with h | hMem
      · rw [h]; simp; decide
      rcases List.mem_cons.mp hMem with h | hMem
      · rw [h]; simp; decide
      rcases List.mem_cons.mp hMem with h | hMem
      · rw [h]; simp; decide
      exact absurd hMem (by intro h; cases h)

end SeLe4n.Kernel
