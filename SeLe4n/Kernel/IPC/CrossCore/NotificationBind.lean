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
          -- IPC de-threading D3 (Finding F-1): the bound TCB was
          -- `.blockedOnReceive`; a non-`Call` badge delivery clears its
          -- server-first `pendingReceiveReply` stash (no `Call` arrived).
          match storeTcbReceiveComplete st1 t (some badgeMsg) with
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
    (hStore : storeTcbReceiveComplete st1 t
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
    (hStore : storeTcbReceiveComplete st1 t
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
    (hStore : storeTcbReceiveComplete st1 t
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
      cases hStore : storeTcbReceiveComplete p.2 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact hObjInv
      | ok st2 =>
        simp only
        have hInv2 := storeTcbReceiveComplete_preserves_objects_invExt p.2 st2 t _ hInv1 hStore
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
      cases hStore : storeTcbReceiveComplete p.2 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact hInv
      | ok st2 =>
        simp only
        have hInv2 := storeTcbReceiveComplete_preserves_ipcInvariant p.2 st2 t _ hInv1 hObj1 hStore
        have hObj2 := storeTcbReceiveComplete_preserves_objects_invExt p.2 st2 t _ hObj1 hStore
        obtain ⟨tr, hTrGet, hTrReady⟩ :=
          storeTcbReceiveComplete_getTcb?_ipcState p.2 st2 t _ hObj1 hStore
        show ipcInvariant (wakeThread st2 t executingCore).1
        exact fun oid ntfn' h => hInv2 oid ntfn'
          (by rwa [wakeThread_objects_getElem_eq_of_ready st2 t executingCore tr hTrGet hTrReady hObj2 oid] at h)

open SeLe4n.Model.SystemState in
/-- **WS-RR RR7.22 (residual)**: the bound-aware cross-core signal preserves the
**whole twenty-conjunct bundle**.

This is one of the two consumers RR7.22's splice engine was built for, and the
reason the engine relaxes exactly one conjunct: the bound delivery is
`splice; receive-complete; wake`, and the three legs divide the bundle cleanly.

* The **splice** hands over `ipcInvariantFullExceptMembership` at the delivered
  thread — nineteen conjuncts unconditional, membership relaxed there because
  the splice deliberately leaves that thread's `ipcState` alone.
* The **receive-completing store** is the step that writes it: `.ready` restores
  the relaxed conjunct and carries the other nineteen
  (`storeTcbReceiveComplete_closes_exceptMembership`).  Its three detachment
  premises are what the splice has just established
  (`endpointQueueRemoveDual_removed_detached`) — which is why this pair composes
  and an arbitrary `.ready` rewrite does not.
* The **wake** of an already-`.ready` thread is object-lookup-invisible, so the
  nineteen lookup-only conjuncts transport by congruence and the one
  scheduler-reading conjunct rides the per-core frame at the boot core.

`hPred` is the splice's own `splicePredecessorBlocked` obligation, stated rather
than assumed away: the bundle genuinely does not entail that a predecessor
promoted to tail is blocked on the endpoint, and a caller discharges it from a
reachability witness (`splicePredecessorBlocked_of_head` when the delivered
thread heads the queue, `splicePredecessorBlocked_of_path` otherwise).  Every
other hypothesis is the fall-through path's, unchanged. -/
theorem notificationSignalBoundOnCore_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st notificationId = some (t, epId) →
      splicePredecessorBlocked true epId st t) :
    ipcInvariantFull (notificationSignalBoundOnCore notificationId badge executingCore st).1 := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only
    exact notificationSignalOnCore_preserves_ipcInvariantFull notificationId badge executingCore
      st hInv hObjInv hNWC hAllBudgetsNone
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => simp only; exact hInv
    | ok p =>
      simp only
      obtain ⟨tcb0, hTcb0, hState0⟩ := boundDeliveryTarget?_some st notificationId t epId hTarget
      have hObj1 := endpointQueueRemoveDual_preserves_objects_invExt st p.2 epId true t hObjInv
        hRemove
      have hExcept := endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership
        st p.2 epId true t hObjInv hRemove hInv (hPred t epId hTarget)
      obtain ⟨hIpc1, hDual1, hBounded1, hBadge1, hPend1, hNoDup1, hMem1, hQNB1, hQHB1,
        hTimeout1, hAcyc1, hOwner1, hPsi1, hBudget1, hRTgt1, hRLink1, hStash1, hUniq1,
        hQTB1, hQNT1⟩ := hExcept
      -- The delivered thread survives the splice with its `ipcState` untouched:
      -- still `.blockedOnReceive epId`, which is what the detachment argument reads.
      obtain ⟨tcbPost, hTidPost, _, _, _⟩ :=
        endpointQueueRemoveDual_removed_links_cleared st p.2 epId true t hObjInv hRemove
      obtain ⟨tcbPre, hTcbPre, hStateEq⟩ :=
        endpointQueueRemoveDual_ipcStateFrame st p.2 epId true t hObjInv hRemove t tcbPost hTidPost
      have hStatePost : tcbPost.ipcState = .blockedOnReceive epId := by
        rw [← hStateEq]
        rw [(getTcb?_eq_some_iff st t tcb0).mp hTcb0] at hTcbPre
        obtain rfl : tcbPre = tcb0 := (KernelObject.tcb.inj (Option.some.inj hTcbPre)).symm
        exact hState0
      obtain ⟨hNotHead1, hNotTail1, hNoIncoming1⟩ :=
        endpointQueueRemoveDual_removed_detached st p.2 epId t hObjInv
          hInv.dualQueueSystemInvariant hRemove tcbPost hTidPost hStatePost hQHB1 hQTB1 hDual1.2.1
      have hAllNone1 : allTimeoutBudgetsNone p.2 :=
        allTimeoutBudgetsNone_of_frame
          (endpointQueueRemoveDual_timeoutBudgetFrame st p.2 epId true t hObjInv hRemove)
          hAllBudgetsNone
      have hNotReply1 : ∀ (tcb : TCB), p.2.objects[t.toObjId]? = some (.tcb tcb) →
          ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt := by
        intro tcb hTcb ep rt hEq
        rw [hTidPost] at hTcb
        obtain rfl : tcb = tcbPost := (KernelObject.tcb.inj (Option.some.inj hTcb)).symm
        rw [hStatePost] at hEq
        cases hEq
      cases hStore : storeTcbReceiveComplete p.2 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact hInv
      | ok st2 =>
        simp only
        have hFull2 : ipcInvariantFull st2 :=
          storeTcbReceiveComplete_closes_exceptMembership p.2 st2 t _ hObj1
            (fun m hm => by
              cases hm
              unfold IpcMessage.bounded IpcMessage.empty maxMessageRegisters maxExtraCaps
              simp [Array.size])
            hAllNone1 hNotReply1 hNotHead1 hNotTail1 hNoIncoming1
            ⟨hIpc1, hDual1, hBounded1, hBadge1, hPend1, hNoDup1, hMem1, hQNB1, hQHB1,
              hTimeout1, hAcyc1, hOwner1, hPsi1, hBudget1, hRTgt1, hRLink1, hStash1, hUniq1,
              hQTB1, hQNT1⟩ hStore
        have hObj2 := storeTcbReceiveComplete_preserves_objects_invExt p.2 st2 t _ hObj1 hStore
        obtain ⟨tr, hTrGet, hTrReady⟩ :=
          storeTcbReceiveComplete_getTcb?_ipcState p.2 st2 t _ hObj1 hStore
        show ipcInvariantFull (wakeThread st2 t executingCore).1
        exact ipcInvariantFull_of_getElem_eq
          (fun oid => wakeThread_objects_getElem_eq_of_ready st2 t executingCore tr hTrGet
            hTrReady hObj2 oid)
          (passiveServerIdle_of_frame
            ((passiveServerIdleFrameOnCore_boot_iff st2 (wakeThread st2 t executingCore).1).mp
              (wakeThread_passiveServerIdleFrameOnCore_of_ready st2 t executingCore tr hTrGet
                hTrReady hObj2))
            hFull2.passiveServerIdle)
          hFull2

open SeLe4n.Model.SystemState in
/-- **WS-RR RR7.22 (residual)**: the bound-aware cross-core signal frames every
core's `passiveServerIdle` slice.

The fall-through is the unbound signal's own frame; the delivery path is the
three legs' per-core frames chained — splice, receive-completing store, and the
wake of an already-`.ready` thread.  No idle-core assumption, matching the
sibling `notificationSignalOnCore_passiveServerIdleFrameOnCore`. -/
theorem notificationSignalBoundOnCore_passiveServerIdleFrameOnCore
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (notificationSignalBoundOnCore notificationId badge executingCore st).1 c := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only
    exact notificationSignalOnCore_passiveServerIdleFrameOnCore notificationId badge
      executingCore st c hObjInv
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
    | ok p =>
      simp only
      have hObj1 := endpointQueueRemoveDual_preserves_objects_invExt st p.2 epId true t hObjInv
        hRemove
      have f1 : passiveServerIdleFrameOnCore st p.2 c :=
        endpointQueueRemoveDual_passiveServerIdleFrameOnCore st p.2 epId true t hObjInv hRemove
      cases hStore : storeTcbReceiveComplete p.2 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok st2 =>
        simp only
        have hObj2 := storeTcbReceiveComplete_preserves_objects_invExt p.2 st2 t _ hObj1 hStore
        have f2 : passiveServerIdleFrameOnCore p.2 st2 c :=
          storeTcbReceiveComplete_passiveServerIdleFrameOnCore p.2 st2 t _ hObj1 hStore
        obtain ⟨tr, hTrGet, hTrReady⟩ :=
          storeTcbReceiveComplete_getTcb?_ipcState p.2 st2 t _ hObj1 hStore
        show passiveServerIdleFrameOnCore st (wakeThread st2 t executingCore).1 c
        exact (f1.trans f2).trans
          (wakeThread_passiveServerIdleFrameOnCore_of_ready st2 t executingCore tr hTrGet
            hTrReady hObj2)

open SeLe4n.Model.SystemState in
/-- **WS-RR RR7.22 (residual)** flagship: the bound-aware cross-core signal
preserves **every core's** view of the IPC invariant bundle — the whole-bundle
theorem above through `ipcInvariantFull_perCore_of_full`, with core `c`'s
passive slice riding the frame.  No idle-core assumption. -/
theorem notificationSignalBoundOnCore_preserves_ipcInvariantFull_perCore
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st notificationId = some (t, epId) →
      splicePredecessorBlocked true epId st t)
    (c : CoreId) :
    ipcInvariantFull_perCore
      (notificationSignalBoundOnCore notificationId badge executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (notificationSignalBoundOnCore_preserves_ipcInvariantFull notificationId badge executingCore
      st (ipcInvariantFull_of_smp hInv) hObjInv hNWC hAllBudgetsNone hPred)
    (passiveServerIdle_perCore_of_frameOnCore
      (notificationSignalBoundOnCore_passiveServerIdleFrameOnCore notificationId badge
        executingCore st c hObjInv)
      (hInv c).passiveServerIdle)

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
-- §6  Bound-delivery lock-set coverage (PR #822 review)
--
-- The canonical state-resolved footprint `lockSet_notificationSignalOnCore`
-- (`CrossCore/NotificationSignal`) is now **bound-aware**: on the bound-delivery
-- path (`boundDeliveryTarget? = some (boundTcb, ep)`) it sets the canonical
-- footprint's `boundEndpoint` / `boundTcb` optionals, so the live bound signal's
-- endpoint-dequeue + bound-TCB writes fall inside the acquired 2PL set.  The separate
-- `lockSet_notificationSignalBoundOnCore` that previously carried this — a
-- proven-but-unwired footprint the live path never selected — has been removed as
-- redundant; these state-resolved coverage witnesses delegate to the parametric
-- `lockSet_notificationSignal_bound_{tcb,endpoint}_write_mem`.
-- ============================================================================

/-- WS-SM SM6.B / PR #822 review (coverage): on the bound-delivery path the **bound-TCB
write lock** is a declared member of the canonical signal footprint — the lock under
which the badge + `.ready` write to the dequeued bound TCB happens. -/
theorem lockSet_notificationSignalOnCore_bound_tcb_write_mem
    (st : SystemState) (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId)) :
    (tcbLock t, AccessMode.write) ∈
      (lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId).pairs := by
  unfold lockSet_notificationSignalOnCore
  rw [hTarget]
  exact lockSet_notificationSignal_bound_tcb_write_mem signaller cnodeRootObjId notificationId
    (notificationSignalWaiter? st notificationId) (some epId) t
    (notificationSignalSpliceNeighbors? st notificationId)

/-- WS-SM SM6.B / PR #822 review (coverage): on the bound-delivery path the **endpoint
write lock** is a declared member of the canonical signal footprint — the lock under
which the bound TCB is dequeued from its endpoint (`endpointQueueRemoveDual`). -/
theorem lockSet_notificationSignalOnCore_bound_endpoint_write_mem
    (st : SystemState) (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId)) :
    (endpointLock epId, AccessMode.write) ∈
      (lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId).pairs := by
  unfold lockSet_notificationSignalOnCore
  rw [hTarget]
  exact lockSet_notificationSignal_bound_endpoint_write_mem signaller cnodeRootObjId notificationId
    (notificationSignalWaiter? st notificationId) epId t
    (notificationSignalSpliceNeighbors? st notificationId)

end SeLe4n.Kernel
