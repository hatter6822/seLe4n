-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.B: PRODUCTION (LANDED).  Entered the production import closure with
-- `notificationSignalOnCore` when the live bound-aware `.notificationSignal`
-- dispatch was wired through the cross-core notification stack.  (Former
-- "STATUS: staged" marker replaced per the implement-the-improvement rule; see
-- WS-SM SM6.)

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation

/-!
# WS-SM SM6.B — Cross-core notification IPC-invariant preservation

`notificationSignalOnCore` / `notificationWaitOnCore` preserve the kernel's
object-store integrity (`objects.invExt`) and the IPC `ipcInvariant`
(notification well-formedness).  Each cross-core operation differs from its
single-core form only in the *scheduler* placement of the woken waiter / blocked
caller; `ipcInvariant` is **lookup-only** (it reads the state solely through
`objects[·]?`), so the cross-core receiver wake (`wakeThread`, invisible off run-queue links
on the already-`.ready` waiter — the §2 keystone of `EndpointCallInvariant`) and
the per-core deschedule (`removeRunnableOnCore`, an object-store frame) cannot
disturb it.  The notification-store / TCB-store steps reuse the single-core
per-step preservation lemmas verbatim.

**WS-SM SM6.D closure** (§3–§6): the cross-core transitions preserve the
**whole nineteen-conjunct bundle** and every core's per-core view of it —
`notificationSignalOnCore_preserves_ipcInvariantFull{,_perCore}` /
`notificationWaitOnCore_preserves_ipcInvariantFull{,_perCore}`.  The proof
lever is the off-scheduler agreement dichotomy (§4): a cross-core transition
either fails (post-state = pre-state) or runs the *same* object-store spine as
its single-core counterpart and diverges only in the final scheduler placement
(`wakeThread`/`removeRunnableOnCore` for `ensureRunnable`/`removeRunnable`) —
so the single-core whole-bundle theorem carries across the
`OffSchedulerAgrees` relation via the lookup congruences
(`IPC/Invariant/LookupCongruence.lean`); no conjunct reads the scheduler.
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
    cases hWaiters : ntfn.waitHead with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hObjInv
      | ok pair => simp only; exact storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
    | some waiter =>
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
          show (wakeThread _ waiter executingCore).1.objects.invExt
          exact wakeThread_preserves_objects_invExt _ waiter executingCore
            (detachNtfnHead_linksRewritten _ _ _ hObj2).2.1

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
        · cases hStore : storeObject notificationId _ st with
          | error e => simp only; exact hObjInv
          | ok pair =>
            simp only
            have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            cases hTcb : storeTcbIpcStateAndMessage_fromTcb pair.2 waiter tcb
                (.blockedOnNotification notificationId) none with
            | error e => simp only; exact hObjInv
            | ok st2 =>
              simp only
              have hObj2 : st2.objects.invExt := by
                unfold storeTcbIpcStateAndMessage_fromTcb at hTcb
                cases hSO : storeObject waiter.toObjId
                    (.tcb (TCB.setIpcState { tcb with pendingMessage := none } (.blockedOnNotification notificationId)))
                    pair.2 with
                | error e => simp [hSO] at hTcb
                | ok p =>
                  simp only [hSO] at hTcb
                  have hE := Except.ok.inj hTcb; subst hE
                  exact storeObject_preserves_objects_invExt' pair.2 waiter.toObjId _ p hObj1 hSO
              cases hLink : linkNtfnWaiter st2 waiter ntfn.waitTail with
              | error e => simp only; exact hObjInv
              | ok st'' =>
                simp only
                exact removeRunnableOnCore_objects_invExt _ _ _
                  (linkNtfnWaiter_preserves_objects_invExt hObj2 hLink)

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
    cases hWaiters : ntfn.waitHead with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        exact storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv hObjInv
          hStore (notificationSignal_result_wellFormed_merge _ _)
    | some waiter =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv
          hObjInv hStore (notificationSignal_result_wellFormed_wake ntfn _)
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
          have hD := detachNtfnHead_linksRewritten st'' waiter (ntfnSuccessor? st waiter) hObj2
          obtain ⟨tr3, hTrGet3, ⟨_, _, rfl⟩⟩ := hD.getTcb?_fwd hTrGet
          show ipcInvariant (wakeThread _ waiter executingCore).1
          exact fun oid ntfn' h => hInv2 oid ntfn'
            ((hD.obj_iff _ _ (fun _ e => by cases e)).mp
              ((wakeThread_objectsAgreeOffRunLinks_of_ready _ waiter executingCore _ hTrGet3
                hTrReady hD.2.1).get_notification_iff.mp h))

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
          hObjInv hStore (notificationWait_result_wellFormed_badge _)
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
        · cases hStore : storeObject notificationId _ st with
          | error e => simp only; exact hInv
          | ok pair =>
            simp only
            have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
              (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
            have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObjRaw hObjInv hStore
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId _ hInv
              hObjInv hStore (notificationWait_result_wellFormed_wait ntfn waiter)
            cases hTcb : storeTcbIpcStateAndMessage_fromTcb pair.2 waiter tcb
                (.blockedOnNotification notificationId) none with
            | error e => simp only; exact hInv
            | ok st2 =>
              simp only
              rw [storeTcbIpcStateAndMessage_fromTcb_eq hLk'] at hTcb
              have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 waiter
                (.blockedOnNotification notificationId) none hInv1 hObjInv1 hTcb
              have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st2 waiter _ _
                hObjInv1 hTcb
              cases hLink : linkNtfnWaiter st2 waiter ntfn.waitTail with
              | error e => simp only; exact hInv
              | ok st'' =>
                simp only
                have hInv3 := linkNtfnWaiter_preserves_ipcInvariant hObj2 hLink hInv2
                exact ipcInvariant_of_objectsAgreeOffRunLinks
                  (removeRunnableOnCore_objectsAgreeOffRunLinks st'' waiter executingCore) hInv3

-- ============================================================================
-- §4  SM6.D: cross-core / single-core off-scheduler agreement dichotomies
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: agreement dichotomy for the cross-core signal.  Either the
cross-core transition failed (post-state = pre-state), or its single-core
counterpart succeeds from the same pre-state and the two post-states agree
off-scheduler — both spines run the *same* notification/TCB stores and differ
only in the final scheduler placement (`wakeThread … executingCore` vs
`ensureRunnable`), whose object effect on the already-`.ready` waiter is
lookup-invisible. -/
theorem notificationSignalOnCore_post_agrees
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationSignalOnCore notificationId badge executingCore st).1 = st ∨
    ∃ r1, notificationSignal notificationId badge st = .ok ((), r1) ∧
      OffSchedulerAgrees r1 (notificationSignalOnCore notificationId badge executingCore st).1 := by
  unfold notificationSignalOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => left; simp only; split <;> rfl
  | some ntfn =>
    have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
      (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
    simp only
    cases hWaiters : ntfn.waitHead with
    | none =>
      simp only
      -- Resolve the `mergedBadge` scrutinee first: the two definitions
      -- elaborate the badge-merge `match` to *distinct* auxiliary matcher
      -- constants, so the stored objects only become syntactically equal
      -- once `ntfn.pendingBadge` is a constructor and both matchers reduce.
      cases hPB : ntfn.pendingBadge with
      | some existing =>
        simp only
        cases hStore : storeObject notificationId _ st with
        | error e => left; rfl
        | ok pair =>
          right
          simp only
          refine ⟨pair.2, ?_, OffSchedulerAgrees.refl pair.2⟩
          unfold notificationSignal SystemState.getObject?
          simp only [hObjRaw, hWaiters, hPB, hStore]
      | none =>
        simp only
        cases hStore : storeObject notificationId _ st with
        | error e => left; rfl
        | ok pair =>
          right
          simp only
          refine ⟨pair.2, ?_, OffSchedulerAgrees.refl pair.2⟩
          unfold notificationSignal SystemState.getObject?
          simp only [hObjRaw, hWaiters, hPB, hStore]
    | some waiter =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => left; rfl
      | ok pair =>
        simp only
        cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => left; rfl
        | ok st2 =>
          right
          simp only
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
          have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st2 waiter _ _
            hObjInv1 hTcb
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2 st2 waiter .ready _ hObjInv1 hTcb
          have hD := detachNtfnHead_linksRewritten st2 waiter (ntfnSuccessor? st waiter) hObjInv2
          obtain ⟨tr3, hTrGet3, ⟨_, _, rfl⟩⟩ := hD.getTcb?_fwd hTrGet
          refine ⟨ensureRunnable (detachNtfnHead st2 waiter (ntfnSuccessor? st waiter)) waiter,
            ?_, ?_⟩
          · unfold notificationSignal SystemState.getObject?
            simp only [hObjRaw, hWaiters, hStore, hTcb]
          · exact (ensureRunnable_offSchedulerAgrees _ waiter).symm.trans
              (wakeThread_offSchedulerAgrees_of_ready _ waiter executingCore _ hTrGet3
                hTrReady hD.2.1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: agreement dichotomy for the cross-core wait.  Either the
cross-core transition failed (post-state = pre-state), or its single-core
counterpart succeeds from the same pre-state with the same result and the two
post-states agree off-scheduler — the badge-consume path is *identical* (no
scheduler step), and the block path diverges only in the final per-core
deschedule (`removeRunnableOnCore … executingCore` vs `removeRunnable`), both
scheduler-only. -/
theorem notificationWaitOnCore_post_agrees
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationWaitOnCore notificationId waiter executingCore st).1 = st ∨
    ∃ r1 result, notificationWait notificationId waiter st = .ok (result, r1) ∧
      OffSchedulerAgrees r1 (notificationWaitOnCore notificationId waiter executingCore st).1 := by
  unfold notificationWaitOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => left; simp only; split <;> rfl
  | some ntfn =>
    have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
      (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
    simp only
    cases hBadge : ntfn.pendingBadge with
    | some badge =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => left; rfl
      | ok pair =>
        simp only
        cases hTcb : storeTcbIpcState pair.2 waiter .ready with
        | error e => left; rfl
        | ok st2 =>
          right
          simp only
          refine ⟨st2, some badge, ?_, OffSchedulerAgrees.refl st2⟩
          unfold notificationWait notificationWaitPark SystemState.getObject?
          simp only [hObjRaw, hBadge, hStore, hTcb]
    | none =>
      simp only
      cases hLk : lookupTcb st waiter with
      | none => left; rfl
      | some tcb =>
        simp only
        split
        · left; rfl
        · rename_i hIpcNe
          cases hStore : storeObject notificationId _ st with
          | error e => left; rfl
          | ok pair =>
            simp only
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            cases hTcb : storeTcbIpcStateAndMessage_fromTcb pair.2 waiter tcb
                (.blockedOnNotification notificationId) none with
            | error e => left; rfl
            | ok st2 =>
              simp only
              have hObj2 : st2.objects.invExt := by
                have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObjRaw hObjInv hStore
                rw [storeTcbIpcStateAndMessage_fromTcb_eq hLk'] at hTcb
                exact storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st2 waiter _ _
                  hObjInv1 hTcb
              cases hLink : linkNtfnWaiter st2 waiter ntfn.waitTail with
              | error e => left; rfl
              | ok st'' =>
                right
                simp only
                obtain ⟨r1, hL1, hAg⟩ := linkNtfnWaiter_offSchedulerAgrees waiter ntfn.waitTail
                  (removeRunnable_offSchedulerAgrees st2 waiter).symm
                  (removeRunnable_objects_invExt st2 waiter hObj2) hObj2 hLink
                refine ⟨r1, none, ?_, hAg.trans
                  (removeRunnableOnCore_offSchedulerAgrees st'' waiter executingCore)⟩
                have hTail : notificationWaitTail? st notificationId = ntfn.waitTail := by
                  unfold notificationWaitTail?; simp only [hObjN, hBadge]
                unfold notificationWait
                have hPark : notificationWaitPark notificationId waiter st
                    = .ok (none, removeRunnable st2 waiter) := by
                  unfold notificationWaitPark SystemState.getObject?
                  simp only [hObjRaw, hBadge, hLk, if_neg hIpcNe, hStore, hTcb]
                simp only [hPark, hTail, hL1]

-- ============================================================================
-- §5  SM6.D: whole-bundle `ipcInvariantFull` preservation (cross-core)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.B closure): the cross-core notification signal preserves
the **whole nineteen-conjunct bundle**, unconditionally over success/failure
(error paths return the pre-state).  Every conjunct is lookup-only, so the
bundle rides the single-core whole-bundle theorem across the §4 agreement
dichotomy.  Hypotheses mirror `notificationSignal_preserves_ipcInvariantFull`, with
the threaded post-state facts stated at the cross-core post-state. -/
theorem notificationSignalOnCore_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull (notificationSignalOnCore notificationId badge executingCore st).1 := by
  rcases notificationSignalOnCore_post_agrees notificationId badge executingCore st hObjInv with
    hPre | ⟨r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_objectsAgreeOffRunLinks hAgree.objects
      (notificationSignal_preserves_ipcInvariantFull st r1 notificationId badge hInv hObjInv
        hNWC hAllBudgetsNone hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.B closure): the cross-core notification wait preserves
the **whole nineteen-conjunct bundle**, unconditionally over success/failure.
Hypotheses mirror `notificationWait_preserves_ipcInvariantFull`, with TCB
lookups routed through the typed `getTcb?` and the threaded post-state facts
stated at the cross-core post-state. -/
theorem notificationWaitOnCore_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull (notificationWaitOnCore notificationId waiter executingCore st).1 := by
  rcases notificationWaitOnCore_post_agrees notificationId waiter executingCore st hObjInv with
    hPre | ⟨r1, result, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_objectsAgreeOffRunLinks hAgree.objects
      (notificationWait_preserves_ipcInvariantFull st r1 notificationId waiter result hInv hObjInv
        hWaiterNotRecv
        (fun tcb hRaw => hWaiterNotReply tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
        hAllBudgetsNone
        (fun tcb hRaw => hWaiterReady tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
        hStep1)

-- ============================================================================
-- §6  SM6.D: per-core bundle preservation (cross-core flagships)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core signal): `notificationSignalOnCore`
preserves **every core's** view of the IPC invariant bundle — the §5
whole-bundle theorem through `ipcInvariantFull_perCore_of_full`, with core
`c`'s passive slice riding the §3 frame.  No idle-core assumption. -/
theorem notificationSignalOnCore_preserves_ipcInvariantFull_perCore
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (c : CoreId) :
    ipcInvariantFull_perCore (notificationSignalOnCore notificationId badge executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (notificationSignalOnCore_preserves_ipcInvariantFull notificationId badge executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hNWC hAllBudgetsNone)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core wait): `notificationWaitOnCore` preserves
**every core's** view of the IPC invariant bundle.  No idle-core
assumption. -/
theorem notificationWaitOnCore_preserves_ipcInvariantFull_perCore
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready)
    (c : CoreId) :
    ipcInvariantFull_perCore (notificationWaitOnCore notificationId waiter executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (notificationWaitOnCore_preserves_ipcInvariantFull notificationId waiter executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hWaiterNotRecv hWaiterNotReply
      hAllBudgetsNone hWaiterReady)

-- ============================================================================
-- WS-RR RR7.4: observer atomicity for the notification pair
--
-- Register §4 finding 7: `notificationSignalOnCore_atomic_under_lockSet` and
-- its `wait` companion are `rfl` instances of the body-agnostic
-- `lockSet_atomic_under_2pl`, which is true of *any* action — the substantive
-- observer form had been instantiated only for the cancellation.  These are
-- the notification half of the five that were missing: under each
-- transition's declared footprint, the whole 2PL bracket is invisible to the
-- rendezvous's own observable.  **WS-LS LS2.1**: stated over the pair; the
-- bracket's phases write the lock half only, so each is `lockSet_observer_atomic`
-- with no `invExt` guard.
-- ============================================================================

/-- **WS-RR RR7.4** (**WS-LS LS2.1**: over the pair, hypothesis-free): under its
declared footprint the cross-core notification signal is observationally atomic
— the bracketed run shows the notification's delivery state exactly as the
transition's own effect leaves it.  No partially-locked intermediate is ever
observable.

Stated for **every** notification, not only the signalled one: the lock
machinery writes the lock table and nothing else, so a caller watching a
different notification sees no more than a caller watching this one.  The
`invExt` hypothesis and the acquire-fold conjunct (the observer unchanged by
the growing phase) are dropped because the growing phase no longer touches the
kernel state — a strengthening (plan O6). -/
theorem notificationSignalOnCore_observer_atomic
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (signaller : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) (observed : SeLe4n.ObjId)
    (s : LockedSystemState) :
    notificationDeliveryObserver observed
        (withLockSet (lockSet_notificationSignal signaller cnRoot notificationId waiter?)
          executingCore (notificationSignalOnCore notificationId badge executingCore) s).1.kernel
      = notificationDeliveryObserver observed
          (notificationSignalOnCore notificationId badge executingCore s.kernel).1 :=
  lockSet_observer_atomic _ executingCore _ s _

/-- **WS-RR RR7.4**: and the wait companion, over the pair as above. -/
theorem notificationWaitOnCore_observer_atomic
    (notificationId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (executingCore : CoreId)
    (cnRoot : SeLe4n.ObjId) (observed : SeLe4n.ObjId)
    (s : LockedSystemState) :
    notificationDeliveryObserver observed
        (withLockSet (lockSet_notificationWaitOnCore s.kernel notificationId caller cnRoot)
          executingCore (notificationWaitOnCore notificationId caller executingCore) s).1.kernel
      = notificationDeliveryObserver observed
          (notificationWaitOnCore notificationId caller executingCore s.kernel).1 :=
  lockSet_observer_atomic _ executingCore _ s _

/-- **WS-RR RR7.4**: the waiter's own IPC state is equally unexposed by the
`wait` bracket — the participant-side observable, beside the object-side one;
over the pair as above. -/
theorem notificationWaitOnCore_thread_observer_atomic
    (notificationId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (executingCore : CoreId)
    (cnRoot : SeLe4n.ObjId) (observed : SeLe4n.ThreadId)
    (s : LockedSystemState) :
    threadIpcStateObserver observed
        (withLockSet (lockSet_notificationWaitOnCore s.kernel notificationId caller cnRoot)
          executingCore (notificationWaitOnCore notificationId caller executingCore) s).1.kernel
      = threadIpcStateObserver observed
          (notificationWaitOnCore notificationId caller executingCore s.kernel).1 :=
  lockSet_observer_atomic _ executingCore _ s _


end SeLe4n.Kernel
