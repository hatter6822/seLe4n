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
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

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
`objects[·]?`), so the cross-core receiver wake (`wakeThread`, object-invisible
on the already-`.ready` waiter — the §2 keystone of `EndpointCallInvariant`) and
the per-core deschedule (`removeRunnableOnCore`, an object-store frame) cannot
disturb it.  The notification-store / TCB-store steps reuse the single-core
per-step preservation lemmas verbatim.

**WS-SM SM6.D closure** (§3–§6): the cross-core transitions preserve the
**whole twenty-conjunct bundle** and every core's per-core view of it —
`notificationSignalOnCore_preserves_ipcInvariantFull{,_perCore}` /
`notificationWaitOnCore_preserves_ipcInvariantFull{,_perCore}`.  The proof
lever is the off-scheduler agreement dichotomy (§4): a cross-core transition
either fails (post-state = pre-state) or runs the *same* object-store spine as
its single-core counterpart and diverges only in the final scheduler placement
(`wakeThread`/`removeRunnableOnCore` for `ensureRunnable`/`removeRunnable`) —
so the single-core whole-bundle theorem carries across the
`OffSchedulerAgrees` relation via the lookup congruences
(`IPC/Invariant/LookupCongruence.lean`), and the one scheduler-reading
conjunct (`passiveServerIdle`) rides the §3 per-core frames.
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

-- ============================================================================
-- §3  SM6.D: per-core passive-server frames for the cross-core transitions
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `notificationSignalOnCore` frames every core's
`passiveServerIdle` slice, unconditionally over success/failure (error paths
return the pre-state).  The head waiter is woken `.ready` (an allowed passive
state) and its cross-core wake only *adds* it to its home core's run queue;
the no-waiter branch only rewrites the notification object. -/
theorem notificationSignalOnCore_passiveServerIdleFrameOnCore
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (notificationSignalOnCore notificationId badge executingCore st).1 c := by
  unfold notificationSignalOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact passiveServerIdleFrameOnCore.refl st
  | some ntfn =>
    simp only
    cases hWaiters : ntfn.waitingThreads.tail? with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok pair =>
        simp only
        exact storeObject_oldNonTcb_passiveServerIdleFrameOnCore st pair.2
          notificationId (.notification _) (fun _ => by simp) hObjInv hStore
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok pair =>
        simp only
        have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c) st pair.2
          notificationId (.notification _) (fun _ => by simp) hObjInv hStore
        have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
        | ok st2 =>
          simp only
          have hF2 := storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore (c := c) pair.2 st2
            waiter .ready _ (Or.inl (Or.inl rfl)) hObjInv1 hTcb
          have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st2 waiter _ _
            hObjInv1 hTcb
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2 st2 waiter .ready _ hObjInv1 hTcb
          show passiveServerIdleFrameOnCore st (wakeThread st2 waiter executingCore).1 c
          exact (hF1.trans hF2).trans
            (wakeThread_passiveServerIdleFrameOnCore_of_ready st2 waiter executingCore tr
              hTrGet hTrReady hObjInv2)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `notificationWaitOnCore` frames every core's
`passiveServerIdle` slice, unconditionally over success/failure.  The deliver
branch wakes the waiter `.ready`; the block branch sets it
`.blockedOnNotification` (both allowed passive states) and deschedules it on
its own core — the per-core dequeue's pullback filter excludes exactly that
thread. -/
theorem notificationWaitOnCore_passiveServerIdleFrameOnCore
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (notificationWaitOnCore notificationId waiter executingCore st).1 c := by
  unfold notificationWaitOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact passiveServerIdleFrameOnCore.refl st
  | some ntfn =>
    simp only
    cases hBadge : ntfn.pendingBadge with
    | some badge =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok pair =>
        simp only
        have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c) st pair.2
          notificationId (.notification _) (fun _ => by simp) hObjInv hStore
        have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcState pair.2 waiter .ready with
        | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
        | ok st2 =>
          simp only
          exact hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore (c := c) pair.2 st2
            waiter .ready (Or.inl (Or.inl rfl)) hObjInv1 hTcb)
    | none =>
      simp only
      cases hLk : lookupTcb st waiter with
      | none => simp only; exact passiveServerIdleFrameOnCore.refl st
      | some tcb =>
        simp only
        split
        · exact passiveServerIdleFrameOnCore.refl st
        · cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
          | none => simp only; exact passiveServerIdleFrameOnCore.refl st
          | some wt' =>
            simp only
            cases hStore : storeObject notificationId _ st with
            | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
            | ok pair =>
              simp only
              have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c) st pair.2
                notificationId (.notification _) (fun _ => by simp) hObjInv hStore
              have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              have hObjRaw : st.objects[notificationId]? = some (.notification ntfn) :=
                (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hObjN
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObjRaw hObjInv hStore
              cases hTcb : storeTcbIpcState_fromTcb pair.2 waiter tcb
                  (.blockedOnNotification notificationId) with
              | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
              | ok st2 =>
                simp only
                rw [storeTcbIpcState_fromTcb_eq hLk'] at hTcb
                show passiveServerIdleFrameOnCore st (removeRunnableOnCore st2 waiter executingCore) c
                refine (hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore (c := c) pair.2 st2
                    waiter (.blockedOnNotification notificationId)
                    (Or.inl (Or.inr (Or.inl ⟨notificationId, Or.inr rfl⟩))) hObjInv1 hTcb)).trans
                  (removeRunnableOnCore_passiveServerIdleFrameOnCore st2 waiter executingCore
                    (fun tcb' hTcb' => Or.inr ?_))
                rw [storeTcbIpcState_ipcState_eq pair.2 st2 waiter _ hObjInv1 hTcb tcb'
                  ((getTcb?_eq_some_iff st2 waiter tcb').mp hTcb')]
                exact Or.inr (Or.inl ⟨notificationId, Or.inr rfl⟩)

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
    cases hWaiters : ntfn.waitingThreads.tail? with
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
          unfold notificationSignal
          simp only [hObjRaw, hWaiters, hPB, hStore]
      | none =>
        simp only
        cases hStore : storeObject notificationId _ st with
        | error e => left; rfl
        | ok pair =>
          right
          simp only
          refine ⟨pair.2, ?_, OffSchedulerAgrees.refl pair.2⟩
          unfold notificationSignal
          simp only [hObjRaw, hWaiters, hPB, hStore]
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
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
          refine ⟨ensureRunnable st2 waiter, ?_, ?_⟩
          · unfold notificationSignal
            simp only [hObjRaw, hWaiters, hStore, hTcb]
          · exact (ensureRunnable_offSchedulerAgrees st2 waiter).symm.trans
              (wakeThread_offSchedulerAgrees_of_ready st2 waiter executingCore tr hTrGet
                hTrReady hObjInv2)

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
    (st : SystemState) :
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
          unfold notificationWait
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
          cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
          | none => left; rfl
          | some wt' =>
            simp only
            cases hStore : storeObject notificationId _ st with
            | error e => left; rfl
            | ok pair =>
              simp only
              cases hTcb : storeTcbIpcState_fromTcb pair.2 waiter tcb
                  (.blockedOnNotification notificationId) with
              | error e => left; rfl
              | ok st2 =>
                right
                simp only
                refine ⟨removeRunnable st2 waiter, none, ?_, ?_⟩
                · unfold notificationWait
                  simp only [hObjRaw, hBadge, hLk, if_neg hIpcNe, hCons, hStore, hTcb]
                · exact (removeRunnable_offSchedulerAgrees st2 waiter).symm.trans
                    (removeRunnableOnCore_offSchedulerAgrees st2 waiter executingCore)

-- ============================================================================
-- §5  SM6.D: whole-bundle `ipcInvariantFull` preservation (cross-core)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.B closure): the cross-core notification signal preserves
the **whole twenty-conjunct bundle**, unconditionally over success/failure
(error paths return the pre-state).  Nineteen lookup-only conjuncts ride the
single-core whole-bundle theorem across the §4 agreement dichotomy; the
scheduler-reading `passiveServerIdle` rides the §3 per-core frame at the boot
core.  Hypotheses mirror `notificationSignal_preserves_ipcInvariantFull`, with
the threaded post-state facts stated at the cross-core post-state. -/
theorem notificationSignalOnCore_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (notificationSignalOnCore notificationId badge executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (notificationSignalOnCore notificationId badge executingCore st).1)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull (notificationSignalOnCore notificationId badge executingCore st).1 := by
  have hPsi' : passiveServerIdle (notificationSignalOnCore notificationId badge executingCore st).1 :=
    (passiveServerIdle_perCore_bootCore_iff _).mp
      (passiveServerIdle_perCore_of_frameOnCore
        (notificationSignalOnCore_passiveServerIdleFrameOnCore notificationId badge executingCore
          st bootCoreId hObjInv)
        ((passiveServerIdle_perCore_bootCore_iff st).mpr hInv.passiveServerIdle))
  rcases notificationSignalOnCore_post_agrees notificationId badge executingCore st hObjInv with
    hPre | ⟨r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_getElem_eq hAgree.objects hPsi'
      (notificationSignal_preserves_ipcInvariantFull st r1 notificationId badge hInv hObjInv
        (waitingThreadsPendingMessageNone_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hWtpmn')
        (replyCallerLinkageReciprocal_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hRCLRecip')
        hNWC hAllBudgetsNone hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.B closure): the cross-core notification wait preserves
the **whole twenty-conjunct bundle**, unconditionally over success/failure.
Hypotheses mirror `notificationWait_preserves_ipcInvariantFull`, with TCB
lookups routed through the typed `getTcb?` and the threaded post-state facts
stated at the cross-core post-state. -/
theorem notificationWaitOnCore_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (notificationWaitOnCore notificationId waiter executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (notificationWaitOnCore notificationId waiter executingCore st).1)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull (notificationWaitOnCore notificationId waiter executingCore st).1 := by
  have hPsi' : passiveServerIdle (notificationWaitOnCore notificationId waiter executingCore st).1 :=
    (passiveServerIdle_perCore_bootCore_iff _).mp
      (passiveServerIdle_perCore_of_frameOnCore
        (notificationWaitOnCore_passiveServerIdleFrameOnCore notificationId waiter executingCore
          st bootCoreId hObjInv)
        ((passiveServerIdle_perCore_bootCore_iff st).mpr hInv.passiveServerIdle))
  rcases notificationWaitOnCore_post_agrees notificationId waiter executingCore st with
    hPre | ⟨r1, result, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_getElem_eq hAgree.objects hPsi'
      (notificationWait_preserves_ipcInvariantFull st r1 notificationId waiter result hInv hObjInv
        (waitingThreadsPendingMessageNone_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hWtpmn')
        (replyCallerLinkageReciprocal_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hRCLRecip')
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
    (hWtpmn' : waitingThreadsPendingMessageNone
      (notificationSignalOnCore notificationId badge executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (notificationSignalOnCore notificationId badge executingCore st).1)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (c : CoreId) :
    ipcInvariantFull_perCore (notificationSignalOnCore notificationId badge executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (notificationSignalOnCore_preserves_ipcInvariantFull notificationId badge executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip' hNWC hAllBudgetsNone)
    (passiveServerIdle_perCore_of_frameOnCore
      (notificationSignalOnCore_passiveServerIdleFrameOnCore notificationId badge executingCore
        st c hObjInv)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core wait): `notificationWaitOnCore` preserves
**every core's** view of the IPC invariant bundle.  No idle-core
assumption. -/
theorem notificationWaitOnCore_preserves_ipcInvariantFull_perCore
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (notificationWaitOnCore notificationId waiter executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (notificationWaitOnCore notificationId waiter executingCore st).1)
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
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip' hWaiterNotRecv hWaiterNotReply
      hAllBudgetsNone hWaiterReady)
    (passiveServerIdle_perCore_of_frameOnCore
      (notificationWaitOnCore_passiveServerIdleFrameOnCore notificationId waiter executingCore
        st c hObjInv)
      (hInv c).passiveServerIdle)

end SeLe4n.Kernel
