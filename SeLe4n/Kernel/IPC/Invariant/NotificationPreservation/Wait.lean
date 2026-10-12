-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.IPC.Invariant.WaitingThreadHelpers
import SeLe4n.Kernel.IPC.Invariant.NotificationQueue

import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation.Signal

/-! # Notification Preservation — Badge, Waiter & Pending (AN3-D)

Extracted from `NotificationPreservation.lean` as part of AN3-D
(IPC-M03 / Theme 4.7).  Contains preservation theorems for
`badgeWellFormed`, `notificationWaiterConsistent`,
`blockedThreadsPendingMessageConsistent` covering both
`notificationSignal` / `notificationWait` and their frame
lemmas.  Declarations are unchanged in order, content, and
proof; only the file boundary has moved.
-/


namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-F5/D1d: Badge well-formedness preservation
-- ============================================================================

/-- WS-F5/D1d: Storing a notification with a valid (or absent) pending badge
preserves `notificationBadgesWellFormed`. -/
theorem storeObject_notification_preserves_notificationBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (ntfn' : Notification)
    (hInv : notificationBadgesWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId (.notification ntfn') st = .ok ((), st'))
    (hValid : ∀ b, ntfn'.pendingBadge = some b → b.valid) :
    notificationBadgesWellFormed st' := by
  intro oid ntfn b hObj hPending
  by_cases hEq : oid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj
    cases hObj; exact hValid b hPending
  · exact hInv oid ntfn b ((storeObject_objects_ne st st' targetId oid _ hEq hObjInv hStore).symm.trans hObj) hPending

/-- WS-F5/D1d: Storing a non-notification object preserves `notificationBadgesWellFormed`. -/
theorem storeObject_nonNotification_preserves_notificationBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : notificationBadgesWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId obj st = .ok ((), st'))
    (hNotNtfn : ∀ ntfn, obj ≠ .notification ntfn) :
    notificationBadgesWellFormed st' := by
  intro oid ntfn b hObj hPending
  by_cases hEq : oid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' oid obj hObjInv hStore] at hObj
    have := Option.some.inj hObj
    cases obj with
    | notification n => exact absurd rfl (hNotNtfn n)
    | _ => cases this
  · exact hInv oid ntfn b ((storeObject_objects_ne st st' targetId oid obj hEq hObjInv hStore).symm.trans hObj) hPending

/-- WS-F5/D1d: Storing a non-CNode object preserves `capabilityBadgesWellFormed`. -/
theorem storeObject_nonCNode_preserves_capabilityBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : capabilityBadgesWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    capabilityBadgesWellFormed st' := by
  intro oid cn slot cap badge hObj hLookup hBadge
  by_cases hEq : oid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' oid obj hObjInv hStore] at hObj
    have := Option.some.inj hObj
    cases obj with
    | cnode c => exact absurd rfl (hNotCNode c)
    | _ => cases this
  · exact hInv oid cn slot cap badge ((storeObject_objects_ne st st' targetId oid obj hEq hObjInv hStore).symm.trans hObj) hLookup hBadge

/-- WS-F5/D1d: `ensureRunnable` preserves `badgeWellFormed`.
It writes only the scheduler and run-queue links; badges live in notifications
and CNodes. -/
theorem ensureRunnable_preserves_badgeWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : badgeWellFormed st) :
    badgeWellFormed (ensureRunnable st tid) :=
  have h := ensureRunnable_objectsAgreeOffRunLinks st tid
  ⟨fun oid ntfn badge hN => hInv.1 oid ntfn badge (h.get_notification_iff.mp hN),
   fun oid cn slot cap badge hC => hInv.2 oid cn slot cap badge (h.get_cnode_iff.mp hC)⟩

/-- WS-F5/D1d: `removeRunnable` preserves `badgeWellFormed`.
Only modifies `scheduler`, never the object store. -/
theorem removeRunnable_preserves_badgeWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : badgeWellFormed st) :
    badgeWellFormed (removeRunnable st tid) := hInv

/-- **Audit IPC-5 (`v0.36.49`)**: any TCB field write preserves
`badgeWellFormed` — it stores a `.tcb`, which is neither a notification nor a
CNode.  The five writer lemmas below are instances. -/
theorem modifyTcb_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : modifyTcb st tid f = .ok st') :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  obtain ⟨_, _, hStore⟩ := modifyTcb_ok_decompose hStep
  exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
           st st' tid.toObjId _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
         storeObject_nonCNode_preserves_capabilityBadgesWellFormed
           st st' tid.toObjId _ hCap hObjInv hStore (fun cn h => by cases h)⟩

/-- WS-F5/D1d: `storeTcbIpcState` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbIpcState_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st') :
    badgeWellFormed st' :=
  modifyTcb_preserves_badgeWellFormed st st' tid _ hInv hObjInv hStep

/-- R3-A: `storeTcbIpcStateAndMessage` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbIpcStateAndMessage_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (msg : Option IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    badgeWellFormed st' :=
  modifyTcb_preserves_badgeWellFormed st st' tid _ hInv hObjInv hStep

/-- Finding F-1: `storeTcbReceiveComplete` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode).  Mirror of
`storeTcbIpcStateAndMessage_preserves_badgeWellFormed`. -/
theorem storeTcbReceiveComplete_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    badgeWellFormed st' :=
  modifyTcb_preserves_badgeWellFormed st st' tid _ hInv hObjInv hStep

/-- U4-K: `storeTcbQueueLinks` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbQueueLinks_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    badgeWellFormed st' :=
  modifyTcb_preserves_badgeWellFormed st st' tid _ hInv hObjInv hStep

/-- U4-K: `storeTcbPendingMessage` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbPendingMessage_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    badgeWellFormed st' :=
  modifyTcb_preserves_badgeWellFormed st st' tid _ hInv hObjInv hStep

/-- U4-K: Storing an endpoint preserves `badgeWellFormed`.
Endpoints are neither notifications nor CNodes. -/
theorem storeObject_endpoint_preserves_badgeWellFormed
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
           st st' oid _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
         storeObject_nonCNode_preserves_capabilityBadgesWellFormed
           st st' oid _ hCap hObjInv hStore (fun cn h => by cases h)⟩

/-- WS-F5/D1d: `notificationSignal` preserves `badgeWellFormed`.
Wake path: stores `hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero`. Merge path: stores `Badge.bor` or
`Badge.ofNatMasked` — both word-bounded. -/
theorem notificationSignal_preserves_badgeWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold notificationSignal SystemState.getObject? at hStep
  cases hObjSrc : st.objects[notificationId]? with
  | none => simp [hObjSrc] at hStep
  | some obj =>
    cases obj with
    | notification ntfnSrc =>
      simp only [hObjSrc] at hStep
      -- WS-ZA ZA4.4: signal wakes the queue head.
      cases hWaiters : ntfnSrc.waitHead with
      | some waiter =>
        simp only [hWaiters] at hStep; revert hStep
        cases hStore1 : storeObject notificationId _ st with
        | error e => simp
        | ok pair1 =>
          simp only []; intro hStep; revert hStep
          -- R3-A/M-16: storeTcbIpcStateAndMessage replaces storeTcbIpcState
          cases hStoreTcb : storeTcbIpcStateAndMessage pair1.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st2 => simp only []; intro hEq; cases hEq
                      apply ensureRunnable_preserves_badgeWellFormed
                      have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                      exact storeTcbIpcStateAndMessage_preserves_badgeWellFormed pair1.2 st2 waiter .ready _
                        ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                          st pair1.2 notificationId _ hNtfn hObjInv hStore1 (fun b hb => by cases hb),
                         storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                          st pair1.2 notificationId _ hCap hObjInv hStore1 (fun cn h => by cases h)⟩
                        hObjInv1 hStoreTcb
      | none =>
        simp only [hWaiters] at hStep
        exact ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                 st st' notificationId _ hNtfn hObjInv hStep
                 (fun b hb => by
                   simp only [Notification.pendingBadge_mk_true, Option.some.injEq] at hb; subst hb
                   cases hPending : ntfnSrc.pendingBadge with
                   | some existing => exact SeLe4n.Badge.bor_valid existing badge
                   | none => exact SeLe4n.Badge.ofNatMasked_valid badge.toNat),
               storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                 st st' notificationId _ hCap hObjInv hStep (fun cn h => by cases h)⟩
    | _ => simp [hObjSrc] at hStep

/-- WS-F5/D1d: `notificationWait` preserves `badgeWellFormed`.
Consume path: stores `hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero`. Block path: stores notification
with waiter prepended (badges unchanged). -/
theorem notificationWaitPark_preserves_badgeWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge) (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWaitPark notificationId waiter st = .ok (result, st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold notificationWaitPark SystemState.getObject? at hStep
  cases hObjSrc : st.objects[notificationId]? with
  | none => simp [hObjSrc] at hStep
  | some obj =>
    cases obj with
    | notification ntfnSrc =>
      simp only [hObjSrc] at hStep
      cases hPending : ntfnSrc.pendingBadge with
      | some pendBadge =>
        simp only [hPending] at hStep; revert hStep
        cases hStore1 : storeObject notificationId _ st with
        | error e => simp
        | ok pair1 => simp only []; intro hStep; revert hStep
                      cases hStoreTcb : storeTcbIpcState pair1.2 waiter .ready with
                      | error e => simp
                      | ok st2 => simp only [Except.ok.injEq, Prod.mk.injEq]
                                  intro ⟨_, hEq⟩; subst hEq
                                  have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                                  exact storeTcbIpcState_preserves_badgeWellFormed pair1.2 st2 waiter .ready
                                    ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                                      st pair1.2 notificationId _ hNtfn hObjInv hStore1 (fun b hb => by cases hb),
                                     storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                                      st pair1.2 notificationId _ hCap hObjInv hStore1 (fun cn h => by cases h)⟩
                                    hObjInv1 hStoreTcb
      | none =>
        simp only [hPending] at hStep; revert hStep
        cases hLk : lookupTcb st waiter with
        | none => simp
        | some tcb =>
          simp only []; split
          · simp
          · intro hStep; revert hStep
            cases hStore1 : storeObject notificationId _ st with
            | error e => simp
            | ok pair1 =>
              simp only []
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObjSrc hObjInv hStore1
              simp only [storeTcbIpcStateAndMessage_fromTcb_eq hLk']
              intro hStep; revert hStep
              cases hStoreTcb : storeTcbIpcStateAndMessage pair1.2 waiter _ _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                apply removeRunnable_preserves_badgeWellFormed
                have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                exact storeTcbIpcStateAndMessage_preserves_badgeWellFormed pair1.2 st2 waiter _ _
                  ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                    st pair1.2 notificationId _ hNtfn hObjInv hStore1
                    (fun b hb => by cases hb),
                   storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                    st pair1.2 notificationId _ hCap hObjInv hStore1 (fun cn h => by cases h)⟩
                  hObjInv1 hStoreTcb
    | _ => simp [hObjSrc] at hStep

-- ============================================================================
-- notificationWaiterConsistent preservation
-- ============================================================================
--
-- WS-ZA ZA4.4: the queue is linked through its waiters' TCBs, so each step is
-- discharged by the `NotificationQueue` theorem for the shape it writes.

/-- A TCB's IPC state and message written at a thread blocked on no
notification, to a state that is not a notification block: the queues are
untouched. -/
theorem storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hPre : ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) →
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hIpc : ∀ oid, ipc ≠ .blockedOnNotification oid) :
    notificationWaiterConsistent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  obtain ⟨tcb, _, hT0, hT1, hO⟩ := modifyTcb_objects hObjInv hStep
  exact notificationWaiterConsistent_of_unblocked_tcb_write hConsist
    ⟨tcb, hT0, hPre tcb hT0⟩ ⟨_, hT1, hIpc⟩ hO

/-- `notificationSignal` keeps the queues consistent: the wake pops the head
and makes it ready; the merge rewrites a notification whose queue is empty. -/
theorem notificationSignal_preserves_notificationWaiterConsistent
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    notificationWaiterConsistent st' := by
  unfold notificationSignal SystemState.getObject? at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ | reply _
    | frame _ | pageTable _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitHead with
      | some waiter =>
        simp only [hWaiters] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification (ntfn.withHeadPopped (ntfnSuccessor? st waiter))) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEqSt⟩; subst hEqSt
            obtain ⟨htcb, hHT, _⟩ := (hConsist.1 notificationId ntfn hObj).2.1 waiter hWaiters
            have hObjInv1 :=
              storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
            unfold storeTcbIpcStateAndMessage at hTcb
            obtain ⟨t1, hLk1, _, hT1, hO1⟩ := modifyTcb_objects hObjInv1 hTcb
            have hSucc : ntfnSuccessor? st waiter = htcb.ntfnNext := by
              unfold ntfnSuccessor?
              rw [lookupTcb_of_objects_of_not_reserved st waiter htcb hHT
                (lookupTcb_some_not_reserved _ _ _ hLk1)]
            have hNW : notificationId ≠ waiter.toObjId := by
              intro e; rw [e, hHT] at hObj; cases hObj
            refine notificationWaiterConsistent_of_objectsAgreeOffRunLinks
              (ensureRunnable_objectsAgreeOffRunLinks _ _)
              (notificationWaiterConsistent_of_headPop hConsist hObj hWaiters hHT ?_ ?_ ?_)
            · rw [hO1 _ hNW, ← hSucc]
              exact storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore
            · exact ⟨_, hT1, fun oid h => by cases h⟩
            · intro x hx hxw
              rw [hO1 _ hxw]
              exact storeObject_objects_ne st pair.2 notificationId x _ hx hObjInv hStore
      | none =>
        simp only [hWaiters] at hStep
        have hTailNone : ntfn.waitTail = none :=
          (hConsist.1 notificationId ntfn hObj).1.mp hWaiters
        exact notificationWaiterConsistent_of_queueEnds_write hConsist hObj
          (storeObject_objects_eq st st' notificationId _ hObjInv hStep)
          (by rw [hWaiters]; rfl) (by rw [hTailNone]; rfl)
          (fun x hx => storeObject_objects_ne st st' notificationId x _ hx hObjInv hStep)

/-- `notificationWait` keeps the queues consistent, for a waiter blocked on no
notification (a running thread is `.ready`).  Consuming a badge rewrites a
notification whose queue is empty (a pending badge means no waiters) and makes
the waiter ready; blocking appends the waiter at the tail and links it behind
the old tail. -/
theorem notificationWait_preserves_notificationWaiterConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (r : Option SeLe4n.Badge)
    (hConsist : notificationWaiterConsistent st)
    (hIpcInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hWaiterNB : ∀ tcb, st.objects[waiter.toObjId]? = some (.tcb tcb) →
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hStep : notificationWait notificationId waiter st = .ok (r, st')) :
    notificationWaiterConsistent st' := by
  rcases notificationWait_ok_cases hStep with ⟨b, _, hP⟩ | ⟨_, stP, hP, hL⟩
  · obtain ⟨ntfn, n', tcb, st1, hN, hB, hH', hT', hW, hN1, hO1, hPW, hO⟩ :=
      notificationWaitPark_badge_objects hObjInv hP
    have hHead := notificationQueueWellFormed_waitHead_of_pendingBadge
      (hIpcInv notificationId ntfn hN) hB
    have hTail : ntfn.waitTail = none := (hConsist.1 notificationId ntfn hN).1.mp hHead
    have hNW : notificationId ≠ waiter.toObjId := by intro e; rw [e, hW] at hN; cases hN
    have h1 : notificationWaiterConsistent st1 :=
      notificationWaiterConsistent_of_queueEnds_write hConsist hN hN1
        (hH'.trans hHead.symm) (hT'.trans hTail.symm) hO1
    exact notificationWaiterConsistent_of_unblocked_tcb_write h1
      ⟨tcb, by rw [hO1 _ (Ne.symm hNW)]; exact hW, hWaiterNB tcb hW⟩
      ⟨_, hPW, fun oid h => by cases h⟩ hO
  · obtain ⟨ntfn, tcb, hN, hB, hLk, _, hPN, hPW, hPO⟩ :=
      notificationWaitPark_block_objects hObjInv hP
    have hW0 := lookupTcb_some_objects st waiter tcb hLk
    have hWNB := hWaiterNB tcb hW0
    rw [notificationWaitTail?_of_objects hN hB] at hL
    obtain ⟨_, _, hTailC⟩ := hConsist.1 notificationId ntfn hN
    have hTailNe : ∀ t, ntfn.waitTail = some t → t ≠ waiter := by
      intro t ht e; subst e
      obtain ⟨tt, hTt, hBt, _⟩ := hTailC t ht
      rw [hW0] at hTt; cases hTt; exact hWNB _ hBt
    have hInvP := notificationWaitPark_preserves_objects_invExt hObjInv hP
    obtain ⟨⟨tw, hTwP, hTwF⟩, hTailF, hO⟩ := linkNtfnWaiter_objects hInvP hL hTailNe
    rw [hPW] at hTwP; cases hTwP
    have hNW : notificationId ≠ waiter.toObjId := by intro e; rw [e, hW0] at hN; cases hN
    have hNT : ∀ t, ntfn.waitTail = some t → notificationId ≠ t.toObjId := by
      intro t ht e; obtain ⟨tt, hTt, _⟩ := hTailC t ht; rw [← e, hN] at hTt; cases hTt
    refine notificationWaiterConsistent_of_append hConsist hN hW0 hWNB ?_ ?_ ?_ ?_
    · rw [hO _ hNW hNT]; exact hPN
    · exact ⟨_, hTwF, rfl, by simp, by simp⟩
    · intro t ttcb ht hTt
      obtain ⟨tt, hTtP, hTtF⟩ := hTailF t ht
      have htw : t.toObjId ≠ waiter.toObjId := fun e =>
        hTailNe t ht (SeLe4n.ThreadId.toObjId_injective _ _ e)
      have htn : t.toObjId ≠ notificationId := by intro e; rw [e, hN] at hTt; cases hTt
      rw [hPO _ htn htw, hTt] at hTtP; cases hTtP
      exact ⟨_, hTtF, rfl, rfl, by simp⟩
    · intro x hxn hxw hxt
      rw [hO x hxw hxt, hPO x hxn hxw]

-- ============================================================================
-- V3-G2/G3 (M-PRF-5): blockedThreadsPendingMessageConsistent preservation
-- for notification operations
-- ============================================================================
--
-- These theorems were previously located in Structural.lean due to a circular
-- import (Structural imports NotificationPreservation). The primitive helpers
-- they depend on now live in WaitingThreadHelpers.lean, which both files can
-- import, enabling these proofs to live in their semantic home.

/-- V3-I (L-IPC-1): Before `notificationSignal` delivers a badge to a waiting
    thread, the waiter's `pendingMessage` was `none`. Direct extraction from the
    `blockedThreadsPendingMessageConsistent` invariant: any thread with
    `ipcState = .blockedOnNotification _` has `pendingMessage = none`. -/
theorem notificationWake_pendingMessage_was_none
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (nid : SeLe4n.ObjId)
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hLookup : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hBlocked : tcb.ipcState = .blockedOnNotification nid) :
    tcb.pendingMessage = none := by
  have h := hInv tid tcb hLookup
  rw [hBlocked] at h
  exact h

/-- V3-G3 (M-PRF-5): `notificationSignal` preserves `blockedThreadsPendingMessageConsistent`.
    Wake path: sets `.ready` (out of scope). Merge path: non-TCB store only. -/
theorem notificationSignal_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    blockedThreadsPendingMessageConsistent st' := by
  simp only [notificationSignal, SystemState.getObject?] at hStep
  split at hStep
  · -- some (.notification ntfn)
    rename_i ntfn hObj
    -- WS-ZA ZA4.4: signal wakes the queue head.
    cases hWaiters : ntfn.waitHead with
    | some waiter =>
      -- Wake path: storeObject → storeTcbIpcStateAndMessage (.ready) → ensureRunnable
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction  -- storeObject error
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction  -- storeTcbIpcStateAndMessage error
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInv2 := storeTcbIpcStateAndMessage_preserves_blockedThreadsPendingMessageConsistent
            st1 st2 waiter .ready _ hObjInv1 hSM hInv1 (by trivial)
          exact ensureRunnable_preserves_blockedThreadsPendingMessageConsistent st2 waiter hInv2
    | none =>
      -- Merge path: storeObject only
      simp only [hWaiters] at hStep
      -- pendingBadge match produces two sub-cases, both are storeObject
      split at hStep
      all_goals (
        exact storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent
          st st' notificationId (.notification _) (fun tcb => by simp) hObjInv hStep hInv)
  · contradiction
  · contradiction

/-- V3-G2 (M-PRF-5): `notificationWait` preserves `blockedThreadsPendingMessageConsistent`.
    Deliver path: `storeTcbIpcState` to `.ready` exits scope.
    Block path: `storeTcbIpcStateAndMessage_fromTcb` to `.blockedOnNotification`
    with `pendingMessage := none` + `removeRunnable`.

    **WS-RR RR3.5**: this used to take `hWaiterMsg`, a precondition that the
    waiter holds no pending message, and nothing established it — a thread that
    has just collected a message stays `.ready` holding it, so the hypothesis is
    FALSE in reachable states and the `ipcInvariantFull` bundles threaded the
    conjunct as a post-state hypothesis rather than discharging it.  The
    transition now clears `pendingMessage` atomically with the block, exactly as
    `endpointReceiveDual` already did, so the block path establishes the conjunct
    outright and the precondition is gone. -/
theorem notificationWaitPark_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hStep : notificationWaitPark notificationId waiter st = .ok (badge, st')) :
    blockedThreadsPendingMessageConsistent st' := by
  simp only [notificationWaitPark, SystemState.getObject?] at hStep
  split at hStep
  · -- some (.notification ntfn)
    rename_i ntfn hObj
    split at hStep
    · -- Deliver path: pendingBadge = some badge
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_preserves_blockedThreadsPendingMessageConsistent
            st1 st2 waiter .ready hObjInv1 hSI hInv1 (fun _ _ => trivial)
    · -- Block path: pendingBadge = none
      split at hStep
      · contradiction -- lookupTcb = none
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction -- already waiting
        · split at hStep
          next => contradiction -- storeObject error
          next st1 hSO =>
          have hInv1 := storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent
            st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
          have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
          -- Split on storeTcbIpcState_fromTcb result
          split at hStep
          next => contradiction -- storeTcbIpcState_fromTcb error
          next st2 hSI =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            apply removeRunnable_preserves_blockedThreadsPendingMessageConsistent
            -- Unfold the atomic block store to extract the underlying storeObject
            simp only [storeTcbIpcStateAndMessage_fromTcb] at hSI
            split at hSI
            next => contradiction -- storeObject error
            next pair hSO2 =>
              simp only [Except.ok.injEq] at hSI
              -- hSI : pair = st2, pair : Unit × SystemState
              subst hSI
              -- Goal is now about pair.2
              intro tid' tcb' hObj'
              by_cases hTidEq : tid'.toObjId = waiter.toObjId
              · -- Same thread: the stored TCB is `.blockedOnNotification` with
                -- `pendingMessage := none` — the conjunct's obligation for that
                -- state, discharged by the store itself (WS-RR RR3.5).
                have hSelf := storeObject_objects_eq st1 pair waiter.toObjId _ hObjInv1 hSO2
                rw [hTidEq] at hObj'; rw [hSelf] at hObj'
                simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObj'; subst hObj'
                dsimp only []
              · -- Different thread: frame
                have hFrame := storeObject_objects_ne st1 pair waiter.toObjId tid'.toObjId
                  _ hTidEq hObjInv1 hSO2
                rw [hFrame] at hObj'
                exact hInv1 tid' tcb' hObj'
  · contradiction
  · contradiction

end SeLe4n.Kernel
