/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.IPC.Invariant.WaitingThreadHelpers

import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation.Signal

/-! # Notification Preservation — Badge, Waiter & Pending (AN3-D)

Extracted from `NotificationPreservation.lean` as part of AN3-D
(IPC-M03 / Theme 4.7).  Contains preservation theorems for
`badgeWellFormed`, `notificationWaiterConsistent`,
`waitingThreadsPendingMessageNone` covering both
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
Only modifies `scheduler.runQueue`, never the object store. -/
theorem ensureRunnable_preserves_badgeWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : badgeWellFormed st) :
    badgeWellFormed (ensureRunnable st tid) := by
  unfold ensureRunnable; split
  · exact hInv
  · split <;> exact hInv

/-- WS-F5/D1d: `removeRunnable` preserves `badgeWellFormed`.
Only modifies `scheduler`, never the object store. -/
theorem removeRunnable_preserves_badgeWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : badgeWellFormed st) :
    badgeWellFormed (removeRunnable st tid) := hInv

/-- WS-F5/D1d: `storeTcbIpcState` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbIpcState_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st') :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold storeTcbIpcState at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep; revert hStep
    cases hStore : storeObject tid.toObjId _ st with
    | error e => simp
    | ok pair => simp only []; intro hEq; cases hEq
                 exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
                           st pair.2 tid.toObjId _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
                        storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                           st pair.2 tid.toObjId _ hCap hObjInv hStore (fun cn h => by cases h)⟩

/-- R3-A: `storeTcbIpcStateAndMessage` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbIpcStateAndMessage_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (msg : Option IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep; revert hStep
    cases hStore : storeObject tid.toObjId _ st with
    | error e => simp
    | ok pair => simp only []; intro hEq; cases hEq
                 exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
                           st pair.2 tid.toObjId _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
                        storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                           st pair.2 tid.toObjId _ hCap hObjInv hStore (fun cn h => by cases h)⟩

/-- U4-K: `storeTcbQueueLinks` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbQueueLinks_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold storeTcbQueueLinks at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep; revert hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp
    | ok pair => simp only []; intro hEq; cases hEq
                 exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
                           st pair.2 tid.toObjId _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
                        storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                           st pair.2 tid.toObjId _ hCap hObjInv hStore (fun cn h => by cases h)⟩

/-- U4-K: `storeTcbPendingMessage` preserves `badgeWellFormed`.
Stores a `.tcb` object (not notification, not CNode). -/
theorem storeTcbPendingMessage_preserves_badgeWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold storeTcbPendingMessage at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep; revert hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp
    | ok pair => simp only []; intro hEq; cases hEq
                 exact ⟨storeObject_nonNotification_preserves_notificationBadgesWellFormed
                           st pair.2 tid.toObjId _ hNtfn hObjInv hStore (fun ntfn h => by cases h),
                        storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                           st pair.2 tid.toObjId _ hCap hObjInv hStore (fun cn h => by cases h)⟩

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
Wake path: stores `pendingBadge := none`. Merge path: stores `Badge.bor` or
`Badge.ofNatMasked` — both word-bounded. -/
theorem notificationSignal_preserves_badgeWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold notificationSignal at hStep
  cases hObjSrc : st.objects[notificationId]? with
  | none => simp [hObjSrc] at hStep
  | some obj =>
    cases obj with
    | notification ntfnSrc =>
      simp only [hObjSrc] at hStep
      cases hWaiters : ntfnSrc.waitingThreads with
      | cons waiter rest =>
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
                          st pair1.2 notificationId _ hNtfn hObjInv hStore1 (fun b hb => by simp at hb),
                         storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                          st pair1.2 notificationId _ hCap hObjInv hStore1 (fun cn h => by cases h)⟩
                        hObjInv1 hStoreTcb
      | nil =>
        simp only [hWaiters] at hStep
        exact ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                 st st' notificationId _ hNtfn hObjInv hStep
                 (fun b hb => by
                   simp only [Option.some.injEq] at hb; subst hb
                   cases hPending : ntfnSrc.pendingBadge with
                   | some existing => exact SeLe4n.Badge.bor_valid existing badge
                   | none => exact SeLe4n.Badge.ofNatMasked_valid badge.toNat),
               storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                 st st' notificationId _ hCap hObjInv hStep (fun cn h => by cases h)⟩
    | _ => simp [hObjSrc] at hStep

/-- WS-F5/D1d: `notificationWait` preserves `badgeWellFormed`.
Consume path: stores `pendingBadge := none`. Block path: stores notification
with waiter prepended (badges unchanged). -/
theorem notificationWait_preserves_badgeWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge) (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold notificationWait at hStep
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
                                      st pair1.2 notificationId _ hNtfn hObjInv hStore1 (fun b hb => by simp at hb),
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
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              intro hStep; revert hStep
              cases hStoreTcb : storeTcbIpcState pair1.2 waiter _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                apply removeRunnable_preserves_badgeWellFormed
                have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                exact storeTcbIpcState_preserves_badgeWellFormed pair1.2 st2 waiter _
                  ⟨storeObject_notification_preserves_notificationBadgesWellFormed
                    st pair1.2 notificationId _ hNtfn hObjInv hStore1
                    (fun b hb => by simp at hb),
                   storeObject_nonCNode_preserves_capabilityBadgesWellFormed
                    st pair1.2 notificationId _ hCap hObjInv hStore1 (fun cn h => by cases h)⟩
                  hObjInv1 hStoreTcb
    | _ => simp [hObjSrc] at hStep

-- ============================================================================
-- R3-C/M-19: notificationWaiterConsistent preservation
-- ============================================================================

/-- R3-C/M-19: storeObject at a non-notification ID preserves notificationWaiterConsistent
when the stored object is a TCB with preserved ipcState for threads in wait lists. -/
theorem storeObject_nonNotification_preserves_notificationWaiterConsistent
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId obj st = .ok ((), st'))
    (hNotNtfn : ∀ ntfn, obj ≠ .notification ntfn)
    (hIpcPreserved : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification) (waiter : SeLe4n.ThreadId),
      st.objects[noid]? = some (.notification ntfn) → waiter ∈ ntfn.waitingThreads →
      waiter.toObjId = targetId →
      ∃ tcb', st'.objects[waiter.toObjId]? = some (.tcb tcb') ∧
              tcb'.ipcState = .blockedOnNotification noid) :
    notificationWaiterConsistent st' := by
  intro noid ntfn waiter hNtfnPost hMem
  -- Notification is at noid ≠ targetId (since stored object is not notification)
  by_cases hEq : noid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' noid obj hObjInv hStore] at hNtfnPost
    have := Option.some.inj hNtfnPost; cases obj with
    | notification n => exact absurd rfl (hNotNtfn n)
    | _ => cases this
  · -- noid ≠ targetId: notification unchanged in pre-state
    have hNtfnPre : st.objects[noid]? = some (.notification ntfn) := by
      rw [storeObject_objects_ne st st' targetId noid obj hEq hObjInv hStore] at hNtfnPost; exact hNtfnPost
    by_cases hTEq : waiter.toObjId = targetId
    · -- waiter is the stored object — use hIpcPreserved
      exact hIpcPreserved noid ntfn waiter hNtfnPre hMem hTEq
    · -- waiter is not the stored object — backward transport
      obtain ⟨tcb, hTcb, hIpc⟩ := hConsist noid ntfn waiter hNtfnPre hMem
      exact ⟨tcb, by rw [storeObject_objects_ne st st' targetId waiter.toObjId obj hTEq hObjInv hStore]; exact hTcb, hIpc⟩

/-- R3-C/M-19: storeObject of a notification preserves notificationWaiterConsistent
when the stored notification has a subset of the original waiting list (or is empty)
and no TCBs are modified. -/
theorem storeObject_notification_preserves_notificationWaiterConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId)
    (ntfnOrig : Notification) (ntfn' : Notification)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjOrig : st.objects[notificationId]? = some (.notification ntfnOrig))
    (hStore : storeObject notificationId (.notification ntfn') st = .ok ((), st'))
    (hSubset : ∀ tid, tid ∈ ntfn'.waitingThreads → tid ∈ ntfnOrig.waitingThreads) :
    notificationWaiterConsistent st' := by
  intro noid ntfn waiter hNtfnPost hMem
  by_cases hEq : noid = notificationId
  · subst hEq
    rw [storeObject_objects_eq st st' noid _ hObjInv hStore] at hNtfnPost
    cases hNtfnPost
    -- waiter ∈ ntfn'.waitingThreads ⊆ ntfnOrig.waitingThreads
    have hMemOrig := hSubset waiter hMem
    obtain ⟨tcb, hTcb, hIpc⟩ := hConsist noid ntfnOrig waiter hObjOrig hMemOrig
    -- TCB at waiter.toObjId is unchanged (waiter.toObjId ≠ noid since one is TCB other is notification)
    have hNeTcb : waiter.toObjId ≠ noid := by
      intro h; rw [h, hObjOrig] at hTcb; cases hTcb
    exact ⟨tcb, by rw [storeObject_objects_ne st st' noid waiter.toObjId _ hNeTcb hObjInv hStore]; exact hTcb, hIpc⟩
  · have hNtfnPre : st.objects[noid]? = some (.notification ntfn) := by
      rw [storeObject_objects_ne st st' notificationId noid _ hEq hObjInv hStore] at hNtfnPost; exact hNtfnPost
    obtain ⟨tcb, hTcb, hIpc⟩ := hConsist noid ntfn waiter hNtfnPre hMem
    have hNeTcb : waiter.toObjId ≠ notificationId := by
      intro h; rw [h, hObjOrig] at hTcb; cases hTcb
    exact ⟨tcb, by rw [storeObject_objects_ne st st' notificationId waiter.toObjId _ hNeTcb hObjInv hStore]; exact hTcb, hIpc⟩

-- ============================================================================
-- R3-C.1/M-19: notificationSignal preserves notificationWaiterConsistent
-- ============================================================================

/-- R3-C.1/M-19: storeTcbIpcStateAndMessage preserves notificationWaiterConsistent
when the stored TCB's target is not in any notification's waiting list (in the
pre-state). This holds because storeTcbIpcStateAndMessage stores a TCB (not a
notification), so all notification waiting lists are unchanged, and only the
target thread's TCB is modified. -/
theorem storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hNotInWaitList : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
      st.objects[noid]? = some (.notification ntfn) → tid ∉ ntfn.waitingThreads) :
    notificationWaiterConsistent st' := by
  intro noid ntfn waiter hNtfnPost hMem
  -- Notifications are preserved backward by storeTcbIpcStateAndMessage (it stores a TCB)
  have hNtfnPre : st.objects[noid]? = some (.notification ntfn) :=
    storeTcbIpcStateAndMessage_notification_backward st st' tid ipc msg noid ntfn hObjInv hStep
      hNtfnPost
  -- Get the pre-state witness
  obtain ⟨tcb, hTcb, hIpc⟩ := hConsist noid ntfn waiter hNtfnPre hMem
  -- waiter ≠ tid because tid is not in any notification's waiting list
  have hNeTid : waiter ≠ tid := by
    intro h; subst h; exact hNotInWaitList noid ntfn hNtfnPre hMem
  have hNeObjId : waiter.toObjId ≠ tid.toObjId := fun h => hNeTid (threadId_toObjId_injective h)
  -- TCB at waiter.toObjId is unchanged
  exact ⟨tcb, by rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg
    waiter.toObjId hNeObjId hObjInv hStep]; exact hTcb, hIpc⟩

/-- R3-C.1/M-19: notificationSignal preserves notificationWaiterConsistent.
Wake path: removes head waiter from notification (subset), then stores TCB
with `.ready` — the woken waiter is not in any remaining wait list (by
`uniqueWaiters` Nodup guarantee). ensureRunnable only touches scheduler.
Merge path: stores notification with empty waiters (vacuous subset). -/
theorem notificationSignal_preserves_notificationWaiterConsistent
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hConsist : notificationWaiterConsistent st)
    (hUnique : uniqueWaiters st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    notificationWaiterConsistent st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject → storeTcbIpcStateAndMessage → ensureRunnable
        simp only [hWaiters] at hStep
        -- Extract uniqueness: waiter ∉ rest
        have hNodup := hUnique notificationId ntfn hObj
        rw [hWaiters] at hNodup
        have hWaiterNotInRest : waiter ∉ rest := (List.nodup_cons.mp hNodup).1
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          -- Step 1: storeObject preserves notificationWaiterConsistent (subset rest ⊆ waiter::rest)
          have hConsist1 := storeObject_notification_preserves_notificationWaiterConsistent
            st pair.2 notificationId ntfn
            { state := if rest.isEmpty then .idle else .waiting,
              waitingThreads := rest, pendingBadge := none }
            hConsist hObjInv hObj hStore
            (fun tid hMem => hWaiters ▸ List.mem_cons_of_mem waiter hMem)
          have hObjInv1 : pair.2.objects.invExt :=
            storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          -- Step 2: storeTcbIpcStateAndMessage — waiter not in any wait list in pair.2
          -- Because: in pair.2, the only modified notification is at notificationId
          -- with rest as waiters. waiter ∉ rest. For other notifications, waiter was
          -- in waiter::rest (original), but after storeObject the other notifications
          -- are unchanged. We need to show waiter is not in any notification wait list
          -- in pair.2. By hConsist (pre-state), waiter had ipcState .blockedOnNotification
          -- notificationId. So waiter could only be in notificationId's wait list.
          -- In pair.2, notificationId has rest (which excludes waiter). Other notifications
          -- haven't changed, and waiter wasn't in their lists either (by notificationWaiterConsistent:
          -- if waiter were in another notification noid's list, waiter's ipcState would be
          -- .blockedOnNotification noid, but we know it's .blockedOnNotification notificationId).
          have hWaiterNotInAny : ∀ (noid : SeLe4n.ObjId) (ntfn' : Notification),
              pair.2.objects[noid]? = some (.notification ntfn') →
              waiter ∉ ntfn'.waitingThreads := by
            intro noid ntfn' hNtfn'
            by_cases hEq : noid = notificationId
            · subst hEq
              rw [storeObject_objects_eq st pair.2 noid _ hObjInv hStore] at hNtfn'
              cases hNtfn'; exact hWaiterNotInRest
            · have hNtfnPre : st.objects[noid]? = some (.notification ntfn') := by
                rw [storeObject_objects_ne st pair.2 notificationId noid _ hEq hObjInv hStore] at hNtfn'
                exact hNtfn'
              -- If waiter were in ntfn'.waitingThreads, then by hConsist,
              -- waiter's ipcState = .blockedOnNotification noid.
              -- But waiter ∈ ntfn.waitingThreads (original), so by hConsist,
              -- waiter's ipcState = .blockedOnNotification notificationId.
              -- Since noid ≠ notificationId, contradiction.
              intro hMem
              obtain ⟨tcb1, hTcb1, hIpc1⟩ := hConsist noid ntfn' waiter hNtfnPre hMem
              obtain ⟨tcb2, hTcb2, hIpc2⟩ := hConsist notificationId ntfn waiter hObj
                (by rw [hWaiters]; exact .head rest)
              rw [hTcb1] at hTcb2; cases hTcb2
              rw [hIpc1] at hIpc2; exact hEq (ThreadIpcState.blockedOnNotification.inj hIpc2)
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEqSt⟩; subst hEqSt
            have hConsist2 := storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent
              pair.2 st'' waiter .ready _ hConsist1 hObjInv1 hTcb hWaiterNotInAny
            -- Step 3: ensureRunnable only modifies scheduler — objects unchanged
            intro noid' ntfn' tid' hNtfn' hMem'
            have hNtfnSt := (ensureRunnable_preserves_objects st'' waiter) ▸ hNtfn'
            obtain ⟨tcb', hTcb', hIpc'⟩ := hConsist2 noid' ntfn' tid' hNtfnSt hMem'
            exact ⟨tcb', by rw [ensureRunnable_preserves_objects]; exact hTcb', hIpc'⟩
      | nil =>
        -- Merge path: storeObject only — empty wait list is vacuous subset
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_notificationWaiterConsistent
          st st' notificationId ntfn
          { state := .active, waitingThreads := [],
            pendingBadge := some (match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat) }
          hConsist hObjInv hObj hStep
          (fun _ hMem => by simp at hMem)

-- ============================================================================
-- R3-C.2/M-19: General frame lemma for notificationWaiterConsistent
-- ============================================================================

/-- R3-C.2/M-19: General frame lemma — if a state transition preserves all
notification objects identically and preserves TCBs for all threads appearing
in notification waiting lists, then `notificationWaiterConsistent` is preserved.
This covers all endpoint operations (which only modify TCBs and endpoints,
never notifications). -/
theorem frame_preserves_notificationWaiterConsistent
    (st st' : SystemState)
    (hConsist : notificationWaiterConsistent st)
    (hNtfnPreserved : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
      st'.objects[noid]? = some (.notification ntfn) →
      st.objects[noid]? = some (.notification ntfn))
    (hTcbPreserved : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification) (tid : SeLe4n.ThreadId),
      st.objects[noid]? = some (.notification ntfn) →
      tid ∈ ntfn.waitingThreads →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?) :
    notificationWaiterConsistent st' := by
  intro noid ntfn waiter hNtfnPost hMem
  have hNtfnPre := hNtfnPreserved noid ntfn hNtfnPost
  obtain ⟨tcb, hTcb, hIpc⟩ := hConsist noid ntfn waiter hNtfnPre hMem
  exact ⟨tcb, (hTcbPreserved noid ntfn waiter hNtfnPre hMem).symm ▸ hTcb, hIpc⟩

-- ============================================================================
-- V3-G2/G3 (M-PRF-5): waitingThreadsPendingMessageNone preservation
-- for notification operations
-- ============================================================================
--
-- These theorems were previously located in Structural.lean due to a circular
-- import (Structural imports NotificationPreservation). The primitive helpers
-- they depend on now live in WaitingThreadHelpers.lean, which both files can
-- import, enabling these proofs to live in their semantic home.

/-- V3-I (L-IPC-1): Before `notificationSignal` delivers a badge to a waiting
    thread, the waiter's `pendingMessage` was `none`. Direct extraction from the
    `waitingThreadsPendingMessageNone` invariant: any thread with
    `ipcState = .blockedOnNotification _` has `pendingMessage = none`. -/
theorem notificationWake_pendingMessage_was_none
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (nid : SeLe4n.ObjId)
    (hInv : waitingThreadsPendingMessageNone st)
    (hLookup : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hBlocked : tcb.ipcState = .blockedOnNotification nid) :
    tcb.pendingMessage = none := by
  have h := hInv tid tcb hLookup
  rw [hBlocked] at h
  exact h

/-- V3-G3 (M-PRF-5): `notificationSignal` preserves `waitingThreadsPendingMessageNone`.
    Wake path: sets `.ready` (out of scope). Merge path: non-TCB store only. -/
theorem notificationSignal_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    waitingThreadsPendingMessageNone st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · -- some (.notification ntfn)
    rename_i ntfn hObj
    -- After first split: ntfn.waitingThreads branches
    cases hWaiters : ntfn.waitingThreads with
    | cons waiter rest =>
      -- Wake path: storeObject → storeTcbIpcStateAndMessage (.ready) → ensureRunnable
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction  -- storeObject error
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction  -- storeTcbIpcStateAndMessage error
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInv2 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
            st1 st2 waiter .ready _ hObjInv1 hSM hInv1 (by trivial)
          exact ensureRunnable_preserves_waitingThreadsPendingMessageNone st2 waiter hInv2
    | nil =>
      -- Merge path: storeObject only
      simp only [hWaiters] at hStep
      -- pendingBadge match produces two sub-cases, both are storeObject
      split at hStep
      all_goals (
        exact storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
          st st' notificationId (.notification _) (fun tcb => by simp) hObjInv hStep hInv)
  · contradiction
  · contradiction

/-- V3-G2 (M-PRF-5): `notificationWait` preserves `waitingThreadsPendingMessageNone`.
    Deliver path: `storeTcbIpcState` to `.ready` exits scope.
    Block path: `storeTcbIpcState_fromTcb` to `.blockedOnNotification` + `removeRunnable`;
    requires `hWaiterMsg` precondition that the waiter's `pendingMessage` is `none`. -/
theorem notificationWait_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hWaiterMsg : ∀ tcb, lookupTcb st waiter = some tcb → tcb.pendingMessage = none)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    waitingThreadsPendingMessageNone st' := by
  simp only [notificationWait] at hStep
  split at hStep
  · -- some (.notification ntfn)
    rename_i ntfn hObj
    split at hStep
    · -- Deliver path: pendingBadge = some badge
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_preserves_waitingThreadsPendingMessageNone
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
            have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
              st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
            have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
            -- Split on storeTcbIpcState_fromTcb result
            split at hStep
            next => contradiction -- storeTcbIpcState_fromTcb error
            next st2 hSI =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              apply removeRunnable_preserves_waitingThreadsPendingMessageNone
              -- Unfold storeTcbIpcState_fromTcb to extract underlying storeObject
              simp only [storeTcbIpcState_fromTcb] at hSI
              split at hSI
              next => contradiction -- storeObject error
              next pair hSO2 =>
                simp only [Except.ok.injEq] at hSI
                -- hSI : pair = st2, pair : SystemState
                subst hSI
                -- Goal is now about pair
                intro tid' tcb' hObj'
                by_cases hTidEq : tid'.toObjId = waiter.toObjId
                · -- Same thread: stored TCB has blockedOnNotification, pendingMessage unchanged
                  have hSelf := storeObject_objects_eq st1 pair waiter.toObjId
                    (.tcb { waiterTcb with ipcState := .blockedOnNotification notificationId })
                    hObjInv1 hSO2
                  rw [hTidEq] at hObj'; rw [hSelf] at hObj'
                  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObj'; subst hObj'
                  dsimp only []
                  exact hWaiterMsg waiterTcb hLookup
                · -- Different thread: frame
                  have hFrame := storeObject_objects_ne st1 pair waiter.toObjId tid'.toObjId
                    (.tcb { waiterTcb with ipcState := .blockedOnNotification notificationId })
                    hTidEq hObjInv1 hSO2
                  rw [hFrame] at hObj'
                  exact hInv1 tid' tcb' hObj'
  · contradiction
  · contradiction

end SeLe4n.Kernel
