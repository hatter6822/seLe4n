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

/-! # Notification Preservation — Signal & IPC/Scheduler Invariants (AN3-D)

Extracted from `NotificationPreservation.lean` as part of AN3-D
(IPC-M03 / Theme 4.7).  Contains preservation theorems for
`ipcInvariant`, `schedulerInvariantBundle`, and
`ipcSchedulerContractPredicates` for the notification operations
`notificationSignal` / `notificationWait`.  Declarations are
unchanged in order, content, and proof; only the file boundary
has moved.  The parent `NotificationPreservation.lean` re-exports
every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`
consumers continue to typecheck without modification.
-/


namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-F4: Notification preservation helpers and theorems
-- ============================================================================

/-- Storing a notification preserves ipcInvariant when the new notification
    satisfies notificationInvariant. Dual of storeObject_endpoint_preserves_ipcInvariant. -/
theorem storeObject_notification_preserves_ipcInvariant
    (st st1 : SystemState) (notifId : SeLe4n.ObjId) (ntfn' : Notification)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject notifId (.notification ntfn') st = .ok ((), st1))
    (hPres : notificationInvariant ntfn') :
    ipcInvariant st1 := by
  intro oid ntfn hObj
  by_cases hNe : oid = notifId
  · rw [hNe] at hObj
    rw [storeObject_objects_eq st st1 notifId (.notification ntfn') hObjInv hStore] at hObj
    simp at hObj; subst hObj; exact hPres
  · exact hInv oid ntfn (by rwa [storeObject_objects_ne st st1 notifId oid _ hNe hObjInv hStore] at hObj)

/-- WS-F4: notificationSignal preserves ipcInvariant.
Wake path: stores updated notification (well-formed) + storeTcbIpcState + ensureRunnable.
Merge path: stores active notification (well-formed). -/
theorem notificationSignal_preserves_ipcInvariant
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariant st' := by
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
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
            _ hInv hObjInv hStore (notificationSignal_result_wellFormed_wake rest)
          have hObjInv1 : pair.2.objects.invExt :=
            storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          -- R3-A/M-16: Badge now delivered via storeTcbIpcStateAndMessage
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st'' waiter .ready _ hInv1 hObjInv1 hTcb
            exact fun oid ntfn' h => hInv2 oid ntfn' (by rwa [ensureRunnable_preserves_objects] at h)
      | nil =>
        -- Merge path: storeObject only
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_ipcInvariant st st' notificationId
          _ hInv hObjInv hStep (notificationSignal_result_wellFormed_merge _)

/-- WS-F4: notificationSignal preserves schedulerInvariantBundle.
Wake path: storeObject + storeTcbIpcStateAndMessage (scheduler unchanged) + ensureRunnable.
Merge path: storeObject only (scheduler unchanged). -/
theorem notificationSignal_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hCurrNotWait : currentNotOnNotificationWaitList st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
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
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          -- R3-A/M-16: storeTcbIpcStateAndMessage replaces storeTcbIpcState
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq : st''.scheduler = st.scheduler := by
              rw [storeTcbIpcStateAndMessage_scheduler_eq pair.2 st'' waiter .ready _ hTcb,
                  storeObject_scheduler_eq st pair.2 notificationId _ hStore]
            refine ⟨?_, ?_, ?_⟩
            · -- queueCurrentConsistent
              unfold queueCurrentConsistent
              rw [ensureRunnable_scheduler_current, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                have hNotMem : x ∉ st.scheduler.runnable := by
                  have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                have hNe : x ≠ waiter := by
                  intro hEq; rw [hEq] at hCurr
                  have hNoWait := hCurrNotWait; simp [currentNotOnNotificationWaitList, hCurr] at hNoWait
                  have hInWait : waiter ∈ ntfn.waitingThreads := by rw [hWaiters]; exact List.mem_cons_self
                  exact hNoWait notificationId ntfn hObj hInWait
                exact ensureRunnable_not_mem_of_not_mem st'' waiter x (hSchedEq ▸ hNotMem) hNe
            · exact ensureRunnable_nodup st'' waiter (hSchedEq ▸ hRQU)
            · show currentThreadValid (ensureRunnable st'' waiter)
              unfold currentThreadValid
              simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                have hNeNotif : x.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                have hObjInv1 : pair.2.objects.invExt :=
                  storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                  rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hObjInv hStore]; exact hTcbX
                by_cases hNeTid : x.toObjId = waiter.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects[waiter.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcbX, hTcb1⟩
                  have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st'' waiter .ready _ hObjInv1 hTcb hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcbX, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter .ready _ x.toObjId hNeTid hObjInv1 hTcb) ▸ hTcb1⟩
      | nil =>
        -- Merge path: storeObject only (scheduler unchanged)
        simp only [hWaiters] at hStep
        have hSchedEq := storeObject_scheduler_eq st st' notificationId _ hStep
        have hCurrEq := congrArg SchedulerState.current hSchedEq
        have hRunEq := congrArg SchedulerState.runnable hSchedEq
        refine ⟨?_, ?_, ?_⟩
        · unfold queueCurrentConsistent; rw [hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => trivial
          | some x =>
            show x ∉ st'.scheduler.runnable; rw [hRunEq]
            have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
        · show st'.scheduler.runnable.Nodup; rw [hRunEq]; exact hRQU
        · unfold currentThreadValid; rw [hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            rcases hCTV' with ⟨tcbX, hTcbX⟩
            have hNeNotif : x.toObjId ≠ notificationId := by
              intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
            exact ⟨tcbX, by rw [storeObject_objects_ne st st' notificationId x.toObjId _ hNeNotif hObjInv hStep]; exact hTcbX⟩

/-- WS-F4: notificationWait preserves ipcInvariant.
Badge-consume path: stores idle notification + storeTcbIpcState.
Wait path: stores waiting notification + storeTcbIpcState + removeRunnable. -/
theorem notificationWait_preserves_ipcInvariant
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariant st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Badge-consume path: storeObject → storeTcbIpcState
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hObjInv1 : pair.2.objects.invExt :=
            storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
          have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
            _ hInv hObjInv hStore notificationWait_result_wellFormed_badge
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter .ready hInv1 hObjInv1 hTcb
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              have hObjInv1 : pair.2.objects.invExt :=
                storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
                _ hInv hObjInv hStore (notificationWait_result_wellFormed_wait waiter ntfn.waitingThreads)
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hInv2 := storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter
                  (.blockedOnNotification notificationId) hInv1 hObjInv1 hTcb
                exact fun oid ntfn' h => hInv2 oid ntfn' (by rwa [removeRunnable_preserves_objects] at h)

/-- WS-F4: notificationWait preserves schedulerInvariantBundle.
Badge-consume path: storeObject + storeTcbIpcState (scheduler unchanged).
Wait path: storeObject + storeTcbIpcState (scheduler unchanged) + removeRunnable. -/
theorem notificationWait_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Badge-consume path: storeObject → storeTcbIpcState (scheduler unchanged)
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st'' notificationId _ waiter _ hStore hTcb
            have hCurrEq := congrArg SchedulerState.current hSchedEq
            have hRunEq := congrArg SchedulerState.runnable hSchedEq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent; rw [hCurrEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                show x ∉ st''.scheduler.runnable; rw [hRunEq]
                have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
            · show st''.scheduler.runnable.Nodup; rw [hRunEq]; exact hRQU
            · unfold currentThreadValid; rw [hCurrEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                have hNeNotif : x.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                have hObjInv1 : pair.2.objects.invExt :=
                  storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                  rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hObjInv hStore]; exact hTcbX
                by_cases hNeTid : x.toObjId = waiter.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects[waiter.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcbX, hTcb1⟩
                  have h := storeTcbIpcState_tcb_exists_at_target pair.2 st'' waiter .ready hObjInv1 hTcb hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcbX, (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter .ready x.toObjId hNeTid hObjInv1 hTcb) ▸ hTcb1⟩
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st'' notificationId _ waiter _ hStore hTcb
                have hCurrEq := congrArg SchedulerState.current hSchedEq
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent
                  rw [removeRunnable_scheduler_current, hCurrEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    by_cases hEq' : x = waiter
                    · subst hEq'; simp
                    · rw [if_neg (show ¬(some x = some waiter) from fun h => hEq' (Option.some.inj h))]
                      show x ∉ (removeRunnable st'' waiter).scheduler.runnable
                      have hNotMem : x ∉ st.scheduler.runnable := by
                        have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                      exact removeRunnable_not_mem_of_not_mem st'' waiter x (hSchedEq ▸ hNotMem)
                · exact removeRunnable_nodup st'' waiter (hSchedEq ▸ hRQU)
                · unfold currentThreadValid
                  rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    by_cases hEq' : x = waiter
                    · subst hEq'; simp
                    · rw [if_neg (show ¬(some x = some waiter) from fun h => hEq' (Option.some.inj h))]
                      show ∃ tcb, st''.objects[x.toObjId]? = some (.tcb tcb)
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                        simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                      rcases hCTV' with ⟨tcbX, hTcbX⟩
                      have hNeNotif : x.toObjId ≠ notificationId := by
                        intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                      have hObjInv1 : pair.2.objects.invExt :=
                        storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
                      have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                        rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hObjInv hStore]; exact hTcbX
                      have hNeTid : x.toObjId ≠ waiter.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                      exact ⟨tcbX, (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter (.blockedOnNotification notificationId) x.toObjId hNeTid hObjInv1 hTcb) ▸ hTcb1⟩

/-- WS-F4/R3-A: notificationSignal preserves ipcSchedulerContractPredicates.
Wake path: storeObject + storeTcbIpcStateAndMessage(.ready) + ensureRunnable — waiter gets
.ready and is added to runnable; other threads are backward-transported.
Merge path: storeObject notification only — scheduler and TCBs unchanged,
contracts preserved via contracts_of_same_scheduler_ipcState. -/
theorem notificationSignal_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        simp only [hWaiters] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          -- R3-A/M-16: storeTcbIpcStateAndMessage replaces storeTcbIpcState
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq : st''.scheduler = st.scheduler := by
              rw [storeTcbIpcStateAndMessage_scheduler_eq pair.2 st'' waiter .ready _ hTcb,
                  storeObject_scheduler_eq st pair.2 notificationId _ hStore]
            have hObjInv1 : pair.2.objects.invExt :=
              storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnNotificationNotRunnable (WS-F6/D2)
              intro tid tcb' nid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st'' waiter .ready _ hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st'' waiter
                    .ready _ tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockNotif tid tcb' nid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
      | nil =>
        simp only [hWaiters] at hStep
        exact contracts_of_same_scheduler_ipcState st st'
          (storeObject_scheduler_eq st st' notificationId _ hStep)
          (fun tid tcb' hTcb' => by
            have hNeNotif : tid.toObjId ≠ notificationId := by
              intro h; rw [h] at hTcb'
              rw [storeObject_objects_eq st st' notificationId _ hObjInv hStep] at hTcb'; cases hTcb'
            exact ⟨tcb', by rwa [storeObject_objects_ne st st' notificationId tid.toObjId
              _ hNeNotif hObjInv hStep] at hTcb', rfl⟩)
          ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩

/-- WS-F4: notificationWait preserves ipcSchedulerContractPredicates.
Badge-consume: storeObject + storeTcbIpcState(.ready) — scheduler unchanged.
Wait: storeObject + storeTcbIpcState(.blockedOnNotification) + removeRunnable —
waiter's .blockedOnNotification is not .blockedOnSend/.blockedOnReceive, so
contract predicates are maintained through backward transport. -/
theorem notificationWait_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st''
              notificationId _ waiter _ hStore hTcb
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · exact storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnNotificationNotRunnable (WS-F6/D2)
              intro tid tcb' nid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockNotif tid tcb' nid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              cases hTcb : storeTcbIpcState pair.2 waiter
                  (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st''
                  notificationId _ waiter _ hStore hTcb
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                · -- runnableThreadIpcReady
                  intro tid tcb' hTcb' hRun'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  rw [removeRunnable_runnable_mem] at hRun'
                  have ⟨hMem, hNeTid⟩ := hRun'
                  have hNe : tid.toObjId ≠ waiter.toObjId :=
                    fun h => hNeTid (threadId_toObjId_injective h)
                  have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                      (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                  have hNeNotif : tid.toObjId ≠ notificationId := by
                    intro h; rw [h] at hTcbMid
                    rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                    cases hTcbMid
                  have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                    _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                  exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnSendNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnReceiveNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnCallNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnReplyNotRunnable
                  intro tid tcb' eid rt hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hObjInv1 hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                  intro tid tcb' nid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · -- tid matches waiter: waiter was removed from runnable
                    have hTidEq := ThreadId.toObjId_injective tid waiter hNe
                    subst hTidEq
                    exact removeRunnable_not_mem_self st'' _
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hObjInv1 hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hObjInv hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hObjInv hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockNotif tid tcb' nid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])

end SeLe4n.Kernel
