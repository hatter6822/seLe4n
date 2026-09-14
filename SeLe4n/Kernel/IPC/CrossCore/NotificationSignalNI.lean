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
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind

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
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
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
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
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

-- ============================================================================
-- §4  SM6.B.7 (wait) — `notificationWaitOnCore` block-path non-interference
-- ============================================================================

/-- `storeTcbIpcState` leaves the machine registers untouched (it writes only the
target TCB's `ipcState`). -/
theorem storeTcbIpcState_machine_eq (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.machine = st.machine := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_machine_eq st pair.2 tid.toObjId _ hStore

/-- SM6.B.7: the per-core form of `storeTcbIpcState_preserves_projection` — a
`storeTcbIpcState` at a **high** thread preserves every core's per-core observer
projection (object-store base preserved; scheduler + machine untouched). -/
theorem storeTcbIpcState_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (c : CoreId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := storeTcbIpcState_scheduler_eq st st' tid ipc hStep
  have hMach := storeTcbIpcState_machine_eq st st' tid ipc hStep
  exact projectStateOnCore_congr ctx observer
    (storeTcbIpcState_preserves_projection ctx observer st st' tid ipc hTidObjHigh hObjInv hStep)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hMach])

/-- WS-SM SM6.B.7 (`notificationWait_perCore_NI`, boot-core form): a cross-core
notification wait that *blocks* on a **non-observable** notification, by a
non-observable caller, is invisible to a low observer — `projectState` is
preserved.  The block path's notification-store, caller-block, and per-core
deschedule all touch only high state. -/
theorem notificationWaitOnCore_block_path_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (tcb : TCB)
    (wt' : SeLe4n.NoDupList SeLe4n.ThreadId) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hBadge : ntfn.pendingBadge = none)
    (hLk : lookupTcb st waiter = some tcb)
    (hNotWaiting : ¬ (tcb.ipcState = .blockedOnNotification notificationId))
    (hCons : ntfn.waitingThreads.consWithGuard? waiter = some wt')
    (hStore : storeObject notificationId (.notification
        { state := .waiting, waitingThreads := wt', pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hTcb : storeTcbIpcStateAndMessage_fromTcb st' waiter tcb
        (.blockedOnNotification notificationId) none = .ok st'')
    (hObjInv : st.objects.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false) :
    projectState ctx observer (notificationWaitOnCore notificationId waiter executingCore st).1
      = projectState ctx observer st := by
  have hLk' : lookupTcb st' waiter = some tcb :=
    lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
  have hTcb' : storeTcbIpcStateAndMessage st' waiter (.blockedOnNotification notificationId) none
      = .ok st'' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk']; exact hTcb
  have hInv' := storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  rw [notificationWaitOnCore_block_eq notificationId waiter executingCore st ntfn tcb wt' st' st''
        hObj hBadge hLk hNotWaiting hCons hStore hTcb]
  show projectState ctx observer (removeRunnableOnCore st'' waiter executingCore)
    = projectState ctx observer st
  rw [removeRunnableOnCore_preserves_projection ctx observer st'' waiter executingCore hWaiterHigh,
      storeTcbIpcStateAndMessage_preserves_projection ctx observer st' st'' waiter _ _ hWaiterObjHigh hInv' hTcb',
      storeObject_preserves_projection ctx observer st st' notificationId _ hNtfnHigh hObjInv hStore]

/-- WS-SM SM6.B.7 (`notificationWait_perCore_NI`, ∀-core form): the blocking wait
is invisible to a low observer on *every* core (the deschedule edits only the
high caller's slots on the executing core; every other core is untouched). -/
theorem notificationWaitOnCore_block_path_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (tcb : TCB)
    (wt' : SeLe4n.NoDupList SeLe4n.ThreadId) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hBadge : ntfn.pendingBadge = none)
    (hLk : lookupTcb st waiter = some tcb)
    (hNotWaiting : ¬ (tcb.ipcState = .blockedOnNotification notificationId))
    (hCons : ntfn.waitingThreads.consWithGuard? waiter = some wt')
    (hStore : storeObject notificationId (.notification
        { state := .waiting, waitingThreads := wt', pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hTcb : storeTcbIpcStateAndMessage_fromTcb st' waiter tcb
        (.blockedOnNotification notificationId) none = .ok st'')
    (hObjInv : st.objects.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false) :
    lowEquivalent_smp ctx observer
      (notificationWaitOnCore notificationId waiter executingCore st).1 st := by
  intro c
  have hLk' : lookupTcb st' waiter = some tcb :=
    lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
  have hTcb' : storeTcbIpcStateAndMessage st' waiter (.blockedOnNotification notificationId) none
      = .ok st'' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk']; exact hTcb
  have hInv' := storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  show projectStateOnCore ctx observer
      (notificationWaitOnCore notificationId waiter executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [notificationWaitOnCore_block_eq notificationId waiter executingCore st ntfn tcb wt' st' st''
        hObj hBadge hLk hNotWaiting hCons hStore hTcb]
  show projectStateOnCore ctx observer (removeRunnableOnCore st'' waiter executingCore) c
    = projectStateOnCore ctx observer st c
  rw [removeRunnableOnCore_preserves_projectionOnCore ctx observer st'' waiter executingCore c hWaiterHigh,
      storeTcbIpcStateAndMessage_preserves_projectionOnCore ctx observer st' st'' waiter _ _ c hWaiterObjHigh hInv' hTcb',
      storeObject_preserves_projectionOnCore ctx observer st st' notificationId _ c
        hNtfnHigh hObjInv hStore]

-- ============================================================================
-- §5  WS-RR RR7.22 — the bound-delivery path's non-interference
-- ============================================================================
--
-- `notificationSignalBoundOnCore` is a **live** `.notificationSignal` path (a
-- notification whose bound TCB is `BlockedOnReceive` and whose waiter list is
-- empty delivers the badge directly to it), and it had no non-interference
-- theorem: §3 covers the *waiter* path and §2's fall-through covers the
-- unbound one, so the arm SM6.B added was the one arm the NI surface never
-- reached.
--
-- The missing engine is the endpoint **splice**.  Every other write on this
-- path already has its projection lemma — the receive-complete store, the
-- cross-core wake — but `endpointQueueRemoveDual` had none, and it is what
-- dequeues the bound TCB from its endpoint.

/-- **WS-RR RR7.22**: the label hypothesis an endpoint splice needs.

`endpointQueueRemoveDual` writes exactly four objects: the endpoint (twice on
the head path), the removed thread's own TCB, and the two queue neighbours
whose links it patches.  This names all four, and names the neighbours *through
the pre-state lookup* rather than as extra arguments — so a caller supplies one
hypothesis instead of remembering which two threads the splice will touch,
which is the shape that makes an under-stated hypothesis possible. -/
def endpointSpliceHigh (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : Prop :=
  objectObservable ctx observer endpointId = false
    ∧ objectObservable ctx observer tid.toObjId = false
    ∧ ∀ tcb : TCB, lookupTcb st tid = some tcb →
        (∀ p : SeLe4n.ThreadId, tcb.queuePPrev = some (.tcbNext p) →
            objectObservable ctx observer p.toObjId = false)
          ∧ (∀ n : SeLe4n.ThreadId, tcb.queueNext = some n →
              objectObservable ctx observer n.toObjId = false)

/-- **WS-RR RR7.22**: an endpoint splice confined to high objects is invisible,
and leaves the object store's external invariant intact.

The theorem the SM6 plan's tracked-debt item 1 names as its engine and the
register's finding 3 names as the engine of the bound-delivery
non-interference.  Both halves are proved together because the chain needs
them together: each projection step's hypothesis is the *previous* state's
`invExt`, so carrying the projection alone would leave every step but the first
unprovable.

The case analysis mirrors `endpointQueueRemoveDual_frame`'s — deliberately, so
the two stay comparable — but cannot reuse it: that combinator's store
hypotheses are unconditional in the key, and a projection is preserved only at
a **high** key.  That difference is the whole content of this lemma. -/
theorem endpointQueueRemoveDual_preserves_projection_and_invExt
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hHigh : endpointSpliceHigh ctx observer st endpointId tid)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st
      ∧ st'.objects.invExt := by
  obtain ⟨hEp, hTid, hNbr⟩ := hHigh
  -- The two step shapes, packaged so each leaf is a chain rather than a
  -- re-derivation.  `hS` is an endpoint store (always at `endpointId`, always
  -- high); `hL` is a queue-link write at a thread the caller has labelled.
  have hS : ∀ (s s' : SystemState) (obj : KernelObject), s.objects.invExt →
      storeObject endpointId obj s = .ok ((), s') →
      projectState ctx observer s' = projectState ctx observer s ∧ s'.objects.invExt :=
    fun s s' obj hi h =>
      ⟨storeObject_preserves_projection ctx observer s s' endpointId obj hEp hi h,
       storeObject_preserves_objects_invExt s s' endpointId obj hi h⟩
  have hL : ∀ (s s' : SystemState) (t : SeLe4n.ThreadId)
      (qp : Option SeLe4n.ThreadId) (qpp : Option QueuePPrev) (qn : Option SeLe4n.ThreadId),
      objectObservable ctx observer t.toObjId = false → s.objects.invExt →
      storeTcbQueueLinks s t qp qpp qn = .ok s' →
      projectState ctx observer s' = projectState ctx observer s ∧ s'.objects.invExt :=
    fun s s' t qp qpp qn ht hi h =>
      ⟨storeTcbQueueLinks_preserves_projection ctx observer s s' t qp qpp qn ht hi h,
       storeTcbQueueLinks_preserves_objects_invExt s s' t qp qpp qn hi h⟩
  unfold endpointQueueRemoveDual SystemState.getObject? at hStep
  revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        obtain ⟨hPrevHigh, hNextHigh⟩ := hNbr tcb hLookup
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    obtain ⟨e1, i1⟩ := hS _ _ _ hObjInv hStore1
                    obtain ⟨e2, i2⟩ := hS _ _ _ i1 hStore2
                    obtain ⟨e3, i3⟩ := hL _ _ _ _ _ _ hTid i2 hFinal
                    exact ⟨e3.trans (e2.trans e1), i3⟩
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []
                  cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    obtain ⟨e1, i1⟩ := hS _ _ _ hObjInv hStore1
                    obtain ⟨e2, i2⟩ := hL _ _ _ _ _ _ (hNextHigh nextTid hNext) i1 hLink
                    obtain ⟨e3, i3⟩ := hS _ _ _ i2 hStore2
                    obtain ⟨e4, i4⟩ := hL _ _ _ _ _ _ hTid i3 hFinal
                    exact ⟨e4.trans (e3.trans (e2.trans e1)), i4⟩
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev
                        prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have hPrev : objectObservable ctx observer prevTid.toObjId = false :=
                      hPrevHigh prevTid (by rw [hPPrev])
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        obtain ⟨e1, i1⟩ := hL _ _ _ _ _ _ hPrev hObjInv hLink0
                        obtain ⟨e2, i2⟩ := hS _ _ _ i1 hStore2
                        obtain ⟨e3, i3⟩ := hL _ _ _ _ _ _ hTid i2 hFinal
                        exact ⟨e3.trans (e2.trans e1), i3⟩
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]
                      cases hLink : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink]
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        obtain ⟨e1, i1⟩ := hL _ _ _ _ _ _ hPrev hObjInv hLink0
                        obtain ⟨e2, i2⟩ := hL _ _ _ _ _ _ (hNextHigh nextTid hNext) i1 hLink
                        obtain ⟨e3, i3⟩ := hS _ _ _ i2 hStore2
                        obtain ⟨e4, i4⟩ := hL _ _ _ _ _ _ hTid i3 hFinal
                        exact ⟨e4.trans (e3.trans (e2.trans e1)), i4⟩

/-- **WS-RR RR7.22**: the projection half on its own — the name the SM6 plan
and the register both cite. -/
theorem endpointQueueRemoveDual_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hHigh : endpointSpliceHigh ctx observer st endpointId tid)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st :=
  (endpointQueueRemoveDual_preserves_projection_and_invExt ctx observer st st'
    endpointId isReceiveQ tid hHigh hObjInv hStep).1

/-- **WS-RR RR7.22 — `notificationSignalBound_perCore_NI`, the theorem the live
bound-delivery path did not have.**

A cross-core notification signal that delivers its badge **directly to a bound
TCB** — the arm SM6.B added, taken when the notification has no waiters and its
bound thread is `BlockedOnReceive` — is invisible to a low observer, provided
every object it writes is high: the endpoint it splices the bound TCB out of,
that TCB, and the TCB's two queue neighbours.

Three writes, three existing lemmas, and the one this row had to build.  The
splice (`endpointQueueRemoveDual_preserves_projection_and_invExt`) is the piece
that did not exist, which is why this arm had no NI theorem while the waiter
path (§3) and the unbound fall-through (§2) both did.

The notification object itself is *not* written on this path — the badge goes
to the thread, not to the notification — so it needs no label hypothesis, which
is the one place this statement is weaker than §3's and correctly so. -/
theorem notificationSignalBoundOnCore_bound_path_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st st1 st2 : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId))
    (hRemove : endpointQueueRemoveDual epId true t st = .ok ((), st1))
    (hRecv : storeTcbReceiveComplete st1 t
        (some { IpcMessage.empty with badge := some badge }) = .ok st2)
    (hSplice : endpointSpliceHigh ctx observer st epId t)
    (hObjInv : st.objects.invExt)
    (hBoundHigh : threadObservable ctx observer t = false)
    (hBoundObjHigh : objectObservable ctx observer t.toObjId = false) :
    projectState ctx observer
        (notificationSignalBoundOnCore notificationId badge executingCore st).1
      = projectState ctx observer st := by
  obtain ⟨eSplice, iSplice⟩ :=
    endpointQueueRemoveDual_preserves_projection_and_invExt ctx observer st st1
      epId true t hSplice hObjInv hRemove
  have iRecv : st2.objects.invExt :=
    storeTcbReceiveComplete_preserves_objects_invExt st1 st2 t _ iSplice hRecv
  have eRecv : projectState ctx observer st2 = projectState ctx observer st1 :=
    storeTcbReceiveComplete_preserves_projection ctx observer st1 st2 t _
      hBoundObjHigh iSplice hRecv
  show projectState ctx observer
      (notificationSignalBoundOnCore notificationId badge executingCore st).1
    = projectState ctx observer st
  unfold notificationSignalBoundOnCore
  rw [hTarget]
  simp only [hRemove, hRecv]
  exact (wakeThread_preserves_projection ctx observer st2 t executingCore
      hBoundHigh hBoundObjHigh iRecv).trans (eRecv.trans eSplice)

/-- **WS-RR RR7.22**: the per-core form of the splice's projection lemma.  The
splice writes only the object store, so the scheduler slots and every core's
register bank are framed and the per-core congruence applies on every core. -/
theorem endpointQueueRemoveDual_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hHigh : endpointSpliceHigh ctx observer st endpointId tid)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := endpointQueueRemoveDual_scheduler_eq st st' endpointId isReceiveQ tid hStep
  have hMach := endpointQueueRemoveDual_machine_eq st st' endpointId isReceiveQ tid hStep
  exact projectStateOnCore_congr ctx observer
    (endpointQueueRemoveDual_preserves_projection ctx observer st st' endpointId
      isReceiveQ tid hHigh hObjInv hStep)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched])
    (by rw [hMach])

/-- **WS-RR RR7.22**: the per-core form of the receive-complete store's
projection lemma — the badge delivery, framed on every core. -/
theorem storeTcbReceiveComplete_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) (c : CoreId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := storeTcbReceiveComplete_scheduler_eq st st' tid msg hStep
  have hMach := storeTcbReceiveComplete_machine_eq st st' tid msg hStep
  exact projectStateOnCore_congr ctx observer
    (storeTcbReceiveComplete_preserves_projection ctx observer st st' tid msg
      hTidObjHigh hObjInv hStep)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched])
    (by rw [hMach])

/-- **WS-RR RR7.22 — `notificationSignalBound_perCore_NI`, the ∀-core form.**

The SMP-faithful strengthening of the boot-core theorem above: the bound
delivery is invisible on **every** core, not only on the one that signalled.
That is the statement the SMP claim needs — the bound TCB is woken on its
*home* core, which may be remote, so a boot-core-only result says nothing about
the core the wake actually lands on. -/
theorem notificationSignalBoundOnCore_bound_path_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st st1 st2 : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, epId))
    (hRemove : endpointQueueRemoveDual epId true t st = .ok ((), st1))
    (hRecv : storeTcbReceiveComplete st1 t
        (some { IpcMessage.empty with badge := some badge }) = .ok st2)
    (hSplice : endpointSpliceHigh ctx observer st epId t)
    (hObjInv : st.objects.invExt)
    (hBoundHigh : threadObservable ctx observer t = false)
    (hBoundObjHigh : objectObservable ctx observer t.toObjId = false) :
    lowEquivalent_smp ctx observer
      (notificationSignalBoundOnCore notificationId badge executingCore st).1 st := by
  intro c
  have iSplice : st1.objects.invExt :=
    (endpointQueueRemoveDual_preserves_projection_and_invExt ctx observer st st1
      epId true t hSplice hObjInv hRemove).2
  have iRecv : st2.objects.invExt :=
    storeTcbReceiveComplete_preserves_objects_invExt st1 st2 t _ iSplice hRecv
  show projectStateOnCore ctx observer
      (notificationSignalBoundOnCore notificationId badge executingCore st).1 c
    = projectStateOnCore ctx observer st c
  unfold notificationSignalBoundOnCore
  rw [hTarget]
  simp only [hRemove, hRecv]
  rw [wakeThread_preserves_projectionOnCore ctx observer st2 t executingCore c
        hBoundHigh hBoundObjHigh iRecv,
      storeTcbReceiveComplete_preserves_projectionOnCore ctx observer st1 st2 t _ c
        hBoundObjHigh iSplice hRecv,
      endpointQueueRemoveDual_preserves_projectionOnCore ctx observer st st1 epId true t c
        hSplice hObjInv hRemove]

end SeLe4n.Kernel
