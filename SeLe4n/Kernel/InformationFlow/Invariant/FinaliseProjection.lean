/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 23 — the finalisation's projection theorem, staged with the reachable-state surface it composes (`IPC.Invariant.CancelAllReachability`).
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability
import SeLe4n.Kernel.IPC.CrossCore.CancellationNI
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignalNI

/-!
# The finalisation is invisible when what it touches is hidden

WS-ZA ZA5.4 part 23: a final delete's finalisation (`finaliseFinalObject`)
writes the object it finalises, the threads waiting on that object, and the run
queues those threads are woken into; the unbind writes the thread the
notification is bound to.  When the observer sees none of them, the projection
is unchanged (`finaliseFinalObject_preserves_projection`), and so is the retire
after it (`retireFinalisedObject_preserves_projection`).

WS-ZA ZA5.4 part 24: a thread's finalisation (`finaliseThread`) writes the
thread, its bound notification, its scheduling context, the notification or
endpoint it waits on and its neighbours in that queue; a scheduling context's
(`finaliseSchedContext`)
writes the context and its bound thread.  The replenish entry and the reschedule
flags they write are outside the projection.  When the observer sees none of the
objects (`threadFinaliseHidden`, `schedContextFinaliseHidden`), the projection is
unchanged (`finaliseThread_hidden`, `finaliseSchedContext_hidden`).

WS-ZA ZA5.4 part 25: a scheduling context's finalisation also releases a holder
it lends to and unlinks the head of its reply stack, a stack link the projection
strips; a reply's (`finaliseReply`) cancels its waiting caller — a head reply's
cancel hands the caller's reservation back and deschedules the thread it is taken
from (seL4 MCS's `reply_pop`) — reverts the boost the caller lent along its
blocking chain, and suspends it.  When the caller is hidden
(`replyFinaliseHidden`), the blocking chain of a hidden thread is hidden
(`hBlockingChainHigh`), and every lender flows to the thread it lends to
(`donationOwnerFlowsToHolder`, so the descheduled thread is hidden too), the
projection is unchanged (`finaliseReply_hidden`).

* **Which threads wait.**  The hypothesis names the threads that wait on the
  object in the pre-state (`waitersHidden`).  Every step leaves each thread
  `.ready` or in the blocking state it had (`waitFrame`), so a thread that waits
  on the object at any step waited on it before, and is hidden.
* **Which threads a step writes.**  The head of the queue, which waits on the
  object (`queueHeadBlockedConsistent`, `notificationWaiterConsistent`), and its
  successor, which does too (`queueNextTargetBlocked`, the notification queue's
  successor clause).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  Hidden writes
-- ============================================================================

/-- **A write the observer cannot see**: only the object table changes, and at
no key the observer sees. -/
def hiddenObjectsWrite (ctx : LabelingContext) (observer : IfObserver)
    (s s' : SystemState) : Prop :=
  s' = { s with objects := s'.objects } ∧
    ∀ k, objectObservable ctx observer k = true → s'.objects[k]? = s.objects[k]?

namespace hiddenObjectsWrite

variable {ctx : LabelingContext} {observer : IfObserver}

theorem projection {s s' : SystemState} (h : hiddenObjectsWrite ctx observer s s') :
    projectState ctx observer s' = projectState ctx observer s := by
  refine projectState_of_objects_only ctx observer h.1 (funext fun k => ?_)
  unfold projectObjects SystemState.getObject?
  split
  · next hk => rw [h.2 k hk]
  · rfl

theorem updateTcb (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : s.objects.invExt) (hT : objectObservable ctx observer t.toObjId = false) :
    hiddenObjectsWrite ctx observer s (s.updateTcb t f) :=
  ⟨SystemState.updateTcb_eq_objects_update s t f, fun k hk =>
    SystemState.updateTcb_objects_ne _ _ _ k (fun e => by rw [← e, hT] at hk; cases hk) hInv⟩

theorem modifyObject (s : SystemState) (x : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : s.objects.invExt) (hX : objectObservable ctx observer x = false) :
    hiddenObjectsWrite ctx observer s (s.modifyObject x f) :=
  ⟨rfl, fun k hk => by
    rw [modifyObject_objects_getElem hInv, if_neg (fun e => by rw [← e, hX] at hk; cases hk)]⟩

theorem rewriteObject (s : SystemState) (x : SeLe4n.ObjId) (o : KernelObject)
    (h : s.rewriteAdmissible x o) (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer x = false) :
    hiddenObjectsWrite ctx observer s (s.rewriteObject x o h) :=
  ⟨rfl, fun k hk => SystemState.rewriteObject_objects_ne _ _ _ _ _
    (fun e => by rw [← e, hX] at hk; cases hk) hInv⟩

/-- Two hidden writes in sequence are one. -/
theorem trans {a b c : SystemState} (h₁ : hiddenObjectsWrite ctx observer a b)
    (h₂ : hiddenObjectsWrite ctx observer b c) : hiddenObjectsWrite ctx observer a c :=
  ⟨h₂.1.trans (by rw [h₁.1]), fun k hk => (h₂.2 k hk).trans (h₁.2 k hk)⟩

end hiddenObjectsWrite

-- ============================================================================
-- §2  The threads that wait
-- ============================================================================

/-- **A thread waits on `x`**: blocked sending, receiving or calling on it, or
waiting on it as a notification. -/
def waitsOn (x : SeLe4n.ObjId) (s : ThreadIpcState) : Prop :=
  s = .blockedOnSend x ∨ s = .blockedOnReceive x ∨ s = .blockedOnCall x ∨
    s = .blockedOnNotification x

/-- **Every thread that waits on `x` is hidden**, as an object and as a
thread. -/
def waitersHidden (ctx : LabelingContext) (observer : IfObserver) (x : SeLe4n.ObjId)
    (s : SystemState) : Prop :=
  ∀ (t : SeLe4n.ThreadId) (tcb : TCB), s.objects[t.toObjId]? = some (.tcb tcb) →
    waitsOn x tcb.ipcState →
    objectObservable ctx observer t.toObjId = false ∧ threadObservable ctx observer t = false

/-- **Each thread is `.ready` or blocked as it was.** -/
def waitFrame (s s' : SystemState) : Prop :=
  ∀ (t : SeLe4n.ThreadId) (tcb' : TCB), s'.objects[t.toObjId]? = some (.tcb tcb') →
    tcb'.ipcState = .ready ∨
      ∃ tcb, s.objects[t.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState

namespace waitFrame

theorem refl (s : SystemState) : waitFrame s s := fun _ tcb' h => Or.inr ⟨tcb', h, rfl⟩

theorem trans {a b c : SystemState} (h₁ : waitFrame a b) (h₂ : waitFrame b c) : waitFrame a c := by
  intro t tc hc
  rcases h₂ t tc hc with e | ⟨tb, hb, eb⟩
  · exact Or.inl e
  · rcases h₁ t tb hb with e | ⟨ta, ha, ea⟩
    · exact Or.inl (eb ▸ e)
    · exact Or.inr ⟨ta, ha, ea.trans eb⟩

theorem of_objectsAgreeOffRunLinks {s s' : SystemState} (h : s'.objectsAgreeOffRunLinks s) :
    waitFrame s s' := by
  intro t tcb' hObj
  run_links_back h at tcb' hObj
  exact Or.inr ⟨tcb', hObj, rfl⟩

theorem of_ntfnUnlinkReach {s s' : SystemState} (h : ntfnUnlinkReach s s') : waitFrame s s' := by
  intro t tcb' hT
  rcases h.2 t.toObjId with e | ⟨_, _, _, e, _⟩ | ⟨t0, t1, h0, h1, hR⟩
  · exact Or.inr ⟨tcb', e.symm.trans hT, rfl⟩
  · rw [hT] at e; cases e
  · rw [hT] at h1; cases h1
    obtain ⟨np, nn, hEq⟩ := hR
    exact Or.inr ⟨t0, h0, by rw [hEq]⟩

/-- A thread rewritten `.ready` or keeping its blocking state. -/
theorem updateTcb (s : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : s.objects.invExt) (hf : ∀ x, (f x).ipcState = .ready ∨ (f x).ipcState = x.ipcState) :
    waitFrame s (s.updateTcb t f) := by
  intro u tcb' h
  by_cases e : t.toObjId = u.toObjId
  · cases hG : s.getTcb? t with
    | none => rw [SystemState.updateTcb_eq_self_of_none hG] at h; exact Or.inr ⟨tcb', h, rfl⟩
    | some x =>
      have hT := (SystemState.getTcb?_eq_some_iff s t x).mp hG
      rw [← e, updateTcb_objects_self_of_tcb f hInv hT] at h
      cases h
      rcases hf x with r | r
      · exact Or.inl r
      · exact Or.inr ⟨x, e ▸ hT, r.symm⟩
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv] at h
    exact Or.inr ⟨tcb', h, rfl⟩

/-- An object that is no thread rewritten as no thread. -/
theorem modifyObject_nonTcb (s : SystemState) (k : SeLe4n.ObjId) {f : KernelObject → KernelObject}
    (hInv : s.objects.invExt) (hf : ∀ o, (∀ t, o ≠ .tcb t) → ∀ t, f o ≠ .tcb t)
    (hk : ∀ t, s.objects[k]? ≠ some (.tcb t)) :
    waitFrame s (s.modifyObject k f) := by
  intro u tcb' h
  rw [modifyObject_objects_getElem hInv] at h
  split at h
  · next e =>
    cases hG : s.objects[k]? with
    | none => rw [hG] at h; cases h
    | some o =>
      rw [hG] at h
      exact absurd (Option.some.inj h) (hf o (fun t ht => hk t (by rw [hG, ht])) tcb')
  · exact Or.inr ⟨tcb', h, rfl⟩

/-- A frame carries the hidden waiters forward. -/
theorem waitersHidden {ctx : LabelingContext} {observer : IfObserver} {x : SeLe4n.ObjId}
    {s s' : SystemState} (h : waitFrame s s') (hW : _root_.SeLe4n.Kernel.waitersHidden ctx observer x s) :
    _root_.SeLe4n.Kernel.waitersHidden ctx observer x s' := by
  intro t tcb' hT hw
  rcases h t tcb' hT with e | ⟨tcb, h0, e⟩
  · rw [e] at hw; rcases hw with h | h | h | h <;> cases h
  · exact hW t tcb h0 (e ▸ hw)

end waitFrame

-- ============================================================================
-- §3  Each step
-- ============================================================================

/-- **An endpoint waiter's cancel is invisible when the endpoint and its waiters
are hidden**: the pop writes the endpoint, the head and the head's successor,
which waits on the endpoint too (`queueNextTargetBlocked`); the cancel writes
the head; the wake runs the head. -/
theorem storeEndpointWaiterCancelled_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (x : SeLe4n.ObjId) (q : Bool) (ep : Endpoint) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : s.objects.invExt) (hFull : ipcInvariantFull s)
    (hX : objectObservable ctx observer x = false) (hW : waitersHidden ctx observer x s)
    (hE : s.getEndpoint? x = some ep) (hH : (endpointWaitQueue ep q).head = some t)
    (hT : s.getTcb? t = some tcb) (hC : endpointWaiterCancellable s x t tcb = true) :
    projectState ctx observer (storeEndpointWaiterCancelled s x q t tcb.queueNext) =
        projectState ctx observer s ∧
      waitFrame s (storeEndpointWaiterCancelled s x q t tcb.queueNext) := by
  obtain ⟨-, -, hG⟩ := endpointWaiterCancellable_parts hC
  have hEo := (SystemState.getEndpoint?_eq_some_iff s x ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
  have hH' : (if q then ep.receiveQ else ep.sendQ).head = some t := hH
  have hBlk : tcb.ipcState = .blockedOnReceive x ∨
      tcb.ipcState = .blockedOnSend x ∨ tcb.ipcState = .blockedOnCall x := by
    have hQ := hFull.queueHeadBlockedConsistent x ep t tcb hEo hTo
    cases q
    · exact Or.inr (hQ.2 (by simpa using hH'))
    · exact Or.inl (hQ.1 (by simpa using hH'))
  have hTh := hW t tcb hTo (by rcases hBlk with e | e | e <;> simp [waitsOn, e])
  have hNext : ∀ b, tcb.queueNext = some b → objectObservable ctx observer b.toObjId = false := by
    intro b hb
    obtain ⟨tb, hTb, -⟩ := hFull.dualQueueSystemInvariant.linkIntegrity.1 t tcb hTo b hb
    have hM := hFull.queueNextTargetBlocked t b tcb tb hTo hTb hb
    refine (hW b tb hTb ?_).1
    rcases hBlk with e | e | e
    · simp [waitsOn, hM.1 x e]
    · rcases hM.2 x (Or.inl e) with e' | e' <;> simp [waitsOn, e']
    · rcases hM.2 x (Or.inr e) with e' | e' <;> simp [waitsOn, e']
  obtain ⟨hPop, hFr⟩ := popHead_inPlace s x q ep t tcb hEo hH' hTo hG
  have hP1 := endpointQueuePopHead_preserves_projection ctx observer x q s _ t tcb hX hTh.1 hNext
    hInv hPop
  have hW1 : waitFrame s (storePopHead s x q t tcb.queueNext) := fun u tcb' h =>
    Or.inr (endpointQueuePopHead_tcb_ipcState_backward x q s _ t u tcb' hInv hPop h)
  have hI1 := endpointQueuePopHead_preserves_objects_invExt x q s _ t tcb hInv hPop
  unfold storeEndpointWaiterCancelled wakeCancelledWaiter
  generalize storePopHead s x q t tcb.queueNext = s1 at hPop hFr hP1 hW1 hI1 ⊢
  have hT1 : s1.objects[t.toObjId]? = some (.tcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hFr.head_tcb
  have hS2 := updateTcb_objects_self_of_tcb cancelledEndpointWaiterTcb hI1 hT1
  have hI2 := SystemState.updateTcb_preserves_objects_invExt s1 t cancelledEndpointWaiterTcb hI1
  have hReady : (cancelledEndpointWaiterTcb (tcbOffQueue tcb)).ipcState = .ready :=
    TCB.ipcState_setIpcState
      { tcbOffQueue tcb with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
  have hP2 := (hiddenObjectsWrite.updateTcb (ctx := ctx) (observer := observer) s1 t
    cancelledEndpointWaiterTcb hI1 hTh.1).projection
  have hW2 := waitFrame.updateTcb s1 t (f := cancelledEndpointWaiterTcb) hI1 (fun y => Or.inl
    (TCB.ipcState_setIpcState { y with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready))
  have hG2 : (s1.updateTcb t cancelledEndpointWaiterTcb).getTcb? t =
      some (cancelledEndpointWaiterTcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS2
  have hAg := enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready _
    (determineTargetCore (s1.updateTcb t cancelledEndpointWaiterTcb) t) t _ hG2 hReady hI2
  refine ⟨?_, (hW1.trans hW2).trans (waitFrame.of_objectsAgreeOffRunLinks hAg)⟩
  rw [enqueueRunnableOnCore_preserves_projection ctx observer _ _ t hTh.2 hTh.1 hI2, hP2, hP1]

/-- **Cancelling a notification's head waiter is invisible when the
notification, the head and the head's successor are hidden**: it rewrites the
notification, detaches the head and restores it. -/
theorem cancelIpcBlocking_notificationHead_hidden (ctx : LabelingContext)
    (observer : IfObserver) {s : SystemState} {x : SeLe4n.ObjId} {ntfn : Notification}
    {t : SeLe4n.ThreadId} {tcb : TCB} (hInv : s.objects.invExt)
    (hN : s.getNotification? x = some ntfn) (hH : ntfn.waitHead = some t)
    (hT : s.getTcb? t = some tcb) (hB : tcb.ipcState = .blockedOnNotification x)
    (hX : objectObservable ctx observer x = false)
    (hTh : objectObservable ctx observer t.toObjId = false)
    (hNext : ∀ b, tcb.ntfnNext = some b → objectObservable ctx observer b.toObjId = false) :
    projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking s t tcb) =
      projectState ctx observer s := by
  obtain ⟨st1, n', hS1, -, hI1, hO1, -, -, hEq⟩ :=
    cancelIpcBlocking_notificationHead_eq hN hH hT hB hInv
  rw [hEq]
  have hA : hiddenObjectsWrite ctx observer s st1 :=
    ⟨hS1, fun k hk => hO1 k (fun e => by rw [← e, hX] at hk; cases hk)⟩
  have hI2 := (detachNtfnHead_linksRewritten st1 t tcb.ntfnNext hI1).2.1
  rw [(hiddenObjectsWrite.updateTcb _ t _ hI2 hTh).projection,
    detachNtfnHead_preserves_projection ctx observer st1 t _ hTh hNext hI1, hA.projection]

/-- **A notification waiter's cancel is invisible when the notification and its
waiters are hidden**: it rewrites the notification, detaches the head, whose
successor waits on the notification too, restores the head and wakes it. -/
theorem notificationWaiterCancel_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (x : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : s.objects.invExt) (hNC : notificationWaiterConsistent s)
    (hX : objectObservable ctx observer x = false) (hW : waitersHidden ctx observer x s)
    (hN : s.getNotification? x = some ntfn) (hH : ntfn.waitHead = some t)
    (hT : s.getTcb? t = some tcb) (hC : notificationWaiterCancellable s x t tcb = true) :
    projectState ctx observer
        (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) =
        projectState ctx observer s ∧
      waitFrame s (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) := by
  obtain ⟨hNotRes, hB, -, -, -⟩ := notificationWaiterCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
  have hLookup : lookupTcb s t = some tcb :=
    lookupTcb_of_objects_of_not_reserved s t tcb hTo hNotRes
  have hTh := hW t tcb hTo (Or.inr (Or.inr (Or.inr hB)))
  have hNext : ∀ b, tcb.ntfnNext = some b → objectObservable ctx observer b.toObjId = false := by
    intro b hb
    obtain ⟨_, -, -, -, hNextH⟩ := hNC.2.1 t tcb x hTo hB
    obtain ⟨-, tb, hTb, hbB, -⟩ := hNextH b hb
    exact (hW b tb hTb (Or.inr (Or.inr (Or.inr hbB)))).1
  have hP1 := cancelIpcBlocking_notificationHead_hidden ctx observer hInv hN hH hT hB hX hTh.1 hNext
  have hFr := FinaliseFrame.notificationCancel s t tcb x hInv hB
  have hI1 := hFr.invExt
  have hW1 : waitFrame s (Lifecycle.Suspend.cancelIpcBlocking s t tcb) := by
    have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    have hReach := removeFromNotificationWaitQueue_reach s t hInv
    rw [hEq]
    exact (waitFrame.of_ntfnUnlinkReach hReach).trans
      (waitFrame.updateTcb _ t hReach.1 (fun _ => Or.inl (by simp)))
  obtain ⟨y, hY⟩ : ∃ y, (Lifecycle.Suspend.cancelIpcBlocking s t tcb).objects[t.toObjId]? =
      some (.tcb y) := by
    rcases hFr.kind t.toObjId with e | ⟨pre, post, hPre, hPost, hTy, -⟩
    · exact ⟨tcb, e.trans hTo⟩
    · rw [hTo] at hPre; cases hPre
      cases post <;> simp [KernelObject.objectType] at hTy
      exact ⟨_, hPost⟩
  have hYr := cancelIpcBlocking_victim_ready s t tcb hInv hLookup y hY
  have hAg := enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready _
    (determineTargetCore (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) t y
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hY) hYr hI1
  unfold wakeCancelledWaiter
  refine ⟨?_, hW1.trans (waitFrame.of_objectsAgreeOffRunLinks hAg)⟩
  rw [enqueueRunnableOnCore_preserves_projection ctx observer _ _ t hTh.2 hTh.1 hI1, hP1]

/-- **The unbind is invisible when the notification and its bound thread are
hidden**: it rewrites the two, each keeping its kind. -/
theorem storeUnbindNotification_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (x : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId)
    (hInv : s.objects.invExt) (hN : s.getNotification? x = some ntfn)
    (hX : objectObservable ctx observer x = false)
    (hT : objectObservable ctx observer t.toObjId = false) :
    projectState ctx observer (storeUnbindNotification s t x) = projectState ctx observer s ∧
      waitFrame s (storeUnbindNotification s t x) := by
  have hNo := (SystemState.getNotification?_eq_some_iff s x ntfn).mp hN
  have hI1 := SystemState.updateTcb_preserves_objects_invExt s t
    (fun y => { y with boundNotificationCode := 0 }) hInv
  have hK1 : (s.updateTcb t (fun y => { y with boundNotificationCode := 0 })).objects[x]? =
      some (.notification ntfn) := by
    by_cases e : t.toObjId = x
    · cases hG : s.getTcb? t with
      | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact hNo
      | some y =>
        have := (SystemState.getTcb?_eq_some_iff s t y).mp hG
        rw [e, hNo] at this; cases this
    · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv]; exact hNo
  unfold storeUnbindNotification
  refine ⟨?_, (waitFrame.updateTcb s t (f := fun y => { y with boundNotificationCode := 0 }) hInv
    (fun _ => Or.inr rfl)).trans
    (waitFrame.modifyObject_nonTcb _ x hI1 ?_ ?_)⟩
  · rw [(hiddenObjectsWrite.modifyObject _ x _ hI1 hX).projection,
      (hiddenObjectsWrite.updateTcb s t _ hInv hT).projection]
  · intro o ho u
    cases o with
    | notification m => exact fun h => KernelObject.noConfusion h
    | _ => exact ho u
  · intro u h; rw [hK1] at h; cases h

-- ============================================================================
-- §3a  A thread's and a scheduling context's finalisation steps
-- ============================================================================

/-- **A reservation unbind is invisible when the context and the thread are
hidden**: it rewrites the two, purges a replenish entry and raises reschedule
flags, none of which the projection reads. -/
theorem cancelBoundDonationOnCore_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s s' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB} {c : CoreId}
    {scId : SeLe4n.SchedContextId} (hInv : s.objects.invExt)
    (hB : tcb.schedContextBinding = .bound scId)
    (hSc : objectObservable ctx observer scId.toObjId = false)
    (hT : objectObservable ctx observer tid.toObjId = false)
    (h : cancelBoundDonationOnCore s tid tcb c = .ok s') :
    projectState ctx observer s' = projectState ctx observer s := by
  unfold cancelBoundDonationOnCore at h
  simp only [hB, Except.ok.injEq] at h
  subst h
  rw [markKeyChangeFrom_extract_frame (projectState ctx observer) _ _ _
    (fun s c => markReschedulePendingOnCore_preserves_projection ctx observer s c)]
  have hI1 := SystemState.updateSchedContext_preserves_objects_invExt s scId
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
  have hA : hiddenObjectsWrite ctx observer s (s.updateSchedContext scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) :=
    ⟨SystemState.updateSchedContext_eq_objects_update _ _ _, fun k hk =>
      SystemState.updateSchedContext_objects_ne _ _ _ k
        (fun e => by rw [← e, hSc] at hk; cases hk) hInv⟩
  refine Eq.trans (hiddenObjectsWrite.updateTcb (ctx := ctx) (observer := observer) _ tid _ ?_
    hT).projection ?_
  · exact hI1
  · exact hA.projection

/-- **A finalised thread's notification unbind is invisible** when the thread
and its notification are hidden; it keeps the thread's IPC state, its
notification and endpoint queue links and its scheduling binding. -/
theorem finaliseThreadUnbindNotification_hidden (ctx : LabelingContext)
    (observer : IfObserver) {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hTh : objectObservable ctx observer tid.toObjId = false)
    (hBn : t.boundNotificationCode ≠ 0 →
      objectObservable ctx observer ⟨t.boundNotificationCode - 1⟩ = false) :
    projectState ctx observer (finaliseThreadUnbindNotification s tid) =
        projectState ctx observer s ∧
      (finaliseThreadUnbindNotification s tid).objects.invExt ∧
      ∃ t', (finaliseThreadUnbindNotification s tid).getTcb? tid = some t' ∧
        t'.ipcState = t.ipcState ∧ t'.ntfnPrev = t.ntfnPrev ∧ t'.ntfnNext = t.ntfnNext ∧
        t'.queuePPrev = t.queuePPrev ∧ t'.queueNext = t.queueNext ∧
        t'.scBindingScCode = t.scBindingScCode ∧
        t'.scBindingOwnerCode = t.scBindingOwnerCode ∧ t'.replyObjectCode = t.replyObjectCode := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  have hc : boundNotificationCodeOf s tid = t.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hT]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  next h0 =>
  split
  · next n hN =>
    split
    · have hne : t.boundNotificationCode ≠ 0 := by simpa using h0
      obtain ⟨hP, -⟩ := storeUnbindNotification_hidden ctx observer s _ n tid hInv hN
        (hBn hne) hTh
      have hNo := (SystemState.getNotification?_eq_some_iff s _ n).mp hN
      have hI1 := SystemState.updateTcb_preserves_objects_invExt s tid
        (fun y => { y with boundNotificationCode := 0 }) hInv
      refine ⟨hP, modifyObject_preserves_objects_invExt hI1,
        { t with boundNotificationCode := 0 }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hNe : (⟨t.boundNotificationCode - 1⟩ : SeLe4n.ObjId) ≠ tid.toObjId := by
        intro e; rw [e, hTo] at hNo; cases hNo
      refine (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_
      unfold storeUnbindNotification
      rw [modifyObject_objects_getElem hI1, if_neg hNe]
      exact updateTcb_objects_self_of_tcb _ hInv hTo
    · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What a finalised thread's notification unbind leaves of the object
table**: the index is the pre-state's, and each slot is the pre-state's, or a
thread rewritten as a thread, or a notification rewritten as a notification. -/
theorem finaliseThreadUnbindNotification_slots {s : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t) :
    (finaliseThreadUnbindNotification s tid).objectIndexSet = s.objectIndexSet ∧
    ∀ k : SeLe4n.ObjId, (finaliseThreadUnbindNotification s tid).objects[k]? = s.objects[k]? ∨
      (∃ a b, s.objects[k]? = some (KernelObject.tcb a) ∧
        (finaliseThreadUnbindNotification s tid).objects[k]? = some (KernelObject.tcb b)) ∨
      (∃ a b, s.objects[k]? = some (KernelObject.notification a) ∧
        (finaliseThreadUnbindNotification s tid).objects[k]? = some (KernelObject.notification b)) := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  have hc : boundNotificationCodeOf s tid = t.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hT]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  split
  · next n hN =>
    split
    · have hNo := (SystemState.getNotification?_eq_some_iff s _ n).mp hN
      have hI1 := SystemState.updateTcb_preserves_objects_invExt s tid
        (fun y => { y with boundNotificationCode := 0 }) hInv
      refine ⟨SystemState.updateTcb_objectIndexSet s tid _, fun k => ?_⟩
      unfold storeUnbindNotification
      rw [modifyObject_objects_getElem hI1]
      by_cases hk : (⟨t.boundNotificationCode - 1⟩ : SeLe4n.ObjId) = k
      · subst hk
        have hNe : tid.toObjId ≠ ⟨t.boundNotificationCode - 1⟩ := by
          intro e; rw [← e, hTo] at hNo; cases hNo
        rw [if_pos rfl, SystemState.updateTcb_objects_ne _ _ _ _ hNe hInv, hNo]
        exact Or.inr (Or.inr ⟨n, _, rfl, rfl⟩)
      · rw [if_neg hk]
        by_cases hk' : tid.toObjId = k
        · subst hk'
          rw [updateTcb_objects_self_of_tcb _ hInv hTo]
          exact Or.inr (Or.inl ⟨t, _, hTo, rfl⟩)
        · exact Or.inl (SystemState.updateTcb_objects_ne _ _ _ _ hk' hInv)
    · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · exact ⟨rfl, fun _ => Or.inl rfl⟩

/-- ...so the unbind keeps the index complete and every reply in its slot. -/
theorem finaliseThreadUnbindNotification_index {s : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hIdx : SeLe4n.Model.objectIndexSetComplete s) :
    SeLe4n.Model.objectIndexSetComplete (finaliseThreadUnbindNotification s tid) ∧
    ∀ (k : SeLe4n.ObjId) (r : Reply),
      (finaliseThreadUnbindNotification s tid).objects[k]? = some (KernelObject.reply r) →
      s.objects[k]? = some (KernelObject.reply r) := by
  obtain ⟨hS, hK⟩ := finaliseThreadUnbindNotification_slots hInv hT
  refine ⟨fun k hk => ?_, fun k r hk => ?_⟩
  · rw [hS]
    refine hIdx k ?_
    rcases hK k with e | ⟨a, -, ha, -⟩ | ⟨a, -, ha, -⟩
    · rwa [← e]
    all_goals (rw [ha]; exact fun h => by cases h)
  · rcases hK k with e | ⟨-, b, -, hb⟩ | ⟨-, b, -, hb⟩
    · rwa [← e]
    all_goals (rw [hb] at hk; cases hk)

/-- **A finalised thread's reservation unbind is invisible** when the thread and
its scheduling context are hidden; it keeps the thread's IPC state and its
notification successor (`cancelBoundDonationOnCore_reachFieldFrame`). -/
theorem finaliseThreadUnbindSchedContext_hidden (ctx : LabelingContext)
    (observer : IfObserver) {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hTh : objectObservable ctx observer tid.toObjId = false)
    (hSc : t.scBindingScCode ≠ 0 → objectObservable ctx observer
      (⟨t.scBindingScCode - 1⟩ : SeLe4n.SchedContextId).toObjId = false) :
    projectState ctx observer (finaliseThreadUnbindSchedContext s tid) =
        projectState ctx observer s ∧
      (finaliseThreadUnbindSchedContext s tid).objects.invExt ∧
      ∃ t', (finaliseThreadUnbindSchedContext s tid).getTcb? tid = some t' ∧
        t'.ipcState = t.ipcState ∧ t'.ntfnNext = t.ntfnNext := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  unfold finaliseThreadUnbindSchedContext
  rw [hT]; dsimp only
  split <;> (split; rotate_left; exact ⟨rfl, hInv, t, hT, rfl, rfl⟩)
  all_goals
    rename_i hG
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.false_eq_true,
      and_false] at hG
  obtain ⟨⟨⟨⟨hS, hO⟩, -⟩, -⟩, -⟩ := hG
  · split
    · next st' hOk =>
      rw [cancelDonationArmOnCore_of_codes s tid hS hO] at hOk
      have hP := cancelBoundDonationOnCore_hidden ctx observer hInv
        (schedContextBinding_of_codes hS hO) (hSc hS) hTh hOk
      have hI := cancelBoundDonationOnCore_preserves_objects_invExt s st' tid t _ hInv hOk
      obtain ⟨tx, hx, hk⟩ := (cancelBoundDonationOnCore_reachFieldFrame hInv hOk).fwd _ t hTo
      exact ⟨hP, hI, tx, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hx, hk.1, hk.2.2.1⟩
    · exact ⟨rfl, hInv, t, hT, rfl, rfl⟩

/-- **Relinking a leaving waiter's notification neighbours is invisible** when
the neighbours are hidden: it rewrites each of them in its slot. -/
theorem unlinkNtfnNeighbours_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (prev next : Option SeLe4n.ThreadId) (hInv : s.objects.invExt)
    (hP : ∀ p, prev = some p → objectObservable ctx observer p.toObjId = false)
    (hN : ∀ b, next = some b → objectObservable ctx observer b.toObjId = false) :
    hiddenObjectsWrite ctx observer s (unlinkNtfnNeighbours s prev next) ∧
      (unlinkNtfnNeighbours s prev next).objects.invExt := by
  have hStep : ∀ (s : SystemState) (u : SeLe4n.ThreadId) (f : TCB → TCB), s.objects.invExt →
      objectObservable ctx observer u.toObjId = false →
      hiddenObjectsWrite ctx observer s (s.updateTcb u f) ∧ (s.updateTcb u f).objects.invExt :=
    fun s u f hi hu => ⟨hiddenObjectsWrite.updateTcb s u f hi hu,
      SystemState.updateTcb_preserves_objects_invExt s u f hi⟩
  unfold unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => exact ⟨⟨rfl, fun _ _ => rfl⟩, hInv⟩
    | some b => exact hStep s b _ hInv (hN b rfl)
  | some p =>
    obtain ⟨h1, i1⟩ := hStep s p (fun t => { t with
      ntfnNextCode := SeLe4n.ThreadId.optCode next }) hInv (hP p rfl)
    cases next with
    | none => exact ⟨h1, i1⟩
    | some b =>
      obtain ⟨h2, i2⟩ := hStep _ b (fun t => { t with
        ntfnPrevCode := SeLe4n.ThreadId.optCode (some p) }) i1 (hN b rfl)
      exact ⟨h1.trans h2, i2⟩

/-- **A notification waiter's in-place cancel is invisible** when the
notification, the waiter and its neighbours are hidden: it rewrites the
notification, clears the waiter's links, relinks the neighbours and restores the
waiter, each in its slot. -/
theorem storeNotificationBlockedCancelled_hidden (ctx : LabelingContext)
    (observer : IfObserver) (s : SystemState) (x : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (isHead : Bool) (prev next : Option SeLe4n.ThreadId) (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer x = false)
    (hT : objectObservable ctx observer t.toObjId = false)
    (hP : ∀ p, prev = some p → objectObservable ctx observer p.toObjId = false)
    (hN : ∀ b, next = some b → objectObservable ctx observer b.toObjId = false) :
    projectState ctx observer (storeNotificationBlockedCancelled s x t isHead prev next) =
        projectState ctx observer s ∧
      (storeNotificationBlockedCancelled s x t isHead prev next).objects.invExt := by
  have h1 := hiddenObjectsWrite.modifyObject (ctx := ctx) (observer := observer) s x
    (cancelledNotificationObject isHead prev next) hInv hX
  have i1 : (s.modifyObject x (cancelledNotificationObject isHead prev next)).objects.invExt :=
    modifyObject_preserves_objects_invExt hInv
  have h2 : hiddenObjectsWrite ctx observer _
      (clearNtfnLinks (s.modifyObject x (cancelledNotificationObject isHead prev next)) t) :=
    hiddenObjectsWrite.updateTcb _ t _ i1 hT
  have i2 : (clearNtfnLinks (s.modifyObject x (cancelledNotificationObject isHead prev next))
      t).objects.invExt := SystemState.updateTcb_preserves_objects_invExt _ t _ i1
  obtain ⟨h3, i3⟩ := unlinkNtfnNeighbours_hidden ctx observer _ (if isHead then none else prev)
    next i2 (fun p hp => by cases isHead <;> simp at hp; exact hP p hp) hN
  unfold storeNotificationBlockedCancelled Lifecycle.Suspend.restoreToReadyCancelled
    Lifecycle.Suspend.restoreToReadyStaging
  exact ⟨((h1.trans h2).trans (h3.trans (hiddenObjectsWrite.updateTcb _ t _ i3 hT))).projection,
    SystemState.updateTcb_preserves_objects_invExt _ t _ i3⟩

/-- **An endpoint-blocked thread's in-place cancel is invisible** when the
endpoint, the thread and its queue neighbours are hidden: the removal is the
specification's (`queueRemove_inPlace`), whose splice writes only those
(`endpointQueueRemoveDual_preserves_projection_and_invExt`), and the IPC end
rewrites the thread. -/
theorem storeEndpointBlockedCancelled_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint)
    (tcb : TCB) (hInv : s.objects.invExt) (hE : s.getEndpoint? e = some ep)
    (hT : s.getTcb? t = some tcb) (hC : endpointBlockedCancellable s e q t ep tcb = true)
    (hX : objectObservable ctx observer e = false)
    (hTh : objectObservable ctx observer t.toObjId = false)
    (hP : ∀ p, tcb.queuePPrev = some (.tcbNext p) → objectObservable ctx observer p.toObjId = false)
    (hN : ∀ b, tcb.queueNext = some b → objectObservable ctx observer b.toObjId = false) :
    projectState ctx observer (storeEndpointBlockedCancelled s e q t ep tcb) =
        projectState ctx observer s ∧
      (storeEndpointBlockedCancelled s e q t ep tcb).objects.invExt := by
  obtain ⟨-, -, hG, -⟩ := endpointBlockedCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
  obtain ⟨hRm, -⟩ := queueRemove_inPlace s e q t ep tcb
    ((SystemState.getEndpoint?_eq_some_iff s e ep).mp hE) hTo hG
  have hHigh : endpointSpliceHigh ctx observer s e t := ⟨hX, hTh, fun y hy => by
    have hy' := (lookupTcb_some_objects s t y hy).symm.trans hTo
    cases hy'
    exact ⟨hP, hN⟩⟩
  obtain ⟨hP1, hI1⟩ := endpointQueueRemoveDual_preserves_projection_and_invExt ctx observer s _
    e q t hHigh hInv hRm
  unfold storeEndpointBlockedCancelled
  exact ⟨(hiddenObjectsWrite.updateTcb _ t _ hI1 hTh).projection.trans hP1,
    SystemState.updateTcb_preserves_objects_invExt _ t _ hI1⟩

/-- **A store agreement off the reply-waiter links keeps every binding.** -/
theorem sameSchedContextBindings_of_objectsAgreeOffReplyLinks {a b : SystemState}
    (h : SystemState.objectsAgreeOffReplyLinks b a) : sameSchedContextBindings a b := by
  intro tid t' hb
  have e := h tid.toObjId
  rw [hb] at e
  cases ha : a.objects[tid.toObjId]? with
  | none => rw [ha] at e; cases e
  | some o =>
    rw [ha] at e
    obtain ⟨t, rfl, ht⟩ := KernelObject.withoutReplyLinks_eq_tcb (Option.some.inj e).symm
    exact ⟨t, rfl, by
      have := congrArg TCB.schedContextBinding ht
      simpa [TCB.withoutReplyLinks, TCB.schedContextBinding] using this⟩

/-- **...and so does one off the run-queue links.** -/
theorem sameSchedContextBindings_of_objectsAgreeOffRunLinks {a b : SystemState}
    (h : b.objectsAgreeOffRunLinks a) : sameSchedContextBindings a b := by
  intro tid t' hb
  obtain ⟨t, ha, ht⟩ := KernelObject.map_withoutRunLinks_tcb (h tid.toObjId).symm hb
  exact ⟨t, ha, TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding ht⟩

/-- **...and so does the priority-inheritance walk**, which rewrites boosts and
run-queue links alone. -/
theorem propagatePipChainCrossCore_sameSchedContextBindings' (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    sameSchedContextBindings st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 := by
  intro t t' h
  obtain ⟨t0, p, h0, e⟩ :=
    PriorityInheritance.propagatePipChainCrossCore_tcb_backward st tid ec fuel hInv t t' h
  exact ⟨t0, h0, (TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding e).symm⟩

/-- Two threads with one binding hold the same context code. -/
theorem TCB.scBindingScCode_eq_of_binding {a b : TCB}
    (h : a.schedContextBinding = b.schedContextBinding) : a.scBindingScCode = b.scBindingScCode := by
  have e := congrArg SchedContextBinding.scCode h
  unfold TCB.schedContextBinding at e
  rwa [SchedContextBinding.scCode_ofCodes, SchedContextBinding.scCode_ofCodes] at e

/-- A thread a donation return rebinds holds that context's code. -/
theorem TCB.scBindingScCode_of_returnBinding {a : TCB} {s : SeLe4n.SchedContextId}
    {n : Option SeLe4n.ThreadId} (h : a.schedContextBinding = donationReturnBinding s n) :
    a.scBindingScCode = s.val + 1 := by
  have e := congrArg SchedContextBinding.scCode h
  unfold TCB.schedContextBinding at e
  rw [SchedContextBinding.scCode_ofCodes] at e
  rw [e]; cases n <;> rfl

/-- **What a reply-blocked caller's cancel leaves in the caller's binding**: the
object table stays well formed, and the caller keeps its context code, or — a
head reply popped — holds the context the reply headed. -/
theorem finaliseReplyCallerCancel_binding {s : SystemState} {c : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? c = some t) :
    (finaliseReplyCallerCancel s c t).objects.invExt ∧
    ∃ t', (finaliseReplyCallerCancel s c t).getTcb? c = some t' ∧
      (t'.scBindingScCode = t.scBindingScCode ∨
        ∃ (r : Reply) (sc : SeLe4n.SchedContextId),
          s.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) ∧
          r.next = some (.head sc) ∧ t'.scBindingScCode = sc.val + 1) := by
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  unfold finaliseReplyCallerCancel
  split
  rotate_left
  · exact ⟨hInv, t, hT, Or.inl rfl⟩
  next r hX =>
  split
  rotate_left
  · exact ⟨hInv, t, hT, Or.inl rfl⟩
  next hG =>
  simp only [Bool.and_eq_true, beq_iff_eq] at hG
  obtain ⟨⟨-, hF⟩, -⟩ := hG
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
  rw [finaliseReplyCancel_eq hX hF]
  -- The stages of the reply arm, each well formed.
  let s0 := Lifecycle.Suspend.returnDonationToCancelledCaller s c t
  have hI0 : s0.objects.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt s c t hInv
  let s1 := spliceThreadReplyFrameOut s0 t
  have hI1 : s1.objects.invExt := spliceThreadReplyFrameOut_preserves_objects_invExt s0 t hI0
  let s2 := Lifecycle.Suspend.restoreToReadyCancelled s1 c
  have hI2 : s2.objects.invExt := restoreToReadyCancelled_preserves_objects_invExt s1 c hI1
  let s3 := Lifecycle.Suspend.consumeReplyLink s2 c t
  have hI3 : s3.objects.invExt := Lifecycle.Suspend.consumeReplyLink_preserves_objects_invExt s2 c t hI2
  have hArm : Lifecycle.Suspend.cancelIpcBlocking s c t = s3.unlinkReplyWaiterOpt c t.blockingServer? := by
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  have hSame : sameSchedContextBindings s0 (Lifecycle.Suspend.cancelIpcBlocking s c t) := by
    rw [hArm]
    exact ((spliceThreadReplyFrameOut_sameSchedContextBindings s0 t hI0).trans
      (restoreToReadyStaging_sameSchedContextBindings s1 c _ hI1)).trans
      ((consumeReplyLink_sameSchedContextBindings s2 c t hI2).trans
        (sameSchedContextBindings_of_objectsAgreeOffReplyLinks
          (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks s3 c _)))
  have hIc := Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s c t hInv
  have hIR := cancelIpcBlockingReclaimed_objects_invExt c t s hIc
  have hSameR : sameSchedContextBindings s0 (cancelIpcBlockingReclaimed c t s) :=
    hSame.trans (sameSchedContextBindings_of_objectsAgreeOffRunLinks
      (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks c t s))
  have hSameV : sameSchedContextBindings s0
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
    unfold finaliseReplyRevert
    cases t.blockingServer? with
    | none => exact hSameR
    | some sv => exact hSameR.trans (propagatePipChainCrossCore_sameSchedContextBindings' _ _ _ _ hIR)
  refine ⟨(FinaliseFrame.finaliseReplyRevert _ _ hIR).invExt, ?_⟩
  -- The caller is still a thread after the cancel.
  obtain ⟨tv, hTv⟩ : ∃ tv, (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s)
      t.blockingServer?).getTcb? c = some tv := by
    obtain ⟨t1, hL1, -⟩ := Lifecycle.Suspend.cancelIpcBlocking_tcb_lookup s c t c.toObjId t hInv hTo
    have hS1 : ((Lifecycle.Suspend.cancelIpcBlocking s c t).getTcb? c).isSome := by
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hL1]; rfl
    have hS2 : ((cancelIpcBlockingReclaimed c t s).getTcb? c).isSome := by
      have hM := cancelIpcBlockingReclaimed_getTcb? c t s c
      rw [← Option.isSome_map (f := TCB.withoutRunLinks), hM, Option.isSome_map]; exact hS1
    have hS3 : ((finaliseReplyRevert (cancelIpcBlockingReclaimed c t s)
        t.blockingServer?).getTcb? c).isSome := by
      unfold finaliseReplyRevert
      cases t.blockingServer? with
      | none => exact hS2
      | some sv =>
        exact PriorityInheritance.propagatePipChainCrossCore_getTcb?_isSome _ _ _ _ hIR c hS2
    exact Option.isSome_iff_exists.mp hS3
  refine ⟨tv, hTv, ?_⟩
  obtain ⟨t0, h0, e0⟩ := hSameV c tv ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTv)
  rcases replyCallerFinalisable_cases hX hF with ⟨-, hD⟩ |
      ⟨s', sc, hd, ht, hN, -, -, -, hHd, hBd, hC, hD⟩
  · have hR : s0 = s := by
      show Lifecycle.Suspend.returnDonationToCancelledCaller s c t = s
      unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
    rw [hR, hTo] at h0
    cases h0
    exact Or.inl (TCB.scBindingScCode_eq_of_binding e0.symm)
  · obtain ⟨n, st', -, hPop, hEq⟩ := replyHeadPop_commits hInv hT hD hC
    have hNe : c ≠ hd := returnDonatedSchedContext_ok_recipient_ne_server s st' hd s' c n ht hHd
      (by rw [hBd]; exact fun h => by cases h) hPop
    have h0' : st'.objects[c.toObjId]? = some (.tcb t0) := by
      rw [← hEq]; exact h0
    have hCases := (returnDonatedSchedContext_tcb_binding_cases s st' hd s' c n hInv hPop
      c.toObjId t0 h0').2.1
      (fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)) rfl
    refine Or.inr ⟨r, s', hX, hN, ?_⟩
    rw [← TCB.scBindingScCode_eq_of_binding e0]
    exact TCB.scBindingScCode_of_returnBinding hCases

/-- **The thread a reply-blocked caller's cancel deschedules is the server it
waits on**: the cancel's admission (`replyHeadHeldByServer`) reads the context a
head reply heads as held by that server, so a hidden caller whose servers are
hidden (`hBlockingChainHigh`) has its holder hidden. -/
theorem descheduledHolderHigh_of_replyHeadHeldByServer (ctx : LabelingContext)
    (observer : IfObserver) {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hX : s.getObject? x = some (.reply r))
    (hF : replyCallerFinalisable s x r c t = true) (hHS : replyHeadHeldByServer s r t = true)
    (hT : s.getTcb? c = some t)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hHigh : threadObservable ctx observer c = false) :
    descheduledHolderHigh ctx observer s c t := by
  intro holder hW
  obtain ⟨scId, hRes⟩ := cancelUnboundHolder?_donation s _ c t holder hW
  rcases replyCallerFinalisable_cases hX hF with ⟨-, hD⟩ |
      ⟨s', sc, hd, ht, hN, hSc, -, hBt, -, -, -, hD⟩
  · rw [hD] at hRes; cases hRes
  · rw [hD] at hRes
    cases hRes
    unfold replyHeadHeldByServer at hHS
    simp only [hN, hSc, beq_iff_eq] at hHS
    have hS : t.blockingServer? = some holder := by
      rw [← ofOptCode_replyCallerServerCode, ← hHS]; exact hBt
    exact hBlockingChainHigh s c holder hHigh (by
      unfold PriorityInheritance.blockingServer; rw [hT]; exact hS)

/-- **A reply-blocked caller's cancel is invisible** when the caller is hidden
and so is every server on its blocking chain: the cancel's reply arm, with the
donation return a head reply makes (`cancelIpcBlocking_blockedOnReply_preserves_projection`),
the replenishment migration (`cancelIpcBlockingMigrated_preserves_projection`),
the deschedule of the thread the context is taken from — the caller's server,
which the admission reads (`descheduledHolderHigh_of_replyHeadHeldByServer`) —
and the boost revert along the caller's blocking chain
(`propagatePipChainCrossCore_preserves_projection`). -/
theorem finaliseReplyCallerCancel_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete s) (hSet : s.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hT : s.getTcb? c = some t) (hHigh : threadObservable ctx observer c = false) :
    projectState ctx observer (finaliseReplyCallerCancel s c t) = projectState ctx observer s := by
  unfold finaliseReplyCallerCancel
  split
  · next r hX =>
    split
    · next hG =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hG
      obtain ⟨⟨-, hF⟩, hHS⟩ := hG
      obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
      have hP1 := cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer s
        c t ep rt hB hValid hHigh hInv hIdx hSet
      have hPR : projectState ctx observer (cancelIpcBlockingReclaimed c t s) =
          projectState ctx observer s := by
        unfold cancelIpcBlockingReclaimed
        rw [descheduleUnboundHolder_preserves_projection ctx observer s _ t
          (descheduledHolderHigh_of_replyHeadHeldByServer ctx observer hX hF hHS hT
            hBlockingChainHigh hHigh), cancelIpcBlockingMigrated_preserves_projection, hP1]
      have hI1 := cancelIpcBlockingReclaimed_objects_invExt c t s
        (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s c t hInv)
      rw [finaliseReplyCancel_eq hX hF]
      unfold finaliseReplyRevert
      cases hS : t.blockingServer? with
      | none => exact hPR
      | some sv =>
        rw [propagatePipChainCrossCore_preserves_projection ctx observer
          (hValid.coherenceImpliesObjectHigh observer) hBlockingChainHigh _ sv _ _
          (hBlockingChainHigh s _ sv hHigh (by
            unfold PriorityInheritance.blockingServer; rw [hT]; exact hS)) hI1]
        exact hPR
    · rfl
  · rfl

/-- **A finalised thread's IPC cancel is invisible** when the thread, the
object it is blocked on and its queue neighbours are hidden, and — a caller
blocked on a reply — every server on the thread's blocking chain is hidden
(`finaliseReplyCallerCancel_hidden`). -/
theorem finaliseThreadCancel_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete s) (hSet : s.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hThr : threadObservable ctx observer tid = false)
    (hTh : objectObservable ctx observer tid.toObjId = false)
    (hW : ∀ x, waitsOn x t.ipcState → objectObservable ctx observer x = false)
    (hNp : ∀ b, t.ntfnPrev = some b → objectObservable ctx observer b.toObjId = false)
    (hNx : ∀ b, t.ntfnNext = some b → objectObservable ctx observer b.toObjId = false)
    (hQp : ∀ p, t.queuePPrev = some (.tcbNext p) → objectObservable ctx observer p.toObjId = false)
    (hQn : ∀ b, t.queueNext = some b → objectObservable ctx observer b.toObjId = false) :
    projectState ctx observer (finaliseThreadCancel s tid) = projectState ctx observer s ∧
      (finaliseThreadCancel s tid).objects.invExt := by
  have hEnd : ∀ e q, objectObservable ctx observer e = false →
      projectState ctx observer (cancelEndpointBlocked s e q tid t) = projectState ctx observer s ∧
        (cancelEndpointBlocked s e q tid t).objects.invExt := by
    intro e q hX
    unfold cancelEndpointBlocked
    split
    · next ep hE =>
      split
      · next hC =>
        exact storeEndpointBlockedCancelled_hidden ctx observer s e q tid ep t hInv hE hT
          hC hX hTh hQp hQn
      · exact ⟨rfl, hInv⟩
    · exact ⟨rfl, hInv⟩
  unfold finaliseThreadCancel
  rw [hT]; dsimp only
  split
  · next n hB =>
    split
    · next ntfn hNt =>
      split
      · rw [cancelIpcBlocking_notification_inPlace hNt hT hB]
        exact storeNotificationBlockedCancelled_hidden ctx observer s n tid _ _ _ hInv
          (hW n (by simp [waitsOn, hB])) hTh hNp hNx
      · exact ⟨rfl, hInv⟩
    · exact ⟨rfl, hInv⟩
  · next e hB => exact hEnd e true (hW e (by simp [waitsOn, hB]))
  · next e hB => exact hEnd e false (hW e (by simp [waitsOn, hB]))
  · next e hB => exact hEnd e false (hW e (by simp [waitsOn, hB]))
  · exact ⟨finaliseReplyCallerCancel_hidden ctx observer hInv hValid hIdx hSet
      hBlockingChainHigh hT hThr, (finaliseReplyCallerCancel_binding hInv hT).1⟩
  · exact ⟨rfl, hInv⟩

/-- **A finalised thread's IPC cancel keeps its scheduling binding**: the
notification cancel rewrites notification links and restores the thread
(`removeFromNotificationWaitQueue_reach`); the endpoint cancel takes the thread
off its queue (`QueueRemoveFrame.removed_tcb`) and ends its IPC; a reply-blocked
caller's cancel that pops a head reply hands it the context the reply headed
(`finaliseReplyCallerCancel_binding`). -/
theorem finaliseThreadCancel_scBinding {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t) :
    ∃ t', (finaliseThreadCancel s tid).getTcb? tid = some t' ∧
      (t'.scBindingScCode = t.scBindingScCode ∨
        ∃ (r : Reply) (sc : SeLe4n.SchedContextId),
          s.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) ∧
          r.next = some (.head sc) ∧ t'.scBindingScCode = sc.val + 1) := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  have hEnd : ∀ e q, ∃ t', (cancelEndpointBlocked s e q tid t).getTcb? tid = some t' ∧
      t'.scBindingScCode = t.scBindingScCode := by
    intro e q
    unfold cancelEndpointBlocked
    split
    · next ep hE =>
      split
      · next hC =>
        obtain ⟨-, -, hG, -⟩ := endpointBlockedCancellable_parts hC
        obtain ⟨hRm, hFr⟩ := queueRemove_inPlace s e q tid ep t
          ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hTo hG
        have hI1 := endpointQueueRemoveDual_preserves_objects_invExt s _ e q tid hInv hRm
        unfold storeEndpointBlockedCancelled
        rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, hFr.removed_tcb]
        exact ⟨_, rfl, rfl⟩
      · exact ⟨t, hT, rfl⟩
    · exact ⟨t, hT, rfl⟩
  unfold finaliseThreadCancel
  rw [hT]; dsimp only
  split
  · next n hB =>
    split
    · split
      · have hEq : Lifecycle.Suspend.cancelIpcBlocking s tid t =
            Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s tid) tid := by
          unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
        have hReach := removeFromNotificationWaitQueue_reach s tid hInv
        rw [hEq]
        unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
        rw [SystemState.updateTcb_getTcb?_self _ _ _ hReach.1]
        rcases hReach.2 tid.toObjId with e | ⟨_, _, hO, -, -⟩ | ⟨t0, t1, h0, h1, np, nn, hR⟩
        · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (e.trans hTo)]
          exact ⟨_, rfl, Or.inl rfl⟩
        · rw [hTo] at hO; cases hO
        · rw [hTo] at h0; cases h0
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h1, hR]
          exact ⟨_, rfl, Or.inl rfl⟩
      · exact ⟨t, hT, Or.inl rfl⟩
    · exact ⟨t, hT, Or.inl rfl⟩
  · obtain ⟨t', h1, h2⟩ := hEnd _ true; exact ⟨t', h1, Or.inl h2⟩
  · obtain ⟨t', h1, h2⟩ := hEnd _ false; exact ⟨t', h1, Or.inl h2⟩
  · obtain ⟨t', h1, h2⟩ := hEnd _ false; exact ⟨t', h1, Or.inl h2⟩
  · exact (finaliseReplyCallerCancel_binding hInv hT).2
  · exact ⟨t, hT, Or.inl rfl⟩

/-- **A finalised thread's suspend keeps the object table well formed and the
thread's scheduling binding**: the deschedule rewrites run-queue links alone,
and the mark the thread state. -/
theorem finaliseThreadSuspend_scBinding {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t) :
    (finaliseThreadSuspend s tid).objects.invExt ∧
      ∃ t', (finaliseThreadSuspend s tid).getTcb? tid = some t' ∧
        t'.scBindingScCode = t.scBindingScCode := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  unfold finaliseThreadSuspend
  rw [hT]; dsimp only
  split
  · have hD : (descheduleAtPlacement s tid).objects.invExt :=
      (FinaliseFrame.descheduleAt s tid (placedCoreOf? s tid) hInv).invExt
    obtain ⟨t1, h1, e⟩ := KernelObject.map_withoutRunLinks_tcb
      (descheduleAtPlacement_objectsAgreeOffRunLinks s tid tid.toObjId) hTo
    refine ⟨(FinaliseFrame.suspend s tid hInv).invExt, ?_⟩
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hD, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h1]
    exact ⟨_, rfl, TCB.proj_eq_of_withoutRunLinks_eq TCB.scBindingScCode e⟩
  · exact ⟨hInv, t, hT, rfl⟩

/-- **A finalised thread's suspend is invisible** when the thread is hidden, as
an object and as a thread: the deschedule wherever it is placed
(`descheduleAtPlacement_preserves_projection`), then the mark. -/
theorem finaliseThreadSuspend_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (tid : SeLe4n.ThreadId) (hInv : s.objects.invExt)
    (hTh : objectObservable ctx observer tid.toObjId = false)
    (hThr : threadObservable ctx observer tid = false) :
    projectState ctx observer (finaliseThreadSuspend s tid) = projectState ctx observer s := by
  unfold finaliseThreadSuspend
  split
  · split
    · have hD : (descheduleAtPlacement s tid).objects.invExt :=
        (FinaliseFrame.descheduleAt s tid (placedCoreOf? s tid) hInv).invExt
      rw [(hiddenObjectsWrite.updateTcb _ tid _ hD hTh).projection,
        descheduleAtPlacement_preserves_projection ctx observer s tid hThr]
    · rfl
  · rfl

/-- **The release of every core's hold on a thread is invisible**: no
projection reads a core's FP/SIMD owner or its resident. -/
theorem finaliseThreadReleaseCores_hidden (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (tid : SeLe4n.ThreadId) :
    projectState ctx observer (finaliseThreadReleaseCores s tid) = projectState ctx observer s := by
  have hHolds : ∀ fo rc, projectState ctx observer
      { s with machine := { s.machine with fpOwner := fo, residentCode := rc } } =
      projectState ctx observer s := fun _ _ => rfl
  rw [onlyObjectsSchedulerCoreHoldsDiffer.releaseCores s tid, finaliseThreadReleaseCores_objects,
    finaliseThreadReleaseCores_scheduler]
  exact hHolds _ _

/-- **What a thread's finalisation writes, besides the thread**: its bound
notification, its scheduling context, the notification or endpoint it waits on
and its neighbours in that queue, and the context its reply heads (a head reply's
pop hands that context back to it, and the reservation unbind then writes it) —
each hidden — and, since the suspend takes it
off whichever core holds it, the thread is hidden as a thread too. -/
def threadFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ t, st.getObject? x = some (.tcb t) →
    (t.boundNotificationCode ≠ 0 →
      objectObservable ctx observer ⟨t.boundNotificationCode - 1⟩ = false) ∧
    (t.scBindingScCode ≠ 0 → objectObservable ctx observer
      (⟨t.scBindingScCode - 1⟩ : SeLe4n.SchedContextId).toObjId = false) ∧
    (∀ y, waitsOn y t.ipcState → objectObservable ctx observer y = false) ∧
    (∀ b, t.ntfnPrev = some b → objectObservable ctx observer b.toObjId = false) ∧
    (∀ b, t.ntfnNext = some b → objectObservable ctx observer b.toObjId = false) ∧
    (∀ p, t.queuePPrev = some (.tcbNext p) → objectObservable ctx observer p.toObjId = false) ∧
    (∀ b, t.queueNext = some b → objectObservable ctx observer b.toObjId = false) ∧
    (∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) → r.next = some (.head sc) →
      objectObservable ctx observer sc.toObjId = false) ∧
    threadObservable ctx observer ⟨x.val⟩ = false

/-- **What a scheduling context's finalisation writes, besides the context**:
the thread bound to it — hidden, as an object (the unbind rewrites it) and as a
thread (the deschedule takes it off its core's run queue). -/
def schedContextFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ sc, st.getObject? x = some (.schedContext sc) → sc.boundThreadCode ≠ 0 →
    objectObservable ctx observer (⟨sc.boundThreadCode - 1⟩ : SeLe4n.ThreadId).toObjId = false ∧
      threadObservable ctx observer ⟨sc.boundThreadCode - 1⟩ = false

/-- ...so what the context's finalisation writes stays hidden after it: the
context in its slot is the pre-state's. -/
theorem schedContextFinaliseHidden.deschedule {ctx : LabelingContext} {observer : IfObserver}
    {st : SystemState} {x : SeLe4n.ObjId} (hH : schedContextFinaliseHidden ctx observer st x) :
    schedContextFinaliseHidden ctx observer (finaliseSchedContextDeschedule st x) x := by
  intro sc hO h0
  simp only [SystemState.getObject?_eq_getElem] at hO
  exact hH sc ((finaliseSchedContextDeschedule_objectsAgreeOffRunLinks st x).get_schedContext_iff.mp hO) h0

/-- **A scheduling context's deschedule of its holder is invisible** when the
thread bound to it is hidden as a thread (`descheduleAtPlacement_preserves_projection`). -/
theorem finaliseSchedContextDeschedule_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hH : schedContextFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseSchedContextDeschedule st x) = projectState ctx observer st := by
  unfold finaliseSchedContextDeschedule
  split
  · next sc hO =>
    split
    · rfl
    · next h0 =>
      dsimp only
      split
      · split
        · exact descheduleAtPlacement_preserves_projection ctx observer st _
            (hH sc hO (by simpa using h0)).2
        · rfl
      · rfl
  · rfl

/-- **A thread's finalisation is invisible** when the thread and what its steps
write are hidden: the unbinds keep what the cancel reads, and the destroy
cleanup is the identity on the finalised thread (`finaliseThread_eq`). -/
theorem finaliseThread_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st) (hSet : st.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hX : objectObservable ctx observer x = false) (hH : threadFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseThread x st) = projectState ctx observer st := by
  rw [finaliseThread_eq]
  split
  · next hAd =>
    obtain ⟨t, hO⟩ : ∃ t, st.getObject? x = some (.tcb t) := by
      unfold threadFinaliseAdmitted at hAd
      split at hAd
      · exact ⟨_, ‹_›⟩
      · cases hAd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ := hH t hO
    have hT : st.getTcb? ⟨x.val⟩ = some t :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO
    obtain ⟨hP1, hI1, t1, hT1, e1, e2, e3, e4, e5, e6, -, e7⟩ :=
      finaliseThreadUnbindNotification_hidden ctx observer hInv hT hX h1
    obtain ⟨hIdx1, hRp⟩ := finaliseThreadUnbindNotification_index hInv hT hIdx
    have hSet1 : (finaliseThreadUnbindNotification st ⟨x.val⟩).objectIndexSet.table.invExt := by
      rw [(finaliseThreadUnbindNotification_slots hInv hT).1]; exact hSet
    obtain ⟨hP2, hI2⟩ := finaliseThreadCancel_hidden ctx observer hI1 hT1 hValid hIdx1 hSet1
      hBlockingChainHigh h8 hX
      (by rw [e1]; exact h3) (by rw [e2]; exact h4) (by rw [e3]; exact h5)
      (by rw [e4]; exact h6) (by rw [e5]; exact h7)
    obtain ⟨t2, hT2, f2⟩ := finaliseThreadCancel_scBinding hI1 hT1
    have hP3 := finaliseThreadSuspend_hidden ctx observer _ ⟨x.val⟩ hI2 hX h8
    obtain ⟨hI3, t3, hT3, f3⟩ := finaliseThreadSuspend_scBinding hI2 hT2
    have hT4 := (finaliseThreadReleaseCores_getTcb? _ ⟨x.val⟩ ⟨x.val⟩).trans hT3
    have hI4 := (FinaliseFrame.releaseCores _ ⟨x.val⟩ hI3).invExt
    have hSc : t3.scBindingScCode ≠ 0 → objectObservable ctx observer
        (⟨t3.scBindingScCode - 1⟩ : SeLe4n.SchedContextId).toObjId = false := by
      rw [f3]
      rcases f2 with f2 | ⟨r, sc, hR, hN, f2⟩
      · rw [f2, e6]; exact h2
      · intro _
        rw [f2, Nat.add_sub_cancel]
        rw [e7, SystemState.getObject?_eq_getElem] at hR
        exact h9 r sc (by rw [SystemState.getObject?_eq_getElem]; exact hRp _ r hR) hN
    obtain ⟨hP5, -, -⟩ := finaliseThreadUnbindSchedContext_hidden ctx observer hI4 hT4 hX hSc
    rw [hP5, finaliseThreadReleaseCores_hidden, hP3, hP2, hP1]
  · rfl

namespace hiddenObjectsWrite

variable {ctx : LabelingContext} {observer : IfObserver}

/-- A scheduling context rewritten in its hidden slot. -/
theorem updateSchedContext (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer scId.toObjId = false) :
    hiddenObjectsWrite ctx observer s (s.updateSchedContext scId f) :=
  ⟨SystemState.updateSchedContext_eq_objects_update _ _ _, fun k hk =>
    SystemState.updateSchedContext_objects_ne _ _ _ k
      (fun e => by rw [← e, hX] at hk; cases hk) hInv⟩

end hiddenObjectsWrite

/-- **A scheduling context's release of its holder is invisible** when the
context and the thread bound to it are hidden: the reservation unbind on the
holder's owner-cleared view (`cancelBoundDonationOnCore_hidden`). -/
theorem finaliseSchedContextUnbind_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hX : objectObservable ctx observer x = false)
    (hH : schedContextFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseSchedContextUnbind st x) = projectState ctx observer st := by
  unfold finaliseSchedContextUnbind
  split
  · next sc hO =>
    split
    · rfl
    · next h0 =>
      dsimp only
      split
      · next t hT =>
        split
        · next hG =>
          simp only [beq_iff_eq] at hG
          split
          · next st' hOk =>
            exact cancelBoundDonationOnCore_hidden ctx observer hInv
              (schedContextBinding_ownerCleared hG) hX (hH sc hO (by simpa using h0)).1 hOk
          · rfl
        · rfl
      · rfl
  · rfl

/-- **A scheduling context's reply-stack unlink is invisible** when the context
is hidden: the head reply's upward link is a stack link, which the projection
strips (`projectKernelObject_reply_next_invariant`), and the context's head is
written in its hidden slot. -/
theorem finaliseSchedContextUnstack_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {x : SeLe4n.ObjId} (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer x = false)
    (hIdx : ∀ (rid : SeLe4n.ReplyId) (r : Reply), s.getReply? rid = some r →
      s.objectIndexSet.contains rid.toObjId = true) :
    projectState ctx observer (finaliseSchedContextUnstack s x) = projectState ctx observer s := by
  unfold finaliseSchedContextUnstack
  split
  · split
    · next rid _ =>
      split
      · next r hR =>
        split
        · split
          · next s1 hS =>
            have hI1 := storeObject_preserves_objects_invExt s s1 _ _ hInv hS
            rw [(hiddenObjectsWrite.updateSchedContext s1 ⟨x.val⟩ _ hI1 hX).projection]
            exact storeObject_projectionStable_preserves_projection ctx observer s s1 _ _ (.reply r)
              ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
              (projectKernelObject_reply_next_invariant ctx observer r none) (hIdx rid r hR) hInv hS
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- **A scheduling context's finalisation is invisible** when the context and
the thread bound to it are hidden: the holder's deschedule
(`finaliseSchedContextDeschedule_hidden`), the release (`finaliseSchedContextUnbind_hidden`),
the reply-stack unlink (`finaliseSchedContextUnstack_hidden`, at the replies the
pre-state indexes — the release writes a thread and a context only, and no
index), and the destroy cleanup, the identity on the finalised context
(`finaliseSchedContext_eq`). -/
theorem finaliseSchedContext_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st)
    (hX : objectObservable ctx observer x = false)
    (hH : schedContextFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseSchedContext x st) = projectState ctx observer st := by
  rw [finaliseSchedContext_eq]
  split
  · have hD : FinaliseFrame st (finaliseSchedContextDeschedule st x) :=
      finaliseSchedContextDeschedule_closed (FinaliseFrame st)
        (fun s t _ h _ _ _ _ => h.trans (FinaliseFrame.descheduleAt s t _ h.invExt)) st x
        (.refl hInv)
    have hF : FinaliseFrame st (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) := by
      refine finaliseSchedContextUnbind_closed (FinaliseFrame st) ?_ _ x hD
      exact FinaliseFrame.releaseStep st
    have hSet : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).objectIndexSet =
        st.objectIndexSet := by
      rw [hF.rest]
    refine (finaliseSchedContextUnstack_hidden ctx observer hF.invExt hX
      (fun rid r hR => ?_)).trans ((finaliseSchedContextUnbind_hidden ctx observer hD.invExt hX
        hH.deschedule).trans (finaliseSchedContextDeschedule_hidden ctx observer hH))
    rw [hSet]
    refine hIdx _ (fun e => ?_)
    have hR' := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
    rcases hF.write rid.toObjId with h | ⟨pre, _, hp, _⟩
    · rw [h, e] at hR'; cases hR'
    · rw [hp] at e; cases e
  · rfl

/-- **What a reply's finalisation writes, besides the reply**: the caller waiting
on it, or the receiver that has it stashed — hidden.  The cancel's other writes
are stack links and reply-waiter links, which the projection strips, and the
boost revert's are threads on the caller's blocking chain, which
`hBlockingChainHigh` puts out of sight. -/
def replyFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  (∀ r, st.getObject? x = some (.reply r) → r.callerCode ≠ 0 →
    threadObservable ctx observer (⟨r.callerCode - 1⟩ : SeLe4n.ThreadId) = false) ∧
  (∀ (tid : SeLe4n.ThreadId) (t : TCB), st.getTcb? tid = some t →
    t.pendingReceiveReplyCode = x.val + 1 → objectObservable ctx observer tid.toObjId = false)

/-- **A stashed reply's unlink is invisible** when the receiver holding it is
hidden: one rewrite in that receiver's slot (`hiddenObjectsWrite.updateTcb`). -/
theorem finaliseReplyUnstash_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} {r : Reply} (hInv : st.objects.invExt)
    (hH : ∀ (tid : SeLe4n.ThreadId) (t : TCB), st.getTcb? tid = some t →
      t.pendingReceiveReplyCode = x.val + 1 → objectObservable ctx observer tid.toObjId = false) :
    projectState ctx observer (finaliseReplyUnstash st x r) = projectState ctx observer st := by
  unfold finaliseReplyUnstash
  split
  · rfl
  · split
    · next t hT =>
      split
      · next hC =>
        exact (hiddenObjectsWrite.updateTcb st _ _ hInv (hH _ t hT (by simpa using hC))).projection
      · rfl
    · rfl

/-- **A reply's finalisation is invisible** when the caller waiting on it is
hidden: the cancel's reply arm, with the donation return a head reply makes
(`cancelIpcBlocking_blockedOnReply_preserves_projection`), the replenishment
migration (`cancelIpcBlockingMigrated_preserves_projection`), the deschedule of
the thread the context is taken from, hidden since the hidden caller lent it the
context (`descheduledHolderHigh_of_donationOwnerFlowsToHolder`, from the loan the
admission reads: `finaliseReply_armPremises`), the boost revert along the
caller's blocking chain (`propagatePipChainCrossCore_preserves_projection`), and
the caller's suspend (`finaliseThreadSuspend_hidden`); a stashed reply's unlink
(`finaliseReplyUnstash_hidden`). -/
theorem finaliseReply_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hFull : ipcInvariantFull st) (hLc : lentContextHeadsLenderFrame st)
    (hFlow : donationOwnerFlowsToHolder ctx st)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st) (hSet : st.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hH : replyFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseReply x st) = projectState ctx observer st := by
  unfold finaliseReply
  split
  · next r hX =>
    split
    · exact finaliseReplyUnstash_hidden ctx observer hInv hH.2
    · next h0 =>
      dsimp only
      split
      · next t hT =>
        split
        · next hF =>
          obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
          obtain ⟨-, hOwed, -, -⟩ := finaliseReply_armPremises hInv hFull hLc hX hT hF
          have hHigh := hH.1 r hX (by simpa using h0)
          have hP1 := cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer st
            ⟨r.callerCode - 1⟩ t ep rt hB hValid hHigh hInv hIdx hSet
          have hPR : projectState ctx observer (cancelIpcBlockingReclaimed ⟨r.callerCode - 1⟩ t st) =
              projectState ctx observer st := by
            unfold cancelIpcBlockingReclaimed
            rw [descheduleUnboundHolder_preserves_projection ctx observer st _ t
              (descheduledHolderHigh_of_donationOwnerFlowsToHolder ctx observer st _ t hFlow hOwed
                hHigh), cancelIpcBlockingMigrated_preserves_projection, hP1]
          have hI1 := cancelIpcBlockingReclaimed_objects_invExt ⟨r.callerCode - 1⟩ t st
            (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st ⟨r.callerCode - 1⟩ t hInv)
          have hRev : projectState ctx observer
              (finaliseReplyRevert (cancelIpcBlockingReclaimed ⟨r.callerCode - 1⟩ t st)
                t.blockingServer?) =
              projectState ctx observer (cancelIpcBlockingReclaimed ⟨r.callerCode - 1⟩ t st) := by
            unfold finaliseReplyRevert
            cases hS : t.blockingServer? with
            | none => rfl
            | some sv =>
              exact propagatePipChainCrossCore_preserves_projection ctx observer
                (hValid.coherenceImpliesObjectHigh observer) hBlockingChainHigh _ sv _ _
                (hBlockingChainHigh st _ sv hHigh (by
                  unfold PriorityInheritance.blockingServer; rw [hT]; exact hS)) hI1
          rw [finaliseReplyCancel_eq hX hF, finaliseThreadSuspend_hidden ctx observer _ _
            (FinaliseFrame.finaliseReplyRevert _ _ hI1).invExt
            (hValid.coherenceImpliesObjectHigh observer _ hHigh) hHigh, hRev, hPR]
        · rfl
      · rfl
  · rfl

-- ============================================================================
-- §4  The finalisation and the retire after it
-- ============================================================================

/-- **The finalisation is invisible when what it touches is hidden**: the object
it finalises, every thread waiting on that object, and the thread a
notification is bound to.  Each walk step keeps the step invariant
(`finaliseStepInvariant`), the hidden waiters (`waitFrame.waitersHidden`) and
the projection; the unbind runs first, on the pre-state itself. -/
theorem finaliseFinalObject_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (target : Nat) {st : SystemState} (h : ipcReachable st)
    (hLc : lentContextHeadsLenderFrame st)
    (hx : target ≠ 0 → objectObservable ctx observer (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hW : target ≠ 0 → waitersHidden ctx observer (SeLe4n.ObjId.ofNat (target - 1)) st)
    (hBd : target ≠ 0 → ∀ (ntfn : Notification) (t : SeLe4n.ThreadId),
      st.getNotification? (SeLe4n.ObjId.ofNat (target - 1)) = some ntfn →
      ntfn.boundTCB = some t → objectObservable ctx observer t.toObjId = false)
    (hTF : target ≠ 0 → threadFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hSF : target ≠ 0 →
      schedContextFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hRF : target ≠ 0 → replyFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hFlow : donationOwnerFlowsToHolder ctx st)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st) (hSet : st.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false) :
    projectState ctx observer (finaliseFinalObject target st) = projectState ctx observer st := by
  unfold finaliseFinalObject
  split
  · rfl
  next h0 =>
  dsimp only
  generalize SeLe4n.ObjId.ofNat (target - 1) = x at hx hW hBd hTF hSF hRF ⊢
  have hX := hx h0
  let P : SystemState → Prop := fun s => finaliseStepInvariant s ∧
    waitersHidden ctx observer x s ∧ projectState ctx observer s = projectState ctx observer st
  have hEp : ∀ (q : Bool) (fuel : Nat) (s : SystemState), P s → P (cancelEndpointQueue x q fuel s) :=
    fun q => cancelEndpointQueue_closed P x q (fun s ep t tcb hP hE hH hT hC =>
      have r := hP.1.endpointCancel hE hH hT hC
      have p := storeEndpointWaiterCancelled_hidden ctx observer s x q ep t tcb hP.1.2.1 hP.1.1 hX
        hP.2.1 hE hH hT hC
      ⟨r.1, p.2.waitersHidden hP.2.1, p.1.trans hP.2.2⟩)
  have hNt : ∀ (fuel : Nat) (s : SystemState), P s → P (cancelNotificationQueue x fuel s) :=
    cancelNotificationQueue_closed P x (fun s n t tcb hP hN hH hT hC =>
      have r := hP.1.notificationCancel hN hT hC
      have p := notificationWaiterCancel_hidden ctx observer s x n t tcb hP.1.2.1 hP.1.2.2.1 hX
        hP.2.1 hN hH hT hC
      ⟨r.1, p.2.waitersHidden hP.2.1, p.1.trans hP.2.2⟩)
  have hP0 : P st := ⟨.of_ipcReachable h hLc, hW h0, rfl⟩
  split
  · split
    · exact (hEp true _ _ (hEp false _ _ hP0)).2.2
    · refine (hNt _ _ ?_).2.2
      unfold unbindMaybeNotification
      split
      · next n hN =>
        split
        · next t hB =>
          split
          · next hC =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hC
            have r := hP0.1.unbind hN hC.1 hC.2
            have p := storeUnbindNotification_hidden ctx observer st x n t h.2.1 hN hX
              (hBd h0 n t hN hB)
            exact ⟨r.1, p.2.waitersHidden hP0.2.1, p.1⟩
          · exact hP0
        · exact hP0
      · exact hP0
    · exact finaliseThread_hidden ctx observer h.2.1 hValid hIdx hSet hBlockingChainHigh hX
        (hTF h0)
    · exact finaliseSchedContext_hidden ctx observer h.2.1 hIdx hX (hSF h0)
    · exact finaliseReply_hidden ctx observer h.2.1 h.1 hLc hFlow hValid hIdx hSet hBlockingChainHigh
        (hRF h0)
    · rfl
  · rfl

/-- **The retire after the finalisation is invisible** when the finalisation is
(`finaliseFinalObject_preserves_projection`) and the retire is
(`retireFinalObject_preserves_projection`): the finalisation records no untyped
child, so the untypeds recording the object are the pre-state's. -/
theorem retireFinalisedObject_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (ec : CoreId) (target recorder : Nat) {st : SystemState}
    (h : ipcReachable st) (hLc : lentContextHeadsLenderFrame st)
    (hx : target ≠ 0 → objectObservable ctx observer (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hW : target ≠ 0 → waitersHidden ctx observer (SeLe4n.ObjId.ofNat (target - 1)) st)
    (hBd : target ≠ 0 → ∀ (ntfn : Notification) (t : SeLe4n.ThreadId),
      st.getNotification? (SeLe4n.ObjId.ofNat (target - 1)) = some ntfn →
      ntfn.boundTCB = some t → objectObservable ctx observer t.toObjId = false)
    (hTF : target ≠ 0 → threadFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hSF : target ≠ 0 →
      schedContextFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hRF : target ≠ 0 → replyFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hFlow : donationOwnerFlowsToHolder ctx st)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st) (hSet : st.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hU : target ≠ 0 → ∀ w, untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = true →
      objectObservable ctx observer w = false)
    (hR : recorder ≠ 0 →
      objectObservable ctx observer (SeLe4n.ObjId.ofNat (recorder - 1)) = false) :
    projectState ctx observer (retireFinalisedObject ec target recorder st) =
      projectState ctx observer st := by
  have hF := finaliseFinalObject_frame target st h.2.1
  have hUt := hF.getUntyped?
  unfold retireFinalisedObject
  rw [retireFinalObject_preserves_projection ctx observer ec target recorder hF.invExt hx
    (fun h0 w hw => hU h0 w (by unfold untypedRecordsChild at hw ⊢; rw [hUt] at hw; exact hw)) hR,
    finaliseFinalObject_preserves_projection ctx observer target h hLc hx hW hBd hTF hSF hRF hFlow
      hValid hIdx hSet hBlockingChainHigh]

end SeLe4n.Kernel
