/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 23 — the finalisation's projection theorem, staged with the reachable-state surface it composes (`IPC.Invariant.CancelAllReachability`).
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability
import SeLe4n.Kernel.IPC.CrossCore.CancellationNI

/-!
# The finalisation is invisible when what it touches is hidden

WS-ZA ZA5.4 part 23: a final delete's finalisation (`finaliseFinalObject`)
writes the object it finalises, the threads waiting on that object, and the run
queues those threads are woken into; the unbind writes the thread the
notification is bound to.  When the observer sees none of them, the projection
is unchanged (`finaliseFinalObject_preserves_projection`), and so is the retire
after it (`retireFinalisedObject_preserves_projection`).

WS-ZA ZA5.4 part 24: a thread's finalisation (`finaliseThread`) writes the
thread, its bound notification, its scheduling context, the notification it
waits on and the waiter after it; a scheduling context's (`finaliseSchedContext`)
writes the context and its bound thread.  The replenish entry and the reschedule
flags they write are outside the projection.  When the observer sees none of the
objects (`threadFinaliseHidden`, `schedContextFinaliseHidden`), the projection is
unchanged (`finaliseThread_hidden`, `finaliseSchedContext_hidden`).

WS-ZA ZA5.4 part 25: a scheduling context's finalisation also releases a holder
it lends to and unlinks the head of its reply stack, a stack link the projection
strips; a reply's (`finaliseReply`) cancels its waiting caller, reverts the boost
the caller lent along its blocking chain, and suspends it.  When the caller is
hidden (`replyFinaliseHidden`) and the blocking chain of a hidden thread is
hidden (`hBlockingChainHigh`), the projection is unchanged
(`finaliseReply_hidden`).

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
notification successor and its scheduling binding. -/
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
        t'.ipcState = t.ipcState ∧ t'.ntfnNext = t.ntfnNext ∧
        t'.scBindingScCode = t.scBindingScCode ∧
        t'.scBindingOwnerCode = t.scBindingOwnerCode := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  have hc : boundNotificationCodeOf s tid = t.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hT]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl⟩
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
        { t with boundNotificationCode := 0 }, ?_, rfl, rfl, rfl, rfl⟩
      have hNe : (⟨t.boundNotificationCode - 1⟩ : SeLe4n.ObjId) ≠ tid.toObjId := by
        intro e; rw [e, hTo] at hNo; cases hNo
      refine (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_
      unfold storeUnbindNotification
      rw [modifyObject_objects_getElem hI1, if_neg hNe]
      exact updateTcb_objects_self_of_tcb _ hInv hTo
    · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, hInv, t, hT, rfl, rfl, rfl, rfl⟩

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
  obtain ⟨⟨⟨⟨⟨hS, hO⟩, -⟩, -⟩, -⟩, -⟩ := hG
  · split
    · next st' hOk =>
      rw [cancelDonationArmOnCore_of_codes s tid hS hO] at hOk
      have hP := cancelBoundDonationOnCore_hidden ctx observer hInv
        (schedContextBinding_of_codes hS hO) (hSc hS) hTh hOk
      have hI := cancelBoundDonationOnCore_preserves_objects_invExt s st' tid t _ hInv hOk
      obtain ⟨tx, hx, hk⟩ := (cancelBoundDonationOnCore_reachFieldFrame hInv hOk).fwd _ t hTo
      exact ⟨hP, hI, tx, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hx, hk.1, hk.2.2.1⟩
    · exact ⟨rfl, hInv, t, hT, rfl, rfl⟩

/-- **A finalised thread's IPC cancel is invisible** when the thread, the
notification it waits on and the waiter after it are hidden. -/
theorem finaliseThreadCancel_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hTh : objectObservable ctx observer tid.toObjId = false)
    (hN : ∀ n, t.ipcState = .blockedOnNotification n → objectObservable ctx observer n = false)
    (hNx : ∀ b, t.ntfnNext = some b → objectObservable ctx observer b.toObjId = false) :
    projectState ctx observer (finaliseThreadCancel s tid) = projectState ctx observer s ∧
      (finaliseThreadCancel s tid).objects.invExt := by
  unfold finaliseThreadCancel
  rw [hT]; dsimp only
  split
  · next n hB =>
    split
    · next ntfn hNt =>
      split
      · next hC =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hC
        exact ⟨cancelIpcBlocking_notificationHead_hidden ctx observer hInv hNt hC.1 hT hB
            (hN n hB) hTh hNx,
          Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s tid t hInv⟩
      · exact ⟨rfl, hInv⟩
    · exact ⟨rfl, hInv⟩
  · exact ⟨rfl, hInv⟩

/-- **A finalised thread's notification cancel keeps its scheduling binding**:
the cancel detaches the queue head, rewriting its notification links, and
restores it to ready. -/
theorem finaliseThreadCancel_scBinding {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t) :
    ∃ t', (finaliseThreadCancel s tid).getTcb? tid = some t' ∧
      t'.scBindingScCode = t.scBindingScCode := by
  have hTo := (SystemState.getTcb?_eq_some_iff s tid t).mp hT
  unfold finaliseThreadCancel
  rw [hT]; dsimp only
  split
  · next n hB =>
    split
    · next ntfn hNt =>
      split
      · next hC =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hC
        obtain ⟨st1, n', -, hn', hI1, hOff, -, -, hEq⟩ :=
          cancelIpcBlocking_notificationHead_eq hNt hC.1 hT hB hInv
        have hNo := (SystemState.getNotification?_eq_some_iff s n ntfn).mp hNt
        have hNe : n ≠ tid.toObjId := by
          intro e; rw [e, hTo] at hNo; cases hNo
        have h1 : st1.objects[tid.toObjId]? = some (.tcb t) := (hOff _ hNe).trans hTo
        have hL := detachNtfnHead_linksRewritten st1 tid t.ntfnNext hI1
        rw [hEq, SystemState.updateTcb_getTcb?_self _ _ _ hL.2.1]
        rcases hL.2.2 tid.toObjId with e | ⟨a, b, ha, hb, np, nn, rfl⟩
        · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (e.trans h1)]
          exact ⟨_, rfl, rfl⟩
        · rw [h1] at ha; cases ha
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hb]
          exact ⟨_, rfl, rfl⟩
      · exact ⟨t, hT, rfl⟩
    · exact ⟨t, hT, rfl⟩
  · exact ⟨t, hT, rfl⟩

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
notification, its scheduling context, the notification it waits on and the
waiter after it — each hidden — and, since the suspend takes it off whichever
core holds it, the thread is hidden as a thread too. -/
def threadFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ t, st.getObject? x = some (.tcb t) →
    (t.boundNotificationCode ≠ 0 →
      objectObservable ctx observer ⟨t.boundNotificationCode - 1⟩ = false) ∧
    (t.scBindingScCode ≠ 0 → objectObservable ctx observer
      (⟨t.scBindingScCode - 1⟩ : SeLe4n.SchedContextId).toObjId = false) ∧
    (∀ n, t.ipcState = .blockedOnNotification n → objectObservable ctx observer n = false) ∧
    (∀ b, t.ntfnNext = some b → objectObservable ctx observer b.toObjId = false) ∧
    threadObservable ctx observer ⟨x.val⟩ = false

/-- **What a scheduling context's finalisation writes, besides the context**:
the thread bound to it — hidden. -/
def schedContextFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ sc, st.getObject? x = some (.schedContext sc) → sc.boundThreadCode ≠ 0 →
    objectObservable ctx observer (⟨sc.boundThreadCode - 1⟩ : SeLe4n.ThreadId).toObjId = false

/-- **A thread's finalisation is invisible** when the thread and what its steps
write are hidden: the unbinds keep what the cancel reads, and the destroy
cleanup is the identity on the finalised thread (`finaliseThread_eq`). -/
theorem finaliseThread_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
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
    obtain ⟨h1, h2, h3, h4, h5⟩ := hH t hO
    have hT : st.getTcb? ⟨x.val⟩ = some t :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO
    obtain ⟨hP1, hI1, t1, hT1, e1, e2, e3, -⟩ :=
      finaliseThreadUnbindNotification_hidden ctx observer hInv hT hX h1
    obtain ⟨hP2, hI2⟩ := finaliseThreadCancel_hidden ctx observer hI1 hT1 hX
      (by rw [e1]; exact h3) (by rw [e2]; exact h4)
    obtain ⟨t2, hT2, f2⟩ := finaliseThreadCancel_scBinding hI1 hT1
    have hP3 := finaliseThreadSuspend_hidden ctx observer _ ⟨x.val⟩ hI2 hX h5
    obtain ⟨hI3, t3, hT3, f3⟩ := finaliseThreadSuspend_scBinding hI2 hT2
    have hT4 := (finaliseThreadReleaseCores_getTcb? _ ⟨x.val⟩ ⟨x.val⟩).trans hT3
    have hI4 := (FinaliseFrame.releaseCores _ ⟨x.val⟩ hI3).invExt
    obtain ⟨hP5, -, -⟩ := finaliseThreadUnbindSchedContext_hidden ctx observer hI4 hT4 hX
      (by rw [f3, f2, e3]; exact h2)
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
          simp only [Bool.and_eq_true, beq_iff_eq] at hG
          split
          · next st' hOk =>
            exact cancelBoundDonationOnCore_hidden ctx observer hInv
              (schedContextBinding_ownerCleared hG.1.1.1) hX (hH sc hO (by simpa using h0)) hOk
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
the thread bound to it are hidden: the release (`finaliseSchedContextUnbind_hidden`),
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
  · have hF : FinaliseFrame st (finaliseSchedContextUnbind st x) := by
      refine finaliseSchedContextUnbind_closed (FinaliseFrame st) ?_ st x (.refl hInv)
      exact FinaliseFrame.releaseStep st
    have hSet : (finaliseSchedContextUnbind st x).objectIndexSet = st.objectIndexSet := by
      rw [hF.rest]
    refine (finaliseSchedContextUnstack_hidden ctx observer hF.invExt hX
      (fun rid r hR => ?_)).trans (finaliseSchedContextUnbind_hidden ctx observer hInv hX hH)
    rw [hSet]
    refine hIdx _ (fun e => ?_)
    have hR' := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
    rcases hF.write rid.toObjId with h | ⟨pre, _, hp, _⟩
    · rw [h, e] at hR'; cases hR'
    · rw [hp] at e; cases e
  · rfl

/-- **What a reply's finalisation writes, besides the reply**: the caller waiting
on it — hidden.  The cancel's other writes are stack links and reply-waiter
links, which the projection strips, and the boost revert's are threads on the
caller's blocking chain, which `hBlockingChainHigh` puts out of sight. -/
def replyFinaliseHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ r, st.getObject? x = some (.reply r) → r.callerCode ≠ 0 →
    threadObservable ctx observer (⟨r.callerCode - 1⟩ : SeLe4n.ThreadId) = false

/-- **A reply's finalisation is invisible** when the caller waiting on it is
hidden: the cancel's reply arm with no donation to return
(`cancelIpcBlocking_blockedOnReply_preserves_projection`), the boost revert along
the caller's blocking chain (`propagatePipChainCrossCore_preserves_projection`),
and the caller's suspend (`finaliseThreadSuspend_hidden`). -/
theorem finaliseReply_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
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
    · rfl
    · next h0 =>
      dsimp only
      split
      · next t hT =>
        split
        · next hF =>
          have hC : r.callerCode = (⟨r.callerCode - 1⟩ : SeLe4n.ThreadId).val + 1 := by
            simp only [beq_iff_eq] at h0; show _ = _ - 1 + 1; omega
          obtain ⟨-, -, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -, -, hD⟩ :=
            replyCallerFinalisable_parts hX hC hF
          have hHigh := hH r hX (by simpa using h0)
          have hP1 := cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer st
            ⟨r.callerCode - 1⟩ t ep rt hB hValid hHigh hInv hIdx hSet
            (fun scId holder e => by rw [hD] at e; cases e)
          have hI1 := Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st
            ⟨r.callerCode - 1⟩ t hInv
          have hRev : projectState ctx observer
              (finaliseReplyRevert (Lifecycle.Suspend.cancelIpcBlocking st ⟨r.callerCode - 1⟩ t)
                t.blockingServer?) =
              projectState ctx observer
                (Lifecycle.Suspend.cancelIpcBlocking st ⟨r.callerCode - 1⟩ t) := by
            unfold finaliseReplyRevert
            cases hS : t.blockingServer? with
            | none => rfl
            | some sv =>
              exact propagatePipChainCrossCore_preserves_projection ctx observer
                (hValid.coherenceImpliesObjectHigh observer) hBlockingChainHigh _ sv _ _
                (hBlockingChainHigh st _ sv hHigh (by
                  unfold PriorityInheritance.blockingServer; rw [hT]; exact hS)) hI1
          rw [finaliseThreadSuspend_hidden ctx observer _ _
            (FinaliseFrame.finaliseReplyRevert _ _ hI1).invExt
            (hValid.coherenceImpliesObjectHigh observer _ hHigh) hHigh, hRev, hP1]
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
    (hx : target ≠ 0 → objectObservable ctx observer (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hW : target ≠ 0 → waitersHidden ctx observer (SeLe4n.ObjId.ofNat (target - 1)) st)
    (hBd : target ≠ 0 → ∀ (ntfn : Notification) (t : SeLe4n.ThreadId),
      st.getNotification? (SeLe4n.ObjId.ofNat (target - 1)) = some ntfn →
      ntfn.boundTCB = some t → objectObservable ctx observer t.toObjId = false)
    (hTF : target ≠ 0 → threadFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hSF : target ≠ 0 →
      schedContextFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hRF : target ≠ 0 → replyFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
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
      have r := hP.1.notificationCancel hN hH hT hC
      have p := notificationWaiterCancel_hidden ctx observer s x n t tcb hP.1.2.1 hP.1.2.2.1 hX
        hP.2.1 hN hH hT hC
      ⟨r.1, p.2.waitersHidden hP.2.1, p.1.trans hP.2.2⟩)
  have hP0 : P st := ⟨.of_ipcReachable h, hW h0, rfl⟩
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
    · exact finaliseThread_hidden ctx observer h.2.1 hX (hTF h0)
    · exact finaliseSchedContext_hidden ctx observer h.2.1 hIdx hX (hSF h0)
    · exact finaliseReply_hidden ctx observer h.2.1 hValid hIdx hSet hBlockingChainHigh (hRF h0)
    · rfl
  · rfl

/-- **The retire after the finalisation is invisible** when the finalisation is
(`finaliseFinalObject_preserves_projection`) and the retire is
(`retireFinalObject_preserves_projection`): the finalisation records no untyped
child, so the untypeds recording the object are the pre-state's. -/
theorem retireFinalisedObject_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (ec : CoreId) (target recorder : Nat) {st : SystemState}
    (h : ipcReachable st)
    (hx : target ≠ 0 → objectObservable ctx observer (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hW : target ≠ 0 → waitersHidden ctx observer (SeLe4n.ObjId.ofNat (target - 1)) st)
    (hBd : target ≠ 0 → ∀ (ntfn : Notification) (t : SeLe4n.ThreadId),
      st.getNotification? (SeLe4n.ObjId.ofNat (target - 1)) = some ntfn →
      ntfn.boundTCB = some t → objectObservable ctx observer t.toObjId = false)
    (hTF : target ≠ 0 → threadFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hSF : target ≠ 0 →
      schedContextFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
    (hRF : target ≠ 0 → replyFinaliseHidden ctx observer st (SeLe4n.ObjId.ofNat (target - 1)))
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
    finaliseFinalObject_preserves_projection ctx observer target h hx hW hBd hTF hSF hRF hValid
      hIdx hSet hBlockingChainHigh]

end SeLe4n.Kernel
