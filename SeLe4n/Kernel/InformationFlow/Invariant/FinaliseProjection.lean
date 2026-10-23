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
  have hP1 : projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking s t tcb) =
      projectState ctx observer s := by
    obtain ⟨st1, n', hS1, -, hI1, hO1, -, -, hEq⟩ :=
      cancelIpcBlocking_notificationHead_eq hN hH hT hB hInv
    rw [hEq]
    have hA : hiddenObjectsWrite ctx observer s st1 :=
      ⟨hS1, fun k hk => hO1 k (fun e => by rw [← e, hX] at hk; cases hk)⟩
    have hI2 := (detachNtfnHead_linksRewritten st1 t tcb.ntfnNext hI1).2.1
    rw [(hiddenObjectsWrite.updateTcb _ t _ hI2 hTh.1).projection,
      detachNtfnHead_preserves_projection ctx observer st1 t _ hTh.1 hNext hI1, hA.projection]
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
      ntfn.boundTCB = some t → objectObservable ctx observer t.toObjId = false) :
    projectState ctx observer (finaliseFinalObject target st) = projectState ctx observer st := by
  unfold finaliseFinalObject
  split
  · rfl
  next h0 =>
  dsimp only
  generalize SeLe4n.ObjId.ofNat (target - 1) = x at hx hW hBd ⊢
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
    finaliseFinalObject_preserves_projection ctx observer target h hx hW hBd]

end SeLe4n.Kernel
