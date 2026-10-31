/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 23 — the finalisation's projection theorem, staged with the reachable-state surface it composes (`IPC.Invariant.CancelAllReachability`).
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability
import SeLe4n.Kernel.IPC.CrossCore.CancellationNI
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignalNI
import SeLe4n.Kernel.Scheduler.ActivateThread

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

/-- A scheduling context rewritten in its hidden slot. -/
theorem updateSchedContext (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer scId.toObjId = false) :
    hiddenObjectsWrite ctx observer s (s.updateSchedContext scId f) :=
  ⟨SystemState.updateSchedContext_eq_objects_update _ _ _, fun k hk =>
    SystemState.updateSchedContext_objects_ne _ _ _ k
      (fun e => by rw [← e, hX] at hk; cases hk) hInv⟩

/-- Two hidden writes in sequence are one. -/
theorem trans {a b c : SystemState} (h₁ : hiddenObjectsWrite ctx observer a b)
    (h₂ : hiddenObjectsWrite ctx observer b c) : hiddenObjectsWrite ctx observer a c :=
  ⟨h₂.1.trans (by rw [h₁.1]), fun k hk => (h₂.2 k hk).trans (h₁.2 k hk)⟩

end hiddenObjectsWrite

/-- **A write the observer sees nothing of** (WS-ZA ZA6.6): only the object
table changes, and at every key the observer sees the projected object is the
one before — what `hiddenObjectsWrite` says, with the projection's erasures
admitted. -/
def projectedObjectsWrite (ctx : LabelingContext) (observer : IfObserver)
    (s s' : SystemState) : Prop :=
  s' = { s with objects := s'.objects } ∧
    ∀ k, objectObservable ctx observer k = true →
      (s'.objects[k]?).map (projectKernelObject ctx observer) =
        (s.objects[k]?).map (projectKernelObject ctx observer)

namespace projectedObjectsWrite

variable {ctx : LabelingContext} {observer : IfObserver}

theorem projection {s s' : SystemState} (h : projectedObjectsWrite ctx observer s s') :
    projectState ctx observer s' = projectState ctx observer s := by
  refine projectState_of_objects_only ctx observer h.1 (funext fun k => ?_)
  unfold projectObjects SystemState.getObject?
  split
  · next hk => exact h.2 k hk
  · rfl

theorem of_hidden {s s' : SystemState} (h : hiddenObjectsWrite ctx observer s s') :
    projectedObjectsWrite ctx observer s s' :=
  ⟨h.1, fun k hk => by rw [h.2 k hk]⟩

theorem refl (s : SystemState) : projectedObjectsWrite ctx observer s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem trans {a b c : SystemState} (h₁ : projectedObjectsWrite ctx observer a b)
    (h₂ : projectedObjectsWrite ctx observer b c) : projectedObjectsWrite ctx observer a c :=
  ⟨h₂.1.trans (by rw [h₁.1]), fun k hk => (h₂.2 k hk).trans (h₁.2 k hk)⟩

/-- A thread rewritten by an update the projection erases. -/
theorem updateTcb (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : s.objects.invExt)
    (hf : ∀ x, projectKernelObject ctx observer (.tcb (f x)) =
      projectKernelObject ctx observer (.tcb x)) :
    projectedObjectsWrite ctx observer s (s.updateTcb t f) := by
  refine ⟨SystemState.updateTcb_eq_objects_update s t f, fun k _ => ?_⟩
  by_cases e : t.toObjId = k
  · subst e
    cases hT : s.getTcb? t with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some x =>
      have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      rw [updateTcb_objects_self_of_tcb f hInv hO, hO]
      exact congrArg some (hf x)
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv]

/-- A context rewritten by an update the projection erases. -/
theorem updateSchedContext (s : SystemState) (c : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : s.objects.invExt)
    (hf : ∀ x, projectKernelObject ctx observer (.schedContext (f x)) =
      projectKernelObject ctx observer (.schedContext x)) :
    projectedObjectsWrite ctx observer s (s.updateSchedContext c f) := by
  refine ⟨SystemState.updateSchedContext_eq_objects_update s c f, fun k _ => ?_⟩
  by_cases e : c.toObjId = k
  · subst e
    cases hS : s.getSchedContext? c with
    | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]
    | some x =>
      have hO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS
      rw [SystemState.updateSchedContext_eq_of_some hS]
      have e : (s.objects.insert c.toObjId (.schedContext (f x)))[c.toObjId]? =
          some (.schedContext (f x)) := RobinHood.RHTable.getElem?_insert_self s.objects _ _ hInv
      show ((s.objects.insert c.toObjId _)[c.toObjId]?).map _ = _
      rw [e, hO]
      exact congrArg some (hf x)
  · rw [SystemState.updateSchedContext_objects_ne _ _ _ _ e hInv]

/-- The thread's yield link cancelled: both ends are erased by the projection. -/
theorem cancelYieldTo (s : SystemState) (t : SeLe4n.ThreadId) (hInv : s.objects.invExt) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.cancelYieldTo s t) := by
  unfold SeLe4n.Kernel.cancelYieldTo
  split
  · split
    · exact refl s
    · rename_i k _
      exact (updateSchedContext s ⟨k⟩ SeLe4n.Kernel.SchedContext.yieldCleared hInv
        (fun _ => rfl)).trans (updateTcb _ t TCB.yieldCleared
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl))
  · exact refl s

/-- The context's end of the cancel: both ends are erased by the projection. -/
theorem cancelYieldFrom (s : SystemState) (c : SeLe4n.SchedContextId)
    (hInv : s.objects.invExt) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.cancelYieldFrom s c) := by
  unfold SeLe4n.Kernel.cancelYieldFrom
  split
  · split
    · exact refl s
    · rename_i k _
      exact (updateSchedContext s c SeLe4n.Kernel.SchedContext.yieldCleared hInv
        (fun _ => rfl)).trans (updateTcb _ ⟨k⟩ TCB.yieldCleared
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl))
  · exact refl s

/-- A hidden context's consumed time handed to a thread: the count is written
at a hidden key, the registers are erased by the projection. -/
theorem setConsumed (s : SystemState) (c : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId)
    (hInv : s.objects.invExt) (hX : objectObservable ctx observer c.toObjId = false) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.setConsumed s c t) := by
  unfold SeLe4n.Kernel.setConsumed
  split
  · exact (of_hidden (hiddenObjectsWrite.updateSchedContext s c _ hInv hX)).trans (updateTcb _ t _
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (by intro; rfl))
  · exact refl s

/-- The completion of a hidden context's recorded yield. -/
theorem completeYieldFrom (s : SystemState) (c : SeLe4n.SchedContextId)
    (hInv : s.objects.invExt) (hX : objectObservable ctx observer c.toObjId = false) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.completeYieldFrom s c) := by
  unfold SeLe4n.Kernel.completeYieldFrom
  split
  · split
    · exact refl s
    · rename_i k _
      exact (setConsumed s c ⟨k⟩ hInv hX).trans
        (cancelYieldFrom _ c (SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv))
  · exact refl s

/-- A thread finalisation's completion of its held context's yield, the context
it held hidden. -/
theorem completeHeldYield (s : SystemState) (held : Nat)
    (hInv : s.objects.invExt)
    (hX : held ≠ 0 → objectObservable ctx observer
      (⟨held - 1⟩ : SeLe4n.SchedContextId).toObjId = false) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.completeHeldYield s held) := by
  unfold SeLe4n.Kernel.completeHeldYield
  split
  · exact refl s
  · rename_i k
    exact completeYieldFrom s ⟨k⟩ hInv (hX (Nat.succ_ne_zero k))

/-- WS-ZA ZA6.7: the completion of a yield to a hidden context, from the
yielder's end. -/
theorem completeYieldTo (s : SystemState) (y : SeLe4n.ThreadId) (hInv : s.objects.invExt)
    (hX : ∀ t k, s.getTcb? y = some t → t.yieldToCode = k + 1 →
      objectObservable ctx observer (⟨k⟩ : SeLe4n.SchedContextId).toObjId = false) :
    projectedObjectsWrite ctx observer s (SeLe4n.Kernel.completeYieldTo s y) := by
  unfold SeLe4n.Kernel.completeYieldTo
  split
  · rename_i t hT
    split
    · exact refl s
    · rename_i k hY
      exact (setConsumed s ⟨k⟩ y hInv (hX t k hT hY)).trans
        (cancelYieldTo _ y (SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv))
  · exact refl s

end projectedObjectsWrite

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
    {s s' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {scId : SeLe4n.SchedContextId} (hInv : s.objects.invExt)
    (hB : tcb.schedContextBinding = .bound scId)
    (hSc : objectObservable ctx observer scId.toObjId = false)
    (hT : objectObservable ctx observer tid.toObjId = false)
    (h : cancelBoundDonationOnCore s tid tcb = .ok s') :
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
  -- The purge writes contexts' release fields alone, which the projection strips.
  refine Eq.trans (hiddenObjectsWrite.updateTcb (ctx := ctx) (observer := observer) _ tid _
    (SchedContextOps.purgeReplenishment_objects_invExt _ _ hI1) hT).projection ?_
  exact (projectState_of_releaseOnlyWrite ctx observer
    (SchedContextOps.purgeReplenishment_releaseOnlyWrite _ scId)
    (SchedContextOps.purgeReplenishment_agree _ scId)).trans hA.projection

/-- **A finalised thread's notification unbind is invisible** when the thread
and its notification are hidden; it keeps the thread's IPC state, its
notification and endpoint queue links and its scheduling binding. -/
theorem finaliseThreadUnbindNotification_hidden (ctx : LabelingContext)
    (observer : IfObserver) {s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hG : notificationUnbindAdmitted s tid t = true)
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
  have hne : t.boundNotificationCode ≠ 0 := by simpa using h0
  obtain ⟨n, hN⟩ := notificationUnbindAdmitted_notification hG hne
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

/-- **What a finalised thread's notification unbind leaves of the object
table**: the index is the pre-state's, and each slot is the pre-state's, or a
thread rewritten as a thread, or a notification rewritten as a notification. -/
theorem finaliseThreadUnbindNotification_slots {s : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hG : notificationUnbindAdmitted s tid t = true) :
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
  next h0 =>
  obtain ⟨n, hN⟩ := notificationUnbindAdmitted_notification hG (by simpa using h0)
  have hNo := (SystemState.getNotification?_eq_some_iff s _ n).mp hN
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

/-- ...so the unbind keeps the index complete and every reply in its slot. -/
theorem finaliseThreadUnbindNotification_index {s : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? tid = some t)
    (hG : notificationUnbindAdmitted s tid t = true)
    (hIdx : SeLe4n.Model.objectIndexSetComplete s) :
    SeLe4n.Model.objectIndexSetComplete (finaliseThreadUnbindNotification s tid) ∧
    ∀ (k : SeLe4n.ObjId) (r : Reply),
      (finaliseThreadUnbindNotification s tid).objects[k]? = some (KernelObject.reply r) →
      s.objects[k]? = some (KernelObject.reply r) := by
  obtain ⟨hS, hK⟩ := finaliseThreadUnbindNotification_slots hInv hT hG
  refine ⟨fun k hk => ?_, fun k r hk => ?_⟩
  · rw [hS]
    refine hIdx k ?_
    rcases hK k with e | ⟨a, -, ha, -⟩ | ⟨a, -, ha, -⟩
    · rwa [← e]
    all_goals (rw [ha]; exact fun h => by cases h)
  · rcases hK k with e | ⟨-, b, -, hb⟩ | ⟨-, b, -, hb⟩
    · rwa [← e]
    all_goals (rw [hb] at hk; cases hk)

/-- **The object index stays complete and well formed across a write that
fills no new slot and keeps the index.** -/
theorem objectIndexFacts_of_writeAny {s s' : SystemState} (hW : finaliseWriteAny s s')
    (hS : s'.objectIndexSet = s.objectIndexSet) (hIdx : SeLe4n.Model.objectIndexSetComplete s)
    (hSet : s.objectIndexSet.table.invExt) :
    SeLe4n.Model.objectIndexSetComplete s' ∧ s'.objectIndexSet.table.invExt := by
  refine ⟨fun k hk => ?_, by rw [hS]; exact hSet⟩
  rw [hS]
  refine hIdx k ?_
  rcases hW k with e | ⟨pre, -, hp, -⟩
  · rwa [← e]
  · rw [hp]; exact fun h => by cases h

/-- **The splice keeps the object index well formed**: at most three reply
stores, each at a key already indexed. -/
theorem spliceReplyFrameOutOrSelf_preserves_objectIndexSet_invExt (st : SystemState)
    (rid : SeLe4n.ReplyId) (hSet : st.objectIndexSet.table.invExt) :
    (spliceReplyFrameOutOrSelf st rid).objectIndexSet.table.invExt := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact hSet
  · rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, _, _, hA, _, hS⟩ |
        ⟨r, below, b, _, _, _, _, _, hS⟩
    · rw [hEq]; exact hSet
    rotate_left
    · obtain ⟨s1, hS1, hS2⟩ := severReplyFrameBelowStores_cases hS
      exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s1 _ _ _
        (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSet hS1) hS2
    · rcases spliceReplyFrameStores_cases hS with ⟨s1, _, hS1, hS2⟩ |
        ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
      · exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s1 _ _ _
          (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSet hS1) hS2
      · exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s2 _ _ _
          (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s1 s2 _ _
            (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSet hS1) hS2) hS3

/-- **A reply-blocked caller's cancel keeps the object index complete and well
formed**: the return and the splice store at indexed keys, the restore and the
unlink keep the index, and the consume's two stores are at indexed keys. -/
theorem cancelIpcBlocking_replyArm_objectIndexFacts (st : SystemState) (c : SeLe4n.ThreadId)
    (t : TCB) {ep : SeLe4n.ObjId} {rt : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hB : t.ipcState = .blockedOnReply ep rt) (hIdx : SeLe4n.Model.objectIndexSetComplete st)
    (hSet : st.objectIndexSet.table.invExt) :
    SeLe4n.Model.objectIndexSetComplete (Lifecycle.Suspend.cancelIpcBlocking st c t) ∧
      (Lifecycle.Suspend.cancelIpcBlocking st c t).objectIndexSet.table.invExt := by
  rw [cancelIpcBlocking_replyArm_unfold st c t hB]
  let s0 := Lifecycle.Suspend.returnDonationToCancelledCaller st c t
  have hI0 : s0.objects.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st c t hInv
  have hC0 : SeLe4n.Model.objectIndexSetComplete s0 :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objectIndexSetComplete st c t
      hInv hSet hIdx
  have hS0 : s0.objectIndexSet.table.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objectIndexSet_invExt st c t hSet
  let s1 := spliceThreadReplyFrameOut s0 t
  have hI1 : s1.objects.invExt := spliceThreadReplyFrameOut_preserves_objects_invExt s0 t hI0
  have hC1 : SeLe4n.Model.objectIndexSetComplete s1 :=
    spliceThreadReplyFrameOut_preserves_objectIndexSetComplete s0 t hI0 hS0 hC0
  have hS1 : s1.objectIndexSet.table.invExt := by
    show (spliceThreadReplyFrameOut s0 t).objectIndexSet.table.invExt
    unfold spliceThreadReplyFrameOut
    cases t.replyObject with
    | none => exact hS0
    | some rid => exact spliceReplyFrameOutOrSelf_preserves_objectIndexSet_invExt s0 rid hS0
  let s2 := Lifecycle.Suspend.restoreToReadyCancelled s1 c
  have hI2 : s2.objects.invExt := restoreToReadyCancelled_preserves_objects_invExt s1 c hI1
  have hC2 : SeLe4n.Model.objectIndexSetComplete s2 :=
    Lifecycle.Suspend.restoreToReadyCancelled_preserves_objectIndexSetComplete s1 c hI1 hC1
  have hS2 : s2.objectIndexSet.table.invExt := by
    show (Lifecycle.Suspend.restoreToReadyCancelled s1 c).objectIndexSet.table.invExt
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_objectIndexSet]; exact hS1
  let s3 := Lifecycle.Suspend.consumeReplyLink s2 c t
  have h3 : SeLe4n.Model.objectIndexSetComplete s3 ∧ s3.objectIndexSet.table.invExt := by
    show SeLe4n.Model.objectIndexSetComplete (Lifecycle.Suspend.consumeReplyLink s2 c t) ∧
      (Lifecycle.Suspend.consumeReplyLink s2 c t).objectIndexSet.table.invExt
    unfold Lifecycle.Suspend.consumeReplyLink
    cases t.replyObject with
    | none => exact ⟨hC2, hS2⟩
    | some rid =>
      exact consumeCallerReply_preserves_objectIndexSetComplete_and_invExt s2 _ c rid hI2 hS2 hC2
        (SystemState.consumeCallerReply_eq_link s2 c rid)
  have hI3 : s3.objects.invExt := Lifecycle.Suspend.consumeReplyLink_preserves_objects_invExt s2 c t hI2
  refine objectIndexFacts_of_writeAny
    (FinaliseFrameAny.unlinkReplyWaiterOpt s3 c t.blockingServer? hI3).write ?_ h3.1 h3.2
  have hU := congrArg SystemState.objectIndexSet
    (SystemState.unlinkReplyWaiterOpt_eq_objects s3 c t.blockingServer?)
  exact hU

/-- **A reply-blocked caller's cancel and revert keep the object index
complete and well formed** (`finaliseReplyCallerCancel`): the cancel's reply arm
(`cancelIpcBlocking_replyArm_objectIndexFacts`), then the migration, the
deschedule and the boost revert, none of which fills a slot or touches the
index. -/
theorem finaliseReplyCallerCancel_objectIndexFacts (s : SystemState) (c : SeLe4n.ThreadId)
    (t : TCB) (hInv : s.objects.invExt) (hIdx : SeLe4n.Model.objectIndexSetComplete s)
    (hSet : s.objectIndexSet.table.invExt) :
    (finaliseReplyCallerCancel s c t).objects.invExt ∧
    SeLe4n.Model.objectIndexSetComplete (finaliseReplyCallerCancel s c t) ∧
      (finaliseReplyCallerCancel s c t).objectIndexSet.table.invExt := by
  unfold finaliseReplyCallerCancel
  split
  rotate_left
  · exact ⟨hInv, hIdx, hSet⟩
  next r hX =>
  split
  rotate_left
  · exact ⟨hInv, hIdx, hSet⟩
  next hG =>
  simp only [Bool.and_eq_true, beq_iff_eq] at hG
  obtain ⟨⟨-, hF⟩, -⟩ := hG
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
  rw [finaliseReplyCancel_eq hX hF]
  have h1 := cancelIpcBlocking_replyArm_objectIndexFacts s c t hInv hB hIdx hSet
  have f1 := FinaliseFrameAny.replyCancel s c t hInv hB
  have f2 := FinaliseFrameAny.cancelIpcBlockingMigrated s c t f1.invExt
  have hM : (cancelIpcBlockingMigrated c t s).objectIndexSet =
      (Lifecycle.Suspend.cancelIpcBlocking s c t).objectIndexSet := by
    unfold cancelIpcBlockingMigrated
    split
    · rw [(migrateSchedContextReplenishment_releaseOnlyWrite _ _ _ _).1]
    · rfl
  have h2 := objectIndexFacts_of_writeAny f2.write hM h1.1 h1.2
  have h3 : SeLe4n.Model.objectIndexSetComplete (cancelIpcBlockingReclaimed c t s) ∧
      (cancelIpcBlockingReclaimed c t s).objectIndexSet.table.invExt := by
    unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
    split
    · exact h2
    · rename_i holder _
      have f3 := FinaliseFrame.descheduleAt (cancelIpcBlockingMigrated c t s) holder
        (placedCoreOf? (cancelIpcBlockingMigrated c t s) holder) f2.invExt
      exact objectIndexFacts_of_writeAny f3.any.write (by have e := congrArg SystemState.objectIndexSet f3.rest; exact e) h2.1 h2.2
  have hI3 := cancelIpcBlockingReclaimed_objects_invExt c t s f1.invExt
  have f4 := FinaliseFrame.finaliseReplyRevert _ t.blockingServer? hI3
  exact ⟨f4.invExt, objectIndexFacts_of_writeAny f4.any.write (by have e := congrArg SystemState.objectIndexSet f4.rest; exact e) h3.1 h3.2⟩

/-- ...and a waiter's whole end, the suspend after the cancel
(`finaliseReplyWaiter`). -/
theorem finaliseReplyWaiter_objectIndexFacts (s : SystemState) (w : SeLe4n.ThreadId)
    (t : TCB) (hInv : s.objects.invExt) (hIdx : SeLe4n.Model.objectIndexSetComplete s)
    (hSet : s.objectIndexSet.table.invExt) :
    (finaliseReplyWaiter s w t).objects.invExt ∧
    SeLe4n.Model.objectIndexSetComplete (finaliseReplyWaiter s w t) ∧
      (finaliseReplyWaiter s w t).objectIndexSet.table.invExt := by
  obtain ⟨hI1, hC1, hS1⟩ := finaliseReplyCallerCancel_objectIndexFacts s w t hInv hIdx hSet
  unfold finaliseReplyWaiter finaliseThreadSuspend
  split
  · split
    · have f := FinaliseFrame.suspend _ w hI1
      exact ⟨f.invExt, objectIndexFacts_of_writeAny f.any.write (by have e := congrArg SystemState.objectIndexSet f.rest; exact e) hC1 hS1⟩
    · exact ⟨hI1, hC1, hS1⟩
  · exact ⟨hI1, hC1, hS1⟩

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
      have hI := cancelBoundDonationOnCore_preserves_objects_invExt s st' tid t hInv hOk
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

/-- ...and so does a write of contexts' release fields alone (the
replenishment migration). -/
theorem sameSchedContextBindings_of_objectsAgreeOffReleaseLinks {a b : SystemState}
    (h : b.objectsAgreeOffReleaseLinks a) : sameSchedContextBindings a b := fun _ t' hb =>
  ⟨t', h.symm.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hb, rfl⟩

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
    (hSame.trans (sameSchedContextBindings_of_objectsAgreeOffReleaseLinks
      (cancelIpcBlockingMigrated_agree c t s))).trans
      (sameSchedContextBindings_of_objectsAgreeOffRunLinks
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

/-- **What a reply-blocked caller's cancel leaves in another thread's binding**:
the thread is still a thread, and keeps its context code, or — the holder a head
reply's pop takes the context from — holds none. -/
theorem finaliseReplyCallerCancel_otherBinding {s : SystemState} {c y : SeLe4n.ThreadId}
    {t ty : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? c = some t) (hy : y ≠ c)
    (hTy : s.getTcb? y = some ty) :
    ∃ ty', (finaliseReplyCallerCancel s c t).getTcb? y = some ty' ∧
      (ty'.scBindingScCode = ty.scBindingScCode ∨ ty'.scBindingScCode = 0) := by
  have hTo := (SystemState.getTcb?_eq_some_iff s y ty).mp hTy
  unfold finaliseReplyCallerCancel
  split
  rotate_left
  · exact ⟨ty, hTy, Or.inl rfl⟩
  next r hX =>
  split
  rotate_left
  · exact ⟨ty, hTy, Or.inl rfl⟩
  next hG =>
  simp only [Bool.and_eq_true, beq_iff_eq] at hG
  obtain ⟨⟨-, hF⟩, -⟩ := hG
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
  rw [finaliseReplyCancel_eq hX hF]
  let s0 := Lifecycle.Suspend.returnDonationToCancelledCaller s c t
  have hI0 : s0.objects.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt s c t hInv
  let s1 := spliceThreadReplyFrameOut s0 t
  have hI1 : s1.objects.invExt := spliceThreadReplyFrameOut_preserves_objects_invExt s0 t hI0
  let s2 := Lifecycle.Suspend.restoreToReadyCancelled s1 c
  have hI2 : s2.objects.invExt := restoreToReadyCancelled_preserves_objects_invExt s1 c hI1
  let s3 := Lifecycle.Suspend.consumeReplyLink s2 c t
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
    (hSame.trans (sameSchedContextBindings_of_objectsAgreeOffReleaseLinks
      (cancelIpcBlockingMigrated_agree c t s))).trans
      (sameSchedContextBindings_of_objectsAgreeOffRunLinks
        (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks c t s))
  have hSameV : sameSchedContextBindings s0
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
    unfold finaliseReplyRevert
    cases t.blockingServer? with
    | none => exact hSameR
    | some sv => exact hSameR.trans (propagatePipChainCrossCore_sameSchedContextBindings' _ _ _ _ hIR)
  obtain ⟨tv, hTv⟩ : ∃ tv, (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s)
      t.blockingServer?).getTcb? y = some tv := by
    obtain ⟨t1, hL1, -⟩ := Lifecycle.Suspend.cancelIpcBlocking_tcb_lookup s c t y.toObjId ty hInv hTo
    have hS1 : ((Lifecycle.Suspend.cancelIpcBlocking s c t).getTcb? y).isSome := by
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hL1]; rfl
    have hS2 : ((cancelIpcBlockingReclaimed c t s).getTcb? y).isSome := by
      have hM := cancelIpcBlockingReclaimed_getTcb? c t s y
      rw [← Option.isSome_map (f := TCB.withoutRunLinks), hM, Option.isSome_map]; exact hS1
    have hS3 : ((finaliseReplyRevert (cancelIpcBlockingReclaimed c t s)
        t.blockingServer?).getTcb? y).isSome := by
      unfold finaliseReplyRevert
      cases t.blockingServer? with
      | none => exact hS2
      | some sv =>
        exact PriorityInheritance.propagatePipChainCrossCore_getTcb?_isSome _ _ _ _ hIR y hS2
    exact Option.isSome_iff_exists.mp hS3
  refine ⟨tv, hTv, ?_⟩
  obtain ⟨t0, h0, e0⟩ := hSameV y tv ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTv)
  rcases replyCallerFinalisable_cases hX hF with ⟨-, hD⟩ |
      ⟨s', sc, hd, ht, hN, -, -, -, hHd, hBd, hC, hD⟩
  · have hR : s0 = s := by
      show Lifecycle.Suspend.returnDonationToCancelledCaller s c t = s
      unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
    rw [hR, hTo] at h0
    cases h0
    exact Or.inl (TCB.scBindingScCode_eq_of_binding e0.symm)
  · obtain ⟨n, st', -, hPop, hEq⟩ := replyHeadPop_commits hInv hT hD hC
    have h0' : st'.objects[y.toObjId]? = some (.tcb t0) := by rw [← hEq]; exact h0
    have hCases := returnDonatedSchedContext_tcb_binding_cases s st' hd s' c n hInv hPop
      y.toObjId t0 h0'
    by_cases hyh : y.toObjId = hd.toObjId
    · refine Or.inr ?_
      have e := congrArg SchedContextBinding.scCode (e0.symm.trans (hCases.1 hyh))
      unfold TCB.schedContextBinding at e
      rw [SchedContextBinding.scCode_ofCodes] at e
      exact e
    · have hyc : y.toObjId ≠ c.toObjId := fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e)
      obtain ⟨t1, h1, e1⟩ := hCases.2.2 hyh hyc
      rw [hTo] at h1
      cases h1
      exact Or.inl (TCB.scBindingScCode_eq_of_binding (e1.trans e0).symm)

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

/-- **A finalised thread's IPC cancel keeps the object index complete and well
formed**: the notification and endpoint cancels keep the index and fill no
slot, and the reply cancel stores at indexed keys
(`finaliseReplyCallerCancel_objectIndexFacts`). -/
theorem finaliseThreadCancel_objectIndexFacts {s : SystemState} {tid : SeLe4n.ThreadId}
    (hInv : s.objects.invExt) (hIdx : SeLe4n.Model.objectIndexSetComplete s)
    (hSet : s.objectIndexSet.table.invExt) :
    SeLe4n.Model.objectIndexSetComplete (finaliseThreadCancel s tid) ∧
      (finaliseThreadCancel s tid).objectIndexSet.table.invExt := by
  have hFr : ∀ {s' : SystemState}, FinaliseFrame s s' →
      SeLe4n.Model.objectIndexSetComplete s' ∧ s'.objectIndexSet.table.invExt :=
    fun f => objectIndexFacts_of_writeAny f.any.write (by have e := congrArg SystemState.objectIndexSet f.rest; exact e) hIdx hSet
  have hEnd : ∀ (t : TCB) e q, SeLe4n.Model.objectIndexSetComplete (cancelEndpointBlocked s e q tid t) ∧
      (cancelEndpointBlocked s e q tid t).objectIndexSet.table.invExt := by
    intro t e q
    unfold cancelEndpointBlocked
    split
    · split
      · exact hFr (FinaliseFrame.storeEndpointBlockedCancelled _ _ _ _ _ _ hInv)
      · exact ⟨hIdx, hSet⟩
    · exact ⟨hIdx, hSet⟩
  unfold finaliseThreadCancel
  split
  · rename_i t hT
    split
    · rename_i n hB
      split
      · split
        · exact hFr (FinaliseFrame.notificationCancel s tid t n hInv hB)
        · exact ⟨hIdx, hSet⟩
      · exact ⟨hIdx, hSet⟩
    · exact hEnd t _ true
    · exact hEnd t _ false
    · exact hEnd t _ false
    · exact (finaliseReplyCallerCancel_objectIndexFacts s tid t hInv hIdx hSet).2
    · exact ⟨hIdx, hSet⟩
  · exact ⟨hIdx, hSet⟩

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

/-- **A waiter's end is invisible** when the waiter is hidden, as an object and
as a thread, and so is every server on its blocking chain: the reply cancel
(`finaliseReplyCallerCancel_hidden`), then the suspend
(`finaliseThreadSuspend_hidden`). -/
theorem finaliseReplyWaiter_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {w : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt)
    (hValid : LabelingContextValid ctx)
    (hIdx : SeLe4n.Model.objectIndexSetComplete s) (hSet : s.objectIndexSet.table.invExt)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hT : s.getTcb? w = some t) (hObj : objectObservable ctx observer w.toObjId = false)
    (hThr : threadObservable ctx observer w = false) :
    projectState ctx observer (finaliseReplyWaiter s w t) = projectState ctx observer s := by
  obtain ⟨hI1, -, -⟩ := finaliseReplyCallerCancel_objectIndexFacts s w t hInv hIdx hSet
  unfold finaliseReplyWaiter
  rw [finaliseThreadSuspend_hidden ctx observer _ w hI1 hObj hThr]
  exact finaliseReplyCallerCancel_hidden ctx observer hInv hValid hIdx hSet hBlockingChainHigh
    hT hThr

/-- **What a waiter's end leaves in another thread's binding**: it is still a
thread, keeping its context code or — a head reply's pop taking the context from
it — holding none (`finaliseReplyCallerCancel_otherBinding`); the suspend writes
the waiter alone and run-queue links. -/
theorem finaliseReplyWaiter_otherBinding {s : SystemState} {w y : SeLe4n.ThreadId}
    {t ty : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? w = some t) (hy : y ≠ w)
    (hTy : s.getTcb? y = some ty) :
    ∃ ty', (finaliseReplyWaiter s w t).getTcb? y = some ty' ∧
      (ty'.scBindingScCode = ty.scBindingScCode ∨ ty'.scBindingScCode = 0) := by
  obtain ⟨ty1, h1, e1⟩ := finaliseReplyCallerCancel_otherBinding (t := t) hInv hT hy hTy
  have hI1 := (finaliseReplyCallerCancel_binding hInv hT).1
  have hyo : w.toObjId ≠ y.toObjId := fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  unfold finaliseReplyWaiter finaliseThreadSuspend
  split
  · split
    · have hD : (descheduleAtPlacement (finaliseReplyCallerCancel s w t) w).objects.invExt :=
        (FinaliseFrame.descheduleAt _ w (placedCoreOf? _ w) hI1).invExt
      obtain ⟨t2, h2, e2⟩ := KernelObject.map_withoutRunLinks_tcb
        (descheduleAtPlacement_objectsAgreeOffRunLinks _ w y.toObjId)
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1)
      rw [SystemState.updateTcb_getTcb?_ne _ _ _ hD _ hyo,
        (SystemState.getTcb?_eq_some_iff _ _ _).mpr h2]
      refine ⟨t2, rfl, ?_⟩
      rw [TCB.proj_eq_of_withoutRunLinks_eq TCB.scBindingScCode e2]; exact e1
    · exact ⟨ty1, h1, e1⟩
  · exact ⟨ty1, h1, e1⟩

/-- **What a waiter's end keeps**: the object table and its index well formed,
the projection (when the waiters of `x` are hidden), and the server `x`'s
binding code, or none. -/
def waiterEndKeeps (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (x : SeLe4n.ThreadId) (code : Nat) (s : SystemState) : Prop :=
  s.objects.invExt ∧ SeLe4n.Model.objectIndexSetComplete s ∧ s.objectIndexSet.table.invExt ∧
    projectState ctx observer s = projectState ctx observer st ∧
    ∃ tx, s.getTcb? x = some tx ∧ (tx.scBindingScCode = code ∨ tx.scBindingScCode = 0)

/-- ...and a waiter's end, admitted (`replyWaiterEndable`), keeps it, when every
thread blocked on `x` is hidden (`hWait`). -/
theorem waiterEndKeeps.step {ctx : LabelingContext} {observer : IfObserver}
    {st : SystemState} {x : SeLe4n.ThreadId} {code : Nat} {s : SystemState}
    (hValid : LabelingContextValid ctx)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hWait : ∀ (s : SystemState) (w : SeLe4n.ThreadId),
      PriorityInheritance.blockingServer s w = some x →
      objectObservable ctx observer w.toObjId = false ∧ threadObservable ctx observer w = false)
    (h : waiterEndKeeps ctx observer st x code s) {w : SeLe4n.ThreadId} {t : TCB}
    (hT : s.getTcb? w = some t) (hE : replyWaiterEndable s x w t = true) :
    waiterEndKeeps ctx observer st x code (finaliseReplyWaiter s w t) := by
  obtain ⟨hInv, hIdx, hSet, hP, tx, hTx, hc⟩ := h
  simp only [replyWaiterEndable, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hE
  obtain ⟨⟨hNe, hS⟩, -⟩ := hE
  have hBs : PriorityInheritance.blockingServer s w = some x := by
    unfold PriorityInheritance.blockingServer; rw [hT]
    show t.blockingServer? = some x
    rw [← ofOptCode_replyCallerServerCode, hS]; rfl
  obtain ⟨hObj, hThr⟩ := hWait s w hBs
  have hF := finaliseReplyWaiter_objectIndexFacts s w t hInv hIdx hSet
  have hxw : x ≠ w := fun e => hNe (by rw [e])
  obtain ⟨tx', hTx', hc'⟩ := finaliseReplyWaiter_otherBinding hInv hT hxw hTx
  refine ⟨hF.1, hF.2.1, hF.2.2, ?_, tx', hTx', ?_⟩
  · rw [finaliseReplyWaiter_hidden ctx observer hInv hValid hIdx hSet hBlockingChainHigh hT hObj
      hThr]; exact hP
  · rcases hc' with e | e
    · rw [e]; exact hc
    · exact Or.inr e

/-- ...so the walk over `x`'s waiters keeps it (`finaliseReplyWaiters`). -/
theorem waiterEndKeeps.walk {ctx : LabelingContext} {observer : IfObserver}
    {st : SystemState} {x : SeLe4n.ThreadId} {code : Nat}
    (hValid : LabelingContextValid ctx)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hWait : ∀ (s : SystemState) (w : SeLe4n.ThreadId),
      PriorityInheritance.blockingServer s w = some x →
      objectObservable ctx observer w.toObjId = false ∧ threadObservable ctx observer w = false) :
    ∀ (fuel : Nat) (s : SystemState), waiterEndKeeps ctx observer st x code s →
      waiterEndKeeps ctx observer st x code (finaliseReplyWaiters x fuel s)
  | 0, s, h => h
  | fuel + 1, s, h => by
    unfold finaliseReplyWaiters
    split
    · split
      · exact h
      · split
        · rename_i t hT
          split
          · rename_i hE
            exact waiterEndKeeps.walk hValid hBlockingChainHigh hWait fuel _
              (waiterEndKeeps.step hValid hBlockingChainHigh hWait h hT hE)
          · exact h
        · exact h
    · exact h

/-- ...and so do the loan return and the waiters' end of a finalised thread. -/
theorem waiterEndKeeps.endAll {ctx : LabelingContext} {observer : IfObserver}
    {st : SystemState} {x : SeLe4n.ThreadId} {code : Nat} {s : SystemState}
    (hValid : LabelingContextValid ctx)
    (hBlockingChainHigh : ∀ (s : SystemState) (t server : SeLe4n.ThreadId),
      threadObservable ctx observer t = false →
      PriorityInheritance.blockingServer s t = some server →
      threadObservable ctx observer server = false)
    (hWait : ∀ (s : SystemState) (w : SeLe4n.ThreadId),
      PriorityInheritance.blockingServer s w = some x →
      objectObservable ctx observer w.toObjId = false ∧ threadObservable ctx observer w = false)
    (h : waiterEndKeeps ctx observer st x code s) :
    waiterEndKeeps ctx observer st x code
      (finaliseThreadEndWaiters (finaliseThreadReturnLoan s x) x) := by
  have h1 : waiterEndKeeps ctx observer st x code (finaliseThreadReturnLoan s x) := by
    unfold finaliseThreadReturnLoan
    split
    · split
      · exact h
      · split
        · rename_i tl hT
          split
          · rename_i hE
            exact waiterEndKeeps.step hValid hBlockingChainHigh hWait h hT hE
          · exact h
        · exact h
    · exact h
  unfold finaliseThreadEndWaiters
  split
  · exact waiterEndKeeps.walk hValid hBlockingChainHigh hWait _ _ h1
  · exact h1

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
each hidden; every thread that waits on it for a reply, as an object and as a
thread (the waiters' end cancels and suspends each) — and, since the suspend takes it
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
    (∀ (s : SystemState) (w : SeLe4n.ThreadId),
      PriorityInheritance.blockingServer s w = some ⟨x.val⟩ →
      objectObservable ctx observer w.toObjId = false ∧ threadObservable ctx observer w = false) ∧
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
write are hidden: the unbinds keep what the cancel reads, and the yield steps
write the held context's consumed count (hidden) and what the projection
erases. -/
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
  unfold finaliseThread; dsimp only
  split
  · next hAd =>
    obtain ⟨t, hO⟩ : ∃ t, st.getObject? x = some (.tcb t) := by
      unfold threadFinaliseAdmitted at hAd
      split at hAd
      · exact ⟨_, ‹_›⟩
      · cases hAd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h9, hWait, h8⟩ := hH t hO
    have hT : st.getTcb? ⟨x.val⟩ = some t :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO
    have hG : notificationUnbindAdmitted st ⟨x.val⟩ t = true := by
      obtain ⟨t', hT', hG'⟩ := threadFinaliseAdmitted_notificationUnbind hAd
      rw [hT] at hT'; cases hT'; exact hG'
    obtain ⟨hP1, hI1, t1, hT1, e1, e2, e3, e4, e5, e6, -, e7⟩ :=
      finaliseThreadUnbindNotification_hidden ctx observer hInv hT hG hX h1
    obtain ⟨hIdx1, hRp⟩ := finaliseThreadUnbindNotification_index hInv hT hG hIdx
    have hSet1 : (finaliseThreadUnbindNotification st ⟨x.val⟩).objectIndexSet.table.invExt := by
      rw [(finaliseThreadUnbindNotification_slots hInv hT hG).1]; exact hSet
    obtain ⟨hP2, hI2⟩ := finaliseThreadCancel_hidden ctx observer hI1 hT1 hValid hIdx1 hSet1
      hBlockingChainHigh h8 hX
      (by rw [e1]; exact h3) (by rw [e2]; exact h4) (by rw [e3]; exact h5)
      (by rw [e4]; exact h6) (by rw [e5]; exact h7)
    obtain ⟨t2, hT2, f2⟩ := finaliseThreadCancel_scBinding hI1 hT1
    -- The loan return and the waiters' end.
    obtain ⟨hIdx2, hSet2⟩ := finaliseThreadCancel_objectIndexFacts (tid := ⟨x.val⟩) hI1 hIdx1 hSet1
    obtain ⟨hI2', -, -, hPW, tw, hTw, fw⟩ := waiterEndKeeps.endAll hValid hBlockingChainHigh hWait
      (show waiterEndKeeps ctx observer _ ⟨x.val⟩ t2.scBindingScCode _ from
        ⟨hI2, hIdx2, hSet2, rfl, t2, hT2, Or.inl rfl⟩)
    have hP3 := finaliseThreadSuspend_hidden ctx observer _ ⟨x.val⟩ hI2' hX h8
    obtain ⟨hI3, t3, hT3, f3⟩ := finaliseThreadSuspend_scBinding hI2' hTw
    -- WS-ZA ZA6.6: the suspend's yield cancel, the thread hidden (`hX`).
    have hP3y := projectedObjectsWrite.cancelYieldTo (ctx := ctx) (observer := observer) _
      ⟨x.val⟩ hI3
    have hI3y := SystemState.cancelYieldTo_preserves_objects_invExt _ ⟨x.val⟩ hI3
    obtain ⟨t3y, hT3y, e3y⟩ :=
      (SystemState.cancelYieldTo_objectsAgreeOffYield _ ⟨x.val⟩ hI3).getTcb?_some hT3
    have f3y : t3y.scBindingScCode = t3.scBindingScCode := by
      have e := congrArg TCB.scBindingScCode e3y; exact e
    have hT4 := (finaliseThreadReleaseCores_getTcb? _ ⟨x.val⟩ ⟨x.val⟩).trans hT3y
    have hI4 := (FinaliseFrame.releaseCores _ ⟨x.val⟩ hI3y).invExt
    have hSc : t3y.scBindingScCode ≠ 0 → objectObservable ctx observer
        (⟨t3y.scBindingScCode - 1⟩ : SeLe4n.SchedContextId).toObjId = false := by
      rw [f3y, f3]
      rcases fw with fw | fw
      rotate_left
      · intro h; exact absurd fw h
      rw [fw]
      rcases f2 with f2 | ⟨r, sc, hR, hN, f2⟩
      · rw [f2, e6]; exact h2
      · intro _
        rw [f2, Nat.add_sub_cancel]
        rw [e7, SystemState.getObject?_eq_getElem] at hR
        exact h9 r sc (by rw [SystemState.getObject?_eq_getElem]; exact hRp _ r hR) hN
    obtain ⟨hP5, hI5, -⟩ := finaliseThreadUnbindSchedContext_hidden ctx observer hI4 hT4 hX hSc
    -- WS-ZA ZA6.6: the yield steps, the context the thread held hidden (`h2`).
    have hHeld : threadHeldContextCode st ⟨x.val⟩ ≠ 0 → objectObservable ctx observer
        (⟨threadHeldContextCode st ⟨x.val⟩ - 1⟩ : SeLe4n.SchedContextId).toObjId = false := by
      unfold threadHeldContextCode; rw [hT]; exact h2
    rw [(projectedObjectsWrite.completeHeldYield _ _ hI5 hHeld).projection,
      hP5, finaliseThreadReleaseCores_hidden, hP3y.projection, hP3, hPW, hP2, hP1]
  · rfl

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

/-- **A hidden context's destroy cleanup is invisible** (WS-ZA ZA6.6): the
completion of the yield it records writes its consumed count, a hidden key, and
the yield codes and a yielder's registers, which the projection erases. -/
theorem finaliseSchedContextCleanupImpl_hidden (ctx : LabelingContext) (observer : IfObserver)
    {s : SystemState} {x : SeLe4n.ObjId} (hInv : s.objects.invExt)
    (hX : objectObservable ctx observer x = false) :
    projectState ctx observer (finaliseSchedContextCleanupImpl s x) =
      projectState ctx observer s := by
  unfold finaliseSchedContextCleanupImpl
  split
  · split
    · exact (projectedObjectsWrite.completeYieldFrom s _ hInv hX).projection
    · rfl
  · rfl

/-- **A scheduling context's finalisation is invisible** when the context and
the thread bound to it are hidden: the holder's deschedule
(`finaliseSchedContextDeschedule_hidden`), the release (`finaliseSchedContextUnbind_hidden`),
the reply-stack unlink (`finaliseSchedContextUnstack_hidden`, at the replies the
pre-state indexes — the release writes a thread and a context only, and no
index), and the destroy cleanup, which completes the yield the context records
(`finaliseSchedContextCleanupImpl_hidden`). -/
theorem finaliseSchedContext_hidden (ctx : LabelingContext) (observer : IfObserver)
    {st : SystemState} {x : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hIdx : SeLe4n.Model.objectIndexSetComplete st)
    (hX : objectObservable ctx observer x = false)
    (hH : schedContextFinaliseHidden ctx observer st x) :
    projectState ctx observer (finaliseSchedContext x st) = projectState ctx observer st := by
  rw [finaliseSchedContext_eq]
  split
  · have hD : FinaliseFrame st (finaliseSchedContextDeschedule st x) :=
      finaliseSchedContextDeschedule_closed_any (FinaliseFrame st)
        (fun s t h => h.trans (FinaliseFrame.descheduleAt s t _ h.invExt)) st x
        (.refl hInv)
    have hF : FinaliseFrame st (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) := by
      refine finaliseSchedContextUnbind_closed (FinaliseFrame st) ?_ _ x hD
      exact FinaliseFrame.releaseStep st
    have hSet : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).objectIndexSet =
        st.objectIndexSet := by
      rw [hF.rest]
    rename_i hA
    have hU := (finaliseSchedContextUnstack_closed (FinaliseFrameAny st)
      (FinaliseFrameAny.unstackStep st) x st (.refl hInv) hA _ rfl hF.any).invExt
    refine (finaliseSchedContextCleanupImpl_hidden ctx observer hU hX).trans
      ((finaliseSchedContextUnstack_hidden ctx observer hF.invExt hX
      (fun rid r hR => ?_)).trans ((finaliseSchedContextUnbind_hidden ctx observer hD.invExt hX
        hH.deschedule).trans (finaliseSchedContextDeschedule_hidden ctx observer hH)))
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
child, so the untypeds recording the object, and the children it records, are
the pre-state's. -/
private theorem finaliseThenRetire_preserves_projection (ctx : LabelingContext)
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
    (hK : target ≠ 0 → ∀ y, untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) y = true →
      objectObservable ctx observer y = false)
    (hR : recorder ≠ 0 →
      objectObservable ctx observer (SeLe4n.ObjId.ofNat (recorder - 1)) = false) :
    projectState ctx observer
        (retireFinalObject ec target recorder (finaliseFinalObject target st)) =
      projectState ctx observer st := by
  have hF := finaliseFinalObject_frame target st h.2.1
  have hUt := hF.getUntyped?
  rw [retireFinalObject_preserves_projection ctx observer ec target recorder hF.invExt hx
    (fun h0 w hw => hU h0 w (by unfold untypedRecordsChild at hw ⊢; rw [hUt] at hw; exact hw))
    (fun h0 y hy => hK h0 y (by unfold untypedRecordsChild at hy ⊢; rw [hUt] at hy; exact hy)) hR,
    finaliseFinalObject_preserves_projection ctx observer target h hLc hx hW hBd hTF hSF hRF hFlow
      hValid hIdx hSet hBlockingChainHigh]

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
    (hK : target ≠ 0 → ∀ y, untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) y = true →
      objectObservable ctx observer y = false)
    (hR : recorder ≠ 0 →
      objectObservable ctx observer (SeLe4n.ObjId.ofNat (recorder - 1)) = false) :
    projectState ctx observer (retireFinalisedObject ec target recorder st) =
      projectState ctx observer st := by
  unfold retireFinalisedObject
  rcases releaseFinalRegistration_cases target st with hE | ⟨ep, h0, hEp, hC, hRev⟩
  · rw [hE]
    exact finaliseThenRetire_preserves_projection ctx observer ec target recorder h hLc hx hW hBd
      hTF hSF hRF hFlow hValid hIdx hSet hBlockingChainHigh hU hK hR
  -- WS-ZA ZA5.5: the release revokes the registration the endpoint records,
  -- which names that endpoint, hidden from the observer; it rewrites that
  -- endpoint alone, so every hypothesis, which reads threads, notifications,
  -- contexts, replies, untypeds and the index, holds after it.
  generalize releaseFinalRegistration target st = s0 at hRev ⊢
  have hObjInv := h.objects_invExt
  have hX := hx h0
  rw [SystemState.getObject?_eq_getElem] at hEp
  have hP0 : projectState ctx observer s0 = projectState ctx observer st :=
    revokeServiceByRecordedRegistration_preserves_projection ctx observer _ st s0 hX hObjInv
      (by unfold revokeServiceByRecordedRegistration; rw [SystemState.getObject?_eq_getElem, hEp]
          simp only [hC]; exact hRev)
  have hBk := fun {k} {o} (ho : s0.objects[k]? = some o) (hN : ∀ e, o ≠ .endpoint e) =>
    revokeService_back hRev hObjInv ho hN
  have hT0 := revokeService_getTcb? hRev hObjInv
  have hFr := revokeService_finaliseFrameAny hRev hObjInv
  have hUt := hFr.getUntyped?
  have hSetEq : s0.objectIndexSet = st.objectIndexSet := by
    obtain ⟨_, _, _, rfl⟩ := revokeService_ok hRev
    rfl
  refine (finaliseThenRetire_preserves_projection ctx observer ec target recorder
    (revokeService_preserves_ipcReachable h hRev)
    (hLc.of_loanWrite (revokeService_loanWrite hRev hObjInv)) hx
    (fun _ t tcb ht hw => hW h0 t tcb (hBk ht (fun _ e => by cases e)) hw)
    (fun _ ntfn t hN hb => hBd h0 ntfn t (by
      rw [SystemState.getNotification?_eq_some_iff] at hN ⊢
      exact hBk hN (fun _ e => by cases e)) hb)
    (fun _ t ht => by
      rw [SystemState.getObject?_eq_getElem] at ht
      have := hBk ht (fun _ e => by cases e)
      rw [hEp] at this; cases this)
    (fun _ sc hs => hSF h0 sc (by
      rw [SystemState.getObject?_eq_getElem] at hs ⊢; exact hBk hs (fun _ e => by cases e)))
    (fun _ => ⟨fun r hr => (hRF h0).1 r (by
        rw [SystemState.getObject?_eq_getElem] at hr ⊢; exact hBk hr (fun _ e => by cases e)),
      fun tid t ht => (hRF h0).2 tid t (by rw [← hT0]; exact ht)⟩)
    (fun holder owner scId hD => hFlow holder owner scId (by
      unfold replyDonationReturn? lookupTcb at hD ⊢; rw [← hT0]; exact hD))
    hValid
    (fun oid hne => by
      rw [hSetEq]
      exact hIdx oid (fun hn => hne ((revokeService_objects_none_iff hRev hObjInv oid).2 hn)))
    (by rw [hSetEq]; exact hSet) hBlockingChainHigh
    (fun h0 w hw => hU h0 w (by unfold untypedRecordsChild at hw ⊢; rw [hUt] at hw; exact hw))
    (fun h0 y hy => hK h0 y (by unfold untypedRecordsChild at hy ⊢; rw [hUt] at hy; exact hy))
    hR).trans hP0

-- ============================================================================
-- §  The activation at entry exit
-- ============================================================================

/-- WS-ZA ZA6.7: **the activation is invisible when what it touches is hidden**:
the context core `c`'s current thread yielded to, whose consumed time it reads
and whose end of the link it clears, and — on the boot core, whose bank the
projection shows while its current thread is observable — that thread.  The
thread's own writes (its link and its saved return registers) are erased by the
projection. -/
theorem activateThreadOnCore_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (s : SystemState) (c : CoreId) (hInv : s.objects.invExt)
    (hX : ∀ tid t k, s.scheduler.currentOnCore c = some tid → s.getTcb? tid = some t →
      t.yieldToCode = k + 1 →
      objectObservable ctx observer (⟨k⟩ : SeLe4n.SchedContextId).toObjId = false)
    (hR : c = Concurrency.bootCoreId → ∀ tid, s.scheduler.currentOnCore c = some tid →
      threadObservable ctx observer tid = false) :
    projectState ctx observer (activateThreadOnCore s c) = projectState ctx observer s := by
  rcases activateThreadOnCore_cases s c with h | ⟨tid, t, k, hC, hT, hY, h⟩
  · rw [h]
  rw [h]
  have hP : projectState ctx observer (SeLe4n.Kernel.completeYieldTo s tid) =
      projectState ctx observer s :=
    (projectedObjectsWrite.completeYieldTo s tid hInv
      (fun t' k' hT' hY' => hX tid t' k' hC hT' hY')).projection
  unfold completeCurrentYield
  split
  · rw [← hP]
    have hSch : (SeLe4n.Kernel.completeYieldTo s tid).scheduler = s.scheduler := by
      rw [SystemState.completeYieldTo_eq_objects s tid]
    simp only [projectState]
    congr 1
    unfold projectMachineRegs
    dsimp only
    rw [hSch]
    by_cases hb : c = Concurrency.bootCoreId
    · subst hb
      rw [hC]
      simp only [hR rfl tid hC, Bool.false_eq_true, ↓reduceIte]
    · rw [MachineState.regs_eq_regsOnCore_bootCore, MachineState.regs_eq_regsOnCore_bootCore,
        MachineState.modifyRegsOnCore_eq, MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ hb]
  · exact hP

end SeLe4n.Kernel
