/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 23 — the finalisation keeps `ipcReachable`, staged with `IPC.Invariant.Reachability`, whose staged pack it extends.
import SeLe4n.Kernel.IPC.Invariant.Reachability
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.IPC.Invariant.NotificationUnlink

/-!
# The finalisation keeps the reachable state

WS-ZA ZA5.4 part 23: the finalisation a final delete runs before its retire
(`finaliseFinalObject`: seL4's `cancelAllIPC`, `unbindMaybeNotification` and
`cancelAllSignals`) keeps `ipcReachable`, so the finalising delete's retire
(`retireFinalisedObject`) does.  Each conjunct is carried one walk step at a
time (`finaliseFinalObject_closed`), except the run queues' agreement with the
threads' links, which is the finalisation's run-queue stage
(`finaliseFinalObject_runQueueEntryStage`).

WS-ZA ZA5.4 part 25: a busy reply's finalisation cancels its caller and reverts
the boost it lent its server, and a scheduling context's unlinks the head of its
reply stack, so two steps write reply stack links.  The donation chains are
therefore carried step by step too (`finaliseStepInvariant`): a step that writes
no reply keeps them by its write frame, the unstack by
`finaliseUnstack_preserves_donationChainWellFormed`, and the caller's cancel by
the splice's, the consume's and the PIP walk's own carriage.  The caller made
`.ready` keeps what the notification queues read of it (`NtfnFrame`): the queues
name only "blocked on this notification".

* **The notification queues** (`notificationWaiterConsistent`).  An endpoint
  waiter's pop writes the endpoint and two threads' endpoint-queue links; its
  cancel makes a thread blocked on no notification `.ready`; its wake writes run
  links.  A notification waiter's cancel takes the queue's head off it — the
  notification's queue ends rewritten, the head's links and its successor's
  predecessor link cleared (`detachNtfnHead`) — and makes the head `.ready`.
  The unbind writes the thread's binding and the notification's.
* **The timeout budgets** and **the reply-waiter queues**: no step writes a
  budget, and no step writes a thread's reply view — a waiter the walk cancels
  is blocked on an endpoint or a notification, so on no server, and `.ready`
  is blocked on none either.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Primitive writes
-- ============================================================================

/-- An object rewritten in its slot, read key by key. -/
theorem modifyObject_objects_getElem {st : SystemState} {k : SeLe4n.ObjId}
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) (x : SeLe4n.ObjId) :
    (st.modifyObject k f).objects[x]? = if k = x then (st.objects[k]?).map f else st.objects[x]? := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    show (st.objects.modify k f)[x]? = _
    rw [e]; split
    · next h => subst h; exact hG
    · rfl
  | some o =>
    show (st.objects.modify k f)[x]? = _
    rw [RobinHood.RHTable.modify_of_get? hG]
    split
    · next h => subst h; exact RobinHood.RHTable.getElem?_insert_self st.objects k (f o) hInv
    · next h =>
      exact RobinHood.RHTable.getElem?_insert_ne st.objects k x (f o) (fun hb => h (eq_of_beq hb)) hInv

/-- A thread rewritten keeping its IPC state and its notification links keeps the
notification queues. -/
theorem notificationWaiterConsistent_updateTcb_keeping {st : SystemState} {t : SeLe4n.ThreadId}
    {f : TCB → TCB} (hInv : st.objects.invExt) (hC : notificationWaiterConsistent st)
    (hf : ∀ x, (f x).ipcState = x.ipcState ∧ (f x).ntfnPrev = x.ntfnPrev ∧
      (f x).ntfnNext = x.ntfnNext) :
    notificationWaiterConsistent (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact hC
  | some x =>
    have hT := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    have hS := updateTcb_objects_self_of_tcb f hInv hT
    have hO : ∀ k, t.toObjId ≠ k → (st.updateTcb t f).objects[k]? = st.objects[k]? :=
      fun k hk => SystemState.updateTcb_objects_ne _ _ _ k hk hInv
    refine notificationWaiterConsistent_of_tcbLinkFrame hC ?_ ?_ ?_ ?_
    · intro k n hk
      by_cases e : t.toObjId = k
      · subst e; rw [hS] at hk; cases hk
      · rwa [hO k e] at hk
    · intro k n hk
      by_cases e : t.toObjId = k
      · subst e; rw [hT] at hk; cases hk
      · rwa [hO k e]
    · intro k ty hk
      by_cases e : t.toObjId = k
      · subst e; rw [hT] at hk; cases hk
        exact ⟨f x, hS, (hf x).1, (hf x).2.1, (hf x).2.2⟩
      · exact ⟨ty, by rw [hO k e]; exact hk, rfl, rfl, rfl⟩
    · intro k tx hk
      by_cases e : t.toObjId = k
      · subst e; rw [hS] at hk; cases hk
        exact ⟨x, hT, (hf x).1, (hf x).2.1, (hf x).2.2⟩
      · exact ⟨tx, by rw [← hO k e]; exact hk, rfl, rfl, rfl⟩

/-- A thread rewritten keeping its timeout budget frames every budget. -/
theorem timeoutBudgetFrame_updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).timeoutBudget = x.timeoutBudget) :
    timeoutBudgetFrame st (st.updateTcb t f) := by
  intro tid tcb' h
  by_cases e : t.toObjId = tid.toObjId
  · cases hG : st.getTcb? t with
    | none => rw [SystemState.updateTcb_eq_self_of_none hG] at h; exact ⟨tcb', h, rfl⟩
    | some x =>
      have hT := (SystemState.getTcb?_eq_some_iff st t x).mp hG
      rw [← e, updateTcb_objects_self_of_tcb f hInv hT] at h
      cases h
      exact ⟨x, e ▸ hT, (hf x).symm⟩
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv] at h
    exact ⟨tcb', h, rfl⟩

/-- An object rewritten in its slot by an update that writes no thread, over
an object that is no thread, frames every budget. -/
theorem timeoutBudgetFrame_modifyObject_nonTcb (st : SystemState) (k : SeLe4n.ObjId)
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt)
    (hf : ∀ o, (∀ t, o ≠ .tcb t) → ∀ t, f o ≠ .tcb t)
    (hk : ∀ t, st.objects[k]? ≠ some (.tcb t)) :
    timeoutBudgetFrame st (st.modifyObject k f) := by
  intro tid tcb' h
  rw [modifyObject_objects_getElem hInv] at h
  split at h
  · next e =>
    cases hG : st.objects[k]? with
    | none => rw [hG] at h; cases h
    | some o =>
      rw [hG] at h
      exact absurd (Option.some.inj h) (hf o (fun t ht => hk t (by rw [hG, ht])) tcb')
  · exact ⟨tcb', h, rfl⟩

/-- An object rewritten in its slot by an update that makes neither a thread
nor a notification, over an object that is neither, keeps the notification
queues. -/
theorem notificationWaiterConsistent_modifyObject_inert {st : SystemState} {k : SeLe4n.ObjId}
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt)
    (hC : notificationWaiterConsistent st)
    (hf : ∀ o, (∀ t, o ≠ .tcb t) → (∀ n, o ≠ .notification n) →
      (∀ t, f o ≠ .tcb t) ∧ ∀ n, f o ≠ .notification n)
    (hkT : ∀ t, st.objects[k]? ≠ some (.tcb t))
    (hkN : ∀ n, st.objects[k]? ≠ some (.notification n)) :
    notificationWaiterConsistent (st.modifyObject k f) := by
  have hG := modifyObject_objects_getElem (f := f) (k := k) hInv
  have hAt : ∀ x, k = x → (∀ t, (st.modifyObject k f).objects[x]? ≠ some (.tcb t)) ∧
      ∀ n, (st.modifyObject k f).objects[x]? ≠ some (.notification n) := by
    intro x e
    rw [hG x, if_pos e]
    cases ho : st.objects[k]? with
    | none => exact ⟨(fun _ h => by simp at h), (fun _ h => by simp at h)⟩
    | some o =>
      simp only [Option.map_some]
      have := hf o (fun t ht => hkT t (by rw [ho, ht])) (fun n hn => hkN n (by rw [ho, hn]))
      exact ⟨fun t h => this.1 t (Option.some.inj h), fun n h => this.2 n (Option.some.inj h)⟩
  have hNe : ∀ x, k ≠ x → (st.modifyObject k f).objects[x]? = st.objects[x]? :=
    fun x e => by rw [hG x, if_neg e]
  refine notificationWaiterConsistent_of_tcbLinkFrame hC ?_ ?_ ?_ ?_
  · intro x n hx
    by_cases e : k = x
    · exact absurd hx ((hAt x e).2 n)
    · rwa [hNe x e] at hx
  · intro x n hx
    by_cases e : k = x
    · subst e; exact absurd hx (hkN n)
    · rwa [hNe x e]
  · intro x ty hx
    by_cases e : k = x
    · subst e; exact absurd hx (hkT ty)
    · exact ⟨ty, by rw [hNe x e]; exact hx, rfl, rfl, rfl⟩
  · intro x tx hx
    by_cases e : k = x
    · exact absurd hx ((hAt x e).1 tx)
    · exact ⟨tx, by rw [← hNe x e]; exact hx, rfl, rfl, rfl⟩

/-- A thread rewritten keeping its reply view, where it stands, keeps every view. -/
theorem replyViews_updateTcb_eq_of (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt)
    (hf : ∀ x, st.getTcb? t = some x → (f x).replyView = x.replyView) :
    (st.updateTcb t f).replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  by_cases e : t.toObjId = k
  · subst e
    cases hG : st.getTcb? t with
    | none => rw [SystemState.updateTcb_eq_self_of_none hG]
    | some x =>
      have hT := (SystemState.getTcb?_eq_some_iff st t x).mp hG
      rw [updateTcb_objects_self_of_tcb f hInv hT, hT]
      simp only [objReplyView_tcb, hf x hG]
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv]

-- ============================================================================
-- §2  An endpoint waiter's cancel
-- ============================================================================

/-- **The in-place pop keeps the notification queues**: it rewrites an
endpoint and two threads' endpoint-queue links. -/
theorem storePopHead_preserves_notificationWaiterConsistent (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (ep : Endpoint) (hInv : st.objects.invExt)
    (hC : notificationWaiterConsistent st) (hE : st.objects[endpointId]? = some (.endpoint ep)) :
    notificationWaiterConsistent (storePopHead st endpointId isReceiveQ head next) := by
  have hf : ∀ o, (∀ t, o ≠ .tcb t) → (∀ n, o ≠ .notification n) →
      (∀ t, popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next) o ≠ .tcb t) ∧
        ∀ n, popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next) o ≠ .notification n := by
    intro o hT hN
    cases o with
    | endpoint e =>
      simp only [popEndpoint]
      split <;> exact ⟨fun _ h => KernelObject.noConfusion h, fun _ h => KernelObject.noConfusion h⟩
    | tcb t => exact absurd rfl (hT t)
    | notification n => exact absurd rfl (hN n)
    | _ => exact ⟨hT, hN⟩
  have h1 := notificationWaiterConsistent_modifyObject_inert hInv hC hf
    (fun t h => by rw [hE] at h; cases h) (fun n h => by rw [hE] at h; cases h)
  have hI1 := modifyObject_preserves_objects_invExt
    (f := popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next)) (k := endpointId) hInv
  unfold storePopHead
  generalize st.modifyObject endpointId (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next)) = s1
    at h1 hI1
  have hKeep : ∀ (g : TCB → TCB), (∀ x, (g x).ipcState = x.ipcState ∧ (g x).ntfnPrev = x.ntfnPrev ∧
      (g x).ntfnNext = x.ntfnNext) → ∀ (s : SystemState) (u : SeLe4n.ThreadId), s.objects.invExt →
      notificationWaiterConsistent s →
      notificationWaiterConsistent (s.updateTcb u g) ∧ (s.updateTcb u g).objects.invExt :=
    fun g hg s u hs hc => ⟨notificationWaiterConsistent_updateTcb_keeping hs hc hg,
      SystemState.updateTcb_preserves_objects_invExt _ _ _ hs⟩
  cases next with
  | none => exact (hKeep tcbOffQueue (fun _ => ⟨rfl, rfl, rfl⟩) s1 head hI1 h1).1
  | some n =>
    have h2 := hKeep tcbAsQueueHead (fun _ => ⟨rfl, rfl, rfl⟩) s1 n hI1 h1
    exact (hKeep tcbOffQueue (fun _ => ⟨rfl, rfl, rfl⟩) _ head h2.2 h2.1).1

/-- **What an endpoint waiter's cancel keeps of the reachable state**: the
notification queues, every timeout budget, and the reply-waiter queues. -/
theorem storeEndpointWaiterCancelled_preserves_reachableParts (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (ep : Endpoint) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (hFull : ipcInvariantFull st)
    (hE : st.getEndpoint? endpointId = some ep)
    (hH : (endpointWaitQueue ep isReceiveQ).head = some t) (hT : st.getTcb? t = some tcb)
    (hC : endpointWaiterCancellable st endpointId t tcb = true)
    (hN : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext) ∧
      timeoutBudgetFrame st (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext) ∧
      (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext).replyWaitersConsistent := by
  obtain ⟨-, -, hG⟩ := endpointWaiterCancellable_parts hC
  have hEo := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hH' : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some t := hH
  have hBlk : tcb.ipcState = .blockedOnReceive endpointId ∨
      tcb.ipcState = .blockedOnSend endpointId ∨ tcb.ipcState = .blockedOnCall endpointId := by
    have hQ := hFull.queueHeadBlockedConsistent endpointId ep t tcb hEo hTo
    cases isReceiveQ
    · exact Or.inr (hQ.2 (by simpa using hH'))
    · exact Or.inl (hQ.1 (by simpa using hH'))
  have hNotNtfn : ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid := by
    intro oid h; rcases hBlk with e | e | e <;> rw [e] at h <;> cases h
  have hNoServer : tcb.blockingServer? = none := by
    rcases hBlk with e | e | e <;> simp [TCB.blockingServer?, e]
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId isReceiveQ ep t tcb hEo hH' hTo hG
  have hN1 := storePopHead_preserves_notificationWaiterConsistent st endpointId isReceiveQ t
    tcb.queueNext ep hInv hN hEo
  have hB1 := endpointQueuePopHead_timeoutBudgetFrame endpointId isReceiveQ st _ t tcb hInv hPop
  have hV1 := SystemState.endpointQueuePopHead_replyViews_eq hInv hPop
  have hI1 :=
    endpointQueuePopHead_preserves_objects_invExt endpointId isReceiveQ st _ t tcb hInv hPop
  unfold storeEndpointWaiterCancelled wakeCancelledWaiter
  generalize storePopHead st endpointId isReceiveQ t tcb.queueNext = s1 at hPop hFr hN1 hB1 hV1 hI1 ⊢
  have hT1 : s1.objects[t.toObjId]? = some (.tcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hFr.head_tcb
  -- The cancel: a thread blocked on an endpoint made `.ready`.
  have hS2 := updateTcb_objects_self_of_tcb cancelledEndpointWaiterTcb hI1 hT1
  have hI2 := SystemState.updateTcb_preserves_objects_invExt s1 t cancelledEndpointWaiterTcb hI1
  have hReady : (cancelledEndpointWaiterTcb (tcbOffQueue tcb)).ipcState = .ready :=
    TCB.ipcState_setIpcState
      { tcbOffQueue tcb with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
  have hN2 : notificationWaiterConsistent (s1.updateTcb t cancelledEndpointWaiterTcb) :=
    notificationWaiterConsistent_of_unblocked_tcb_write hN1 ⟨_, hT1, hNotNtfn⟩
      ⟨_, hS2, fun oid h => by rw [hReady] at h; cases h⟩
      (fun t0 t1 h0 h1 => by rw [hT1] at h0; rw [hS2] at h1; cases h0; cases h1; exact ⟨rfl, rfl⟩)
      (fun x hx => SystemState.updateTcb_objects_ne _ _ _ _ (Ne.symm hx) hI1)
  have hB2 := timeoutBudgetFrame_updateTcb s1 t (f := cancelledEndpointWaiterTcb) hI1 (fun _ => rfl)
  have hV2 : (s1.updateTcb t cancelledEndpointWaiterTcb).replyViews = s1.replyViews :=
    replyViews_updateTcb_eq_of s1 t hI1 (fun x hx => by
      rw [hFr.head_tcb] at hx; cases hx
      simp only [TCB.replyView, TCB.blockingServer?_eq, hReady]
      have : (tcbOffQueue tcb).blockingServer? = none := hNoServer
      simp only [TCB.blockingServer?_eq] at this
      rw [this]; rfl)
  -- The wake: a `.ready` thread's run links.
  have hG2 : (s1.updateTcb t cancelledEndpointWaiterTcb).getTcb? t =
      some (cancelledEndpointWaiterTcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS2
  have hAg := enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready _
    (determineTargetCore (s1.updateTcb t cancelledEndpointWaiterTcb) t) t _ hG2 hReady hI2
  refine ⟨notificationWaiterConsistent_of_objectsAgreeOffRunLinks hAg hN2,
    (hB1.trans hB2).trans (timeoutBudgetFrame.of_objectsAgreeOffRunLinks hAg), ?_⟩
  refine SystemState.replyWaitersConsistent.of_views ?_ hR
  rw [SystemState.enqueueRunnableOnCore_replyViews_eq _ _ _ hI2 (fun v hv => ?_), hV2, hV1]
  unfold SystemState.replyViews SystemState.getObject? at hv
  rw [hS2, objReplyView_tcb] at hv
  cases hv
  simp [TCB.replyView, TCB.blockingServer?_eq, hReady]

/-- **What a removal's writes keep, step by step**: the object table's
well-formedness, the notification queues, every timeout budget and every reply
view, with the endpoint's slot holding neither a thread nor a notification. -/
def queueRemoveKeeps (st : SystemState) (e : SeLe4n.ObjId) (s : SystemState) : Prop :=
  s.objects.invExt ∧ notificationWaiterConsistent s ∧ timeoutBudgetFrame st s ∧
    s.replyViews = st.replyViews ∧ (∀ t, s.objects[e]? ≠ some (.tcb t)) ∧
    ∀ n, s.objects[e]? ≠ some (.notification n)

/-- A thread's link write that keeps its IPC state, notification links, budget
and reply view keeps what a removal keeps. -/
theorem queueRemoveKeeps.updateTcb {st s : SystemState} {e : SeLe4n.ObjId}
    (h : queueRemoveKeeps st e s) (u : SeLe4n.ThreadId) {g : TCB → TCB}
    (hg : ∀ x, (g x).ipcState = x.ipcState ∧ (g x).ntfnPrev = x.ntfnPrev ∧
      (g x).ntfnNext = x.ntfnNext ∧ (g x).timeoutBudget = x.timeoutBudget ∧
      (g x).replyView = x.replyView) :
    queueRemoveKeeps st e (s.updateTcb u g) := by
  obtain ⟨hI, hN, hB, hV, hT, hNn⟩ := h
  have hAt : (s.updateTcb u g).objects[e]? = s.objects[e]? := by
    by_cases hue : u.toObjId = e
    · cases hG : s.getTcb? u with
      | none => rw [SystemState.updateTcb_eq_self_of_none hG]
      | some x =>
        exact absurd (hue ▸ (SystemState.getTcb?_eq_some_iff _ _ _).mp hG) (hT x)
    · exact SystemState.updateTcb_objects_ne _ _ _ _ hue hI
  refine ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ hI,
    notificationWaiterConsistent_updateTcb_keeping hI hN (fun x => ⟨(hg x).1, (hg x).2.1,
      (hg x).2.2.1⟩),
    hB.trans (timeoutBudgetFrame_updateTcb s u hI (fun x => (hg x).2.2.2.1)),
    (replyViews_updateTcb_eq_of s u hI (fun x _ => (hg x).2.2.2.2)).trans hV,
    fun t => by rw [hAt]; exact hT t, fun n => by rw [hAt]; exact hNn n⟩

/-- An endpoint rewritten in its slot, as an endpoint, keeps what a removal
keeps. -/
theorem queueRemoveKeeps.modifyObject {st s : SystemState} {e : SeLe4n.ObjId}
    (h : queueRemoveKeeps st e s) {f : KernelObject → KernelObject}
    (hf : ∀ o, f o = o ∨ ∃ ep ep', o = .endpoint ep ∧ f o = .endpoint ep') :
    queueRemoveKeeps st e (s.modifyObject e f) := by
  obtain ⟨hI, hN, hB, hV, hT, hNn⟩ := h
  have hf2 : ∀ o, (∀ t, o ≠ .tcb t) → (∀ n, o ≠ .notification n) →
      (∀ t, f o ≠ .tcb t) ∧ ∀ n, f o ≠ .notification n := by
    intro o hoT hoN
    rcases hf o with e | ⟨ep, ep', rfl, e⟩
    · rw [e]; exact ⟨hoT, hoN⟩
    · rw [e]; exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  have hf1 : ∀ o, (∀ t, o ≠ .tcb t) → ∀ t, f o ≠ .tcb t := by
    intro o hoT t
    rcases hf o with e | ⟨ep, ep', rfl, e⟩
    · rw [e]; exact hoT t
    · rw [e]; exact fun h => by cases h
  have hG := modifyObject_objects_getElem (f := f) (k := e) hI
  have hAt : (∀ t, (s.modifyObject e f).objects[e]? ≠ some (.tcb t)) ∧
      ∀ n, (s.modifyObject e f).objects[e]? ≠ some (.notification n) := by
    rw [hG e, if_pos rfl]
    cases ho : s.objects[e]? with
    | none => exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
    | some o =>
      simp only [Option.map_some]
      have := hf2 o (fun t ht => hT t (by rw [ho, ht])) (fun n hn => hNn n (by rw [ho, hn]))
      exact ⟨fun t h => this.1 t (Option.some.inj h), fun n h => this.2 n (Option.some.inj h)⟩
  refine ⟨modifyObject_preserves_objects_invExt hI,
    notificationWaiterConsistent_modifyObject_inert hI hN hf2 hT hNn,
    hB.trans (timeoutBudgetFrame_modifyObject_nonTcb s e hI hf1 hT), ?_, hAt.1, hAt.2⟩
  rw [← hV]
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  rw [hG k]
  split
  · next hk =>
    subst hk
    cases ho : s.objects[e]? with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      rcases hf o with h' | ⟨ep, ep', rfl, h'⟩
      · rw [h']
      · rw [h']; rfl
  · rfl

/-- **The removal's in-place writes keep what a removal keeps** (from the
endpoint at `e`): the endpoint's ends, the neighbours' endpoint-queue links and
the thread's. -/
theorem storeQueueRemove_keeps (st : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt)
    (hN : notificationWaiterConsistent st) (hE : st.objects[e]? = some (.endpoint ep)) :
    queueRemoveKeeps st e (storeQueueRemove st e q t ep tcb) := by
  have h0 : queueRemoveKeeps st e st :=
    ⟨hInv, hN, .refl st, rfl, fun _ h => (by rw [hE] at h; cases h),
      fun _ h => (by rw [hE] at h; cases h)⟩
  have hHead : ∀ c, ∀ o, headAdvancedEndpoint q c o = o ∨
      ∃ ep ep', o = .endpoint ep ∧ headAdvancedEndpoint q c o = .endpoint ep' := by
    intro c o; cases o with
    | endpoint x => exact Or.inr ⟨x, _, rfl, rfl⟩
    | _ => exact Or.inl rfl
  have hEnds : ∀ h t, ∀ o, endsSetEndpoint q h t o = o ∨
      ∃ ep ep', o = .endpoint ep ∧ endsSetEndpoint q h t o = .endpoint ep' := by
    intro h t o; cases o with
    | endpoint x => exact Or.inr ⟨x, _, rfl, rfl⟩
    | _ => exact Or.inl rfl
  have h1 : queueRemoveKeeps st e (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) := by
    split
    · exact h0.modifyObject (hHead _)
    · exact h0.updateTcb _ (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
    · exact h0
  have hNext : ∀ s1, queueRemoveKeeps st e s1 → queueRemoveKeeps st e (match tcb.queueNext with
      | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
      | none => s1) := by
    intro s1 h1; split
    · exact h1.updateTcb _ (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
    · exact h1
  unfold storeQueueRemove
  exact ((hNext _ h1).modifyObject (hEnds _ _)).updateTcb t (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- **What a thread's endpoint cancel keeps of the reachable state**: the
removal's writes keep the notification queues, every budget and every reply view
(`storeQueueRemove_keeps`); the thread, blocked sending, calling or receiving, so
on no notification and no server, is made `.ready`. -/
theorem storeEndpointBlockedCancelled_preserves_reachableParts (st : SystemState)
    (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hInv : st.objects.invExt) (hT : st.getTcb? t = some tcb) (hE : st.getEndpoint? e = some ep)
    (hC : endpointBlockedCancellable st e q t ep tcb = true)
    (hN : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent (storeEndpointBlockedCancelled st e q t ep tcb) ∧
      timeoutBudgetFrame st (storeEndpointBlockedCancelled st e q t ep tcb) ∧
      (storeEndpointBlockedCancelled st e q t ep tcb).replyWaitersConsistent := by
  obtain ⟨hSide, -, hG, -⟩ := endpointBlockedCancellable_parts hC
  have hEo := (SystemState.getEndpoint?_eq_some_iff st e ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  obtain ⟨-, hFr⟩ := queueRemove_inPlace st e q t ep tcb hEo hTo hG
  have hS := blockedOnQueueSide_ipcState hSide
  have hBlk : tcb.ipcState = .blockedOnReceive e ∨ tcb.ipcState = .blockedOnSend e ∨
      tcb.ipcState = .blockedOnCall e := by
    cases q
    · exact Or.inr (hS.2 rfl)
    · exact Or.inl (hS.1 rfl)
  have hNotNtfn : ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid := by
    intro oid h; rcases hBlk with x | x | x <;> rw [x] at h <;> cases h
  have hNoServer : tcb.blockingServer? = none := by
    rcases hBlk with x | x | x <;> simp [TCB.blockingServer?, x]
  obtain ⟨hI1, hN1, hB1, hV1, -, -⟩ := storeQueueRemove_keeps st e q t ep tcb hInv hN hEo
  unfold storeEndpointBlockedCancelled
  generalize storeQueueRemove st e q t ep tcb = s1 at hFr hI1 hN1 hB1 hV1 ⊢
  have hT1 : s1.objects[t.toObjId]? = some (.tcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hFr.removed_tcb
  have hS2 := updateTcb_objects_self_of_tcb cancelledEndpointWaiterTcb hI1 hT1
  have hReady : (cancelledEndpointWaiterTcb (tcbOffQueue tcb)).ipcState = .ready :=
    TCB.ipcState_setIpcState
      { tcbOffQueue tcb with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
  refine ⟨notificationWaiterConsistent_of_unblocked_tcb_write hN1 ⟨_, hT1, hNotNtfn⟩
      ⟨_, hS2, fun oid h => by rw [hReady] at h; cases h⟩
      (fun t0 t1 h0 h1 => by rw [hT1] at h0; rw [hS2] at h1; cases h0; cases h1; exact ⟨rfl, rfl⟩)
      (fun x hx => SystemState.updateTcb_objects_ne _ _ _ _ (Ne.symm hx) hI1),
    hB1.trans (timeoutBudgetFrame_updateTcb s1 t (f := cancelledEndpointWaiterTcb) hI1
      (fun _ => rfl)), ?_⟩
  refine SystemState.replyWaitersConsistent.of_views ?_ hR
  rw [replyViews_updateTcb_eq_of s1 t hI1 (fun x hx => ?_), hV1]
  rw [hFr.removed_tcb] at hx; cases hx
  simp only [TCB.replyView, TCB.blockingServer?_eq, hReady]
  have : (tcbOffQueue tcb).blockingServer? = none := hNoServer
  simp only [TCB.blockingServer?_eq] at this
  rw [this]; rfl

-- ============================================================================
-- §3  A notification waiter's cancel
-- ============================================================================

/-- **A notification's head taken off its queue keeps the queues**: the
notification rewritten with the successor as its head (`n'`, the queue's tail
kept unless the queue empties), then the head's links and its successor's
predecessor link cleared (`detachNtfnHead`), then the head rewritten `.ready`
with its links kept.  Read through the signal's head pop
(`notificationWaiterConsistent_of_headPop`), whose notification
(`Notification.withHeadPopped`) has the same queue ends as `n'`. -/
theorem notificationWaiterConsistent_headDetached {st st1 : SystemState} {n : SeLe4n.ObjId}
    {ntfn n' : Notification} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hC : notificationWaiterConsistent st)
    (hNo : st.objects[n]? = some (.notification ntfn)) (hH : ntfn.waitHead = some t)
    (hTo : st.objects[t.toObjId]? = some (.tcb tcb))
    (hI1 : st1.objects.invExt) (hN1 : st1.objects[n]? = some (.notification n'))
    (hO1 : ∀ x, n ≠ x → st1.objects[x]? = st.objects[x]?)
    (hHd : n'.waitHead = tcb.ntfnNext)
    (hTl : n'.waitTail = if tcb.ntfnNext.isSome then ntfn.waitTail else none)
    (g : TCB → TCB)
    (hg : ∀ x, (g x).ipcState = .ready ∧ (g x).ntfnPrev = x.ntfnPrev ∧ (g x).ntfnNext = x.ntfnNext) :
    notificationWaiterConsistent ((detachNtfnHead st1 t tcb.ntfnNext).updateTcb t g) := by
  have hBh : tcb.ipcState = .blockedOnNotification n := by
    obtain ⟨t0, ht0, hb⟩ := (hC.1 n ntfn hNo).2.1 t hH
    rw [hTo] at ht0; cases ht0; exact hb
  obtain ⟨n0, hN0, -, -, hNextH⟩ := hC.2.1 t tcb n hTo hBh
  rw [hNo] at hN0; cases hN0
  have hInj : ∀ (x y : SeLe4n.ThreadId), x ≠ y → x.toObjId ≠ y.toObjId :=
    fun x y hne e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hNotSelf : tcb.ntfnNext ≠ some t := fun e => (hNextH t e).1 hH
  have hnt : n ≠ t.toObjId := by intro e; rw [e, hTo] at hNo; cases hNo
  have hSucc : ∀ b, tcb.ntfnNext = some b → b ≠ t ∧ n ≠ b.toObjId ∧
      ∃ tb, st.objects[b.toObjId]? = some (.tcb tb) := by
    intro b hb
    obtain ⟨-, tb, hTb, -⟩ := hNextH b hb
    refine ⟨fun e => hNotSelf (e ▸ hb), fun e => ?_, tb, hTb⟩
    rw [e, hTb] at hNo; cases hNo
  have hT1 : st1.objects[t.toObjId]? = some (.tcb tcb) := (hO1 _ hnt).trans hTo
  have hL2 := detachNtfnHead_linksRewritten st1 t tcb.ntfnNext hI1
  have hI2 := hL2.2.1
  have hDetNe : ∀ x, t.toObjId ≠ x → (∀ b, tcb.ntfnNext = some b → b.toObjId ≠ x) →
      (detachNtfnHead st1 t tcb.ntfnNext).objects[x]? = st1.objects[x]? :=
    fun x h1 h2 => detachNtfnHead_objects_ne _ _ _ hI1 x h1 h2
  generalize hS2 : detachNtfnHead st1 t tcb.ntfnNext = s2 at hL2 hI2 hDetNe
  obtain ⟨th, hTh, hIh, hPh, hNh⟩ := hS2 ▸ detachNtfnHead_head hI1 hT1 hNotSelf
  have hS3 := updateTcb_objects_self_of_tcb g hI2 hTh
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 t g hI2
  have hO3 : ∀ x, t.toObjId ≠ x → (s2.updateTcb t g).objects[x]? = s2.objects[x]? :=
    fun x hx => SystemState.updateTcb_objects_ne _ _ _ x hx hI2
  generalize s2.updateTcb t g = s3 at hS3 hI3 hO3 ⊢
  -- The same writes with the signal's notification.
  let s4 : SystemState :=
    { s3 with objects := s3.objects.insert n (.notification (ntfn.withHeadPopped tcb.ntfnNext)) }
  have h4N : s4.objects[n]? = some (.notification (ntfn.withHeadPopped tcb.ntfnNext)) :=
    RobinHood.RHTable.getElem?_insert_self s3.objects n _ hI3
  have h4O : ∀ x, n ≠ x → s4.objects[x]? = s3.objects[x]? := fun x hx =>
    RobinHood.RHTable.getElem?_insert_ne s3.objects n x _ (fun hb => hx (eq_of_beq hb)) hI3
  have h4 : notificationWaiterConsistent s4 := by
    refine notificationWaiterConsistent_of_headPop hC hNo hH hTo h4N ?_ ?_ ?_
    · refine ⟨g th, by rw [h4O _ hnt, hS3], fun oid h => ?_, ?_, ?_⟩
      · rw [(hg th).1] at h; cases h
      · rw [(hg th).2.1, hPh]
      · rw [(hg th).2.2, hNh]
    · intro b tb hb hTb
      obtain ⟨hbt, hbn, -⟩ := hSucc b hb
      have hTb1 : st1.objects[b.toObjId]? = some (.tcb tb) := (hO1 _ hbn).trans hTb
      have hDs := detachNtfnHead_successor hI1 hbt hTb1
      rw [← hb, hS2] at hDs
      obtain ⟨tb', hTb', hI, hP, hNx⟩ := hDs
      exact ⟨tb', by rw [h4O _ hbn, hO3 _ (hInj t b (Ne.symm hbt))]; exact hTb', hI, hP, hNx⟩
    · intro x hx hxt hxs
      rw [h4O _ (Ne.symm hx), hO3 _ (Ne.symm hxt),
        hDetNe _ (Ne.symm hxt) (fun b hb => Ne.symm (hxs b hb)), hO1 _ (Ne.symm hx)]
  refine notificationWaiterConsistent_of_queueEnds_write h4 h4N (n' := n') ?_ ?_ ?_ ?_
  · rw [hO3 _ hnt.symm, hDetNe _ hnt.symm (fun b hb => Ne.symm (hSucc b hb).2.1)]; exact hN1
  · rw [hHd]; simp [Notification.withHeadPopped, Notification.waitHead]
  · rw [hTl]; cases tcb.ntfnNext <;> rfl
  · intro x hx; exact (h4O x (Ne.symm hx)).symm

/-- **A notification head's cancel, as the queue writes it**: the notification
rewritten with the head's successor as its head, then the head detached
(`detachNtfnHead`), then the head restored `.ready` with the cancellation
frame. -/
theorem cancelIpcBlocking_notificationHead_eq {st : SystemState} {n : SeLe4n.ObjId}
    {ntfn : Notification} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hN : st.getNotification? n = some ntfn) (hH : ntfn.waitHead = some t)
    (hT : st.getTcb? t = some tcb) (hB : tcb.ipcState = .blockedOnNotification n)
    (hInv : st.objects.invExt) :
    ∃ (st1 : SystemState) (n' : Notification), st1 = { st with objects := st1.objects } ∧
      st1.objects[n]? = some (.notification n') ∧ st1.objects.invExt ∧ (∀ x, n ≠ x → st1.objects[x]? = st.objects[x]?) ∧
      n'.waitHead = tcb.ntfnNext ∧
      n'.waitTail = (if tcb.ntfnNext.isSome then ntfn.waitTail else none) ∧
      Lifecycle.Suspend.cancelIpcBlocking st t tcb =
        (detachNtfnHead st1 t tcb.ntfnNext).updateTcb t
          (fun x => x.restoredToReady.withReturnFrame Architecture.cancelledIpcFrame) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    removeFromNotificationWaitQueue
  simp only [hT, hB, SystemState.getNotificationWitnessed?_eq_some hN, hH, if_true]
  refine ⟨_, _, rfl, SystemState.rewriteObject_objects_self _ _ _ _ hInv,
    SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv,
    fun x hx => SystemState.rewriteObject_objects_ne _ _ _ _ _ hx hInv, ?_, ?_, rfl⟩
  · simp [Notification.waitHead]
  · simp only [Notification.waitTail, SeLe4n.ThreadId.ofOptCode_optCode]

/-- A notification queue's unlink frames every budget: it rewrites a
notification and threads' notification links. -/
theorem timeoutBudgetFrame_of_ntfnUnlinkReach {st s : SystemState} (h : ntfnUnlinkReach st s) :
    timeoutBudgetFrame st s := by
  intro tid tcb' hT
  rcases h.2 tid.toObjId with e | ⟨_, _, _, e, _⟩ | ⟨t0, t1, h0, h1, hR⟩
  · exact ⟨tcb', e.symm.trans hT, rfl⟩
  · rw [hT] at e; cases e
  · rw [hT] at h1; cases h1
    obtain ⟨np, nn, hEq⟩ := hR
    exact ⟨t0, h0, by rw [hEq]⟩

/-- **A waiter with a predecessor `p` cancelled off its notification's queue,
as the queue writes it** (`storeNotificationBlockedCancelled` when the waiter is
not the head): the notification keeps its head and ends at `p` when the waiter
ended it; the waiter is `.ready` with no links; `p` links to the waiter's
successor `next`, and `next` back to `p`; nothing else changes. -/
theorem storeNotificationBlockedCancelled_unlinked {st : SystemState} {n : SeLe4n.ObjId}
    {ntfn : Notification} {t p : SeLe4n.ThreadId} {next : Option SeLe4n.ThreadId} {tcb tp : TCB}
    (hInv : st.objects.invExt) (hNo : st.objects[n]? = some (.notification ntfn))
    (hTo : st.objects[t.toObjId]? = some (.tcb tcb))
    (hTp : st.objects[p.toObjId]? = some (.tcb tp)) (hpt : p ≠ t)
    (hNx : ∀ b, next = some b → b ≠ t ∧ b ≠ p) :
    (∃ n', (storeNotificationBlockedCancelled st n t false (some p) next).objects[n]? =
        some (.notification n') ∧ n'.waitHead = ntfn.waitHead ∧
        n'.waitTail = (if next.isSome then ntfn.waitTail else some p)) ∧
    (∃ x, (storeNotificationBlockedCancelled st n t false (some p) next).objects[t.toObjId]? =
        some (.tcb x) ∧ x.ipcState = .ready ∧ x.ntfnPrev = none ∧ x.ntfnNext = none) ∧
    (storeNotificationBlockedCancelled st n t false (some p) next).objects[p.toObjId]? =
        some (.tcb { tp with ntfnNextCode := SeLe4n.ThreadId.optCode next }) ∧
    (∀ b tb, next = some b → st.objects[b.toObjId]? = some (.tcb tb) →
      (storeNotificationBlockedCancelled st n t false (some p) next).objects[b.toObjId]? =
        some (.tcb { tb with ntfnPrevCode := SeLe4n.ThreadId.optCode (some p) })) ∧
    (∀ x, x ≠ n → x ≠ t.toObjId → x ≠ p.toObjId → (∀ b, next = some b → x ≠ b.toObjId) →
      (storeNotificationBlockedCancelled st n t false (some p) next).objects[x]? =
        st.objects[x]?) ∧
    (storeNotificationBlockedCancelled st n t false (some p) next).objects.invExt := by
  have hInj : ∀ (x y : SeLe4n.ThreadId), x ≠ y → x.toObjId ≠ y.toObjId :=
    fun x y hne e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hnt : n ≠ t.toObjId := fun e => by rw [e, hTo] at hNo; cases hNo
  have hnp : n ≠ p.toObjId := fun e => by rw [e, hTp] at hNo; cases hNo
  have hI1 := modifyObject_preserves_objects_invExt
    (f := cancelledNotificationObject false (some p) next) (k := n) hInv
  have hG1 := modifyObject_objects_getElem (f := cancelledNotificationObject false (some p) next)
    (k := n) hInv
  have h1O : ∀ x, n ≠ x → (st.modifyObject n (cancelledNotificationObject false (some p) next)
      ).objects[x]? = st.objects[x]? := fun x hx => by rw [hG1, if_neg hx]
  have h1N := hG1 n
  rw [if_pos rfl, hNo] at h1N
  unfold storeNotificationBlockedCancelled Lifecycle.Suspend.restoreToReadyCancelled
    Lifecycle.Suspend.restoreToReadyStaging unlinkNtfnNeighbours clearNtfnLinks
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize st.modifyObject n (cancelledNotificationObject false (some p) next) = s1
    at hI1 h1O h1N
  -- The waiter's links cleared.
  have h2T := updateTcb_objects_self_of_tcb (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none, ntfnNextCode := SeLe4n.ThreadId.optCode none })
    hI1 ((h1O _ hnt).trans hTo)
  have hI2 := SystemState.updateTcb_preserves_objects_invExt s1 t (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none, ntfnNextCode := SeLe4n.ThreadId.optCode none }) hI1
  have h2O := fun x hx => SystemState.updateTcb_objects_ne s1 t (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none, ntfnNextCode := SeLe4n.ThreadId.optCode none })
    x hx hI1
  generalize s1.updateTcb t _ = s2 at h2T hI2 h2O
  -- The predecessor pointed at the successor.
  have h3P := updateTcb_objects_self_of_tcb (fun t => { t with
    ntfnNextCode := SeLe4n.ThreadId.optCode next }) hI2
    ((h2O _ (hInj t p (Ne.symm hpt))).trans ((h1O _ hnp).trans hTp))
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 p (fun t => { t with
    ntfnNextCode := SeLe4n.ThreadId.optCode next }) hI2
  have h3O := fun x hx => SystemState.updateTcb_objects_ne s2 p (fun t => { t with
    ntfnNextCode := SeLe4n.ThreadId.optCode next }) x hx hI2
  generalize s2.updateTcb p _ = s3 at h3P hI3 h3O
  -- The restore of the waiter, over whatever the successor's write left.
  have hFin : ∀ (s4 : SystemState), s4.objects.invExt →
      s4.objects[t.toObjId]? = some (.tcb { tcb with ntfnPrevCode := 0, ntfnNextCode := 0 }) →
      (∀ x, t.toObjId ≠ x →
        (s4.updateTcb t (fun x => x.restoredToReady.withReturnFrame Architecture.cancelledIpcFrame)
          ).objects[x]? = s4.objects[x]?) ∧
      (∃ x, (s4.updateTcb t (fun x => x.restoredToReady.withReturnFrame
          Architecture.cancelledIpcFrame)).objects[t.toObjId]? = some (.tcb x) ∧
        x.ipcState = .ready ∧ x.ntfnPrev = none ∧ x.ntfnNext = none) ∧
      (s4.updateTcb t (fun x => x.restoredToReady.withReturnFrame
          Architecture.cancelledIpcFrame)).objects.invExt := by
    intro s4 hI4 h4T
    refine ⟨fun x hx => SystemState.updateTcb_objects_ne _ _ _ x hx hI4,
      ⟨_, updateTcb_objects_self_of_tcb _ hI4 h4T, by simp, rfl, rfl⟩,
      SystemState.updateTcb_preserves_objects_invExt _ _ _ hI4⟩
  have hTp3 : s3.objects[t.toObjId]? = some (.tcb { tcb with ntfnPrevCode := 0, ntfnNextCode := 0 }) :=
    (h3O _ (hInj p t hpt)).trans h2T
  have hN3 : s3.objects[n]? = s1.objects[n]? :=
    (h3O _ (Ne.symm hnp)).trans (h2O _ (Ne.symm hnt))
  have hNtfnEnds : ∃ n', s1.objects[n]? = some (.notification n') ∧ n'.waitHead = ntfn.waitHead ∧
      n'.waitTail = (if next.isSome then ntfn.waitTail else some p) := by
    rw [h1N]
    refine ⟨_, rfl, ?_, ?_⟩
    · exact SeLe4n.ThreadId.ofOptCode_optCode _
    · exact SeLe4n.ThreadId.ofOptCode_optCode _
  cases next with
  | none =>
    dsimp only
    obtain ⟨hO5, hT5, hI5⟩ := hFin s3 hI3 hTp3
    obtain ⟨n', hN', hH', hT'⟩ := hNtfnEnds
    refine ⟨⟨n', by rw [hO5 _ (Ne.symm hnt), hN3]; exact hN', hH', hT'⟩, hT5,
      by rw [hO5 _ (hInj t p (Ne.symm hpt))]; exact h3P, fun b _ hb _ => (by cases hb),
      fun x h1 h2 h3 _ => ?_, hI5⟩
    rw [hO5 _ (Ne.symm h2), h3O _ (Ne.symm h3), h2O _ (Ne.symm h2), h1O _ (Ne.symm h1)]
  | some b =>
    dsimp only
    obtain ⟨hbt, hbp⟩ := hNx b rfl
    have hRest : ∀ tb, st.objects[b.toObjId]? = some (.tcb tb) →
        s3.objects[b.toObjId]? = some (.tcb tb) := fun tb hTb =>
      (h3O _ (hInj p b (Ne.symm hbp))).trans ((h2O _ (hInj t b (Ne.symm hbt))).trans
        ((h1O _ (fun e => by rw [e, hTb] at hNo; cases hNo)).trans hTb))
    have hI4 := SystemState.updateTcb_preserves_objects_invExt s3 b (fun t => { t with
      ntfnPrevCode := SeLe4n.ThreadId.optCode (some p) }) hI3
    have h4O := fun x hx => SystemState.updateTcb_objects_ne s3 b (fun t => { t with
      ntfnPrevCode := SeLe4n.ThreadId.optCode (some p) }) x hx hI3
    obtain ⟨hO5, hT5, hI5⟩ := hFin _ hI4 ((h4O _ (hInj b t hbt)).trans hTp3)
    obtain ⟨n', hN', hH', hT'⟩ := hNtfnEnds
    have hnb : ∀ tb, st.objects[b.toObjId]? = some (.tcb tb) → n ≠ b.toObjId :=
      fun tb hTb e => by rw [e, hTb] at hNo; cases hNo
    refine ⟨⟨n', ?_, hH', hT'⟩, hT5, ?_, fun b' tb hb hTb => ?_, fun x h1 h2 h3 h4 => ?_, hI5⟩
    · rw [hO5 _ (Ne.symm hnt)]
      by_cases hbn : b.toObjId = n
      · -- `b` holds no TCB, so its write is the identity.
        have hNone : s3.getTcb? b = none := by
          cases hG : s3.getTcb? b with
          | none => rfl
          | some x =>
            have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hG
            rw [hbn, hN3, hN'] at this; cases this
        rw [SystemState.updateTcb_eq_self_of_none hNone, hN3]; exact hN'
      · rw [h4O _ hbn, hN3]; exact hN'
    · rw [hO5 _ (hInj t p (Ne.symm hpt)), h4O _ (hInj b p hbp)]; exact h3P
    · simp only [Option.some.injEq] at hb; subst hb
      rw [hO5 _ (hInj t b (Ne.symm hbt))]
      exact updateTcb_objects_self_of_tcb _ hI3 (hRest tb hTb)
    · rw [hO5 _ (Ne.symm h2), h4O _ (Ne.symm (h4 b rfl)), h3O _ (Ne.symm h3),
        h2O _ (Ne.symm h2), h1O _ (Ne.symm h1)]

/-- **What a notification waiter's cancel keeps of the reachable state**,
before any wake, wherever the waiter waits in the queue: the queue it leaves —
the head's detach (`cancelIpcBlocking_notificationHead_eq`), or a waiter's unlink
behind its predecessor (`storeNotificationBlockedCancelled_unlinked`,
`notificationWaiterConsistent_of_unlink`) — every timeout budget, and the
reply-waiter queues (the cancellation's own theorem). -/
theorem notificationCancel_preserves_reachableParts (st : SystemState)
    (notificationId : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) (hN : st.getNotification? notificationId = some ntfn)
    (hT : st.getTcb? t = some tcb)
    (hB : tcb.ipcState = .blockedOnNotification notificationId)
    (hNC : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent (Lifecycle.Suspend.cancelIpcBlocking st t tcb) ∧
      timeoutBudgetFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) ∧
      (Lifecycle.Suspend.cancelIpcBlocking st t tcb).replyWaitersConsistent := by
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hNo := (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN
  refine ⟨?_, ?_, cancelIpcBlocking_preserves_replyWaitersConsistent st t tcb hT hInv hR⟩
  · by_cases hH : ntfn.waitHead = some t
    · obtain ⟨st1, n', -, hN1, hI1, hO1, hHd, hTl, hEq⟩ :=
        cancelIpcBlocking_notificationHead_eq hN hH hT hB hInv
      rw [hEq]
      exact notificationWaiterConsistent_headDetached hNC hNo hH hTo hI1 hN1 hO1 hHd hTl _
        (fun x => ⟨by simp, rfl, rfl⟩)
    · -- Not the head: the waiter has a predecessor, which links to it.
      obtain ⟨n0, hN0, hPrevT, -, -⟩ := hNC.2.1 t tcb notificationId hTo hB
      rw [hNo] at hN0; cases hN0
      obtain ⟨p, tp, hP, hTp, -, -⟩ : ∃ p tp, tcb.ntfnPrev = some p ∧
          st.objects[p.toObjId]? = some (.tcb tp) ∧ tp.ipcState = .blockedOnNotification notificationId ∧
          tp.ntfnNext = some t := by
        rcases hPrevT with e | ⟨a, ta, ha, hTa, hBa, hNa⟩
        · exact absurd e hH
        · exact ⟨a, ta, ha, hTa, hBa, hNa⟩
      obtain ⟨hpt, hbD⟩ := notificationWaiter_neighbours_distinct hNC hTo hB
      rw [cancelIpcBlocking_notification_inPlace hN hT hB,
        show (ntfn.waitHead == some t) = false from by simp [hH], hP]
      obtain ⟨⟨n', hN', hH', hT'⟩, ⟨x, hX, hXr, hXp, hXn⟩, hPP, hPS, hPO, -⟩ :=
        storeNotificationBlockedCancelled_unlinked (next := tcb.ntfnNext) hInv hNo hTo hTp
          (hpt p hP) (fun b hb => ⟨(hbD b hb).1, (hbD b hb).2 p hP⟩)
      refine notificationWaiterConsistent_of_unlink hNC hNo hTo hB hP hN' hH' hT'
        ⟨x, hX, fun oid h => (by rw [hXr] at h; cases h), hXp, hXn⟩
        (fun tp' hTp' => ?_) (fun b tb hb hTb => ?_) hPO
      · rw [hTp] at hTp'; cases hTp'
        exact ⟨_, hPP, rfl, rfl, SeLe4n.ThreadId.ofOptCode_optCode tcb.ntfnNext⟩
      · exact ⟨_, hPS b tb hb hTb, rfl, SeLe4n.ThreadId.ofOptCode_optCode (some p), rfl⟩
  · have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue st t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    have hReach := removeFromNotificationWaitQueue_reach st t hInv
    rw [hEq]
    exact (timeoutBudgetFrame_of_ntfnUnlinkReach hReach).trans
      (timeoutBudgetFrame_updateTcb _ t hReach.1 (fun _ => rfl))

/-- **What a notification waiter's cancel keeps of the reachable state**: the
cancel's (`notificationCancel_preserves_reachableParts`), then the wake of the
`.ready` thread, which writes run links alone. -/
theorem notificationWaiterCancel_preserves_reachableParts (st : SystemState)
    (notificationId : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) (hN : st.getNotification? notificationId = some ntfn)
    (hT : st.getTcb? t = some tcb)
    (hC : notificationWaiterCancellable st notificationId t tcb = true)
    (hNC : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent
        (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) ∧
      timeoutBudgetFrame st
        (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) ∧
      (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t).replyWaitersConsistent := by
  obtain ⟨hNotRes, hB, -, -, -⟩ := notificationWaiterCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hLookup : lookupTcb st t = some tcb :=
    lookupTcb_of_objects_of_not_reserved st t tcb hTo hNotRes
  obtain ⟨hNC1, hB1, hR1⟩ :=
    notificationCancel_preserves_reachableParts st notificationId ntfn t tcb hInv hN hT hB hNC hR
  have hFr := FinaliseFrame.notificationCancel st t tcb notificationId hInv hB
  have hI1 := hFr.invExt
  -- The victim, `.ready`, where it stands.
  obtain ⟨x, hX⟩ : ∃ x, (Lifecycle.Suspend.cancelIpcBlocking st t tcb).objects[t.toObjId]? =
      some (.tcb x) := by
    rcases hFr.kind t.toObjId with e | ⟨pre, post, hPre, hPost, hTy, -⟩
    · exact ⟨tcb, e.trans hTo⟩
    · rw [hTo] at hPre; cases hPre
      cases post <;> simp [KernelObject.objectType] at hTy
      exact ⟨_, hPost⟩
  have hXr := cancelIpcBlocking_victim_ready st t tcb hInv hLookup x hX
  have hAg := enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready _
    (determineTargetCore (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) t x
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hX) hXr hI1
  unfold wakeCancelledWaiter
  refine ⟨notificationWaiterConsistent_of_objectsAgreeOffRunLinks hAg hNC1,
    hB1.trans (timeoutBudgetFrame.of_objectsAgreeOffRunLinks hAg), ?_⟩
  refine SystemState.replyWaitersConsistent.of_views ?_ hR1
  rw [SystemState.enqueueRunnableOnCore_replyViews_eq _ _ _ hI1 (fun v hv => ?_)]
  unfold SystemState.replyViews SystemState.getObject? at hv
  rw [hX, objReplyView_tcb] at hv
  cases hv
  simp [TCB.replyView, TCB.blockingServer?_eq, hXr]

-- ============================================================================
-- §4  The unbind
-- ============================================================================

/-- **What the unbind keeps of the reachable state**: it clears the thread's
binding, which no queue reads, and the notification's, which leaves its queue
ends alone; it writes no budget and no reply view. -/
theorem storeUnbindNotification_preserves_reachableParts (st : SystemState)
    (notificationId : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hN : st.getNotification? notificationId = some ntfn)
    (hNC : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent (storeUnbindNotification st t notificationId) ∧
      timeoutBudgetFrame st (storeUnbindNotification st t notificationId) ∧
      (storeUnbindNotification st t notificationId).replyWaitersConsistent := by
  have hNo := (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN
  have hN1 := notificationWaiterConsistent_updateTcb_keeping (t := t)
    (f := fun x => { x with boundNotificationCode := 0 }) hInv hNC (fun _ => ⟨rfl, rfl, rfl⟩)
  have hI1 := SystemState.updateTcb_preserves_objects_invExt st t
    (fun x => { x with boundNotificationCode := 0 }) hInv
  have hB1 := timeoutBudgetFrame_updateTcb st t
    (f := fun x => { x with boundNotificationCode := 0 }) hInv (fun _ => rfl)
  have hV1 := replyViews_updateTcb_eq_of st t
    (f := fun x => { x with boundNotificationCode := 0 }) hInv (fun _ _ => rfl)
  have hK1 : (st.updateTcb t (fun x => { x with boundNotificationCode := 0 })).objects[notificationId]? =
      some (.notification ntfn) := by
    by_cases e : t.toObjId = notificationId
    · cases hG : st.getTcb? t with
      | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact hNo
      | some x =>
        have := (SystemState.getTcb?_eq_some_iff st t x).mp hG
        rw [e, hNo] at this; cases this
    · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hInv]; exact hNo
  unfold storeUnbindNotification
  generalize st.updateTcb t (fun x => { x with boundNotificationCode := 0 }) = s1
    at hN1 hI1 hB1 hV1 hK1
  have hG := modifyObject_objects_getElem
    (f := mapNotificationObject fun n => { n with boundTCBCode := 0 }) (k := notificationId) hI1
  refine ⟨notificationWaiterConsistent_of_queueEnds_write hN1 hK1
    (n' := { ntfn with boundTCBCode := 0 }) (by rw [hG, if_pos rfl, hK1]; rfl) rfl rfl
    (fun x hx => by rw [hG, if_neg (Ne.symm hx)]), ?_, ?_⟩
  · refine hB1.trans (timeoutBudgetFrame_modifyObject_nonTcb s1 notificationId hI1 ?_ ?_)
    · intro o ho u
      cases o with
      | notification m => exact fun h => KernelObject.noConfusion h
      | _ => exact ho u
    · intro u h; rw [hK1] at h; cases h
  · refine SystemState.replyWaitersConsistent.of_views ?_ hR
    rw [← hV1]
    funext k
    unfold SystemState.replyViews SystemState.getObject?
    rw [hG k]
    split
    · next e => rw [← e, hK1]; rfl
    · rfl

-- ============================================================================
-- §4a  A step that writes only fields the reachable parts do not read
-- ============================================================================

/-- **What the notification queues, the budgets and the reply views read of a
thread**, kept by a step. -/
def tcbReachFieldsKept (tx ty : TCB) : Prop :=
  tx.ipcState = ty.ipcState ∧ tx.ntfnPrev = ty.ntfnPrev ∧ tx.ntfnNext = ty.ntfnNext ∧
    tx.timeoutBudget = ty.timeoutBudget ∧ tx.replyView = ty.replyView

/-- **A step that keeps every notification, and every thread up to fields the
reachable parts do not read** (a scheduling binding, the thread state), with
any other object free to change: what a reservation unbind and a suspend
write. -/
structure ReachFieldFrame (st st' : SystemState) : Prop where
  ntfn : ∀ (k : SeLe4n.ObjId) (n : Notification),
    st'.objects[k]? = some (.notification n) ↔ st.objects[k]? = some (.notification n)
  fwd : ∀ (k : SeLe4n.ObjId) (ty : TCB), st.objects[k]? = some (.tcb ty) →
    ∃ tx, st'.objects[k]? = some (.tcb tx) ∧ tcbReachFieldsKept tx ty
  bwd : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
    ∃ ty, st.objects[k]? = some (.tcb ty) ∧ tcbReachFieldsKept tx ty

namespace ReachFieldFrame

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    ReachFieldFrame st st' :=
  ⟨fun _ _ => by rw [h], fun _ ty hy => ⟨ty, by rw [h]; exact hy, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ tx hx => ⟨tx, by rw [← h]; exact hx, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem trans {a b c : SystemState} (h₁ : ReachFieldFrame a b) (h₂ : ReachFieldFrame b c) :
    ReachFieldFrame a c := by
  refine ⟨fun k n => (h₂.ntfn k n).trans (h₁.ntfn k n), fun k ty hy => ?_, fun k tx hx => ?_⟩
  · obtain ⟨tm, hm, r₁⟩ := h₁.fwd k ty hy
    obtain ⟨tx, hx, r₂⟩ := h₂.fwd k tm hm
    exact ⟨tx, hx, r₂.1.trans r₁.1, r₂.2.1.trans r₁.2.1, r₂.2.2.1.trans r₁.2.2.1,
      r₂.2.2.2.1.trans r₁.2.2.2.1, r₂.2.2.2.2.trans r₁.2.2.2.2⟩
  · obtain ⟨tm, hm, r₂⟩ := h₂.bwd k tx hx
    obtain ⟨ty, hy, r₁⟩ := h₁.bwd k tm hm
    exact ⟨ty, hy, r₂.1.trans r₁.1, r₂.2.1.trans r₁.2.1, r₂.2.2.1.trans r₁.2.2.1,
      r₂.2.2.2.1.trans r₁.2.2.2.1, r₂.2.2.2.2.trans r₁.2.2.2.2⟩

/-- A thread rewritten in its slot keeping what the reachable parts read. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, tcbReachFieldsKept (f x) x) :
    ReachFieldFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact of_objects_eq rfl
  | some x =>
    have hT := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    have hS := updateTcb_objects_self_of_tcb f hInv hT
    have hO : ∀ k, t.toObjId ≠ k → (st.updateTcb t f).objects[k]? = st.objects[k]? :=
      fun k hk => SystemState.updateTcb_objects_ne _ _ _ k hk hInv
    refine ⟨fun k n => ?_, fun k ty hy => ?_, fun k tx hx => ?_⟩
    · by_cases e : t.toObjId = k
      · subst e; rw [hS, hT]; simp
      · rw [hO k e]
    · by_cases e : t.toObjId = k
      · subst e; rw [hT] at hy; cases hy; exact ⟨f x, hS, hf x⟩
      · exact ⟨ty, by rw [hO k e]; exact hy, rfl, rfl, rfl, rfl, rfl⟩
    · by_cases e : t.toObjId = k
      · subst e; rw [hS] at hx; cases hx; exact ⟨x, hT, hf x⟩
      · exact ⟨tx, by rw [← hO k e]; exact hx, rfl, rfl, rfl, rfl, rfl⟩

/-- A scheduling context rewritten in its slot. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    ReachFieldFrame st (st.updateSchedContext s f) := by
  cases hG : st.getSchedContext? s with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact of_objects_eq rfl
  | some x =>
    have hT := (SystemState.getSchedContext?_eq_some_iff st s x).mp hG
    rw [SystemState.updateSchedContext_eq_of_some hG]
    have hS : (st.objects.insert s.toObjId (.schedContext (f x)))[s.toObjId]? =
        some (.schedContext (f x)) := RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
    have hO : ∀ k, s.toObjId ≠ k →
        (st.objects.insert s.toObjId (.schedContext (f x)))[k]? = st.objects[k]? :=
      fun k hk => RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun h => hk (eq_of_beq h)) hInv
    refine ⟨fun k n => ?_, fun k ty hy => ?_, fun k tx hx => ?_⟩
    · show (st.objects.insert s.toObjId _)[k]? = _ ↔ _
      by_cases e : s.toObjId = k
      · subst e; rw [hS, hT]; simp
      · rw [hO k e]
    · show ∃ tx, (st.objects.insert s.toObjId _)[k]? = _ ∧ _
      by_cases e : s.toObjId = k
      · subst e; rw [hT] at hy; cases hy
      · exact ⟨ty, by rw [hO k e]; exact hy, rfl, rfl, rfl, rfl, rfl⟩
    · change (st.objects.insert s.toObjId _)[k]? = _ at hx
      by_cases e : s.toObjId = k
      · subst e; rw [hS] at hx; cases hx
      · exact ⟨tx, by rw [← hO k e]; exact hx, rfl, rfl, rfl, rfl, rfl⟩

/-- WS-ZA ZA6.6: a thread's yield link cancelled. -/
theorem cancelYieldTo (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    ReachFieldFrame st (SeLe4n.Kernel.cancelYieldTo st t) := by
  unfold SeLe4n.Kernel.cancelYieldTo
  split
  · split
    · exact of_objects_eq rfl
    · rename_i k _
      exact (updateSchedContext st ⟨k⟩ _ hInv).trans (updateTcb _ t
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
        (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · exact of_objects_eq rfl

/-- WS-ZA ZA6.6: a context's consumed time handed to a thread's registers. -/
theorem setConsumed (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : ReachFieldFrame st (SeLe4n.Kernel.setConsumed st s t) := by
  unfold SeLe4n.Kernel.setConsumed
  split
  · exact (updateSchedContext st s _ hInv).trans (updateTcb _ t
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
      (by intro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · exact of_objects_eq rfl

/-- WS-ZA ZA6.6: a context's yield link cancelled. -/
theorem cancelYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : ReachFieldFrame st (SeLe4n.Kernel.cancelYieldFrom st s) := by
  unfold SeLe4n.Kernel.cancelYieldFrom
  split
  · split
    · exact of_objects_eq rfl
    · exact (updateSchedContext st s _ hInv).trans (updateTcb _ _
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
        (by intro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · exact of_objects_eq rfl

/-- WS-ZA ZA6.6: the completion of a context's recorded yield. -/
theorem completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : ReachFieldFrame st (SeLe4n.Kernel.completeYieldFrom st s) := by
  unfold SeLe4n.Kernel.completeYieldFrom
  split
  · split
    · exact of_objects_eq rfl
    · rename_i k _
      exact (setConsumed st s ⟨k⟩ hInv).trans
        (cancelYieldFrom _ s (SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv))
  · exact of_objects_eq rfl

/-- **The reachable parts a frame keeps**: the notification queues, every
budget, and the reply views. -/
theorem parts {st st' : SystemState} (h : ReachFieldFrame st st')
    (hC : notificationWaiterConsistent st) :
    notificationWaiterConsistent st' ∧ timeoutBudgetFrame st st' ∧
      st'.replyViews = st.replyViews := by
  refine ⟨notificationWaiterConsistent_of_tcbLinkFrame hC (fun k n hk => (h.ntfn k n).mp hk)
    (fun k n hk => (h.ntfn k n).mpr hk)
    (fun k ty hy => ?_) (fun k tx hx => ?_), fun tid tcb' hx => ?_, ?_⟩
  · obtain ⟨tx, hx, r⟩ := h.fwd k ty hy; exact ⟨tx, hx, r.1, r.2.1, r.2.2.1⟩
  · obtain ⟨ty, hy, r⟩ := h.bwd k tx hx; exact ⟨ty, hy, r.1, r.2.1, r.2.2.1⟩
  · obtain ⟨ty, hy, r⟩ := h.bwd _ tcb' hx; exact ⟨ty, hy, r.2.2.2.1.symm⟩
  · funext k
    unfold SystemState.replyViews SystemState.getObject?
    by_cases hT' : ∃ tx, st'.objects[k]? = some (.tcb tx)
    · obtain ⟨tx, hx⟩ := hT'
      obtain ⟨ty, hy, r⟩ := h.bwd k tx hx
      rw [hx, hy, objReplyView_tcb, objReplyView_tcb, r.2.2.2.2]
    · have hT : ¬ ∃ ty, st.objects[k]? = some (.tcb ty) := fun ⟨ty, hy⟩ =>
        hT' (let ⟨tx, hx, _⟩ := h.fwd k ty hy; ⟨tx, hx⟩)
      have a : ∀ x : Option KernelObject, (¬ ∃ t, x = some (.tcb t)) → objReplyView x = none := by
        intro x hx
        rcases x with _ | o
        · rfl
        · cases o <;> first | rfl | exact absurd ⟨_, rfl⟩ hx
      rw [a _ hT', a _ hT]

/-- **A step that changes only run-queue links and keeps every reply view**
keeps what the reachable parts read: the run-queue fields are no notification
link, no IPC state and no budget. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st)
    (hV : st'.replyViews = st.replyViews) : ReachFieldFrame st st' := by
  have hView : ∀ (k : SeLe4n.ObjId) (tx ty : TCB), st'.objects[k]? = some (KernelObject.tcb tx) →
      st.objects[k]? = some (KernelObject.tcb ty) → tx.replyView = ty.replyView := by
    intro k tx ty hx hy
    have e := congrFun hV k
    unfold SystemState.replyViews SystemState.getObject? at e
    rw [hx, hy, objReplyView_tcb, objReplyView_tcb] at e
    exact Option.some.inj e
  have hKept : ∀ (tx ty : TCB), tx.withoutRunLinks = ty.withoutRunLinks →
      tx.replyView = ty.replyView → tcbReachFieldsKept tx ty := fun tx ty e hv =>
    ⟨TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState e,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnPrev e,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnNext e,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.timeoutBudget e, hv⟩
  refine ⟨fun k n => ⟨fun hk => ?_, fun hk => ?_⟩, fun k ty hy => ?_, fun k tx hx => ?_⟩
  · exact KernelObject.map_withoutRunLinks_of_not_tcb (h k).symm hk
      (fun _ e => KernelObject.noConfusion e)
  · exact KernelObject.map_withoutRunLinks_of_not_tcb (h k) hk
      (fun _ e => KernelObject.noConfusion e)
  · obtain ⟨tx, hx, e⟩ := KernelObject.map_withoutRunLinks_tcb (h k) hy
    exact ⟨tx, hx, hKept tx ty e (hView k tx ty hx hy)⟩
  · obtain ⟨ty, hy, e⟩ := KernelObject.map_withoutRunLinks_tcb (h k).symm hx
    exact ⟨ty, hy, hKept tx ty e.symm (hView k tx ty hx hy)⟩

/-- **A step that writes contexts' release fields alone** keeps what the
reachable parts read: those fields are no thread's and no notification's. -/
theorem of_agreeOffReleaseLinks {st st' : SystemState} (h : st'.objectsAgreeOffReleaseLinks st) :
    ReachFieldFrame st st' :=
  ⟨fun _ _ => ⟨fun hk => h.symm.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hk,
      fun hk => h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hk⟩,
    fun _ ty hy => ⟨ty, h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hy,
      rfl, rfl, rfl, rfl, rfl⟩,
    fun _ tx hx => ⟨tx, h.symm.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hx,
      rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The deschedule at a thread's placement: it rewrites run-queue links alone. -/
theorem descheduleAtPlacement (st : SystemState) (t : SeLe4n.ThreadId) :
    ReachFieldFrame st (SeLe4n.Kernel.descheduleAtPlacement st t) := by
  refine of_agreeOffRunLinks (descheduleAtPlacement_objectsAgreeOffRunLinks st t) ?_
  unfold SeLe4n.Kernel.descheduleAtPlacement descheduleAt
  split
  · exact SystemState.removeRunnableOnCore_replyViews_eq _ _ _
  · rfl

end ReachFieldFrame

/-- **The reservation unbind keeps the reachable parts' fields**: a context
rewritten, the scheduler, the thread's binding codes, the key hook. -/
theorem cancelBoundDonationOnCore_reachFieldFrame {st st' : SystemState} {t : SeLe4n.ThreadId}
    {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st t tcb = .ok st') : ReachFieldFrame st st' := by
  cases hBind : tcb.schedContextBinding with
  | bound scId =>
    let g : SchedContext → SchedContext := fun sc =>
      { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
    have h1 := ReachFieldFrame.updateSchedContext st scId g hInv
    have hI1 : (st.updateSchedContext scId g).objects.invExt :=
      (FinaliseFrame.updateSchedContext st scId g hInv (fun _ => rfl)).invExt
    have h2 := h1.trans (ReachFieldFrame.updateTcb (st.updateSchedContext scId g) t
      (f := fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) hI1
      (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))
    exact h2.trans (ReachFieldFrame.of_agreeOffReleaseLinks
      (cancelBoundDonationOnCore_objects st st' t tcb scId hBind hInv h))
  | _ => unfold cancelBoundDonationOnCore at h; rw [hBind] at h; cases h

-- ============================================================================
-- §4b  A step that keeps what the notification queues and the budgets read
-- ============================================================================

namespace ReachFieldFrame

/-- A reply stored over a reply: no thread and no notification written. -/
theorem storeReplyOver {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : Reply}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.reply o))
    (hS : storeObject k (.reply o') st = .ok ((), st')) : ReachFieldFrame st st' := by
  have hAt := storeObject_objects_eq st st' _ _ hInv hS
  have hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]? :=
    fun j e => storeObject_objects_ne st st' k j _ e hInv hS
  refine ⟨fun j n => ?_, fun j ty hy => ?_, fun j tx hx => ?_⟩
  · by_cases e : j = k
    · subst e; rw [hAt, hPre]; simp
    · rw [hNe j e]
  · by_cases e : j = k
    · subst e; rw [hPre] at hy; cases hy
    · exact ⟨ty, by rw [hNe j e]; exact hy, rfl, rfl, rfl, rfl, rfl⟩
  · by_cases e : j = k
    · subst e; rw [hAt] at hx; cases hx
    · exact ⟨tx, by rw [← hNe j e]; exact hx, rfl, rfl, rfl, rfl, rfl⟩

end ReachFieldFrame

/-- **What the notification queues and the budgets read of a thread**, kept by
a step: blocked on the same notifications, both notification-queue links, and
the timeout budget.  Weaker than `tcbReachFieldsKept`: a reply-blocked caller
made `.ready` keeps it, since the queues name neither state. -/
def tcbNtfnFieldsKept (tx ty : TCB) : Prop :=
  (∀ o, tx.ipcState = .blockedOnNotification o ↔ ty.ipcState = .blockedOnNotification o) ∧
    tx.ntfnPrev = ty.ntfnPrev ∧ tx.ntfnNext = ty.ntfnNext ∧ tx.timeoutBudget = ty.timeoutBudget

namespace tcbNtfnFieldsKept

theorem refl (t : TCB) : tcbNtfnFieldsKept t t := ⟨fun _ => Iff.rfl, rfl, rfl, rfl⟩

theorem trans {a b c : TCB} (h₁ : tcbNtfnFieldsKept a b) (h₂ : tcbNtfnFieldsKept b c) :
    tcbNtfnFieldsKept a c :=
  ⟨fun o => (h₁.1 o).trans (h₂.1 o), h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

theorem of_reach {tx ty : TCB} (h : tcbReachFieldsKept tx ty) : tcbNtfnFieldsKept tx ty :=
  ⟨fun _ => by rw [h.1], h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Two threads agreeing off their run-queue fields keep the fields. -/
theorem of_withoutRunLinks {tx ty : TCB} (h : tx.withoutRunLinks = ty.withoutRunLinks) :
    tcbNtfnFieldsKept tx ty := by
  have hI : tx.ipcState = ty.ipcState := by have := congrArg TCB.ipcState h; exact this
  have hP : tx.ntfnPrev = ty.ntfnPrev := by have := congrArg TCB.ntfnPrev h; exact this
  have hN : tx.ntfnNext = ty.ntfnNext := by have := congrArg TCB.ntfnNext h; exact this
  have hB : tx.timeoutBudget = ty.timeoutBudget := by
    have := congrArg TCB.timeoutBudget h; exact this
  exact ⟨fun _ => by rw [hI], hP, hN, hB⟩

end tcbNtfnFieldsKept

/-- **A step that keeps every notification, and every thread up to fields the
notification queues and the budgets do not read**, with any other object free
to change. -/
structure NtfnFrame (st st' : SystemState) : Prop where
  ntfn : ∀ (k : SeLe4n.ObjId) (n : Notification),
    st'.objects[k]? = some (.notification n) ↔ st.objects[k]? = some (.notification n)
  fwd : ∀ (k : SeLe4n.ObjId) (ty : TCB), st.objects[k]? = some (.tcb ty) →
    ∃ tx, st'.objects[k]? = some (.tcb tx) ∧ tcbNtfnFieldsKept tx ty
  bwd : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
    ∃ ty, st.objects[k]? = some (.tcb ty) ∧ tcbNtfnFieldsKept tx ty

namespace NtfnFrame

theorem refl (st : SystemState) : NtfnFrame st st :=
  ⟨fun _ _ => Iff.rfl, fun _ ty hy => ⟨ty, hy, .refl ty⟩, fun _ tx hx => ⟨tx, hx, .refl tx⟩⟩

theorem trans {a b c : SystemState} (h₁ : NtfnFrame a b) (h₂ : NtfnFrame b c) : NtfnFrame a c :=
  ⟨fun k n => (h₂.ntfn k n).trans (h₁.ntfn k n),
    fun k ty hy => let ⟨tm, hm, r₁⟩ := h₁.fwd k ty hy
      let ⟨tx, hx, r₂⟩ := h₂.fwd k tm hm; ⟨tx, hx, r₂.trans r₁⟩,
    fun k tx hx => let ⟨tm, hm, r₂⟩ := h₂.bwd k tx hx
      let ⟨ty, hy, r₁⟩ := h₁.bwd k tm hm; ⟨ty, hy, r₂.trans r₁⟩⟩

theorem of_reach {st st' : SystemState} (h : ReachFieldFrame st st') : NtfnFrame st st' :=
  ⟨h.ntfn, fun k ty hy => let ⟨tx, hx, r⟩ := h.fwd k ty hy; ⟨tx, hx, .of_reach r⟩,
    fun k tx hx => let ⟨ty, hy, r⟩ := h.bwd k tx hx; ⟨ty, hy, .of_reach r⟩⟩

/-- A step agreeing off the run-queue fields (a reply-waiter unlink). -/
theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    NtfnFrame st st' :=
  ⟨fun _ _ => h.get_notification_iff,
    fun _ _ hy => let ⟨tx, hx, e⟩ := h.get_tcb hy; ⟨tx, hx, .of_withoutRunLinks e⟩,
    fun _ _ hx => let ⟨ty, hy, e⟩ := h.get_tcb' hx; ⟨ty, hy, .of_withoutRunLinks e⟩⟩

/-- A reply stored over a reply. -/
theorem storeReplyOver {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : Reply}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.reply o))
    (hS : storeObject k (.reply o') st = .ok ((), st')) : NtfnFrame st st' :=
  of_reach (ReachFieldFrame.storeReplyOver hInv hPre hS)

/-- A thread stored over a thread, keeping the fields. -/
theorem storeTcbOver {st st' : SystemState} {k : SeLe4n.ObjId} {t t' : TCB}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.tcb t))
    (hS : storeObject k (.tcb t') st = .ok ((), st')) (hK : tcbNtfnFieldsKept t' t) :
    NtfnFrame st st' := by
  have hAt := storeObject_objects_eq st st' _ _ hInv hS
  have hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]? :=
    fun j e => storeObject_objects_ne st st' k j _ e hInv hS
  refine ⟨fun j n => ?_, fun j ty hy => ?_, fun j tx hx => ?_⟩
  · by_cases e : j = k
    · subst e; rw [hAt, hPre]; simp
    · rw [hNe j e]
  · by_cases e : j = k
    · subst e; rw [hPre] at hy; cases hy; exact ⟨t', hAt, hK⟩
    · exact ⟨ty, by rw [hNe j e]; exact hy, .refl ty⟩
  · by_cases e : j = k
    · subst e; rw [hAt] at hx; cases hx; exact ⟨t, hPre, hK⟩
    · exact ⟨tx, by rw [← hNe j e]; exact hx, .refl tx⟩

/-- **The parts a frame keeps**: the notification queues and every budget. -/
theorem parts {st st' : SystemState} (h : NtfnFrame st st') (hC : notificationWaiterConsistent st) :
    notificationWaiterConsistent st' ∧ timeoutBudgetFrame st st' :=
  ⟨notificationWaiterConsistent_of_ntfnBlockFrame hC (fun k n hk => (h.ntfn k n).mp hk)
    (fun k n hk => (h.ntfn k n).mpr hk)
    (fun k ty hy => let ⟨tx, hx, r⟩ := h.fwd k ty hy; ⟨tx, hx, r.1, r.2.1, r.2.2.1⟩)
    (fun k tx hx => let ⟨ty, hy, r⟩ := h.bwd k tx hx; ⟨ty, hy, r.1, r.2.1, r.2.2.1⟩),
    fun _ tcb' hx => let ⟨ty, hy, r⟩ := h.bwd _ tcb' hx; ⟨ty, hy, r.2.2.2.symm⟩⟩

end NtfnFrame

namespace NtfnFrame

/-- A thread's reply frame spliced off its stack: at most three replies
rewritten. -/
theorem spliceThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    NtfnFrame st (SeLe4n.Kernel.spliceThreadReplyFrameOut st t) := by
  unfold SeLe4n.Kernel.spliceThreadReplyFrameOut
  cases t.replyObject with
  | none => exact .refl st
  | some rid =>
    obtain ⟨m1, m2, h1, h2, h3⟩ := spliceReplyFrameOutOrSelf_store_cases st rid hInv
    have step : ∀ {a b : SystemState}, a.objects.invExt →
        (b = a ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply), a.objects[k.toObjId]? = some (.reply o) ∧
          storeObject k.toObjId (.reply o') a = .ok ((), b)) →
        NtfnFrame a b ∧ b.objects.invExt := by
      intro a b hA h
      rcases h with rfl | ⟨k, o, o', hO, hS⟩
      · exact ⟨.refl _, hA⟩
      · exact ⟨storeReplyOver hA hO hS, storeObject_preserves_objects_invExt _ _ _ _ hA hS⟩
    have f1 := step hInv h1
    have f2 := step f1.2 h2
    exact f1.1.trans (f2.1.trans (step f2.2 h3).1)

/-- The restore of a thread blocked on no notification: its own TCB rewritten,
made `.ready`, its notification links and budget kept. -/
theorem restoreToReadyStaging (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hNotN : ∀ o, tcbV.ipcState ≠ .blockedOnNotification o) :
    NtfnFrame st (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  have hV := lookupTcb_some_objects st v tcbV hLookup
  have hGet : st.getTcb? v = some tcbV := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hV
  have hK : tcbNtfnFieldsKept (restoredTcb tcbV frame) tcbV := by
    refine ⟨fun o => ⟨fun e => (by rw [restoredTcb_ipcState] at e; cases e),
      fun e => absurd e (hNotN o)⟩, ?_, ?_, ?_⟩ <;>
      (unfold restoredTcb; cases frame <;> rfl)
  refine ⟨fun k n => restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup k _
    (fun _ h => by cases h), fun k ty hy => ?_, fun k tx hx => ?_⟩
  · by_cases hk : k = v.toObjId
    · subst hk; rw [hV] at hy; cases hy
      exact ⟨_, restoreToReadyStaging_objects_self st v frame _ hInv hGet, hK⟩
    · exact ⟨ty, restoreToReadyStaging_tcb_forward st v frame hInv k ty hk hy, .refl ty⟩
  · rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup k tx hx with
      ⟨_, h0⟩ | ⟨hk, rfl⟩
    · exact ⟨tx, h0, .refl tx⟩
    · exact ⟨tcbV, by rw [hk]; exact hV, hK⟩

/-- The consume of a caller's reply link: the reply consumed, the caller's link
cleared. -/
theorem consumeCallerReply {st st' : SystemState} {c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : SystemState.consumeCallerReply c rid st = .ok ((), st')) :
    NtfnFrame st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    rw [hC] at h
    have f1 : NtfnFrame st st1 ∧ st1.objects.invExt := by
      unfold SystemState.consumeReply at hC
      cases hR : st.getReply? rid with
      | none => rw [hR] at hC; cases hC; exact ⟨.refl _, hInv⟩
      | some r =>
        rw [hR] at hC
        exact ⟨storeReplyOver hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hC,
          storeObject_preserves_objects_invExt _ _ _ _ hInv hC⟩
    simp only at h
    cases hT : st1.getTcb? c with
    | none => rw [hT] at h; cases h; exact f1.1
    | some tcb =>
      rw [hT] at h
      exact f1.1.trans (storeTcbOver f1.2 ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) h
        ⟨fun _ => Iff.rfl, rfl, rfl, rfl⟩)

theorem consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    NtfnFrame st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl st
  · rename_i rid _
    exact consumeCallerReply hInv (SystemState.consumeCallerReply_eq_link st c rid)

/-- The PIP chain walk: each thread it writes keeps every field but its run
links and its boost (`propagatePipChainCrossCore_tcb_backward`). -/
theorem propagatePip (st : SystemState) (s : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    NtfnFrame st (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 := by
  have hBack : ∀ (k : SeLe4n.ObjId) (tx : TCB),
      (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1.objects[k]? = some (.tcb tx) →
      ∃ ty, st.objects[k]? = some (.tcb ty) ∧ tcbNtfnFieldsKept tx ty := by
    intro k tx hx
    obtain ⟨ty, p, hy, e⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st s ec
      fuel hInv ⟨k.val⟩ tx hx
    exact ⟨ty, hy, (tcbNtfnFieldsKept.of_withoutRunLinks e).trans ⟨fun _ => Iff.rfl, rfl, rfl, rfl⟩⟩
  refine ⟨fun k n => ⟨PriorityInheritance.propagatePipChainCrossCore_notification_backward st s ec
    fuel hInv k n, fun hk => ?_⟩, fun k ty hy => ?_, hBack⟩
  · rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv k with
      e | ⟨pre, -, hp, -, -, -, -⟩
    · rw [e]; exact hk
    · rw [hp] at hk; cases hk
  · rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv k with
      e | ⟨pre, post, hp, hq, -, -, -⟩
    · exact ⟨ty, by rw [e]; exact hy, .refl ty⟩
    · rw [hp] at hy; cases hy
      obtain ⟨ty', hy', r⟩ := hBack k post hq
      rw [hp] at hy'; cases hy'
      exact ⟨post, hq, r⟩

/-- The revert of a finalised reply's caller's boost. -/
theorem finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : NtfnFrame st (SeLe4n.Kernel.finaliseReplyRevert st server?) := by
  cases server? with
  | none => exact .refl st
  | some s => exact propagatePip st s _ _ hInv

end NtfnFrame

-- ============================================================================
-- §5  The finalisation
-- ============================================================================

/-- **A finalisation write frames the donation chains**: it writes no reply, and
no scheduling context's reply-stack head. -/
theorem finaliseWrite.donationChainFrame {st st' : SystemState} (h : finaliseWrite st st') :
    donationChainFrame st st' := by
  have hNot : ∀ o : KernelObject, finaliseWritable o → replyStackLinks? (some o) = none ∧
      ∀ r, o ≠ .reply r := by
    intro o hw
    cases o <;> simp_all [finaliseWritable, KernelObject.objectType, replyStackLinks?]
  have hPost : ∀ {pre post : KernelObject}, post.objectType = pre.objectType →
      finaliseWritable pre → finaliseWritable post := by
    intro pre post ht hw; unfold finaliseWritable; rw [ht]; exact hw
  refine ⟨fun oid => ?_, fun oid => ?_, fun oid r' hR hC => ?_⟩
  · rcases h oid with e | ⟨pre, post, hp, hq, ht, -, -, hw⟩
    · rw [e]
    · rw [hp, hq, (hNot _ hw).1, (hNot _ (hPost ht hw)).1]
  · rcases h oid with e | ⟨pre, post, hp, hq, -, -, hh, -⟩
    · rw [e]
    · rw [hp, hq, hh]
  · rcases h oid with e | ⟨pre, post, hp, hq, ht, -, -, hw⟩
    · exact ⟨r', e.symm.trans hR, hC⟩
    · rw [hq] at hR; cases hR; exact absurd rfl ((hNot _ (hPost ht hw)).2 r')

/-- **The unstack's object table**: the context's head cleared, the head reply's
upward link cleared, every other object as it was. -/
theorem finaliseUnstack_objects {s s1 : SystemState} {x : SeLe4n.ObjId} {sc : SchedContext}
    {rid : SeLe4n.ReplyId} {r : Reply} (hInv : s.objects.invExt)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hR : s.getReply? rid = some r)
    (hS : storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1))
    (k : SeLe4n.ObjId) :
    (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }).objects[k]? =
      if k = (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId then
        some (.schedContext { sc with scReply := none })
      else if k = rid.toObjId then some (.reply { r with next := none }) else s.objects[k]? := by
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hNe : rid.toObjId ≠ (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId := fun h => by
    rw [h, hScO] at hRO; cases hRO
  have hI1 := storeObject_preserves_objects_invExt s s1 _ _ hInv hS
  have hSc1 : s1.getSchedContext? ⟨x.val⟩ = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
      (by rw [storeObject_objects_ne s s1 _ _ _ (Ne.symm hNe) hInv hS]; exact hScO)
  rw [SystemState.updateSchedContext_eq_of_some hSc1]
  show (s1.objects.insert _ _)[k]? = _
  by_cases e1 : k = (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId
  · subst e1; rw [if_pos rfl, RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hI1
  · rw [if_neg e1, RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_ne _ _ _ _
      (fun h => e1 (eq_of_beq h).symm) hI1, ← RHTable_getElem?_eq_get?]
    by_cases e2 : k = rid.toObjId
    · subst e2; rw [if_pos rfl]; exact storeObject_objects_eq s s1 _ _ hInv hS
    · rw [if_neg e2]; exact storeObject_objects_ne s s1 _ _ _ e2 hInv hS

/-- **The unstack keeps the donation chains** — seL4's `finaliseCap` on a
scheduling context: `sc->scReply->replyNext = 0; sc->scReply = NULL`.  The head
reply keeps its downward link, which its frame below still answers, so every
`prev` stays answered; the context's stack is empty; and no other context's
walk passes the old head, whose upward link named this context only. -/
theorem finaliseUnstack_preserves_donationChainWellFormed {s s1 : SystemState}
    {x : SeLe4n.ObjId} {sc : SchedContext} {rid : SeLe4n.ReplyId} {r : Reply}
    (hInv : s.objects.invExt) (hC : donationChainWellFormed s)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hR : s.getReply? rid = some r)
    (hNext : r.next = some (.head ⟨x.val⟩))
    (hS : storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1)) :
    donationChainWellFormed
      (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) := by
  have hO := finaliseUnstack_objects hInv hSc hR hS
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  -- A key holding a reply in the pre-state is not the context's.
  have hRX : ∀ {q : SeLe4n.ObjId} {rq : Reply}, s.objects[q]? = some (.reply rq) →
      q ≠ (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId := fun h e => by rw [e, hScO] at h; cases h
  -- A key holding a context in the pre-state is not the reply's.
  have hSR : ∀ {q : SeLe4n.ObjId} {sq : SchedContext}, s.objects[q]? = some (.schedContext sq) →
      q ≠ rid.toObjId := fun h e => by rw [e, hRO] at h; cases h
  -- A reply other than the head answering a frame or another head is not `rid`.
  have hNotRid : ∀ {q : SeLe4n.ReplyId} {rq : Reply} {l : ReplyStackLink},
      s.objects[q.toObjId]? = some (.reply rq) → rq.next = some l → l ≠ ReplyStackLink.head ⟨x.val⟩ → q ≠ rid :=
    fun h hn hl e => by subst e; rw [hRO] at h; cases h; rw [hNext] at hn; cases hn; exact hl rfl
  refine ⟨fun q rq hq => ?_, fun scId sc2 hsc q hq => ?_, fun q rq scId hq hn => ?_,
    fun q rq below hq hp => ?_, fun scId sc2 hsc => ?_, fun q rq above hq hn => ?_⟩
  · -- replyWellFormed
    rw [hO] at hq
    split at hq
    · cases hq
    · split at hq
      · cases hq
        intro hc
        obtain ⟨hp, -⟩ := hC.replyWellFormed rid r hRO hc
        exact ⟨hp, rfl⟩
      · exact hC.replyWellFormed q rq hq
  · -- headLinkReciprocal
    rw [hO] at hsc
    split at hsc
    · cases hsc; cases hq
    · split at hsc
      · cases hsc
      · next e1 e2 =>
        obtain ⟨r2, h2, hn2⟩ := hC.headLinkReciprocal scId sc2 hsc q hq
        refine ⟨r2, ?_, hn2⟩
        have hq1 : q ≠ rid := hNotRid h2 hn2 (fun e => e1 (by cases e; rfl))
        rw [hO, if_neg (hRX h2), if_neg (fun e => hq1 (SeLe4n.ReplyId.toObjId_injective _ _ e))]
        exact h2
  · -- headLinkResolves
    rw [hO] at hq
    split at hq
    · cases hq
    · split at hq
      · cases hq; cases hn
      · next e1 e2 =>
        obtain ⟨sc2, h2, hr2⟩ := hC.headLinkResolves q rq scId hq hn
        refine ⟨sc2, ?_, hr2⟩
        rw [hO, if_neg (hSR h2)]
        split
        · next e3 =>
          have hX := SeLe4n.SchedContextId.toObjId_injective _ _ e3
          subst hX
          obtain ⟨sc3, h3, hr3⟩ := hC.headLinkResolves rid r _ hRO hNext
          rw [h2] at h3; cases h3
          rw [hr2] at hr3; cases hr3
          exact absurd rfl e2
        · exact h2
  · -- prevLinkReciprocal
    have hKeep : ∀ {b : Reply}, s.objects[below.toObjId]? = some (.reply b) →
        b.next = some (.frame q) →
        (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }).objects[
          below.toObjId]? = some (.reply b) := fun hb hbn => by
      rw [hO, if_neg (hRX hb), if_neg (fun e => hNotRid hb hbn (by intro h; cases h)
        (SeLe4n.ReplyId.toObjId_injective _ _ e))]
      exact hb
    rw [hO] at hq
    split at hq
    · cases hq
    · split at hq
      · next e2 =>
        cases hq
        obtain rfl := SeLe4n.ReplyId.toObjId_injective _ _ e2
        obtain ⟨b, hb, hbn⟩ := hC.prevLinkReciprocal q r below hRO hp
        exact ⟨b, hKeep hb hbn, hbn⟩
      · obtain ⟨b, hb, hbn⟩ := hC.prevLinkReciprocal q rq below hq hp
        exact ⟨b, hKeep hb hbn, hbn⟩
  · -- headTerminates
    rw [hO] at hsc
    split at hsc
    · cases hsc; exact ⟨0, [], by simp⟩
    · split at hsc
      · cases hsc
      · next e1 _ =>
        obtain ⟨fuel, chain, hW⟩ := hC.headTerminates scId sc2 hsc
        have hAg : ∀ q ∈ chain, replyStackLinksAt?
            (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) q =
            replyStackLinksAt? s q := by
          intro q hq
          obtain ⟨rq, hrq, hnx⟩ := donationChainWalk_mem_next s fuel _ _ chain hW q hq
          have hq1 : q ≠ rid := by
            rcases hnx with hn | ⟨p, -, hn⟩
            · exact hNotRid hrq hn (fun e => e1 (by cases e; rfl))
            · exact hNotRid hrq hn (by intro h; cases h)
          unfold replyStackLinksAt? SystemState.getObject?
          rw [hO, if_neg (hRX hrq), if_neg (fun e => hq1 (SeLe4n.ReplyId.toObjId_injective _ _ e))]
        obtain ⟨chain', h'⟩ := donationChainWalk_exists_of_agree_or_cut fuel (.head scId)
          sc2.scReply chain hW (fun q hq => Or.inl (hAg q hq))
        exact ⟨fuel, chain', h'⟩
  · -- nextLinkReciprocal: the head's cleared `next` names nothing, and the head
    -- keeps its `prev`, so a frame below it is still answered.
    rw [hO] at hq
    split at hq
    · cases hq
    · split at hq
      · cases hq; simp at hn
      · obtain ⟨a, ha, hap⟩ := hC.nextLinkReciprocal q rq above hq hn
        by_cases e3 : above.toObjId = rid.toObjId
        · refine ⟨{ r with next := none }, ?_, ?_⟩
          · rw [hO, if_neg (hRX ha), if_pos e3]
          · rw [e3, hRO] at ha; cases ha; exact hap
        · exact ⟨a, by rw [hO, if_neg (hRX ha), if_neg e3]; exact ha, hap⟩

/-- **A scheduling context's unstack keeps the donation chains** (seL4's
`schedContext_unbindReply`): the stack it let go of is no context's, so every
remaining context's walk reads what it read before. -/
theorem finaliseSchedContextUnstack_preserves_donationChainWellFormed {s : SystemState}
    (x : SeLe4n.ObjId) (hInv : s.objects.invExt) (hC : donationChainWellFormed s) :
    donationChainWellFormed (finaliseSchedContextUnstack s x) := by
  unfold finaliseSchedContextUnstack
  split
  · next sc hSc =>
    split
    · next rid _ =>
      split
      · next r hR =>
        split
        · next hH =>
          split
          · next s1 hS =>
            have hNext : r.next = some (.head ⟨x.val⟩) := by
              unfold replyStackLinkHeads at hH
              split at hH
              · next sId hn =>
                have : sId = ⟨x.val⟩ := by
                  cases sId; simp only [beq_iff_eq] at hH; subst hH; rfl
                rw [hn, this]
              · cases hH
            exact finaliseUnstack_preserves_donationChainWellFormed hInv hC hSc hR hNext hS
          · exact hC
        · exact hC
      · exact hC
    · exact hC
  · exact hC

/-- A binding rewrite keeps what the notification queues and the budgets read. -/
theorem tcbNtfnFieldsKept.of_bindingRewrite {tx ty : TCB} (h : tcbBindingRewrite tx ty) :
    tcbNtfnFieldsKept tx ty := by
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨fun _ => Iff.rfl, rfl, rfl, rfl⟩

/-- **The donation return** (seL4 MCS's `reply_pop`) writes a context, the
stack's replies and two threads' binding codes: no notification, and nothing
the notification queues or the budgets read of a thread. -/
theorem NtfnFrame.returnDonatedSchedContext {st st' : SystemState} {h : SeLe4n.ThreadId}
    {sc : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : SeLe4n.Kernel.returnDonatedSchedContext st h sc c n = .ok st') :
    NtfnFrame st st' :=
  ⟨fun k o => ⟨fun hk => returnDonatedSchedContext_objects_backward_of_kind st st' h sc c n hInv hPop
      k _ (donationReturnWritesKind_notification o) hk,
    fun hk => returnDonatedSchedContext_objects_forward_of_kind st st' h sc c n hInv hPop
      k _ (donationReturnWritesKind_notification o) hk⟩,
    fun k ty hy =>
      let ⟨tx, hx, hR⟩ := returnDonatedSchedContext_tcb_rewrite st st' h sc c hInv n hPop k ty hy
      ⟨tx, hx, .of_bindingRewrite hR⟩,
    fun k tx hx =>
      let ⟨ty, hy, hR⟩ := returnDonatedSchedContext_tcb_rewrite_backward st st' h sc c n hInv hPop
        k tx hx
      ⟨ty, hy, .of_bindingRewrite hR⟩⟩

/-- **A cancelled caller's donation return**: the return when it commits, the
state itself when there is none to make. -/
theorem NtfnFrame.returnDonationToCancelledCaller (st : SystemState) (c : SeLe4n.ThreadId)
    (t : TCB) (hInv : st.objects.invExt) :
    NtfnFrame st (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact NtfnFrame.returnDonatedSchedContext hInv hPop
    · exact .refl st
  · exact .refl st

/-- **A cancelled caller's donation return keeps the donation chains**
(`returnDonatedSchedContext_preserves_donationChainWellFormed`, unconditional in
the outer caller). -/
theorem returnDonationToCancelledCaller_preserves_donationChainWellFormed (st : SystemState)
    (c : SeLe4n.ThreadId) (t : TCB) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) :
    donationChainWellFormed (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact returnDonatedSchedContext_preserves_donationChainWellFormed _ _ _ _ _ n hInv hChain hPop
    · exact hChain
  · exact hChain

/-- **What each step of a finalisation carries**: the IPC bundle, the object
table's well-formedness, the notification queues, the reply-waiter queues, the
donation chains and the delete's stated lent-context fact. -/
def finaliseStepInvariant (s : SystemState) : Prop :=
  ipcInvariantFull s ∧ s.objects.invExt ∧ notificationWaiterConsistent s ∧
    s.replyWaitersConsistent ∧ donationChainWellFormed s ∧ lentContextHeadsLenderFrame s

namespace finaliseStepInvariant

theorem of_ipcReachable {st : SystemState} (h : ipcReachable st)
    (hW : lentContextHeadsLenderFrame st) : finaliseStepInvariant st :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.2.1, hW⟩

/-- A step whose write frame keeps the donation chains outright. -/
theorem chain_of_frame {s s' : SystemState} (h : finaliseStepInvariant s) (F : FinaliseFrame s s') :
    donationChainWellFormed s' :=
  donationChainWellFormed_of_frame (finaliseWrite.donationChainFrame F.write) h.2.2.2.2.1

/-- ...and the lent-context fact. -/
theorem loan_of_frame {s s' : SystemState} (h : finaliseStepInvariant s) (F : FinaliseFrame s s') :
    lentContextHeadsLenderFrame s' :=
  h.2.2.2.2.2.of_loanWrite F.loan

/-- An endpoint waiter's cancel carries it, and frames every budget. -/
theorem endpointCancel {s : SystemState} {e : SeLe4n.ObjId} {q : Bool} {ep : Endpoint}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : finaliseStepInvariant s)
    (hE : s.getEndpoint? e = some ep) (hH : (endpointWaitQueue ep q).head = some t)
    (hT : s.getTcb? t = some tcb) (hC : endpointWaiterCancellable s e t tcb = true) :
    finaliseStepInvariant (storeEndpointWaiterCancelled s e q t tcb.queueNext) ∧
      timeoutBudgetFrame s (storeEndpointWaiterCancelled s e q t tcb.queueNext) :=
  have r := storeEndpointWaiterCancelled_preserves_reachableParts s e q ep t tcb h.2.1 h.1
    hE hH hT hC h.2.2.1 h.2.2.2.1
  have F := FinaliseFrame.storeEndpointWaiterCancelled s e q t tcb.queueNext h.2.1
  ⟨⟨storeEndpointWaiterCancelled_preserves_ipcInvariantFull s e q ep t tcb h.2.1 h.1 hE hH hT hC,
    F.invExt, r.1, r.2.2, h.chain_of_frame F, h.loan_of_frame F⟩, r.2.1⟩

/-- A notification waiter's cancel carries it, and frames every budget. -/
theorem notificationCancel {s : SystemState} {n : SeLe4n.ObjId} {ntfn : Notification}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : finaliseStepInvariant s)
    (hN : s.getNotification? n = some ntfn)
    (hT : s.getTcb? t = some tcb) (hC : notificationWaiterCancellable s n t tcb = true) :
    finaliseStepInvariant (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) ∧
      timeoutBudgetFrame s (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) :=
  have r := notificationWaiterCancel_preserves_reachableParts s n ntfn t tcb h.2.1 hN hT hC
    h.2.2.1 h.2.2.2.1
  have hF := FinaliseFrame.notificationCancel s t tcb n h.2.1
    (notificationWaiterCancellable_blocked hC)
  have F := hF.trans (FinaliseFrame.wakeCancelledWaiter _ t hF.invExt)
  ⟨⟨notificationWaiterCancel_preserves_ipcInvariantFull s n t tcb h.2.1 h.1 hT hC,
    F.invExt, r.1, r.2.2, h.chain_of_frame F, h.loan_of_frame F⟩, r.2.1⟩

/-- The unbind carries it, and frames every budget. -/
theorem unbind {s : SystemState} {n : SeLe4n.ObjId} {ntfn : Notification} {t : SeLe4n.ThreadId}
    (h : finaliseStepInvariant s) (hN : s.getNotification? n = some ntfn)
    (hCode : boundNotificationCodeOf s t = n.val + 1) (hIn : unbindNotificationInPlace s t = true) :
    finaliseStepInvariant (storeUnbindNotification s t n) ∧
      timeoutBudgetFrame s (storeUnbindNotification s t n) :=
  have r := storeUnbindNotification_preserves_reachableParts s n ntfn t h.2.1 hN h.2.2.1
    h.2.2.2.1
  have F := FinaliseFrame.storeUnbindNotification s t n h.2.1
  ⟨⟨storeUnbindNotification_preserves_ipcInvariantFull s n t h.2.1 h.1 hCode hIn,
    F.invExt, r.1, r.2.2, h.chain_of_frame F, h.loan_of_frame F⟩, r.2.1⟩

/-- A context's release of its holder — the thread's own unbind among them —
carries it, and frames every budget. -/
theorem release {s s' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB} {sc : SchedContext}
    {x : SeLe4n.ObjId} (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb)
    (hS : tcb.scBindingScCode = x.val + 1)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hB : sc.boundThreadCode = t.val + 1)
    (hOk : cancelBoundDonationOnCore s t { tcb with scBindingOwnerCode := 0 }
      = .ok s') :
    finaliseStepInvariant s' ∧ timeoutBudgetFrame s s' :=
  have hI := finaliseScReleaseStep_keepsIpcInvariantFull s s' t tcb sc x ⟨h.1, h.2.1⟩ hT hS
    hSc hB hOk
  have r := (cancelBoundDonationOnCore_reachFieldFrame h.2.1 hOk).parts h.2.2.1
  ⟨⟨hI.1, hI.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2.1,
    h.chain_of_frame (FinaliseFrame.cancelBoundDonationOnCore h.2.1 hOk), h.loan_of_frame (FinaliseFrame.cancelBoundDonationOnCore h.2.1 hOk)⟩, r.2.1⟩

/-- A context's deschedule of its holder carries it, and frames every budget:
the dequeue wherever the holder is placed. -/
theorem deschedule {s : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb) (hS : tcb.ipcStateCode = 0)
    (hO : tcb.ipcObjectCode = 0) (hId : isIdleThreadId t = false) :
    finaliseStepInvariant (descheduleAtPlacement s t) ∧
      timeoutBudgetFrame s (descheduleAtPlacement s t) :=
  have hF := finaliseScDescheduleStep_keepsIpcInvariantFull s t tcb ⟨h.1, h.2.1⟩ hT hS hO hId
  have r := (ReachFieldFrame.descheduleAtPlacement s t).parts h.2.2.1
  ⟨⟨hF.1, hF.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2.1,
    h.chain_of_frame (FinaliseFrame.descheduleAt s t (placedCoreOf? s t) h.2.1), h.loan_of_frame (FinaliseFrame.descheduleAt s t (placedCoreOf? s t) h.2.1)⟩, r.2.1⟩

/-- A thread's notification cancel, before any wake, carries it, and frames
every budget. -/
theorem cancel {s : SystemState} {n : SeLe4n.ObjId} {t : SeLe4n.ThreadId} {tcb : TCB}
    {ntfn : Notification} (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb)
    (hI : tcb.ipcState = .blockedOnNotification n) (hN : s.getNotification? n = some ntfn)
    (hC : notificationWaiterCancellable s n t tcb = true) :
    finaliseStepInvariant (Lifecycle.Suspend.cancelIpcBlocking s t tcb) ∧
      timeoutBudgetFrame s (Lifecycle.Suspend.cancelIpcBlocking s t tcb) :=
  have hF := finaliseNotificationCancelStep_keepsIpcInvariantFull s n t tcb ntfn ⟨h.1, h.2.1⟩
    hT hI hN hC
  have r := notificationCancel_preserves_reachableParts s n ntfn t tcb h.2.1 hN hT hI
    h.2.2.1 h.2.2.2.1
  ⟨⟨hF.1, hF.2, r.1, r.2.2,
    h.chain_of_frame (FinaliseFrame.notificationCancel s t tcb n h.2.1 hI), h.loan_of_frame (FinaliseFrame.notificationCancel s t tcb n h.2.1 hI)⟩, r.2.1⟩

/-- A thread's endpoint cancel, before any wake, carries it, and frames every
budget. -/
theorem endpointBlockedCancel {s : SystemState} {e : SeLe4n.ObjId} {q : Bool}
    {t : SeLe4n.ThreadId} {ep : Endpoint} {tcb : TCB} (h : finaliseStepInvariant s)
    (hT : s.getTcb? t = some tcb) (hE : s.getEndpoint? e = some ep)
    (hC : endpointBlockedCancellable s e q t ep tcb = true) :
    finaliseStepInvariant (storeEndpointBlockedCancelled s e q t ep tcb) ∧
      timeoutBudgetFrame s (storeEndpointBlockedCancelled s e q t ep tcb) :=
  have hF := finaliseEndpointCancelStep_keepsIpcInvariantFull s e q t ep tcb ⟨h.1, h.2.1⟩ hT hE hC
  have r := storeEndpointBlockedCancelled_preserves_reachableParts s e q t ep tcb h.2.1 hT hE hC
    h.2.2.1 h.2.2.2.1
  ⟨⟨hF.1, hF.2, r.1, r.2.2,
    h.chain_of_frame (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.2.1), h.loan_of_frame (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.2.1)⟩, r.2.1⟩

/-- A finalised thread's suspend carries it, and frames every budget: the
deschedule wherever it is placed, then the inactive mark. -/
theorem suspend {s : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb) (hS : tcb.ipcStateCode = 0)
    (hO : tcb.ipcObjectCode = 0)
    (hI : tcb.threadState ≠ .Inactive ∨ tcb.pendingMessage.isSome = true)
    (hId : isIdleThreadId t = false) :
    finaliseStepInvariant ((descheduleAtPlacement s t).updateTcb t finalisedSuspendMark) ∧
      timeoutBudgetFrame s ((descheduleAtPlacement s t).updateTcb t finalisedSuspendMark) :=
  have hF := finaliseSuspendStep_keepsIpcInvariantFull s t tcb ⟨h.1, h.2.1⟩ hT hS hO hI hId
  have hD := (FinaliseFrame.descheduleAt s t (placedCoreOf? s t) h.2.1).invExt
  have r := ((ReachFieldFrame.descheduleAtPlacement s t).trans
    (ReachFieldFrame.updateTcb (descheduleAtPlacement s t) t
      (f := finalisedSuspendMark) hD
      (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))).parts h.2.2.1
  ⟨⟨hF.1, hF.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2.1,
    h.chain_of_frame (FinaliseFrame.suspend s t h.2.1), h.loan_of_frame (FinaliseFrame.suspend s t h.2.1)⟩, r.2.1⟩

/-- The release of every core's hold on a thread carries it, and frames every
budget: it writes no object. -/
theorem releaseCores {s : SystemState} (t : SeLe4n.ThreadId) (h : finaliseStepInvariant s) :
    finaliseStepInvariant (finaliseThreadReleaseCores s t) ∧
      timeoutBudgetFrame s (finaliseThreadReleaseCores s t) :=
  have hF := finaliseReleaseStep_keepsIpcInvariantFull s t ⟨h.1, h.2.1⟩
  have r := (ReachFieldFrame.of_objects_eq (st := s) (st' := finaliseThreadReleaseCores s t)
    (finaliseThreadReleaseCores_objects s t)).parts h.2.2.1
  ⟨⟨hF.1, hF.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2.1,
    h.chain_of_frame (FinaliseFrame.releaseCores s t h.2.1), h.loan_of_frame (FinaliseFrame.releaseCores s t h.2.1)⟩, r.2.1⟩

/-- A context's reply-stack unlink carries it, and frames every budget: a reply
and a context rewritten, neither read by the queues or the budgets; the chains
by `finaliseUnstack_preserves_donationChainWellFormed`. -/
theorem unstack {s s1 : SystemState} {x : SeLe4n.ObjId} {sc : SchedContext}
    {rid : SeLe4n.ReplyId} {r : Reply} (h : finaliseStepInvariant s)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hRep : sc.scReply = some rid)
    (hR : s.getReply? rid = some r) (hN : r.next = some (.head ⟨x.val⟩))
    (hS : storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1))
    {s₀ : SystemState} (h₀ : finaliseStepInvariant s₀) (hA : schedContextFinaliseAdmitted s₀ x = true)
    (hS₀ : s = finaliseSchedContextUnbind (finaliseSchedContextDeschedule s₀ x) x) :
    finaliseStepInvariant (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) ∧
      timeoutBudgetFrame s (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) :=
  have hI := finaliseUnstackStep_keepsIpcInvariantFull s s1 x sc rid r ⟨h.1, h.2.1⟩ hSc hRep hR hN
    hS s₀ ⟨h₀.1, h₀.2.1⟩ hA hS₀
  have hI1 := storeObject_preserves_objects_invExt s s1 _ _ h.2.1 hS
  have q := ((ReachFieldFrame.storeReplyOver h.2.1
    ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hS).trans
    (ReachFieldFrame.updateSchedContext s1 ⟨x.val⟩ _ hI1)).parts h.2.2.1
  ⟨⟨hI.1, hI.2, q.1, SystemState.replyWaitersConsistent.of_views q.2.2 h.2.2.2.1,
    finaliseUnstack_preserves_donationChainWellFormed h.2.1 h.2.2.2.2.1 hSc hR hN hS,
    finaliseUnstack_keepsLentContextHeads h.2.1 h.1.donationOwnerValid h.2.2.2.2.2 hSc
      (finaliseSchedContextUnbind_unbound h₀.2.1 hA (hS₀ ▸ hSc)) hR hN hS⟩, q.2.1⟩

/-- A reply's caller cancel, with its boost reverted, carries it, and frames
every budget.  A head reply's cancel first hands the caller's reservation back
(seL4 MCS's `reply_pop`): a context, the stack's replies and two threads'
binding codes written (`NtfnFrame.returnDonationToCancelledCaller`), the chains
kept (`returnDonationToCancelledCaller_preserves_donationChainWellFormed`) and
the reply left heading no stack (`finaliseReplyReturn_replyUnheaded`).  Then the
splice, the restore, the consume, the unlink, the replenishment migration, the
holder's deschedule and the PIP walk keep every notification and what the
queues and budgets read of every thread (`NtfnFrame`); the reply-waiter queues
by the cancel's own carriage
(`cancelIpcBlocking_preserves_replyWaitersConsistent`), the migration's, the
deschedule's and the walk's (`propagatePipChainCrossCore_replyViews_eq`); the
chains by the splice's, the consume's (on a frame heading no context, which no
`prev` names once spliced), the run-link frame's and the walk's. -/
theorem reply {s : SystemState} {x : SeLe4n.ObjId} {r : Reply} {c : SeLe4n.ThreadId} {t : TCB}
    (h : finaliseStepInvariant s) (hX : s.getObject? x = some (.reply r))
    (hC : r.callerCode = c.val + 1) (hT : s.getTcb? c = some t)
    (hF : replyCallerFinalisable s x r c t = true) :
    finaliseStepInvariant
        (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) ∧
      timeoutBudgetFrame s
        (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  have hI := finaliseReplyStep_keepsIpcInvariantFull s x r c t ⟨h.1, h.2.1, h.2.2.2.2.2⟩ hX hC hT hF
  obtain ⟨-, hNotRes, -, -, ⟨ep, rt, hB⟩, hRO, -, -, -⟩ := replyCallerFinalisable_parts hF
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  have hLk : lookupTcb s c = some t := lookupTcb_of_objects_of_not_reserved s c t hTo hNotRes
  -- The donation return.
  have g0 := FinaliseFrameAny.returnDonationToCancelledCaller s c t h.2.1
  have n0 := NtfnFrame.returnDonationToCancelledCaller s c t h.2.1
  have hC0 := returnDonationToCancelledCaller_preserves_donationChainWellFormed s c t h.2.1
    h.2.2.2.2.1
  obtain ⟨rR, hPreR, hNotHeadPre⟩ := finaliseReplyReturn_replyUnheaded h.2.1 hX hT hF
  obtain ⟨tR, hAtR, hRw⟩ := returnDonationToCancelledCaller_victim_tcb_rewrite s c t h.2.1 hLk
  have hIpcR : tR.ipcState = t.ipcState := by obtain ⟨_, _, e⟩ := hRw; rw [e]
  have hEq := cancelIpcBlocking_replyArm_unfold s c t hB
  generalize hR0 : Lifecycle.Suspend.returnDonationToCancelledCaller s c t = R at *
  -- The cancel, step by step.
  have g1 := FinaliseFrameAny.spliceThreadReplyFrameOut R t g0.invExt
  generalize hS1 : spliceThreadReplyFrameOut R t = s1 at g1
  have hAt1 : s1.objects[c.toObjId]? = some (.tcb tR) := by
    rw [← hS1]; exact spliceThreadReplyFrameOut_tcb_eq R t g0.invExt c.toObjId tR hAtR
  have hLk1 : lookupTcb s1 c = some tR := lookupTcb_of_objects_of_not_reserved _ c tR hAt1 hNotRes
  have hR2 : FinaliseFrameAny s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact (FinaliseFrame.updateTcb _ c _ g1.invExt).any
  have g3 := FinaliseFrameAny.consumeReplyLink _ c t hR2.invExt
  have g4 := FinaliseFrameAny.unlinkReplyWaiterOpt _ c t.blockingServer? g3.invExt
  rw [hS1] at hEq
  have n1 : NtfnFrame R s1 := hS1 ▸ NtfnFrame.spliceThreadReplyFrameOut R t g0.invExt
  have n2 : NtfnFrame s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 c) :=
    NtfnFrame.restoreToReadyStaging s1 c _ tR g1.invExt hLk1
      (fun o e => by rw [hIpcR, hB] at e; cases e)
  have n3 := NtfnFrame.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s1 c) c t
    hR2.invExt
  have n4 := NtfnFrame.of_agreeOffRunLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks
    (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s1 c) c t) c
    t.blockingServer?)
  have hInvC : (Lifecycle.Suspend.cancelIpcBlocking s c t).objects.invExt := by
    rw [hEq]; exact g4.invExt
  have nC : NtfnFrame s (Lifecycle.Suspend.cancelIpcBlocking s c t) := by
    rw [hEq]; exact n0.trans (n1.trans (n2.trans (n3.trans n4)))
  -- The replenishment migration writes release fields alone, and the holder's
  -- deschedule run links alone.
  have hAgM := cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks c t s
  have hInvM : (cancelIpcBlockingReclaimed c t s).objects.invExt :=
    cancelIpcBlockingReclaimed_objects_invExt c t s hInvC
  have nAll := ((nC.trans (NtfnFrame.of_reach (ReachFieldFrame.of_agreeOffReleaseLinks
    (cancelIpcBlockingMigrated_agree c t s)))).trans (NtfnFrame.of_agreeOffRunLinks hAgM)).trans
    (NtfnFrame.finaliseReplyRevert _ t.blockingServer? hInvM)
  have q := nAll.parts h.2.2.1
  -- The reply-waiter queues.
  have hRW1 := cancelIpcBlocking_preserves_replyWaitersConsistent s c t hT h.2.1 h.2.2.2.1
  have hRWM : (cancelIpcBlockingReclaimed c t s).replyWaitersConsistent := by
    refine SystemState.replyWaitersConsistent.of_views ?_ hRW1
    unfold cancelIpcBlockingReclaimed
    rw [descheduleUnboundHolder_replyViews_eq, cancelIpcBlockingMigrated_replyViews_eq]
  have hRW : (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s)
      t.blockingServer?).replyWaitersConsistent := by
    unfold finaliseReplyRevert
    cases t.blockingServer? with
    | none => exact hRWM
    | some sv =>
      exact SystemState.replyWaitersConsistent.of_views
        (propagatePipChainCrossCore_replyViews_eq _ sv _ _ hInvM) hRWM
  -- The donation chains.
  have hC1 : donationChainWellFormed s1 := by
    rw [← hS1]; exact spliceThreadReplyFrameOut_preserves_donationChainWellFormed R t g0.invExt hC0
  have hC2 : donationChainWellFormed (Lifecycle.Suspend.restoreToReadyCancelled s1 c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact donationChainWellFormed_of_frame
      (finaliseWrite.donationChainFrame (FinaliseFrame.updateTcb _ c _ g1.invExt).write) hC1
  have hRid : (⟨x.val⟩ : SeLe4n.ReplyId).toObjId = x := rfl
  -- The restore writes no reply, so a reply reads the same in the spliced state.
  have hRestR : ∀ (k : SeLe4n.ObjId) (rq : Reply),
      (Lifecycle.Suspend.restoreToReadyCancelled s1 c).objects[k]? = some (.reply rq) →
      s1.objects[k]? = some (.reply rq) := fun k rq hk =>
    (restoreToReadyStaging_nonTcb s1 c _ tR g1.invExt hLk1 k _ (fun _ e => by cases e)).mp hk
  have hC3 : donationChainWellFormed
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s1 c) c t) := by
    have hNH : ∀ (rid : SeLe4n.ReplyId) (rq : Reply) (sc : SeLe4n.SchedContextId),
        t.replyObject = some rid →
        (Lifecycle.Suspend.restoreToReadyCancelled s1 c).getReply? rid = some rq →
        rq.next ≠ some (.head sc) := by
      intro rid rq sc hr hq e
      rw [hRO] at hr; cases hr
      have hq1 := hRestR _ rq ((SystemState.getReply?_eq_some_iff _ _ _).mp hq)
      -- The spliced frame's upward link is its pre-state one, or a frame link.
      rcases spliceThreadReplyFrameOut_cases R t with e1 | ⟨rid0, hr0, e1⟩
      · rw [← hS1, e1, hRid, hPreR] at hq1
        have hrq : rq = rR := by cases hq1; rfl
        exact hNotHeadPre sc (by rw [← hrq]; exact e)
      · rw [hRO] at hr0; cases hr0
        rw [← hS1] at hq1
        rcases spliceReplyFrameOut_cases e1 with e2 | ⟨r1, above, a1, hR1, hN1, hA1, hP1, hSt⟩ |
            ⟨r1, below, b1, hR1, hN1, _, hB1, hBn1, hSt⟩
        · rw [e2, hRid, hPreR] at hq1
          have hrq : rq = rR := by cases hq1; rfl
          exact hNotHeadPre sc (by rw [← hrq]; exact e)
        rotate_left
        · -- The cut from below keeps the cut frame's `next`, which is `none`.
          obtain ⟨-, hRv, -⟩ := severReplyFrameBelowStores_values g0.invExt hR1 hN1 hB1 hBn1 hSt
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hq1] at hRv
          cases hRv
          exact absurd e (by simp [hN1])
        · obtain ⟨rp, hrp, -, hnx⟩ := spliceReplyFrameStores_reply_caller_and_headLink g0.invExt
            hR1 hN1 hA1 hP1 hSt _ rq ((SystemState.getReply?_eq_some_iff _ _ _).mpr hq1)
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPreR] at hrp
          have hrp' : rp = rR := by cases hrp; rfl
          subst hrp'
          rcases hnx with hn | ⟨_, -, hy⟩
          · exact hNotHeadPre sc (hn.symm.trans e)
          · exact hy sc e
    refine consumeReplyLink_preserves_donationChainWellFormed _ c t hR2.invExt hC2
      hNH (fun rid a ra hr ha => ?_) (fun rid rq hr hq => ?_)
    · rw [hRO] at hr; cases hr
      exact spliceThreadReplyFrameOut_unreferenced R t _ g0.invExt hC0 hRO a ra
        (by rw [hS1]; exact hRestR _ ra ha)
    · have hq1 := hRestR _ rq ((SystemState.getReply?_eq_some_iff _ _ _).mp hq)
      have hRid' := hr
      rw [hRO] at hRid'; cases hRid'
      exact spliceThreadReplyFrameOut_cut_prev_none R t _ g0.invExt hC0 hRO rq
        (by rw [hS1]; exact (SystemState.getReply?_eq_some_iff _ _ _).mpr hq1)
        (fun sc => hNH _ rq sc hr hq)
  have hC4 : donationChainWellFormed (Lifecycle.Suspend.cancelIpcBlocking s c t) := by
    rw [hEq]
    exact donationChainWellFormed_of_frame (finaliseWrite.donationChainFrame
      (.of_agreeOffRunLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ c _))) hC3
  have hCM : donationChainWellFormed (cancelIpcBlockingReclaimed c t s) :=
    donationChainWellFormed_of_frame (finaliseWrite.donationChainFrame (.of_agreeOffRunLinks hAgM))
      (donationChainWellFormed_of_frame (finaliseWrite.donationChainFrame
        (.of_agreeOffReleaseLinks (cancelIpcBlockingMigrated_agree c t s))) hC4)
  have hC5 : donationChainWellFormed
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
    unfold finaliseReplyRevert
    cases t.blockingServer? with
    | none => exact hCM
    | some sv => exact propagatePipChainCrossCore_preserves_donationChainWellFormed _ sv _ _ hInvM hCM
  exact ⟨⟨hI.1, hI.2.1, q.1, hRW, hC5, hI.2.2⟩, q.2⟩

/-- A stashed reply's unlink carries it, and frames every budget: the
receiver's stash, a field neither the queues nor the budgets read, rewritten in
its slot. -/
theorem unstash {s s1 : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} (x : SeLe4n.ObjId)
    (h : finaliseStepInvariant s) (hT : s.getTcb? tid = some t)
    (hC : t.pendingReceiveReplyCode = x.val + 1) (e : s1 = s.updateTcb tid TCB.stashCleared) :
    finaliseStepInvariant s1 ∧ timeoutBudgetFrame s s1 := by
  subst e
  have hI := finaliseUnstashStep_keepsIpcInvariantFull s _ x tid t ⟨h.1, h.2.1⟩ hT hC rfl
  have q := (ReachFieldFrame.updateTcb s tid (f := TCB.stashCleared) h.2.1
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)).parts h.2.2.1
  exact ⟨⟨hI.1, hI.2, q.1, SystemState.replyWaitersConsistent.of_views q.2.2 h.2.2.2.1,
    h.chain_of_frame (FinaliseFrame.updateTcb s tid _ h.2.1), h.loan_of_frame (FinaliseFrame.updateTcb s tid _ h.2.1)⟩, q.2.1⟩

/-- WS-ZA ZA6.6: a yield step carries it, and frames every budget: the yield
codes, a context's consumed count and a yielder's two return registers. -/
theorem yieldStep {s s' : SystemState} (h : finaliseStepInvariant s)
    (hI : ipcInvariantFull s') (R : ReachFieldFrame s s') (F : FinaliseFrame s s') :
    finaliseStepInvariant s' ∧ timeoutBudgetFrame s s' :=
  have q := R.parts h.2.2.1
  ⟨⟨hI, F.invExt, q.1, SystemState.replyWaitersConsistent.of_views q.2.2 h.2.2.2.1,
    h.chain_of_frame F, h.loan_of_frame F⟩, q.2.1⟩

end finaliseStepInvariant

/-- **The finalisation's timeout-budget checks refuse no reachable thread**: no
reachable thread holds a timeout budget (`allTimeoutBudgetsNone`, a conjunct of
`ipcReachable`, since no transition writes one), so the clause of
`threadFinaliseAdmitted` and of `endpointBlockedCancellable` that reads it holds
of every thread a reachable state stores. -/
theorem timeoutBudget_isNone_of_ipcReachable {st : SystemState} (h : ipcReachable st)
    {tid : SeLe4n.ThreadId} {t : TCB} (hT : st.getTcb? tid = some t) :
    t.timeoutBudget.isNone = true := by
  rw [h.2.2.1 tid t ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)]; rfl

/-- **The finalisation keeps the reachable state**: the bundle, the notification
queues, the budgets, the reply-waiter queues and the donation chains carried one
walk step at a time (`finaliseFinalObject_closed`, `finaliseStepInvariant`); the
run queues' agreement by its run-queue stage. -/
theorem finaliseFinalObject_preserves_ipcReachable (target : Nat) {st : SystemState}
    (h : ipcReachable st) (hW : lentContextHeadsLenderFrame st) :
    ipcReachable (finaliseFinalObject target st) := by
  obtain ⟨⟨hFull', hInv', hNC', hRW', hCh', -⟩, hB'⟩ := finaliseFinalObject_closed
    (fun s => finaliseStepInvariant s ∧ timeoutBudgetFrame st s)
    (fun _ _ _ _ _ _ h hE hH hT hC =>
      have r := h.1.endpointCancel hE hH hT hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hN _ hT hC =>
      have r := h.1.notificationCancel hN hT hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ h hN _ hCode hIn =>
      have r := h.1.unbind hN hCode hIn
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ h hT hS hO hId =>
      have r := h.1.deschedule hT hS hO hId
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ _ h hT hS hSc hB hOk =>
      have r := h.1.release hT hS hSc hB hOk
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hT hI hN hC =>
      have r := h.1.cancel hT hI hN hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ _ h hT hE hC =>
      have r := h.1.endpointBlockedCancel hT hE hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ h hT hS hO hI hId =>
      have r := h.1.suspend hT hS hO hI hId
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ t h =>
      have r := h.1.releaseCores t
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ _ h hSc hRep hR hN hS _ h₀ hA hS₀ =>
      have r := h.1.unstack hSc hRep hR hN hS h₀.1 hA hS₀
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hX hC hT hF =>
      have r := h.1.reply hX hC hT hF
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ x _ _ h hT hC hS =>
      have r := h.1.unstash x hT hC hS
      ⟨r.1, h.2.trans r.2⟩)
    ⟨fun s t h =>
      have r := h.1.yieldStep (cancelYieldTo_preserves_ipcInvariantFull s t h.1.2.1 h.1.1)
        (ReachFieldFrame.cancelYieldTo s t h.1.2.1) (FinaliseFrame.cancelYieldTo s t h.1.2.1)
      ⟨r.1, h.2.trans r.2⟩,
     fun s c h =>
      have r := h.1.yieldStep (completeYieldFrom_preserves_ipcInvariantFull s c h.1.2.1 h.1.1)
        (ReachFieldFrame.completeYieldFrom s c h.1.2.1) (FinaliseFrame.completeYieldFrom s c h.1.2.1)
      ⟨r.1, h.2.trans r.2⟩⟩
    target st ⟨.of_ipcReachable h hW, .refl st⟩
  exact ⟨hFull', hInv', allTimeoutBudgetsNone_of_frame hB' h.2.2.1, hNC', hCh',
    ((finaliseFinalObject_runQueueEntryStage target st).1 h.2.1 h.2.2.2.2.2.1).2, hRW'⟩

/-- **WS-ZA ZA5.5: a revocation keeps the reachable state**: it rewrites one
endpoint's `serviceRegistered`, which nothing the reachable state reads, and keeps
every thread, notification, reply and scheduling context, and the scheduler. -/
theorem revokeService_preserves_ipcReachable {sid : ServiceId} {st st' : SystemState}
    (h : ipcReachable st) (hR : revokeService sid st = .ok ((), st')) : ipcReachable st' := by
  have hObjInv := h.objects_invExt
  have hRw := revokeService_serviceRecordRewrite hR
  have hL := hRw.lookup hObjInv
  have hBack : ∀ (k : SeLe4n.ObjId) (o : KernelObject), st'.objects[k]? = some o →
      (∀ ep, o ≠ .endpoint ep) → st.objects[k]? = some o := fun k o ho hN => by
    rcases hL k with e | ⟨ep, c, h0, h1⟩
    · rw [← e]; exact ho
    · rw [h1] at ho; cases ho; exact absurd rfl (hN _)
  have hFwd : ∀ (k : SeLe4n.ObjId) (o : KernelObject), st.objects[k]? = some o →
      (∀ ep, o ≠ .endpoint ep) → st'.objects[k]? = some o := fun k o ho hN => by
    rcases hL k with e | ⟨ep, c, h0, h1⟩
    · rw [e]; exact ho
    · rw [h0] at ho; cases ho; exact absurd rfl (hN _)
  have hRL : ∀ k, replyStackLinks? st'.objects[k]? = replyStackLinks? st.objects[k]? := fun k => by
    rcases hL k with e | ⟨ep, c, h0, h1⟩
    · rw [e]
    · rw [h0, h1]; rfl
  have hSH : ∀ k, schedContextStackHead? st'.objects[k]? = schedContextStackHead? st.objects[k]? :=
    fun k => by
      rcases hL k with e | ⟨ep, c, h0, h1⟩
      · rw [e]
      · rw [h0, h1]; rfl
  have hViews : st'.replyViews = st.replyViews := funext fun k => by
    unfold SystemState.replyViews SystemState.getObject?
    rcases hL k with e | ⟨ep, c, h0, h1⟩
    · rw [e]
    · rw [h0, h1]; rfl
  refine ⟨revokeService_preserves_ipcInvariantFull st st' sid hObjInv h.ipcInvariantFull hR,
    hRw.invExt hObjInv,
    fun tid tcb hT => h.allTimeoutBudgetsNone tid tcb (hBack _ _ hT (fun _ e => by cases e)),
    notificationWaiterConsistent_of_tcbLinkFrame h.notificationWaiterConsistent
      (fun k n hn => hBack k _ hn (fun _ e => by cases e))
      (fun k n hn => hFwd k _ hn (fun _ e => by cases e))
      (fun k ty hy => ⟨ty, hFwd k _ hy (fun _ e => by cases e), rfl, rfl, rfl⟩)
      (fun k tx hx => ⟨tx, hBack k _ hx (fun _ e => by cases e), rfl, rfl, rfl⟩),
    donationChainWellFormed_of_frame ⟨hRL, hSH, fun oid r' hr hc =>
      ⟨r', hBack oid _ hr (fun _ e => by cases e), hc⟩⟩ h.donationChainWellFormed,
    ((revokeService_runQueueStage hR).entry.1 hObjInv h.runQueueRefined).2,
    SystemState.replyWaitersConsistent.of_views hViews h.replyWaitersConsistent⟩

/-- **The retire after the finalisation keeps the reachable state**: the
release's (`revokeService_preserves_ipcReachable`), the finalisation's
(`finaliseFinalObject_preserves_ipcReachable`), then the retire's
(`retireFinalObject_preserves_ipcReachable`). -/
theorem retireFinalisedObject_preserves_ipcReachable (ec : Concurrency.CoreId)
    (target recorder : Nat) {st : SystemState} (h : ipcReachable st)
    (hW : lentContextHeadsLenderFrame st) :
    ipcReachable (retireFinalisedObject ec target recorder st) := by
  have h0 := releaseFinalRegistration_closed
    (fun s => ipcReachable s ∧ lentContextHeadsLenderFrame s)
    (fun _ _ _ hs hR => ⟨revokeService_preserves_ipcReachable hs.1 hR,
      hs.2.of_loanWrite (revokeService_loanWrite hR hs.1.objects_invExt)⟩)
    target st ⟨h, hW⟩
  exact retireFinalObject_preserves_ipcReachable ec target recorder
    (finaliseFinalObject_preserves_ipcReachable target h0.1 h0.2)


/-- **The compiled splice keeps the donation chain.**  The in-place form a final
delete runs is `spliceReplyFrameOutOrSelf` (`spliceReplyFrameOutOrSelfInPlace_eq`),
so it keeps `donationChainWellFormed` for the same reason. -/
theorem spliceReplyFrameOutOrSelfInPlace_preserves_donationChainWellFormed (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (spliceReplyFrameOutOrSelfInPlace st rid) := by
  rw [spliceReplyFrameOutOrSelfInPlace_eq]
  exact spliceReplyFrameOutOrSelf_preserves_donationChainWellFormed st rid hInv hChain

/-- **The compiled consume keeps the donation chain** under the premises the
link form needs: the reply heads no stack, no frame's `prev` names it, and its own `prev` is clear.  It is
`consumeCallerReplyLink` (`consumeCallerReplyInPlace_eq`). -/
theorem consumeCallerReplyInPlace_preserves_donationChainWellFormed (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (a : SeLe4n.ReplyId) (ra : Reply),
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid)
    (hPrevNone : ∀ r : Reply, st.getReply? rid = some r → r.prev = none) :
    donationChainWellFormed (consumeCallerReplyInPlace st caller rid) := by
  rw [consumeCallerReplyInPlace_eq]
  exact consumeCallerReplyLink_preserves_donationChainWellFormed st caller rid hInv hChain
    hNotHead hUnreferenced hPrevNone

end SeLe4n.Kernel
