/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 23 — the finalisation keeps `ipcReachable`, staged with `IPC.Invariant.Reachability`, whose staged pack it extends.
import SeLe4n.Kernel.IPC.Invariant.Reachability
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake

/-!
# The finalisation keeps the reachable state

WS-ZA ZA5.4 part 23: the finalisation a final delete runs before its retire
(`finaliseFinalObject`: seL4's `cancelAllIPC`, `unbindMaybeNotification` and
`cancelAllSignals`) keeps `ipcReachable`, so the finalising delete's retire
(`retireFinalisedObject`) does.  Each conjunct is carried one walk step at a
time (`finaliseFinalObject_closed`), except the donation chains, which the
finalisation's write frame leaves alone outright (`FinaliseFrame`: no reply and
no scheduling context is written), and the run queues' agreement with the
threads' links, which is the finalisation's run-queue stage
(`finaliseFinalObject_runQueueEntryStage`).

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

theorem modifyObject_preserves_objects_invExt {st : SystemState} {k : SeLe4n.ObjId}
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) :
    (st.modifyObject k f).objects.invExt := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    show (st.objects.modify k f).invExt
    rw [e]; exact hInv
  | some o =>
    show (st.objects.modify k f).invExt
    rw [RobinHood.RHTable.modify_of_get? hG]
    exact RHTable_insert_preserves_invExt _ _ _ hInv

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

/-- **What a notification waiter's cancel keeps of the reachable state**,
before any wake: the queue it leaves (the head's detach,
`cancelIpcBlocking_notificationHead_eq`), every timeout budget, and the
reply-waiter queues (the cancellation's own theorem). -/
theorem notificationCancel_preserves_reachableParts (st : SystemState)
    (notificationId : SeLe4n.ObjId) (ntfn : Notification) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) (hN : st.getNotification? notificationId = some ntfn)
    (hH : ntfn.waitHead = some t) (hT : st.getTcb? t = some tcb)
    (hB : tcb.ipcState = .blockedOnNotification notificationId)
    (hNC : notificationWaiterConsistent st) (hR : st.replyWaitersConsistent) :
    notificationWaiterConsistent (Lifecycle.Suspend.cancelIpcBlocking st t tcb) ∧
      timeoutBudgetFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) ∧
      (Lifecycle.Suspend.cancelIpcBlocking st t tcb).replyWaitersConsistent := by
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hNo := (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN
  refine ⟨?_, ?_, cancelIpcBlocking_preserves_replyWaitersConsistent st t tcb hT hInv hR⟩
  · obtain ⟨st1, n', -, hN1, hI1, hO1, hHd, hTl, hEq⟩ :=
      cancelIpcBlocking_notificationHead_eq hN hH hT hB hInv
    rw [hEq]
    exact notificationWaiterConsistent_headDetached hNC hNo hH hTo hI1 hN1 hO1 hHd hTl _
      (fun x => ⟨by simp, rfl, rfl⟩)
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
    (hH : ntfn.waitHead = some t) (hT : st.getTcb? t = some tcb)
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
    notificationCancel_preserves_reachableParts st notificationId ntfn t tcb hInv hN hH hT hB hNC hR
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
    {tcb : TCB} {c : Concurrency.CoreId} (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st t tcb c = .ok st') : ReachFieldFrame st st' := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    injection h with h; subst h
    let g : SchedContext → SchedContext := fun sc =>
      { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
    have h1 := ReachFieldFrame.updateSchedContext st scId g hInv
    have hI1 : (st.updateSchedContext scId g).objects.invExt :=
      (FinaliseFrame.updateSchedContext st scId g hInv (fun _ => rfl)).invExt
    generalize st.updateSchedContext scId _ = st1 at h1 hI1 ⊢
    let sch := st1.scheduler.setReplenishQueueOnCore c
      (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore c) scId)
    have h2 := (h1.trans (ReachFieldFrame.of_objects_eq (st' := { st1 with scheduler := sch })
      rfl)).trans (ReachFieldFrame.updateTcb { st1 with scheduler := sch } t
      (f := fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) hI1
      (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))
    exact h2.trans (ReachFieldFrame.of_objects_eq (markKeyChangeFrom_objects _ _ _))
  · cases h

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

/-- **What each step of a finalisation carries**: the IPC bundle, the object
table's well-formedness, the notification queues and the reply-waiter queues. -/
def finaliseStepInvariant (s : SystemState) : Prop :=
  ipcInvariantFull s ∧ s.objects.invExt ∧ notificationWaiterConsistent s ∧
    s.replyWaitersConsistent

namespace finaliseStepInvariant

theorem of_ipcReachable {st : SystemState} (h : ipcReachable st) : finaliseStepInvariant st :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2.2⟩

/-- An endpoint waiter's cancel carries it, and frames every budget. -/
theorem endpointCancel {s : SystemState} {e : SeLe4n.ObjId} {q : Bool} {ep : Endpoint}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : finaliseStepInvariant s)
    (hE : s.getEndpoint? e = some ep) (hH : (endpointWaitQueue ep q).head = some t)
    (hT : s.getTcb? t = some tcb) (hC : endpointWaiterCancellable s e t tcb = true) :
    finaliseStepInvariant (storeEndpointWaiterCancelled s e q t tcb.queueNext) ∧
      timeoutBudgetFrame s (storeEndpointWaiterCancelled s e q t tcb.queueNext) :=
  have r := storeEndpointWaiterCancelled_preserves_reachableParts s e q ep t tcb h.2.1 h.1
    hE hH hT hC h.2.2.1 h.2.2.2
  ⟨⟨storeEndpointWaiterCancelled_preserves_ipcInvariantFull s e q ep t tcb h.2.1 h.1 hE hH hT hC,
    (FinaliseFrame.storeEndpointWaiterCancelled s e q t _ h.2.1).invExt, r.1, r.2.2⟩, r.2.1⟩

/-- A notification waiter's cancel carries it, and frames every budget. -/
theorem notificationCancel {s : SystemState} {n : SeLe4n.ObjId} {ntfn : Notification}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : finaliseStepInvariant s)
    (hN : s.getNotification? n = some ntfn) (hH : ntfn.waitHead = some t)
    (hT : s.getTcb? t = some tcb) (hC : notificationWaiterCancellable s n t tcb = true) :
    finaliseStepInvariant (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) ∧
      timeoutBudgetFrame s (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) :=
  have r := notificationWaiterCancel_preserves_reachableParts s n ntfn t tcb h.2.1 hN hH hT hC
    h.2.2.1 h.2.2.2
  have hF := FinaliseFrame.notificationCancel s t tcb n h.2.1
    (notificationWaiterCancellable_blocked hC)
  ⟨⟨notificationWaiterCancel_preserves_ipcInvariantFull s n t tcb h.2.1 h.1 hT hC,
    (hF.trans (FinaliseFrame.wakeCancelledWaiter _ t hF.invExt)).invExt, r.1, r.2.2⟩, r.2.1⟩

/-- The unbind carries it, and frames every budget. -/
theorem unbind {s : SystemState} {n : SeLe4n.ObjId} {ntfn : Notification} {t : SeLe4n.ThreadId}
    (h : finaliseStepInvariant s) (hN : s.getNotification? n = some ntfn)
    (hCode : boundNotificationCodeOf s t = n.val + 1) (hIn : unbindNotificationInPlace s t = true) :
    finaliseStepInvariant (storeUnbindNotification s t n) ∧
      timeoutBudgetFrame s (storeUnbindNotification s t n) :=
  have r := storeUnbindNotification_preserves_reachableParts s n ntfn t h.2.1 hN h.2.2.1 h.2.2.2
  ⟨⟨storeUnbindNotification_preserves_ipcInvariantFull s n t h.2.1 h.1 hCode hIn,
    (FinaliseFrame.storeUnbindNotification s t n h.2.1).invExt, r.1, r.2.2⟩, r.2.1⟩

/-- A thread's or a context's reservation unbind carries it, and frames every
budget. -/
theorem scUnbind {s s' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB} {sc : SchedContext}
    (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb) (hS : tcb.scBindingScCode ≠ 0)
    (hO : tcb.scBindingOwnerCode = 0) (hR : tcb.runCoreCode = 0)
    (hH : threadHeldOnSomeCore s t = false)
    (hA : ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true)
    (hSc : s.getSchedContext? ⟨tcb.scBindingScCode - 1⟩ = some sc)
    (hB : sc.boundThreadCode = t.val + 1)
    (hOk : cancelDonationArmOnCore s t tcb = .ok s') :
    finaliseStepInvariant s' ∧ timeoutBudgetFrame s s' :=
  have hI := finaliseScUnbindStep_keepsIpcInvariantFull s s' t tcb sc ⟨h.1, h.2.1⟩ hT hS hO hR
    hH hA hSc hB hOk
  have hOk' : cancelBoundDonationOnCore s t tcb (determineTargetCore s t) = .ok s' := by
    rw [← cancelDonationArmOnCore_of_codes s t hS hO]; exact hOk
  have r := (cancelBoundDonationOnCore_reachFieldFrame h.2.1 hOk').parts h.2.2.1
  ⟨⟨hI.1, hI.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2⟩, r.2.1⟩

/-- A thread's notification cancel, before any wake, carries it, and frames
every budget. -/
theorem cancel {s : SystemState} {n : SeLe4n.ObjId} {t : SeLe4n.ThreadId} {tcb : TCB}
    {ntfn : Notification} (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb)
    (hI : tcb.ipcState = .blockedOnNotification n) (hN : s.getNotification? n = some ntfn)
    (hH : ntfn.waitHead = some t) (hC : notificationWaiterCancellable s n t tcb = true) :
    finaliseStepInvariant (Lifecycle.Suspend.cancelIpcBlocking s t tcb) ∧
      timeoutBudgetFrame s (Lifecycle.Suspend.cancelIpcBlocking s t tcb) :=
  have hF := finaliseCancelStep_keepsIpcInvariantFull s n t tcb ntfn ⟨h.1, h.2.1⟩ hT hI hN hH hC
  have r := notificationCancel_preserves_reachableParts s n ntfn t tcb h.2.1 hN hH hT hI
    h.2.2.1 h.2.2.2
  ⟨⟨hF.1, hF.2, r.1, r.2.2⟩, r.2.1⟩

/-- A finalised thread's suspend carries it, and frames every budget: the
deschedule wherever it is placed, then the inactive mark. -/
theorem suspend {s : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : finaliseStepInvariant s) (hT : s.getTcb? t = some tcb) (hS : tcb.ipcStateCode = 0)
    (hO : tcb.ipcObjectCode = 0) (hI : tcb.threadState ≠ .Inactive)
    (hId : isIdleThreadId t = false) :
    finaliseStepInvariant ((descheduleAtPlacement s t).updateTcb t (fun t => { t with threadState := .Inactive })) ∧
      timeoutBudgetFrame s ((descheduleAtPlacement s t).updateTcb t (fun t => { t with threadState := .Inactive })) :=
  have hF := finaliseSuspendStep_keepsIpcInvariantFull s t tcb ⟨h.1, h.2.1⟩ hT hS hO hI hId
  have hD := (FinaliseFrame.descheduleAt s t (placedCoreOf? s t) h.2.1).invExt
  have r := ((ReachFieldFrame.descheduleAtPlacement s t).trans
    (ReachFieldFrame.updateTcb (descheduleAtPlacement s t) t
      (f := fun t => { t with threadState := .Inactive }) hD
      (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))).parts h.2.2.1
  ⟨⟨hF.1, hF.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2⟩, r.2.1⟩

/-- The release of every core's hold on a thread carries it, and frames every
budget: it writes no object. -/
theorem release {s : SystemState} (t : SeLe4n.ThreadId) (h : finaliseStepInvariant s) :
    finaliseStepInvariant (finaliseThreadReleaseCores s t) ∧
      timeoutBudgetFrame s (finaliseThreadReleaseCores s t) :=
  have hF := finaliseReleaseStep_keepsIpcInvariantFull s t ⟨h.1, h.2.1⟩
  have r := (ReachFieldFrame.of_objects_eq (st := s) (st' := finaliseThreadReleaseCores s t)
    (finaliseThreadReleaseCores_objects s t)).parts h.2.2.1
  ⟨⟨hF.1, hF.2, r.1, SystemState.replyWaitersConsistent.of_views r.2.2 h.2.2.2⟩, r.2.1⟩

end finaliseStepInvariant

/-- **The finalisation keeps the reachable state**: the bundle, the notification
queues, the budgets and the reply-waiter queues carried one walk step at a time
(`finaliseFinalObject_closed`, `finaliseStepInvariant`); the donation chains by
the finalisation's write frame; the run queues' agreement by its run-queue
stage. -/
theorem finaliseFinalObject_preserves_ipcReachable (target : Nat) {st : SystemState}
    (h : ipcReachable st) : ipcReachable (finaliseFinalObject target st) := by
  obtain ⟨⟨hFull', hInv', hNC', hRW'⟩, hB'⟩ := finaliseFinalObject_closed
    (fun s => finaliseStepInvariant s ∧ timeoutBudgetFrame st s)
    (fun _ _ _ _ _ _ h hE hH hT hC =>
      have r := h.1.endpointCancel hE hH hT hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hN hH hT hC =>
      have r := h.1.notificationCancel hN hH hT hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ h hN _ hCode hIn =>
      have r := h.1.unbind hN hCode hIn
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hT hS hO hR hH hA hSc hB hOk =>
      have r := h.1.scUnbind hT hS hO hR hH hA hSc hB hOk
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ _ _ h hT hI hN hH hC =>
      have r := h.1.cancel hT hI hN hH hC
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ _ _ h hT hS hO hI hId =>
      have r := h.1.suspend hT hS hO hI hId
      ⟨r.1, h.2.trans r.2⟩)
    (fun _ t h =>
      have r := h.1.release t
      ⟨r.1, h.2.trans r.2⟩)
    target st ⟨.of_ipcReachable h, .refl st⟩
  exact ⟨hFull', hInv', allTimeoutBudgetsNone_of_frame hB' h.2.2.1, hNC',
    donationChainWellFormed_of_frame
      (finaliseWrite.donationChainFrame (finaliseFinalObject_frame target st h.2.1).write)
      h.2.2.2.2.1,
    ((finaliseFinalObject_runQueueEntryStage target st).1 h.2.1 h.2.2.2.2.2.1).2, hRW'⟩

/-- **The retire after the finalisation keeps the reachable state**: the
finalisation's (`finaliseFinalObject_preserves_ipcReachable`), then the
retire's (`retireFinalObject_preserves_ipcReachable`). -/
theorem retireFinalisedObject_preserves_ipcReachable (ec : Concurrency.CoreId)
    (target recorder : Nat) {st : SystemState} (h : ipcReachable st) :
    ipcReachable (retireFinalisedObject ec target recorder st) :=
  retireFinalObject_preserves_ipcReachable ec target recorder
    (finaliseFinalObject_preserves_ipcReachable target h)

end SeLe4n.Kernel
