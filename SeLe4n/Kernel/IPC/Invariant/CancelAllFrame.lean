/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.CancelAll
import SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# What a final delete's finalisation writes

WS-ZA ZA5.4 part 23: `finaliseFinalObject` (`IPC/Operations/CancelAll.lean`)
cancels an endpoint's or a notification's waiters and unbinds a notification
before the retire.  This module states what those writes are, once, for every
consumer:

* **The walks' induction** (`cancelEndpointQueue_closed`,
  `cancelNotificationQueue_closed`, `finaliseFinalObject_closed`): a property
  every step keeps holds after the whole finalisation, whatever the fuel.
* **The write frame** (`FinaliseFrame`): only the object store, the
  scheduler and the cores' FP/SIMD-owner and residency records change (a
  finalised thread is released by every core, WS-ZA ZA5.4 part 24), the object
  table stays well formed, and every key either
  keeps its object or holds a thread, an endpoint or a notification before and
  after, of the same kind and with the same capability slots.  So no CNode, no
  untyped, no VSpace root and no page table is written
  (`FinaliseFrame.kind`, `FinaliseFrame.roots_iff`), and the teardown's
  well-formedness carries across the finalisation
  (`finaliseFinalObject_preserves_teardownWellFormed`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The walks' induction
-- ============================================================================

/-- **A property every endpoint cancel keeps holds after the walk.** -/
theorem cancelEndpointQueue_closed (P : SystemState → Prop) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (hStep : ∀ (s : SystemState) (ep : Endpoint) (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getEndpoint? endpointId = some ep → (endpointWaitQueue ep isReceiveQ).head = some t →
      s.getTcb? t = some tcb → endpointWaiterCancellable s endpointId t tcb = true →
      P (storeEndpointWaiterCancelled s endpointId isReceiveQ t tcb.queueNext)) :
    ∀ (fuel : Nat) (st : SystemState), P st →
      P (cancelEndpointQueue endpointId isReceiveQ fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [cancelEndpointQueue]
    split
    · next ep hE =>
      split
      · next t hH =>
        split
        · next tcb hT =>
          split
          · next hC => exact ih _ (hStep st ep t tcb h hE hH hT hC)
          · exact h
        · exact h
      · exact h
    · exact h

/-- **A property every notification cancel keeps holds after the walk.** -/
theorem cancelNotificationQueue_closed (P : SystemState → Prop) (notificationId : SeLe4n.ObjId)
    (hStep : ∀ (s : SystemState) (n : Notification) (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getNotification? notificationId = some n → n.waitHead = some t →
      s.getTcb? t = some tcb → notificationWaiterCancellable s notificationId t tcb = true →
      P (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t)) :
    ∀ (fuel : Nat) (st : SystemState), P st →
      P (cancelNotificationQueue notificationId fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [cancelNotificationQueue]
    split
    · next n hN =>
      split
      · next t hH =>
        split
        · next tcb hT =>
          split
          · next hC => exact ih _ (hStep st n t tcb h hN hH hT hC)
          · exact h
        · exact h
      · exact h
    · exact h

/-- **A property the unbind keeps holds after `unbindMaybeNotification`.** -/
theorem unbindMaybeNotification_closed (P : SystemState → Prop) (notificationId : SeLe4n.ObjId)
    (hStep : ∀ (s : SystemState) (n : Notification) (t : SeLe4n.ThreadId), P s →
      s.getNotification? notificationId = some n → n.boundTCB = some t →
      boundNotificationCodeOf s t = notificationId.val + 1 →
      unbindNotificationInPlace s t = true →
      P (storeUnbindNotification s t notificationId))
    (st : SystemState) (h : P st) : P (unbindMaybeNotification notificationId st) := by
  unfold unbindMaybeNotification
  split
  · next n hN =>
    split
    · next t hB =>
      split
      · next hC =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hC
        exact hStep st n t h hN hB hC.1 hC.2
      · exact h
    · exact h
  · exact h

/-- **The reservation-unbind step a thread's or a context's finalisation takes**:
a `.bound` thread, queued and held nowhere, whose context is bound back to it,
unbound by the destroy cleanup's reservation arm (`cancelDonationArmOnCore`). -/
def FinaliseScUnbindStep (P : SystemState → Prop) : Prop :=
  ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (sc : SchedContext), P s →
    s.getTcb? t = some tcb → tcb.scBindingScCode ≠ 0 → tcb.scBindingOwnerCode = 0 →
    tcb.runCoreCode = 0 → threadHeldOnSomeCore s t = false →
    ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true →
    s.getSchedContext? ⟨tcb.scBindingScCode - 1⟩ = some sc → sc.boundThreadCode = t.val + 1 →
    cancelDonationArmOnCore s t tcb = .ok s' → P s'

/-- **The cancel step a thread's finalisation takes**: the head waiter of a
notification leaves its queue, and is not woken (`cancelIpcBlocking`). -/
def FinaliseCancelStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (tcb : TCB) (ntfn : Notification),
    P s → s.getTcb? t = some tcb → tcb.ipcState = .blockedOnNotification n →
    s.getNotification? n = some ntfn → ntfn.waitHead = some t →
    notificationWaiterCancellable s n t tcb = true →
    P (Lifecycle.Suspend.cancelIpcBlocking s t tcb)

/-- **The suspend step a thread's finalisation takes**: a ready thread that is
not suspended and is no core's idle thread leaves the scheduler where the state
places it (`descheduleAtPlacement`) and is marked `.Inactive`. -/
def FinaliseSuspendStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB), P s → s.getTcb? t = some tcb →
    tcb.ipcStateCode = 0 → tcb.ipcObjectCode = 0 → tcb.threadState ≠ .Inactive →
    isIdleThreadId t = false →
    P ((descheduleAtPlacement s t).updateTcb t finaliseSuspendMark)

/-- **The release step a thread's finalisation takes**: no core holds the thread
as its FP/SIMD owner or its resident (`finaliseThreadReleaseCores`). -/
def FinaliseReleaseStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId), P s → P (finaliseThreadReleaseCores s t)

/-- **The notification-unbind step**: as `unbindMaybeNotification_closed` asks. -/
def FinaliseUnbindStep (P : SystemState → Prop) : Prop :=
  ∀ (notificationId : SeLe4n.ObjId) (s : SystemState) (n : Notification)
    (t : SeLe4n.ThreadId), P s →
    s.getNotification? notificationId = some n → n.boundTCB = some t →
    boundNotificationCodeOf s t = notificationId.val + 1 →
    unbindNotificationInPlace s t = true →
    P (storeUnbindNotification s t notificationId)

/-- **The deschedule step a scheduling context's finalisation takes**: its
ready holder, no core's idle thread, taken off the scheduler where the state
places it. -/
def FinaliseScDescheduleStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB), P s → s.getTcb? t = some tcb →
    tcb.ipcStateCode = 0 → tcb.ipcObjectCode = 0 → isIdleThreadId t = false →
    P (descheduleAtPlacement s t)

/-- **The release step a scheduling context's finalisation takes**: the thread
bound to the context — as its own or on loan — in a state an unbound thread may
idle in, unbound by the reservation arm's in-place unbind with its binding read
as the context's own. -/
def FinaliseScReleaseStep (P : SystemState → Prop) : Prop :=
  ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (sc : SchedContext)
    (x : SeLe4n.ObjId), P s →
    s.getTcb? t = some tcb → tcb.scBindingScCode = x.val + 1 →
    ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true →
    s.getSchedContext? ⟨x.val⟩ = some sc → sc.boundThreadCode = t.val + 1 →
    cancelBoundDonationOnCore s t { tcb with scBindingOwnerCode := 0 }
      (determineTargetCore s t) = .ok s' → P s'

/-- **The unstack step a scheduling context's finalisation takes**: the head of
the reply stack the context heads loses its upward link, then the context its
head. -/
def FinaliseUnstackStep (P : SystemState → Prop) : Prop :=
  ∀ (s s1 : SystemState) (x : SeLe4n.ObjId) (sc : SchedContext) (rid : SeLe4n.ReplyId)
    (r : Reply), P s →
    s.getSchedContext? ⟨x.val⟩ = some sc → sc.scReply = some rid → s.getReply? rid = some r →
    r.next = some (.head ⟨x.val⟩) →
    storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1) →
    P (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none })

/-- **The cancel step a reply's finalisation takes**: the reply's waiting caller,
admitted by `replyCallerFinalisable`, cancelled, and the boost it lent its server
reverted. -/
def FinaliseReplyStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (x : SeLe4n.ObjId) (r : Reply) (c : SeLe4n.ThreadId) (t : TCB), P s →
    s.getObject? x = some (.reply r) → r.callerCode = c.val + 1 → s.getTcb? c = some t →
    replyCallerFinalisable s x r c t = true →
    P (finaliseReplyRevert (Lifecycle.Suspend.cancelIpcBlocking s c t) t.blockingServer?)

/-- **The unlink step a stashed reply's finalisation takes**: the receiver
holding the reply stashed, its stash cleared in its slot. -/
def FinaliseUnstashStep (P : SystemState → Prop) : Prop :=
  ∀ (s s1 : SystemState) (x : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (t : TCB), P s →
    s.getTcb? tid = some t → t.pendingReceiveReplyCode = x.val + 1 →
    s1 = s.updateTcb tid TCB.stashCleared → P s1

/-- A thread whose owner code is already clear is its own owner-cleared view. -/
theorem TCB.ownerCleared_of_zero {t : TCB} (h : t.scBindingOwnerCode = 0) :
    ({ t with scBindingOwnerCode := 0 } : TCB) = t := by
  cases t; cases h; rfl

/-- **The release step covers the thread finalisation's unbind**: a `.bound`
thread is its own owner-cleared view. -/
theorem FinaliseScReleaseStep.scUnbind {P : SystemState → Prop} (h : FinaliseScReleaseStep P) :
    FinaliseScUnbindStep P := by
  intro s s' t tcb sc hP hT hS hO _ _ hA hSc hB hOk
  rw [cancelDonationArmOnCore_of_codes s t hS hO] at hOk
  refine h s s' t tcb sc ⟨tcb.scBindingScCode - 1⟩ hP hT (by show _ = _ - 1 + 1; omega) hA
    hSc hB ?_
  rw [TCB.ownerCleared_of_zero hO]; exact hOk

/-- `replyStackLinkHeads` reads the head link naming the context. -/
theorem replyStackLinkHeads_spec {x : SeLe4n.ObjId} {n : Option ReplyStackLink}
    (h : replyStackLinkHeads x n = true) : n = some (.head ⟨x.val⟩) := by
  rcases n with _ | (_ | ⟨v⟩)
  · cases h
  · cases h
  · simp only [replyStackLinkHeads, beq_iff_eq] at h
    obtain ⟨vv⟩ := v
    simp only at h
    subst h; rfl

/-- **What the reply finalisation's check admits**, read off its codes: the
reply heads no stack, the caller is no reserved or idle thread and is held and
queued nowhere, is blocked on this reply and linked into no endpoint queue, has
no timeout budget, lends no reservation, and so is owed none back. -/
theorem replyCallerFinalisable_parts {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hX : st.getObject? x = some (.reply r))
    (hC : r.callerCode = c.val + 1)
    (h : replyCallerFinalisable st x r c t = true) :
    replyStackLinkIsHead r.next = false ∧ ¬ c.isReserved ∧ isIdleThreadId c = false ∧
      t.runCoreCode = 0 ∧
      (∃ ep rt, t.ipcState = .blockedOnReply ep rt) ∧ t.replyObject = some ⟨x.val⟩ ∧
      t.queueNext = none ∧ t.queuePrev = none ∧ t.timeoutBudget = none ∧
      (∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.schedContextBinding ≠ .donated scId c) ∧
      Lifecycle.Suspend.cancelledCallerDonation? st c t = none := by
  simp only [replyCallerFinalisable, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hHd, hRes⟩, hId⟩, hRun⟩, hSt⟩, hRO⟩, hQN⟩, hQP⟩, hBud⟩, hL⟩ := h
  have hIpc : ∃ ep rt, t.ipcState = .blockedOnReply ep rt := by
    obtain ⟨k, hk⟩ : ∃ k, t.ipcStateCode = k + 4 := ⟨t.ipcStateCode - 4, by omega⟩
    unfold TCB.ipcState ThreadIpcState.ofCodes
    rw [hk]
    exact ⟨_, _, rfl⟩
  have hRO' : t.replyObject = some ⟨x.val⟩ := by
    unfold TCB.replyObject; rw [hRO]; rfl
  refine ⟨hHd, by simpa using hRes, hId, hRun, hIpc, hRO', ?_, ?_, hBud, ?_, ?_⟩
  · simp [TCB.queueNext, hQN, SeLe4n.ThreadId.ofOptCode]
  · simp [TCB.queuePrev, hQP, SeLe4n.ThreadId.ofOptCode]
  · intro tid tcb scId hO hD
    have hf := RobinHood.RHTable.fold_and_true_of_get? st.objects
      (fun _ o => !objectHoldsLoanFrom o r.callerCode) hL
      (by rw [← RHTable_getElem?_eq_get?]; exact hO)
    revert hD
    unfold TCB.schedContextBinding SchedContextBinding.ofCodes
    simp only [objectHoldsLoanFrom, Bool.not_eq_true', Bool.and_eq_false_iff, bne_eq_false_iff_eq,
      beq_eq_false_iff_ne, ne_eq] at hf
    cases hs : tcb.scBindingScCode with
    | zero => intro hD; cases hD
    | succ sv =>
      cases ho : tcb.scBindingOwnerCode with
      | zero => intro hD; cases hD
      | succ ov =>
        intro hD
        simp only [SchedContextBinding.donated.injEq] at hD
        rw [hs, ho] at hf
        rcases hf with hf | hf
        · omega
        · apply hf; rw [hC, ← hD.2]
  · obtain ⟨ep, rt, hB⟩ := hIpc
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hB]
    simp only [hRO']
    apply replyFrameHeadHolder?_of_no_head
    have hGR : st.getReply? ⟨x.val⟩ = some r := by
      unfold SystemState.getReply?
      rw [show (⟨x.val⟩ : SeLe4n.ReplyId).toObjId = x from rfl, ← SystemState.getObject?_eq_getElem,
        hX]
    unfold replyFrameHeadContext?
    rw [hGR]
    simp only
    cases hN : r.next with
    | none => rfl
    | some l =>
      cases l with
      | frame _ => rfl
      | head _ => rw [hN] at hHd; cases hHd

/-- **The priority-inheritance walk writes only the object store and the
scheduler.** -/
theorem propagatePipChainCrossCore_onlyObjectsSchedulerDiffer :
    ∀ (fuel : Nat) (st : SystemState) (s : SeLe4n.ThreadId) (ec : Concurrency.CoreId),
      SystemState.onlyObjectsSchedulerDiffer
        (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 st
  | 0, st, _, _ => by rw [PriorityInheritance.propagatePipChainCrossCore_zero]; exact .refl st
  | n + 1, st, s, ec => by
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    simp only
    have h1 : SystemState.onlyObjectsSchedulerDiffer
        (PriorityInheritance.pipBoostWithWake st s ec).1 st := by
      rw [PriorityInheritance.pipBoostWithWake_state]
      exact PriorityInheritance.updatePipBoostOnCore_onlyObjectsSchedulerDiffer _ _ _
    cases PriorityInheritance.blockingServer st s with
    | none => exact h1
    | some nx => exact (propagatePipChainCrossCore_onlyObjectsSchedulerDiffer n _ nx ec).trans h1

/-- **A reply-blocked caller's cancel, with nothing to give back**: the donation
return declines, so the arm is the splice, the restore, the consume and the
unlink. -/
theorem cancelIpcBlocking_replyArm_of_noDonation (st : SystemState) (c : SeLe4n.ThreadId)
    (t : TCB) {ep : SeLe4n.ObjId} {rt : Option SeLe4n.ThreadId}
    (hB : t.ipcState = .blockedOnReply ep rt)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st c t = none) :
    Lifecycle.Suspend.cancelIpcBlocking st c t =
      SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled (spliceThreadReplyFrameOut st t) c) c t)
        c t.blockingServer? := by
  have hR : Lifecycle.Suspend.returnDonationToCancelledCaller st c t = st := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]
  simp only [hR]

/-- **An IPC state `ipcCodesIdleAllowed` admits is one an unbound thread may
idle in.** -/
theorem passiveServerIdleAllowed_of_codes {tcb : TCB}
    (h : ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true) :
    passiveServerIdleAllowed tcb.ipcState := by
  unfold ipcCodesIdleAllowed at h
  unfold TCB.ipcState ThreadIpcState.ofCodes passiveServerIdleAllowed
  generalize tcb.ipcObjectCode = o at h ⊢
  generalize tcb.ipcStateCode = c at h ⊢
  match c, o with
  | 0, 0 => exact Or.inl rfl
  | 0, _ + 1 => simp at h
  | 1, _ => exact Or.inr (Or.inl ⟨_, Or.inl rfl⟩)
  | 2, _ => exact Or.inr (Or.inl ⟨_, Or.inr rfl⟩)
  | 3, _ => simp at h
  | _ + 4, _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- A thread code `t + 1` decodes to `t`. -/
theorem threadOfOptCode_succ (t : SeLe4n.ThreadId) :
    SeLe4n.ThreadId.ofOptCode (t.val + 1) = some t := by
  have := SeLe4n.ThreadId.ofOptCode_optCode (some t)
  exact this

/-- **A property the unstack keeps holds after it.** -/
theorem finaliseSchedContextUnstack_closed (P : SystemState → Prop) (hUn : FinaliseUnstackStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) : P (finaliseSchedContextUnstack st x) := by
  unfold finaliseSchedContextUnstack
  split
  · rename_i sc hSc
    split
    · rename_i rid hR
      split
      · rename_i r hRr
        split
        · rename_i hH
          split
          · rename_i s1 hS
            exact hUn st s1 x sc rid r h hSc hR hRr (replyStackLinkHeads_spec hH) hS
          · exact h
        · exact h
      · exact h
    · exact h
  · exact h

/-- **A property the release keeps holds after `finaliseSchedContextUnbind`.** -/
theorem finaliseSchedContextUnbind_closed (P : SystemState → Prop) (hRel : FinaliseScReleaseStep P)
    (st : SystemState) (x : SeLe4n.ObjId) (h : P st) : P (finaliseSchedContextUnbind st x) := by
  unfold finaliseSchedContextUnbind
  split
  · rename_i sc hX
    split
    · exact h
    · rename_i hB0
      dsimp only
      split
      · rename_i t hT
        split
        · rename_i hG
          simp only [Bool.and_eq_true, beq_iff_eq] at hG
          obtain ⟨hS, hA⟩ := hG
          split
          · rename_i s' hOk
            refine hRel st s' _ t sc x h hT hS hA ?_ ?_ hOk
            · have hO : st.objects[x]? = some (.schedContext sc) := by rw [← hX]; simp
              unfold SystemState.getSchedContext?
              rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl, hO]
            · simp only [beq_iff_eq] at hB0
              show _ = _ - 1 + 1; omega
          · exact h
        · exact h
      · exact h
  · exact h

/-- **A property the deschedule keeps holds after
`finaliseSchedContextDeschedule`.** -/
theorem finaliseSchedContextDeschedule_closed (P : SystemState → Prop)
    (hDes : FinaliseScDescheduleStep P) (st : SystemState) (x : SeLe4n.ObjId) (h : P st) :
    P (finaliseSchedContextDeschedule st x) := by
  unfold finaliseSchedContextDeschedule
  split
  · split
    · exact h
    · dsimp only
      split
      · rename_i t hT
        split
        · rename_i hG
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hG
          exact hDes st _ t h hT hG.1.1.2 hG.1.2 hG.2
        · exact h
      · exact h
  · exact h

/-- **A property the deschedule, the release and the unstack keep holds after
the scheduling-context finalisation.** -/
theorem finaliseSchedContext_closed (P : SystemState → Prop) (hDes : FinaliseScDescheduleStep P)
    (hRel : FinaliseScReleaseStep P)
    (hUn : FinaliseUnstackStep P) (x : SeLe4n.ObjId) (st : SystemState) (h : P st) :
    P (finaliseSchedContext x st) := by
  rw [finaliseSchedContext_eq]
  split
  · exact finaliseSchedContextUnstack_closed P hUn x _ (finaliseSchedContextUnbind_closed P hRel _ x
      (finaliseSchedContextDeschedule_closed P hDes st x h))
  · exact h

/-- **A property the suspend keeps holds after `finaliseThreadSuspend`.** -/
theorem finaliseThreadSuspend_closed (P : SystemState → Prop) (hSuspend : FinaliseSuspendStep P)
    (s : SystemState) (tid : SeLe4n.ThreadId) (h : P s) : P (finaliseThreadSuspend s tid) := by
  unfold finaliseThreadSuspend
  split
  · rename_i t hT
    split
    · rename_i hG
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hG
      obtain ⟨⟨⟨hS, hO⟩, hI⟩, hId⟩ := hG
      exact hSuspend s tid t h hT hS hO hI hId
    · exact h
  · exact h

/-- **A property the thread finalisation's steps keep holds after it.** -/
theorem finaliseThread_closed (P : SystemState → Prop) (hUnbind : FinaliseUnbindStep P)
    (hSc : FinaliseScUnbindStep P) (hCancel : FinaliseCancelStep P)
    (hSuspend : FinaliseSuspendStep P) (hRelease : FinaliseReleaseStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) :
    P (finaliseThread x st) := by
  rw [finaliseThread_eq]
  split
  · generalize hTid : (⟨x.val⟩ : SeLe4n.ThreadId) = tid
    -- The notification unbind.
    have h1 : P (finaliseThreadUnbindNotification st tid) := by
      unfold finaliseThreadUnbindNotification
      dsimp only
      split
      · exact h
      · rename_i hc
        split
        · rename_i n hN
          split
          · rename_i hB
            simp only [Bool.and_eq_true, beq_iff_eq] at hB hc
            refine hUnbind _ st n tid h hN ?_ ?_ hB.2
            · unfold Notification.boundTCB; rw [hB.1]; exact threadOfOptCode_succ tid
            · simp only [SeLe4n.ObjId.val]; omega
          · exact h
        · exact h
    -- The cancel.
    have h2 : P (finaliseThreadCancel (finaliseThreadUnbindNotification st tid) tid) := by
      generalize finaliseThreadUnbindNotification st tid = s at h1 ⊢
      unfold finaliseThreadCancel
      split
      · rename_i t hT
        split
        · rename_i n hI
          split
          · rename_i ntfn hN
            split
            · rename_i hG
              simp only [Bool.and_eq_true, beq_iff_eq] at hG
              exact hCancel s n tid t ntfn h1 hT hI hN hG.1 hG.2
            · exact h1
          · exact h1
        · exact h1
      · exact h1
    -- The suspend.
    have h3 : P (finaliseThreadSuspend
        (finaliseThreadCancel (finaliseThreadUnbindNotification st tid) tid) tid) :=
      finaliseThreadSuspend_closed P hSuspend _ tid h2
    -- The release.
    have h4 := hRelease _ tid h3
    -- The reservation unbind.
    generalize finaliseThreadReleaseCores _ tid = s at h4 ⊢
    unfold finaliseThreadUnbindSchedContext
    split
    · rename_i t hT
      cases hM : s.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
      | none => simp only [hM, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; exact h4
      | some sc =>
        simp only [hM]
        split
        · rename_i hG
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at hG
          obtain ⟨⟨⟨⟨⟨hS, hO⟩, hR⟩, hH⟩, hA⟩, hM'⟩ := hG
          split
          · rename_i s' hOk
            exact hSc s s' tid t sc h4 hT hS hO hR hH hA hM hM' hOk
          · exact h4
        · exact h4
    · exact h4
  · exact h

/-- **A property the stash clear keeps holds after `finaliseReplyUnstash`.** -/
theorem finaliseReplyUnstash_closed (P : SystemState → Prop) (hSt : FinaliseUnstashStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) : P (finaliseReplyUnstash st x) := by
  unfold finaliseReplyUnstash
  dsimp only
  split
  · exact h
  · split
    · rename_i t hT
      split
      · rename_i hC
        exact hSt st _ x _ t h hT (by simpa using hC) rfl
      · exact h
    · exact h

/-- **A property the reply cancel, the suspend and the stash clear keep holds
after the reply finalisation.** -/
theorem finaliseReply_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (hSuspend : FinaliseSuspendStep P) (hSt : FinaliseUnstashStep P) (x : SeLe4n.ObjId)
    (st : SystemState) (h : P st) :
    P (finaliseReply x st) := by
  unfold finaliseReply
  split
  · rename_i r hX
    split
    · exact finaliseReplyUnstash_closed P hSt x st h
    · rename_i h0
      dsimp only
      split
      · rename_i t hT
        split
        · rename_i hG
          refine finaliseThreadSuspend_closed P hSuspend _ _ (hRep st x r _ t h hX ?_ hT hG)
          simp only [beq_iff_eq] at h0
          show _ = _ - 1 + 1; omega
        · exact h
      · exact h
  · exact h

/-- **A property every cancel, unbind and suspend keeps holds after the
finalisation.** -/
theorem finaliseFinalObject_closed (P : SystemState → Prop)
    (hEp : ∀ (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (s : SystemState) (ep : Endpoint)
      (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getEndpoint? endpointId = some ep → (endpointWaitQueue ep isReceiveQ).head = some t →
      s.getTcb? t = some tcb → endpointWaiterCancellable s endpointId t tcb = true →
      P (storeEndpointWaiterCancelled s endpointId isReceiveQ t tcb.queueNext))
    (hNtfn : ∀ (notificationId : SeLe4n.ObjId) (s : SystemState) (n : Notification)
      (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getNotification? notificationId = some n → n.waitHead = some t →
      s.getTcb? t = some tcb → notificationWaiterCancellable s notificationId t tcb = true →
      P (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t))
    (hUnbind : FinaliseUnbindStep P) (hDes : FinaliseScDescheduleStep P)
    (hRel : FinaliseScReleaseStep P)
    (hCancel : FinaliseCancelStep P) (hSuspend : FinaliseSuspendStep P)
    (hRelease : FinaliseReleaseStep P) (hUn : FinaliseUnstackStep P) (hRep : FinaliseReplyStep P)
    (hSt : FinaliseUnstashStep P)
    (target : Nat) (st : SystemState) (h : P st) : P (finaliseFinalObject target st) := by
  unfold finaliseFinalObject
  split
  · exact h
  dsimp only
  split
  · split
    · exact cancelEndpointQueue_closed P _ true (hEp _ true) _ _
        (cancelEndpointQueue_closed P _ false (hEp _ false) _ _ h)
    · exact cancelNotificationQueue_closed P _ (hNtfn _) _ _
        (unbindMaybeNotification_closed P _ (hUnbind _) st h)
    · exact finaliseThread_closed P hUnbind hRel.scUnbind hCancel hSuspend hRelease _ st h
    · exact finaliseSchedContext_closed P hDes hRel hUn _ st h
    · exact finaliseReply_closed P hRep hSuspend hSt _ st h
    · exact h
  · exact h

-- ============================================================================
-- §2  The write frame
-- ============================================================================

/-- **An object a finalisation may write**: a thread, an endpoint, a
notification or a scheduling context. -/
def finaliseWritable (o : KernelObject) : Prop :=
  o.objectType = .tcb ∨ o.objectType = .endpoint ∨ o.objectType = .notification ∨
    o.objectType = .schedContext

theorem finaliseWritable.untyped {o : KernelObject} (h : finaliseWritable o) :
    o.untyped? = none := by
  cases o <;> simp_all [finaliseWritable, KernelObject.objectType, KernelObject.untyped?]

theorem finaliseWritable.not_cnode {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .cnode := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem finaliseWritable.not_vspaceRoot {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .vspaceRoot := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem finaliseWritable_tcb (t : TCB) : finaliseWritable (.tcb t) := Or.inl rfl

theorem finaliseWritable_schedContext (sc : SchedContext) :
    finaliseWritable (.schedContext sc) := Or.inr (Or.inr (Or.inr rfl))

/-- **What a finalisation writes, key by key**: each key keeps its object, or
holds a thread, an endpoint, a notification or a scheduling context before and
after, of the same kind, with the same capability slots and, for a context, the
same reply-stack head. -/
def finaliseWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      post.objectType = pre.objectType ∧ post.tcbSlots = pre.tcbSlots ∧
      schedContextStackHead? (some post) = schedContextStackHead? (some pre) ∧
      finaliseWritable pre

namespace finaliseWrite

theorem refl (st : SystemState) : finaliseWrite st st := fun _ => Or.inl rfl

theorem trans {a b c : SystemState} (h₁ : finaliseWrite a b) (h₂ : finaliseWrite b c) :
    finaliseWrite a c := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, ht₁, hs₁, hh₁, hw₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, ht₁, hs₁, hh₁, hw₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, ht₂.trans ht₁, hs₂.trans hs₁, hh₂.trans hh₁, hw₁⟩

/-- A finalisation write is kind-preserving: what it writes is no CNode, and
keeps its untyped record (none). -/
theorem kind {st st' : SystemState} (h : finaliseWrite st st') : kindPreservingWrite st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, ht, hs, -, hw⟩
  · exact Or.inl e
  · have hw' : finaliseWritable post := by unfold finaliseWritable; rw [ht]; exact hw
    exact Or.inr ⟨pre, post, hp, hq, ht, ht ▸ hw.not_cnode, hs, by
      rw [hw.untyped, hw'.untyped]⟩

/-- An object the finalisation may not write is kept where it is. -/
theorem keeps {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st'.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, -, -, -, -, hw⟩
  · rw [e]; exact hO
  · rw [hO] at hp; cases hp; exact absurd hw hN

/-- …and an object present after a finalisation that it may not write was there
before it. -/
theorem keeps' {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st'.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, hq, ht, -, -, hw⟩
  · rw [← e]; exact hO
  · rw [hO] at hq; cases hq
    exact absurd (by unfold finaliseWritable; rw [ht]; exact hw) hN

/-- **The finalisation writes no VSpace root.** -/
theorem roots_iff {st st' : SystemState} (h : finaliseWrite st st') (oid : SeLe4n.ObjId)
    (r : VSpaceRoot) :
    st'.objects[oid]? = some (.vspaceRoot r) ↔ st.objects[oid]? = some (.vspaceRoot r) := by
  have hN : ¬ finaliseWritable (.vspaceRoot r) := fun hw => hw.not_vspaceRoot rfl
  exact ⟨fun hO => h.keeps' hO hN, fun hO => h.keeps hO hN⟩

/-- **A write that keeps the kinds and every object it may not write is a
finalisation write.** -/
theorem of_kind_keeps {st st' : SystemState} (hK : kindPreservingWrite st st')
    (hT : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), st.objects[oid]? = some o →
      ¬ finaliseWritable o → st'.objects[oid]? = some o)
    (hH : ∀ (oid : SeLe4n.ObjId), schedContextStackHead? st'.objects[oid]? =
      schedContextStackHead? st.objects[oid]?) :
    finaliseWrite st st' := by
  intro oid
  rcases hK oid with e | ⟨pre, post, hp, hq, ht, -, hs, -⟩
  · exact Or.inl e
  · by_cases hw : finaliseWritable pre
    · have := hH oid; rw [hp, hq] at this
      exact Or.inr ⟨pre, post, hp, hq, ht, hs, this, hw⟩
    · exact Or.inl ((hT oid pre hp hw).trans hp.symm)

/-- **A store of a finalisation-writable object's like at its own key.** -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o')
    (hPre : st.objects[k]? = some o) (hW : finaliseWritable o)
    (hT : o'.objectType = o.objectType) (hS : o'.tcbSlots = o.tcbSlots)
    (hH : schedContextStackHead? (some o') = schedContextStackHead? (some o) := by
      first | rfl | simp [schedContextStackHead?]) :
    finaliseWrite st st' := by
  intro oid
  rw [hO]
  by_cases e : oid = k
  · subst e
    exact Or.inr ⟨o, o', hPre, RobinHood.RHTable.getElem?_insert_self st.objects oid o' hInv,
      hT, hS, hH, hW⟩
  · exact Or.inl (RobinHood.RHTable.getElem?_insert_ne st.objects k oid o'
      (by intro h; exact e (eq_of_beq h).symm) hInv)

/-- **Writes off the run-queue links are finalisation writes**: they rewrite
threads only, keeping their slots. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    finaliseWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨t, t', ht, ht'⟩
  · exact Or.inl e
  · obtain ⟨t'', ht'', hE⟩ := h.get_tcb ht
    rw [ht'] at ht''
    cases ht''
    refine Or.inr ⟨.tcb t, .tcb t', ht, ht', rfl, ?_, rfl, finaliseWritable_tcb t⟩
    simp only [KernelObject.tcbSlots,
      TCB.proj_eq_of_withoutRunLinks_eq (·.spaceCells) hE,
      TCB.proj_eq_of_withoutRunLinks_eq (·.spaceLinks) hE]

/-- **A notification-queue unlink is a finalisation write**: it rewrites
notifications and threads' notification links. -/
theorem of_ntfnUnlinkReach {st st' : SystemState} (h : ntfnUnlinkReach st st') :
    finaliseWrite st st' := by
  intro oid
  rcases h.2 oid with e | ⟨n, n', hn, hn', -⟩ | ⟨t, t', ht, ht', ⟨np, nn, rfl⟩⟩
  · exact Or.inl e
  · exact Or.inr ⟨.notification n, .notification n', hn, hn', rfl, rfl, rfl,
      Or.inr (Or.inr (Or.inl rfl))⟩
  · exact Or.inr ⟨.tcb t, .tcb _, ht, ht', rfl, rfl, rfl, finaliseWritable_tcb t⟩

end finaliseWrite

/-- **`st'` is `st` with at most its object store, its scheduler and the cores'
FP/SIMD-owner and residency records rewritten** — what a finalisation writes,
once a finalised thread is released by every core (`finaliseThreadReleaseCores`):
every other machine field, every register bank and the memory are `st`'s. -/
def onlyObjectsSchedulerCoreHoldsDiffer (st' st : SystemState) : Prop :=
  st' = { st with objects := st'.objects, scheduler := st'.scheduler,
                  machine := { st.machine with fpOwner := st'.machine.fpOwner,
                                               residentCode := st'.machine.residentCode } }

namespace onlyObjectsSchedulerCoreHoldsDiffer

theorem refl (st : SystemState) : onlyObjectsSchedulerCoreHoldsDiffer st st := rfl

theorem trans {a b c : SystemState} (h₂ : onlyObjectsSchedulerCoreHoldsDiffer c b)
    (h₁ : onlyObjectsSchedulerCoreHoldsDiffer b a) : onlyObjectsSchedulerCoreHoldsDiffer c a := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer at *
  calc c = { b with objects := c.objects, scheduler := c.scheduler,
                    machine := { b.machine with fpOwner := c.machine.fpOwner,
                                                residentCode := c.machine.residentCode } } := h₂
    _ = _ := by rw [h₁]

theorem of_onlyObjectsSchedulerDiffer {st st' : SystemState}
    (h : SystemState.onlyObjectsSchedulerDiffer st' st) : onlyObjectsSchedulerCoreHoldsDiffer st' st := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

theorem cdt {st st' : SystemState} (h : onlyObjectsSchedulerCoreHoldsDiffer st' st) :
    st'.cdt = st.cdt := by
  have e := congrArg SystemState.cdt h; exact e

theorem asidTable {st st' : SystemState} (h : onlyObjectsSchedulerCoreHoldsDiffer st' st) :
    st'.asidTable = st.asidTable := by
  have e := congrArg SystemState.asidTable h; exact e

/-- The release writes the two records alone. -/
theorem releaseCores (st : SystemState) (t : SeLe4n.ThreadId) :
    onlyObjectsSchedulerCoreHoldsDiffer (finaliseThreadReleaseCores st t) st := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer finaliseThreadReleaseCores
  simp only []
  rw [MachineState.releaseThread, MachineState.releaseThreadOnCores_fields]

end onlyObjectsSchedulerCoreHoldsDiffer

/-- **What a finalisation's step leaves**: only the object store, the scheduler
and the cores' hold records changed, the object table well formed, and a
finalisation write. -/
structure FinaliseFrame (st st' : SystemState) : Prop where
  rest : onlyObjectsSchedulerCoreHoldsDiffer st' st
  invExt : st'.objects.invExt
  write : finaliseWrite st st'

namespace FinaliseFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : FinaliseFrame st st :=
  ⟨.refl st, hInv, .refl st⟩

theorem trans {a b c : SystemState} (h₁ : FinaliseFrame a b) (h₂ : FinaliseFrame b c) :
    FinaliseFrame a c :=
  ⟨h₂.rest.trans h₁.rest, h₂.invExt, h₁.write.trans h₂.write⟩

theorem kind {st st' : SystemState} (h : FinaliseFrame st st') : kindPreservingWrite st st' :=
  h.write.kind

theorem asidTable {st st' : SystemState} (h : FinaliseFrame st st') :
    st'.asidTable = st.asidTable := h.rest.asidTable

theorem cdt {st st' : SystemState} (h : FinaliseFrame st st') : st'.cdt = st.cdt := h.rest.cdt

/-- **The finalisation keeps the teardown's well-formedness, and only shrinks
the roots** — it keeps every root. -/
theorem preserves_teardownWellFormed {st st' : SystemState} (h : FinaliseFrame st st')
    (hW : teardownWellFormed st) :
    teardownWellFormed st' ∧
      vspaceRootsShrink st st' := by
  refine ⟨teardownWellFormed_of_roots_eq h.invExt h.asidTable
    (h.write.roots_iff) hW, fun oid r' hR => ⟨r', (h.write.roots_iff oid r').1 hR, rfl,
      fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩⟩

/-- **The finalisation keeps every slot's capability**: it writes no CNode, and
a thread it writes keeps its space slots. -/
theorem slotCapAt {st st' : SystemState} (h : FinaliseFrame st st') (r : SlotRef) :
    st'.slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
  rcases h.write r.cnode with e | ⟨pre, post, hp, hq, ht, hs, -, hw⟩
  · rw [e]
  · rw [hp, hq]
    simp only [Option.bind_some,
      (KernelObject.slots_eq_of_tcbSlots ht (ht ▸ hw.not_cnode) hs).1]

/-- **The finalisation keeps every untyped record.** -/
theorem getUntyped? {st st' : SystemState} (h : FinaliseFrame st st') :
    st'.getUntyped? = st.getUntyped? :=
  funext fun o => by
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]; exact h.kind.untyped o

end FinaliseFrame

-- ============================================================================
-- §2a  The write frame once reply links are let go
-- ============================================================================

/-- **An object a finalisation may write once it lets go of reply links**: a
reply as well as what `finaliseWritable` admits. -/
def finaliseWritableAny (o : KernelObject) : Prop :=
  finaliseWritable o ∨ o.objectType = .reply

theorem finaliseWritableAny.untyped {o : KernelObject} (h : finaliseWritableAny o) :
    o.untyped? = none := by
  rcases h with h | h
  · exact h.untyped
  · cases o <;> simp_all [KernelObject.objectType, KernelObject.untyped?]

theorem finaliseWritableAny.not_cnode {o : KernelObject} (h : finaliseWritableAny o) :
    o.objectType ≠ .cnode := by
  rcases h with h | h
  · exact h.not_cnode
  · rw [h]; decide

theorem finaliseWritableAny.not_vspaceRoot {o : KernelObject} (h : finaliseWritableAny o) :
    o.objectType ≠ .vspaceRoot := by
  rcases h with h | h
  · exact h.not_vspaceRoot
  · rw [h]; decide

theorem finaliseWritableAny_reply (r : Reply) : finaliseWritableAny (.reply r) := Or.inr rfl

/-- **What a finalisation writes, key by key, once it lets go of reply links**:
each key keeps its object, or holds a thread, an endpoint, a notification, a
scheduling context or a reply before and after, of the same kind and with the
same capability slots.  A context's reply-stack head and a reply's links may
move. -/
def finaliseWriteAny (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      post.objectType = pre.objectType ∧ post.tcbSlots = pre.tcbSlots ∧ finaliseWritableAny pre

namespace finaliseWriteAny

theorem refl (st : SystemState) : finaliseWriteAny st st := fun _ => Or.inl rfl

theorem trans {a b c : SystemState} (h₁ : finaliseWriteAny a b) (h₂ : finaliseWriteAny b c) :
    finaliseWriteAny a c := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, ht₁, hs₁, hw₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hw₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, ht₂, hs₂, hw₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hw₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, ht₁, hs₁, hw₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, ht₂.trans ht₁, hs₂.trans hs₁, hw₁⟩

/-- A finalisation write is one that lets go of no reply link. -/
theorem of_write {st st' : SystemState} (h : finaliseWrite st st') : finaliseWriteAny st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, ht, hs, -, hw⟩
  · exact Or.inl e
  · exact Or.inr ⟨pre, post, hp, hq, ht, hs, Or.inl hw⟩

theorem kind {st st' : SystemState} (h : finaliseWriteAny st st') : kindPreservingWrite st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, ht, hs, hw⟩
  · exact Or.inl e
  · have hw' : finaliseWritableAny post := by
      rcases hw with hw | hw
      · exact Or.inl (by unfold finaliseWritable; rw [ht]; exact hw)
      · exact Or.inr (ht.trans hw)
    exact Or.inr ⟨pre, post, hp, hq, ht, ht ▸ hw.not_cnode, hs, by
      rw [hw.untyped, hw'.untyped]⟩

theorem keeps {st st' : SystemState} (h : finaliseWriteAny st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st.objects[oid]? = some o) (hN : ¬ finaliseWritableAny o) :
    st'.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, -, -, -, hw⟩
  · rw [e]; exact hO
  · rw [hO] at hp; cases hp; exact absurd hw hN

theorem keeps' {st st' : SystemState} (h : finaliseWriteAny st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st'.objects[oid]? = some o) (hN : ¬ finaliseWritableAny o) :
    st.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, hq, ht, -, hw⟩
  · rw [← e]; exact hO
  · rw [hO] at hq; cases hq
    refine absurd ?_ hN
    rcases hw with hw | hw
    · exact Or.inl (by unfold finaliseWritable; rw [ht]; exact hw)
    · exact Or.inr (ht.trans hw)

theorem roots_iff {st st' : SystemState} (h : finaliseWriteAny st st') (oid : SeLe4n.ObjId)
    (r : VSpaceRoot) :
    st'.objects[oid]? = some (.vspaceRoot r) ↔ st.objects[oid]? = some (.vspaceRoot r) := by
  have hN : ¬ finaliseWritableAny (.vspaceRoot r) := fun hw => hw.not_vspaceRoot rfl
  exact ⟨fun hO => h.keeps' hO hN, fun hO => h.keeps hO hN⟩

/-- A store at a key holding a writable object, of its like. -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some o) (hW : finaliseWritableAny o)
    (hT : o'.objectType = o.objectType) (hS : o'.tcbSlots = o.tcbSlots)
    (hAt : st'.objects[k]? = some o')
    (hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]?) :
    finaliseWriteAny st st' := by
  intro oid
  by_cases e : oid = k
  · subst e; exact Or.inr ⟨o, o', hPre, hAt, hT, hS, hW⟩
  · exact Or.inl (hNe oid e)

end finaliseWriteAny

/-- **What a finalisation's step leaves once it lets go of reply links**: the
derivation tree and the ASID table kept, the object table well formed, and a
write of `finaliseWriteAny`. -/
structure FinaliseFrameAny (st st' : SystemState) : Prop where
  cdt : st'.cdt = st.cdt
  asidTable : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt
  write : finaliseWriteAny st st'

/-- A finalisation step's frame is one that lets go of no reply link. -/
theorem FinaliseFrame.any {st st' : SystemState} (h : FinaliseFrame st st') :
    FinaliseFrameAny st st' :=
  ⟨h.cdt, h.asidTable, h.invExt, .of_write h.write⟩

namespace FinaliseFrameAny

theorem refl {st : SystemState} (hInv : st.objects.invExt) : FinaliseFrameAny st st :=
  ⟨rfl, rfl, hInv, .refl st⟩

theorem trans {a b c : SystemState} (h₁ : FinaliseFrameAny a b) (h₂ : FinaliseFrameAny b c) :
    FinaliseFrameAny a c :=
  ⟨h₂.cdt.trans h₁.cdt, h₂.asidTable.trans h₁.asidTable, h₂.invExt, h₁.write.trans h₂.write⟩

theorem kind {st st' : SystemState} (h : FinaliseFrameAny st st') : kindPreservingWrite st st' :=
  h.write.kind

theorem preserves_teardownWellFormed {st st' : SystemState} (h : FinaliseFrameAny st st')
    (hW : teardownWellFormed st) :
    teardownWellFormed st' ∧ vspaceRootsShrink st st' := by
  refine ⟨teardownWellFormed_of_roots_eq h.invExt h.asidTable
    (h.write.roots_iff) hW, fun oid r' hR => ⟨r', (h.write.roots_iff oid r').1 hR, rfl,
      fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩⟩

theorem slotCapAt {st st' : SystemState} (h : FinaliseFrameAny st st') (r : SlotRef) :
    st'.slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
  rcases h.write r.cnode with e | ⟨pre, post, hp, hq, ht, hs, hw⟩
  · rw [e]
  · rw [hp, hq]
    simp only [Option.bind_some,
      (KernelObject.slots_eq_of_tcbSlots ht (ht ▸ hw.not_cnode) hs).1]

theorem getUntyped? {st st' : SystemState} (h : FinaliseFrameAny st st') :
    st'.getUntyped? = st.getUntyped? :=
  funext fun o => by
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]; exact h.kind.untyped o

/-- **A store of a writable object's like at its own key** (no VSpace root). -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some o) (hW : finaliseWritableAny o)
    (h : SeLe4n.Model.storeObject k o' st = .ok ((), st'))
    (hT : o'.objectType = o.objectType) (hS : o'.tcbSlots = o.tcbSlots) : FinaliseFrameAny st st' := by
  have hNR : ∀ r, o' ≠ .vspaceRoot r := by
    intro r e; subst e
    exact hW.not_vspaceRoot (by rw [← hT]; rfl)
  have hOldNR : ∀ r, o ≠ .vspaceRoot r := by
    intro r e; subst e; exact hW.not_vspaceRoot rfl
  refine ⟨storeObject_cdt_eq st st' k o' h, ?_, storeObject_preserves_objects_invExt st st' k o' hInv h,
    finaliseWriteAny.of_insert hInv hPre hW hT hS (storeObject_objects_eq st st' k o' hInv h)
      (fun oid hne => storeObject_objects_ne st st' k oid o' hne hInv h)⟩
  rw [storeObject_asidTable_non_vspaceRoot st st' k o' hNR h, hPre]
  cases o with
  | vspaceRoot r => exact absurd rfl (hOldNR r)
  | _ => rfl

end FinaliseFrameAny

-- ============================================================================
-- §3  Each step's frame
-- ============================================================================

namespace FinaliseFrame

/-- A thread rewritten in its slot, its capability slots kept. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).spaceCells = x.spaceCells ∧ (f x).spaceLinks = x.spaceLinks := by
      intro _; exact ⟨rfl, rfl⟩) :
    FinaliseFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl ((SystemState.getTcb?_eq_some_iff st t x).mp hG)
        (finaliseWritable_tcb x) rfl (by simp only [KernelObject.tcbSlots, (hf x).1, (hf x).2])⟩

/-- An object rewritten in its slot by an update that keeps every object, or
keeps a writable one's kind and slots. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt)
    (hf : ∀ o, f o = o ∨ ((f o).objectType = o.objectType ∧ (f o).tcbSlots = o.tcbSlots ∧
      schedContextStackHead? (some (f o)) = schedContextStackHead? (some o) ∧
      finaliseWritable o)) :
    FinaliseFrame st (st.modifyObject k f) := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    rw [e]; exact .refl hInv
  | some o =>
    rw [RobinHood.RHTable.modify_of_get? hG]
    refine ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv, ?_⟩
    rcases hf o with e | ⟨hT, hS, hH, hW⟩
    · rw [e]
      intro oid
      left
      show (st.objects.insert k o)[oid]? = st.objects[oid]?
      by_cases h : oid = k
      · subst h; exact (RobinHood.RHTable.getElem?_insert_self st.objects oid o hInv).trans hG.symm
      · exact RobinHood.RHTable.getElem?_insert_ne st.objects k oid o
          (by intro h'; exact h (eq_of_beq h').symm) hInv
    · exact finaliseWrite.of_insert hInv rfl hG hW hT hS hH

/-- The wake: a run-queue insert and the `.ready` mark, on threads only. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  refine ⟨.of_onlyObjectsSchedulerDiffer (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c t),
    enqueueRunnableOnCore_preserves_objects_invExt st c t hInv, ?_⟩
  cases hT : st.getTcb? t with
  | none =>
    simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl _
  | some tcb =>
    cases hD : wakeDeclines st c t with
    | true =>
      simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD,
        if_true]
      exact .refl _
    | false =>
      exact (finaliseWrite.of_insert
        (st' := { st with objects := st.objects.insert t.toObjId (.tcb (tcb.setIpcState .ready)) })
        hInv rfl ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT) (finaliseWritable_tcb tcb)
        rfl rfl).trans
        (finaliseWrite.of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD))

theorem wakeCancelledWaiter (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.wakeCancelledWaiter st t) :=
  enqueueRunnableOnCore st _ t hInv

/-- The pop of an endpoint queue's head, each write in its slot. -/
theorem storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storePopHead st endpointId isReceiveQ head next) := by
  have h1 := modifyObject st endpointId (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next))
    hInv (fun o => by
      cases o with
      | endpoint e =>
        right
        simp only [popEndpoint]
        split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl)⟩
      | _ => exact Or.inl rfl)
  cases next with
  | none =>
    simp only [SeLe4n.Kernel.storePopHead]
    exact h1.trans (updateTcb _ _ _ h1.invExt)
  | some n =>
    simp only [SeLe4n.Kernel.storePopHead]
    have h2 := h1.trans (updateTcb _ n tcbAsQueueHead h1.invExt)
    exact h2.trans (updateTcb _ _ _ h2.invExt)

/-- An endpoint waiter's cancel: the pop, the thread's IPC ended, the wake. -/
theorem storeEndpointWaiterCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeEndpointWaiterCancelled st endpointId isReceiveQ t next) := by
  unfold SeLe4n.Kernel.storeEndpointWaiterCancelled
  have h1 := storePopHead st endpointId isReceiveQ t next hInv
  have h2 := h1.trans (updateTcb _ t cancelledEndpointWaiterTcb h1.invExt)
  exact h2.trans (wakeCancelledWaiter _ t h2.invExt)

/-- A notification waiter's cancel: it leaves the notification's queue and is
restored, staged with the cancellation frame. -/
theorem notificationCancel (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (hB : tcb.ipcState = .blockedOnNotification n) :
    FinaliseFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
      Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue st t) t := by
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  rw [hEq]
  have hR := removeFromNotificationWaitQueue_reach st t hInv
  have h1 : FinaliseFrame st (removeFromNotificationWaitQueue st t) := by
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects st t
    exact ⟨by rw [e]; rfl, hR.1, finaliseWrite.of_ntfnUnlinkReach hR⟩
  exact h1.trans (updateTcb _ _ _ h1.invExt)

/-- The unbind, each side in its slot. -/
theorem storeUnbindNotification (st : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeUnbindNotification st t n) := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  have h1 := updateTcb st t (fun x => { x with boundNotificationCode := 0 }) hInv
  exact h1.trans (modifyObject _ n _ h1.invExt (fun o => by
    cases o with
    | notification m => exact Or.inr ⟨rfl, rfl, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    | _ => exact Or.inl rfl))

/-- A step that writes the scheduler alone. -/
theorem of_objects_eq {st st' : SystemState} (hR : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hO : st'.objects = st.objects) (hInv : st.objects.invExt) : FinaliseFrame st st' :=
  ⟨.of_onlyObjectsSchedulerDiffer hR, hO ▸ hInv, fun oid => Or.inl (by rw [hO])⟩

/-- A scheduling context rewritten in its slot, its reply-stack head kept. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).scReply = x.scReply) :
    FinaliseFrame st (st.updateSchedContext scId f) := by
  cases hG : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl ((SystemState.getSchedContext?_eq_some_iff st scId x).mp hG)
        (finaliseWritable_schedContext x) rfl rfl (by simp [schedContextStackHead?, hf x])⟩

/-- The key hook rewrites the scheduler alone. -/
theorem markKeyChangeFrom (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.markKeyChangeFrom pre st tid) :=
  let post := SeLe4n.Kernel.markKeyChangeFrom pre st tid
  of_objects_eq (markKeyChangeFrom_extract_frame
    (fun s : SystemState => ({ s with objects := post.objects, scheduler := post.scheduler } :
      SystemState)) pre st tid (fun _ _ => rfl))
    (markKeyChangeFrom_objects pre st tid) hInv

/-- **The reservation unbind**: the context's binding cleared, its replenishment
purged, the thread's binding cleared, the key hook. -/
theorem cancelBoundDonationOnCore {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    {c : Concurrency.CoreId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.cancelBoundDonationOnCore st t tcb c = .ok st') : FinaliseFrame st st' := by
  unfold SeLe4n.Kernel.cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    injection h with h; subst h
    have h1 := updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      hInv (fun _ => rfl)
    generalize st.updateSchedContext scId _ = st1 at h1 ⊢
    let sch := st1.scheduler.setReplenishQueueOnCore c
      (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore c) scId)
    have h2 := h1.trans (of_objects_eq (st' := { st1 with scheduler := sch }) rfl rfl h1.invExt)
    have h3 := h2.trans (updateTcb _ t
      (fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) h2.invExt)
    exact h3.trans (markKeyChangeFrom _ _ t h3.invExt)
  · cases h

/-- **A deschedule where the state places the thread**: run-queue links and the
scheduler alone. -/
theorem descheduleAt (st : SystemState) (t : SeLe4n.ThreadId) (p : Option Concurrency.CoreId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.descheduleAt st t p) := by
  cases p with
  | none => exact .refl hInv
  | some c =>
    exact ⟨.of_onlyObjectsSchedulerDiffer (removeRunnableOnCore_onlyObjectsSchedulerDiffer st t c),
      removeRunnableOnCore_objects_invExt st t c hInv,
      finaliseWrite.of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)⟩

/-- **A finalised thread's suspend**: the deschedule, then the `.Inactive` mark. -/
theorem suspend (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st ((descheduleAtPlacement st t).updateTcb t finaliseSuspendMark) := by
  have h1 := descheduleAt st t (placedCoreOf? st t) hInv
  exact h1.trans (updateTcb _ t _ h1.invExt)

/-- **A finalised thread's release by every core**: the cores' hold records
alone. -/
theorem releaseCores (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st (finaliseThreadReleaseCores st t) := by
  have hO := finaliseThreadReleaseCores_objects st t
  constructor
  · exact onlyObjectsSchedulerCoreHoldsDiffer.releaseCores st t
  · rw [hO]; exact hInv
  · intro oid; left; rw [hO]

/-- The release step, as the closure asks it. -/
theorem releaseStep (st : SystemState) : FinaliseScReleaseStep (FinaliseFrame st) := by
  intro s s' _ _ _ _ h _ _ _ _ _ hOk
  exact h.trans (cancelBoundDonationOnCore h.invExt hOk)

/-- **The priority-inheritance walk**: boosts and run-queue moves, threads
rewritten keeping their slots. -/
theorem propagatePip (st : SystemState) (s : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    FinaliseFrame st (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 := by
  refine ⟨.of_onlyObjectsSchedulerDiffer (propagatePipChainCrossCore_onlyObjectsSchedulerDiffer fuel st s ec),
    PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st s ec fuel hInv,
    fun oid => ?_⟩
  rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv oid with
    e | ⟨pre, post, hp, hq, hC, hL⟩
  · exact Or.inl e
  · exact Or.inr ⟨.tcb pre, .tcb post, hp, hq, rfl, by simp [KernelObject.tcbSlots, hC, hL], rfl,
      finaliseWritable_tcb pre⟩

/-- The revert of a finalised reply's caller's boost. -/
theorem finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.finaliseReplyRevert st server?) := by
  cases server? with
  | none => exact .refl hInv
  | some s => exact propagatePip st s _ _ hInv

end FinaliseFrame

namespace FinaliseFrameAny

/-- The splice of a reply off its stack: at most three replies rewritten. -/
theorem spliceReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) :
    FinaliseFrameAny st (SeLe4n.Kernel.spliceReplyFrameOutOrSelf st rid) := by
  obtain ⟨m1, m2, h1, h2, h3⟩ := spliceReplyFrameOutOrSelf_store_cases st rid hInv
  have step : ∀ {a b : SystemState}, a.objects.invExt →
      (b = a ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply), a.objects[k.toObjId]? = some (.reply o) ∧
        SeLe4n.Model.storeObject k.toObjId (.reply o') a = .ok ((), b)) →
      FinaliseFrameAny a b := by
    intro a b hA h
    rcases h with rfl | ⟨k, o, o', hO, hS⟩
    · exact .refl hA
    · exact storeObject hA hO (finaliseWritableAny_reply o) hS rfl rfl
  have f1 := step hInv h1
  have f2 := step f1.invExt h2
  exact f1.trans (f2.trans (step f2.invExt h3))

/-- A thread's reply frame spliced off its stack. -/
theorem spliceThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (SeLe4n.Kernel.spliceThreadReplyFrameOut st t) := by
  unfold SeLe4n.Kernel.spliceThreadReplyFrameOut
  cases t.replyObject with
  | none => exact .refl hInv
  | some rid => exact spliceReplyFrameOutOrSelf st rid hInv

/-- The consume of a caller's reply link: the reply consumed, the caller's link
cleared. -/
theorem consumeCallerReply {st st' : SystemState} {c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : SystemState.consumeCallerReply c rid st = .ok ((), st')) :
    FinaliseFrameAny st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    rw [hC] at h
    have f1 : FinaliseFrameAny st st1 := by
      unfold SystemState.consumeReply at hC
      cases hR : st.getReply? rid with
      | none => rw [hR] at hC; cases hC; exact .refl hInv
      | some r =>
        rw [hR] at hC
        exact storeObject hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
          (finaliseWritableAny_reply r) hC rfl rfl
    simp only at h
    cases hT : st1.getTcb? c with
    | none => rw [hT] at h; cases h; exact f1
    | some tcb =>
      rw [hT] at h
      exact f1.trans (storeObject f1.invExt ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
        (Or.inl (finaliseWritable_tcb tcb)) h rfl rfl)

theorem consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    FinaliseFrameAny st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl hInv
  · rename_i rid _
    exact consumeCallerReply hInv (SystemState.consumeCallerReply_eq_link st c rid)

/-- The unlink of a waiter from its server's reply-waiter queue. -/
theorem unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (st.unlinkReplyWaiterOpt w s?) := by
  have e := SystemState.unlinkReplyWaiterOpt_eq_objects st w s?
  exact ⟨by rw [e], by rw [e],
    SystemState.unlinkReplyWaiterOpt_objects_invExt st w s? hInv,
    .of_write (.of_agreeOffRunLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks st w s?))⟩

/-- **A reply-blocked caller's cancel, with nothing to give back**: the splice,
the restore, the consume and the unlink (`cancelIpcBlocking`'s reply arm, its
donation return declining). -/
theorem replyCancel (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) {ep : SeLe4n.ObjId}
    {rt : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hB : t.ipcState = .blockedOnReply ep rt)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st c t = none) :
    FinaliseFrameAny st (Lifecycle.Suspend.cancelIpcBlocking st c t) := by
  rw [cancelIpcBlocking_replyArm_of_noDonation st c t hB hD]
  have f1 := spliceThreadReplyFrameOut st t hInv
  have f2 := f1.trans (show FinaliseFrameAny _ (Lifecycle.Suspend.restoreToReadyCancelled _ c) by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact (FinaliseFrame.updateTcb _ c _ f1.invExt).any)
  have f3 := f2.trans (consumeReplyLink _ c t f2.invExt)
  exact f3.trans (unlinkReplyWaiterOpt _ c _ f3.invExt)

/-- **The unstack**: the head reply's upward link cleared, then the context's
head. -/
theorem unstack {s s1 : SystemState} {x : SeLe4n.ObjId}
    {rid : SeLe4n.ReplyId} {r : Reply} (hInv : s.objects.invExt)
    (hR : s.getReply? rid = some r)
    (hS : SeLe4n.Model.storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1)) :
    FinaliseFrameAny s (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) := by
  have f1 := storeObject hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
    (finaliseWritableAny_reply r) hS rfl rfl
  refine f1.trans ?_
  cases hG : s1.getSchedContext? ⟨x.val⟩ with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact .refl f1.invExt
  | some y =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    have hI := f1.invExt
    exact ⟨rfl, rfl, RHTable_insert_preserves_invExt _ _ _ hI,
      finaliseWriteAny.of_insert (o' := .schedContext { y with scReply := none }) hI
        ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hG)
        (Or.inl (finaliseWritable_schedContext y)) rfl rfl
        (by dsimp only; rw [RHTable_getElem?_eq_get?]
            exact RobinHood.RHTable.getElem?_insert_self s1.objects _ _ hI)
        (fun oid hne => RobinHood.RHTable.getElem?_insert_ne s1.objects _ oid _
          (fun h => hne (eq_of_beq h).symm) hI)⟩

/-- The unstack step, as the closure asks it. -/
theorem unstackStep (st : SystemState) : FinaliseUnstackStep (FinaliseFrameAny st) := by
  intro s s1 x sc rid r h _ _ hR _ hS
  exact h.trans (unstack h.invExt hR hS)

end FinaliseFrameAny

/-- **What a notification waiter's cancel admits**: the waiter is no reserved
thread, is blocked on the notification, is linked into no endpoint queue, and a
cancel may wake it. -/
theorem notificationWaiterCancellable_parts {st : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : notificationWaiterCancellable st n t tcb = true) :
    ¬ t.isReserved ∧ tcb.ipcState = .blockedOnNotification n ∧ tcb.queuePrev = none ∧
      tcb.queueNext = none ∧ cancelledWaiterWakeable st t tcb = true := by
  simp only [notificationWaiterCancellable, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hR, hB⟩, hP⟩, hN⟩, hW⟩ := h
  refine ⟨by simp [hR], hB, ?_, ?_, hW⟩
  · simp [TCB.queuePrev, hP, SeLe4n.ThreadId.ofOptCode]
  · simp [TCB.queueNext, hN, SeLe4n.ThreadId.ofOptCode]

theorem notificationWaiterCancellable_blocked {st : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : notificationWaiterCancellable st n t tcb = true) :
    tcb.ipcState = .blockedOnNotification n :=
  (notificationWaiterCancellable_parts h).2.1

/-- **The finalisation's write frame.** -/
theorem finaliseFinalObject_frame (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (finaliseFinalObject target st) :=
  finaliseFinalObject_closed (FinaliseFrameAny st)
    (fun _ _ _ _ _ _ h _ _ _ _ => h.trans (FinaliseFrame.storeEndpointWaiterCancelled _ _ _ _ _ h.invExt).any)
    (fun _ s _ t tcb h _ _ _ hC =>
      have h1 := FinaliseFrame.notificationCancel s t tcb _ h.invExt
        (notificationWaiterCancellable_blocked hC)
      h.trans (h1.trans (.wakeCancelledWaiter _ _ h1.invExt)).any)
    (fun _ _ _ _ h _ _ _ _ => h.trans (FinaliseFrame.storeUnbindNotification _ _ _ h.invExt).any)
    (fun s t _ h _ _ _ _ => h.trans (FinaliseFrame.descheduleAt s t _ h.invExt).any)
    (fun s s' t tcb sc x h hT hS hA hSc hB hOk =>
      h.trans (FinaliseFrame.releaseStep s s s' t tcb sc x (.refl h.invExt) hT hS hA hSc hB
        hOk).any)
    (fun s n t tcb _ h _ hI _ _ _ =>
      h.trans (FinaliseFrame.notificationCancel s t tcb n h.invExt hI).any)
    (fun s t _ h _ _ _ _ _ => h.trans (FinaliseFrame.suspend s t h.invExt).any)
    (fun s t h => h.trans (FinaliseFrame.releaseCores s t h.invExt).any)
    (FinaliseFrameAny.unstackStep st)
    (fun s x r c t h hX hC _ hG => by
      obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -, -, hD⟩ := replyCallerFinalisable_parts hX hC hG
      have h1 := FinaliseFrameAny.replyCancel s c t h.invExt hB hD
      exact h.trans (h1.trans (FinaliseFrame.finaliseReplyRevert _ _ h1.invExt).any))
    (fun s _ _ tid _ h _ _ e => e ▸ h.trans (FinaliseFrame.updateTcb s tid _ h.invExt).any)
    target st (.refl hInv)

/-- **The finalisation keeps the derivation tree**, on any state. -/
theorem finaliseFinalObject_cdt (target : Nat) (st : SystemState) :
    (finaliseFinalObject target st).cdt = st.cdt := by
  have hU : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB),
      SystemState.onlyObjectsSchedulerDiffer (s.updateTcb t f) s := by
    intro s t f; unfold SystemState.updateTcb; split <;> rfl
  have hM : ∀ (s : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject),
      SystemState.onlyObjectsSchedulerDiffer (s.modifyObject k f) s := fun _ _ _ => rfl
  have hP : ∀ (s : SystemState) (e : SeLe4n.ObjId) (q : Bool) (h : SeLe4n.ThreadId)
      (n : Option SeLe4n.ThreadId),
      SystemState.onlyObjectsSchedulerDiffer (SeLe4n.Kernel.storePopHead s e q h n) s := by
    intro s e q h n
    cases n with
    | none => simp only [SeLe4n.Kernel.storePopHead]; exact (hU _ _ _).trans (hM _ _ _)
    | some m =>
      simp only [SeLe4n.Kernel.storePopHead]
      exact (hU _ _ _).trans ((hU _ _ _).trans (hM _ _ _))
  have hS : ∀ (s : SystemState) (k : SeLe4n.SchedContextId) (f : SchedContext → SchedContext),
      SystemState.onlyObjectsSchedulerDiffer (s.updateSchedContext k f) s := by
    intro s k f; unfold SystemState.updateSchedContext; split <;> rfl
  have hK : ∀ (pre s : SystemState) (t : SeLe4n.ThreadId),
      SystemState.onlyObjectsSchedulerDiffer (markKeyChangeFrom pre s t) s := by
    intro pre s t
    let post := markKeyChangeFrom pre s t
    exact markKeyChangeFrom_extract_frame
      (fun x : SystemState => ({ x with objects := post.objects, scheduler := post.scheduler } :
        SystemState)) pre s t (fun _ _ => rfl)
  have hNc : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (n : SeLe4n.ObjId),
      tcb.ipcState = .blockedOnNotification n →
      SystemState.onlyObjectsSchedulerDiffer (Lifecycle.Suspend.cancelIpcBlocking s t tcb) s := by
    intro s t tcb n hB
    have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [hEq]
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects s t
    have hR : SystemState.onlyObjectsSchedulerDiffer (removeFromNotificationWaitQueue s t) s := by
      rw [e]; rfl
    exact (hU _ _ _).trans hR
  have hC : ∀ {a b : SystemState}, SystemState.onlyObjectsSchedulerDiffer a b → a.cdt = b.cdt := by
    intro a b e; unfold SystemState.onlyObjectsSchedulerDiffer at e; rw [e]
  have hSt : ∀ {a b : SystemState} {k : SeLe4n.ObjId} {o : KernelObject},
      SeLe4n.Model.storeObject k o a = .ok ((), b) → b.cdt = a.cdt :=
    fun e => storeObject_cdt_eq _ _ _ _ e
  refine finaliseFinalObject_closed (fun s => s.cdt = st.cdt)
    (fun _ _ s _ t _ h _ _ _ _ => ?_) (fun _ s _ t tcb h _ _ _ hC' => ?_)
    (fun _ s _ t h _ _ _ _ => ?_)
    (fun s t _ h _ _ _ _ => (hC (descheduleAtPlacement_onlyObjectsSchedulerDiffer s t)).trans h)
    (fun s s' t tcb _ x h _ _ _ _ _ hOk => ?_)
    (fun s n t tcb _ h _ hI _ _ _ => (hC (hNc s t tcb n hI)).trans h)
    (fun s t _ h _ _ _ _ _ => (hC ((hU _ t _).trans
      (descheduleAtPlacement_onlyObjectsSchedulerDiffer s t))).trans h)
    (fun s t h => (onlyObjectsSchedulerCoreHoldsDiffer.releaseCores s t).cdt.trans h)
    (fun s s1 x _ _ _ h _ _ _ _ hSt1 => ?_)
    (fun s x r c t h hX hCc _ hG => ?_) (fun s _ _ tid _ h _ _ e => e ▸ (hC (hU s tid _)).trans h)
    target st rfl
  · unfold storeEndpointWaiterCancelled wakeCancelledWaiter
    exact (hC ((enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans (hP _ _ _ _ _)))).trans h
  · have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [notificationWaiterCancellable_blocked hC']
    unfold wakeCancelledWaiter
    rw [hEq]
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects s t
    have hR : SystemState.onlyObjectsSchedulerDiffer (removeFromNotificationWaitQueue s t) s := by
      rw [e]; rfl
    exact (hC ((enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans hR))).trans h
  · unfold SeLe4n.Kernel.storeUnbindNotification
    exact (hC ((hM _ _ _).trans (hU _ _ _))).trans h
  · unfold cancelBoundDonationOnCore at hOk
    split at hOk
    · rename_i scId _
      injection hOk with hOk; subst hOk
      have h1 := hS s scId
        (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      generalize s.updateSchedContext scId _ = s1 at h1 ⊢
      let c := determineTargetCore s t
      let sch := s1.scheduler.setReplenishQueueOnCore c
        (ReplenishQueue.remove (s1.scheduler.replenishQueueOnCore c) scId)
      have h2 : SystemState.onlyObjectsSchedulerDiffer { s1 with scheduler := sch } s :=
        SystemState.onlyObjectsSchedulerDiffer.trans
          (show SystemState.onlyObjectsSchedulerDiffer { s1 with scheduler := sch } s1 from rfl) h1
      exact (hC ((hK _ _ _).trans ((hU _ _ _).trans h2))).trans h
    · cases hOk
  · exact (hC (hS s1 _ _)).trans ((hSt hSt1).trans h)
  · obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -, -, hD⟩ := replyCallerFinalisable_parts hX hCc hG
    have hRev : ∀ (a : SystemState) (sv : Option SeLe4n.ThreadId),
        (finaliseReplyRevert a sv).cdt = a.cdt := by
      intro a sv; cases sv with
      | none => rfl
      | some v => exact PriorityInheritance.propagatePipChainCrossCore_cdt _ a v _
    rw [hRev, cancelIpcBlocking_replyArm_of_noDonation s c t hB hD]
    have hCons : ∀ (a : SystemState), (Lifecycle.Suspend.consumeReplyLink a c t).cdt = a.cdt := by
      intro a
      unfold Lifecycle.Suspend.consumeReplyLink
      split
      · rfl
      · rename_i rid _
        have hE := SystemState.consumeCallerReply_eq_link a c rid
        unfold SystemState.consumeCallerReply at hE
        cases hR : SystemState.consumeReply rid a with
        | error _ => rw [hR] at hE; cases hE
        | ok p =>
          obtain ⟨⟨⟩, a1⟩ := p
          rw [hR] at hE
          have h1 : a1.cdt = a.cdt := by
            unfold SystemState.consumeReply at hR
            split at hR
            · exact hSt hR
            · cases hR; rfl
          simp only at hE
          split at hE
          · cases hE; exact h1
          · exact (hSt hE).trans h1
    have e := SystemState.unlinkReplyWaiterOpt_eq_objects
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled (spliceThreadReplyFrameOut s t) c) c t)
      c t.blockingServer?
    refine (show _ = _ by rw [e]).trans ((hCons _).trans ?_)
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [hC (hU _ _ _)]
    unfold spliceThreadReplyFrameOut
    split
    · exact h
    · exact (spliceReplyFrameOutOrSelf_cdt_eq _ _).trans h

/-- **The finalisation keeps the teardown's well-formedness and shrinks no
root.** -/
theorem finaliseFinalObject_preserves_teardownWellFormed (target : Nat) (st : SystemState)
    (hW : teardownWellFormed st) :
    teardownWellFormed (finaliseFinalObject target st) ∧
      vspaceRootsShrink st (finaliseFinalObject target st) :=
  (finaliseFinalObject_frame target st hW.1).preserves_teardownWellFormed hW

/-- **The retire after the finalisation keeps the teardown's well-formedness and
only shrinks the roots**: the finalisation's, then the retire's
(`retireFinalObject_preserves_teardownWellFormed`). -/
theorem retireFinalisedObject_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hW : teardownWellFormed st) :
    teardownWellFormed (retireFinalisedObject ec target recorder st) ∧
      vspaceRootsShrink st (retireFinalisedObject ec target recorder st) := by
  obtain ⟨h1, s1⟩ := finaliseFinalObject_preserves_teardownWellFormed target st hW
  obtain ⟨h2, s2⟩ := retireFinalObject_preserves_teardownWellFormed ec target recorder _ h1
  exact ⟨h2, s1.trans s2⟩

end SeLe4n.Kernel
