/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.CancelAll
import SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation
import SeLe4n.Kernel.Architecture.PageTeardownClears
import SeLe4n.Kernel.IPC.Invariant.LoanCoherence

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
    s.getSchedContext? ⟨tcb.scBindingScCode - 1⟩ = some sc → sc.boundThreadCode = t.val + 1 →
    cancelDonationArmOnCore s t tcb = .ok s' → P s'

/-- **The notification cancel a thread's finalisation takes**: a waiter of a
notification, wherever it waits in the queue, leaves it, and is not woken
(`cancelIpcBlocking`). -/
def FinaliseNotificationCancelStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (tcb : TCB) (ntfn : Notification),
    P s → s.getTcb? t = some tcb → tcb.ipcState = .blockedOnNotification n →
    s.getNotification? n = some ntfn → notificationWaiterCancellable s n t tcb = true →
    P (Lifecycle.Suspend.cancelIpcBlocking s t tcb)

/-- **The endpoint cancel a thread's finalisation takes**: a thread blocked on
an endpoint, wherever it waits in the queue, leaves it, and is not woken
(`storeEndpointBlockedCancelled`). -/
def FinaliseEndpointCancelStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint)
    (tcb : TCB), P s → s.getTcb? t = some tcb → s.getEndpoint? e = some ep →
    endpointBlockedCancellable s e q t ep tcb = true →
    P (storeEndpointBlockedCancelled s e q t ep tcb)

/-- **The suspend step a thread's finalisation takes**: a ready thread that is
not suspended, or holds a message, and is no core's idle thread leaves the
scheduler where the state places it (`descheduleAtPlacement`) and is marked
`.Inactive`, its message dropped (`finalisedSuspendMark`). -/
def FinaliseSuspendStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB), P s → s.getTcb? t = some tcb →
    tcb.ipcStateCode = 0 → tcb.ipcObjectCode = 0 →
    (tcb.threadState ≠ .Inactive ∨ tcb.pendingMessage.isSome = true) →
    isIdleThreadId t = false →
    P ((descheduleAtPlacement s t).updateTcb t finalisedSuspendMark)

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
bound to the context — as its own or on loan, in whatever state it waits —
unbound by the reservation arm's in-place unbind with its binding read as the
context's own. -/
def FinaliseScReleaseStep (P : SystemState → Prop) : Prop :=
  ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (sc : SchedContext)
    (x : SeLe4n.ObjId), P s →
    s.getTcb? t = some tcb → tcb.scBindingScCode = x.val + 1 →
    s.getSchedContext? ⟨x.val⟩ = some sc → sc.boundThreadCode = t.val + 1 →
    cancelBoundDonationOnCore s t { tcb with scBindingOwnerCode := 0 }
      = .ok s' → P s'

/-- **The unstack step a scheduling context's finalisation takes**: the head of
the reply stack the context heads loses its upward link, then the context its
head — on the state the holder's deschedule and unbind left (`s₀`, where the
finalisation was admitted and `P` held), so the context is bound to no thread
(`finaliseSchedContextUnbind_unbound`). -/
def FinaliseUnstackStep (P : SystemState → Prop) : Prop :=
  ∀ (s s1 : SystemState) (x : SeLe4n.ObjId) (sc : SchedContext) (rid : SeLe4n.ReplyId)
    (r : Reply), P s →
    s.getSchedContext? ⟨x.val⟩ = some sc → sc.scReply = some rid → s.getReply? rid = some r →
    r.next = some (.head ⟨x.val⟩) →
    storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1) →
    ∀ s₀ : SystemState, P s₀ → schedContextFinaliseAdmitted s₀ x = true →
      s = finaliseSchedContextUnbind (finaliseSchedContextDeschedule s₀ x) x →
    P (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none })

/-- **The cancel step a reply's finalisation takes**: the reply's waiting caller,
admitted by `replyCallerFinalisable`, cancelled with the reservation it lent
handed back (`cancelIpcBlockingReclaimed`, which `finaliseReplyCancel` runs, or
reduces to, on every admitted reply: `finaliseReplyCancel_eq`), and the boost it
lent its server reverted. -/
def FinaliseReplyStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (x : SeLe4n.ObjId) (r : Reply) (c : SeLe4n.ThreadId) (t : TCB), P s →
    s.getObject? x = some (.reply r) → r.callerCode = c.val + 1 → s.getTcb? c = some t →
    replyCallerFinalisable s x r c t = true →
    P (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?)

/-- **The unlink step a stashed reply's finalisation takes**: the receiver
holding the reply stashed, its stash cleared in its slot. -/
def FinaliseUnstashStep (P : SystemState → Prop) : Prop :=
  ∀ (s s1 : SystemState) (x : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (t : TCB), P s →
    s.getTcb? tid = some t → t.pendingReceiveReplyCode = x.val + 1 →
    s1 = s.updateTcb tid TCB.stashCleared → P s1

/-- **The yield steps a thread's and a context's finalisation take** (WS-ZA
ZA6.6): a thread's yield link cancelled (`cancelYieldTo`), and the yield a
context records completed (`completeYieldFrom`). -/
structure FinaliseYieldStep (P : SystemState → Prop) : Prop where
  cancel : ∀ (s : SystemState) (t : SeLe4n.ThreadId), P s → P (cancelYieldTo s t)
  complete : ∀ (s : SystemState) (c : SeLe4n.SchedContextId), P s → P (completeYieldFrom s c)

/-- A held context's completion keeps what the completion keeps. -/
theorem FinaliseYieldStep.completeHeldYield {P : SystemState → Prop} (h : FinaliseYieldStep P)
    (s : SystemState) (held : Nat) (hs : P s) : P (completeHeldYield s held) := by
  unfold SeLe4n.Kernel.completeHeldYield
  split
  · exact hs
  · exact h.complete _ _ hs

/-- A context finalisation's destroy cleanup keeps what the completion keeps. -/
theorem FinaliseYieldStep.schedContextCleanup {P : SystemState → Prop} (h : FinaliseYieldStep P)
    (s : SystemState) (x : SeLe4n.ObjId) (hs : P s) :
    P (finaliseSchedContextCleanupImpl s x) := by
  unfold finaliseSchedContextCleanupImpl
  split
  · split
    · exact h.complete _ _ hs
    · exact hs
  · exact hs

/-- A thread whose owner code is already clear is its own owner-cleared view. -/
theorem TCB.ownerCleared_of_zero {t : TCB} (h : t.scBindingOwnerCode = 0) :
    ({ t with scBindingOwnerCode := 0 } : TCB) = t := by
  cases t; cases h; rfl

/-- **The release step covers the thread finalisation's unbind**: a `.bound`
thread is its own owner-cleared view. -/
theorem FinaliseScReleaseStep.scUnbind {P : SystemState → Prop} (h : FinaliseScReleaseStep P) :
    FinaliseScUnbindStep P := by
  intro s s' t tcb sc hP hT hS hO _ _ hSc hB hOk
  rw [cancelDonationArmOnCore_of_codes s t hS hO] at hOk
  refine h s s' t tcb sc ⟨tcb.scBindingScCode - 1⟩ hP hT (by show _ = _ - 1 + 1; omega)
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
head pop commits (or the reply heads no stack), the caller is no reserved or
idle thread and is held and queued nowhere, is blocked on this reply and linked
into no endpoint queue, and has no timeout budget.  What the cancel hands back
is `replyCallerFinalisable_cases`. -/
theorem replyCallerFinalisable_parts {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (h : replyCallerFinalisable st x r c t = true) :
    replyHeadPopCommits st x r c = true ∧ ¬ c.isReserved ∧ isIdleThreadId c = false ∧
      t.runCoreCode = 0 ∧
      (∃ ep rt, t.ipcState = .blockedOnReply ep rt) ∧ t.replyObject = some ⟨x.val⟩ ∧
      t.queueNext = none ∧ t.queuePrev = none ∧ t.timeoutBudget = none := by
  simp only [replyCallerFinalisable, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hHd, hRes⟩, hId⟩, hRun⟩, hSt⟩, hRO⟩, hQN⟩, hQP⟩, hBud⟩ := h
  have hIpc : ∃ ep rt, t.ipcState = .blockedOnReply ep rt := by
    obtain ⟨k, hk⟩ : ∃ k, t.ipcStateCode = k + 4 := ⟨t.ipcStateCode - 4, by omega⟩
    unfold TCB.ipcState ThreadIpcState.ofCodes
    rw [hk]
    exact ⟨_, _, rfl⟩
  have hRO' : t.replyObject = some ⟨x.val⟩ := by
    unfold TCB.replyObject; rw [hRO]; rfl
  refine ⟨hHd, by simpa using hRes, hId, hRun, hIpc, hRO', ?_, ?_, hBud⟩
  · simp [TCB.queueNext, hQN, SeLe4n.ThreadId.ofOptCode]
  · simp [TCB.queuePrev, hQP, SeLe4n.ThreadId.ofOptCode]

/-- **What a committing head pop reads**: the context `s` the reply heads names
the reply back, is bound to a thread `h` holding it on loan from the caller
(`.donated s c`), and the donation return of `s` from `h` to `c` commits. -/
theorem replyHeadPopCommits_head {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId} (hN : r.next = some (.head s))
    (h : replyHeadPopCommits st x r c = true) :
    ∃ (sc : SchedContext) (hd : SeLe4n.ThreadId) (ht : TCB),
      st.getSchedContext? s = some sc ∧ sc.scReply = some ⟨x.val⟩ ∧ sc.boundThread = some hd ∧
      st.getTcb? hd = some ht ∧ ht.schedContextBinding = .donated s c ∧
      donatedReturnCommits st hd s c = true := by
  unfold replyHeadPopCommits at h
  rw [hN] at h
  simp only at h
  cases hSc : st.getSchedContext? s with
  | none => rw [hSc] at h; cases h
  | some sc =>
    rw [hSc] at h
    simp only at h
    cases hB : sc.boundThreadCode with
    | zero => rw [hB] at h; cases h
    | succ k =>
      rw [hB] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hR, hT⟩, hC⟩ := h
      cases hRp : sc.scReply with
      | none => rw [hRp] at hR; cases hR
      | some rid =>
        rw [hRp] at hR
        cases hTk : st.getTcb? ⟨k⟩ with
        | none => rw [hTk] at hT; cases hT
        | some ht =>
          rw [hTk] at hT
          simp only [Bool.and_eq_true, beq_iff_eq] at hT hR
          obtain ⟨hS, hO⟩ := hT
          refine ⟨sc, ⟨k⟩, ht, rfl, ?_, ?_, hTk, ?_, hC⟩
          · obtain ⟨rv⟩ := rid
            simp only at hR
            subst hR; exact hRp
          · show SeLe4n.ThreadId.ofOptCode sc.boundThreadCode = _
            rw [hB]; rfl
          · unfold TCB.schedContextBinding SchedContextBinding.ofCodes
            rw [hS, hO]

/-- **What a finalised reply's cancel hands back**: nothing, for a reply heading
no stack; for a head reply, the context it heads, from the thread holding it on
loan from the caller, through a return that commits. -/
theorem replyCallerFinalisable_cases {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hX : st.getObject? x = some (.reply r))
    (h : replyCallerFinalisable st x r c t = true) :
    (replyStackLinkIsHead r.next = false ∧
      Lifecycle.Suspend.cancelledCallerDonation? st c t = none) ∨
    ∃ (s : SeLe4n.SchedContextId) (sc : SchedContext) (hd : SeLe4n.ThreadId) (ht : TCB),
      r.next = some (.head s) ∧ st.getSchedContext? s = some sc ∧
      sc.scReply = some ⟨x.val⟩ ∧ sc.boundThread = some hd ∧
      st.getTcb? hd = some ht ∧ ht.schedContextBinding = .donated s c ∧
      donatedReturnCommits st hd s c = true ∧
      Lifecycle.Suspend.cancelledCallerDonation? st c t = some (s, hd) := by
  obtain ⟨hHd, -, -, -, ⟨ep, rt, hB⟩, hRO, -, -, -⟩ := replyCallerFinalisable_parts h
  have hGR : st.getReply? ⟨x.val⟩ = some r := by
    unfold SystemState.getReply?
    rw [show (⟨x.val⟩ : SeLe4n.ReplyId).toObjId = x from rfl, ← SystemState.getObject?_eq_getElem,
      hX]
  have hDon : Lifecycle.Suspend.cancelledCallerDonation? st c t =
      replyFrameHeadHolder? st ⟨x.val⟩ := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hB]
    simp only [hRO]
  cases hN : r.next with
  | none =>
    refine Or.inl ⟨rfl, ?_⟩
    rw [hDon]; apply replyFrameHeadHolder?_of_no_head
    unfold replyFrameHeadContext?; rw [hGR]; simp only [hN]
  | some l =>
    cases l with
    | frame _ =>
      refine Or.inl ⟨rfl, ?_⟩
      rw [hDon]; apply replyFrameHeadHolder?_of_no_head
      unfold replyFrameHeadContext?; rw [hGR]; simp only [hN]
    | head s =>
      obtain ⟨sc, hd, ht, hSc, hRp, hBt, hT, hBind, hC⟩ := replyHeadPopCommits_head hN hHd
      refine Or.inr ⟨s, sc, hd, ht, rfl, hSc, hRp, hBt, hT, hBind, hC, ?_⟩
      rw [hDon]
      unfold replyFrameHeadHolder? replyFrameHeadContext?
      rw [hGR]
      simp only [hN, hSc, hRp, beq_self_eq_true, ↓reduceIte, Option.bind_some, hBt]

/-- **A head reply's admitted pop commits**: the cancelled caller's donation
return is the return of the context the reply heads, from the thread holding it
on loan, at the reply stack's answer, which the admission's
`donatedReturnCommits` has read (`returnDonatedSchedContextResolved_ok_of_commits`). -/
theorem replyHeadPop_commits {st : SystemState} {c : SeLe4n.ThreadId} {t : TCB}
    {s : SeLe4n.SchedContextId} {hd : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hT : st.getTcb? c = some t)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st c t = some (s, hd))
    (hC : donatedReturnCommits st hd s c = true) :
    ∃ (n : Option SeLe4n.ThreadId) (st' : SystemState), replyStackOuterCaller? st s = .ok n ∧
      returnDonatedSchedContext st hd s c n = .ok st' ∧
      Lifecycle.Suspend.returnDonationToCancelledCaller st c t = st' := by
  obtain ⟨st', hOk⟩ := returnDonatedSchedContextResolved_ok_of_commits hInv hC
  obtain ⟨n, hResN, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
  refine ⟨n, st', hResN, hPop, ?_⟩
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  rw [hD, hT]
  simp only [hOk]

/-- **A head reply's pop never refuses for the caller's own binding on a
reachable state**: the pop's `donationRecipientAcceptable` conjunct of
`donatedReturnCommits` asks that the caller the context goes back to holds no
binding, and `donationOwnerValid` makes the owner a `.donated` holder names
`.unbound`.  The conjunct stays in the check, since the shared pop
(`returnDonatedSchedContext`) refuses there on an arbitrary state too, so the
check reads exactly what the pop does before any write; on a state the kernel
reaches it always passes, and the finalise refuses no thread or reply for it. -/
theorem donationRecipientAcceptable_of_donationOwnerValid {st : SystemState}
    {hd c : SeLe4n.ThreadId} {ht : TCB} {s : SeLe4n.SchedContextId}
    (hOV : donationOwnerValid st) (hT : st.getTcb? hd = some ht)
    (hB : ht.schedContextBinding = .donated s c) :
    donationRecipientAcceptable st c = true := by
  obtain ⟨-, ownerTcb, hO, hU, -⟩ :=
    hOV hd ht s c ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hB
  unfold donationRecipientAcceptable
  cases hL : lookupTcb st c with
  | none => rfl
  | some tcb =>
    rw [lookupTcb_some_objects st c tcb hL] at hO
    cases hO
    show (ownerTcb.schedContextBinding == .unbound) = true
    rw [hU]; rfl

/-- **The cancel a finalised reply runs is the reclaim**: a head reply's pop is
`cancelIpcBlockingReclaimed` itself, and a reply heading no stack hands nothing
back, where the reclaim is the bare cancel
(`cancelIpcBlockingReclaimed_of_no_donation`). -/
theorem finaliseReplyCancel_eq {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hX : st.getObject? x = some (.reply r))
    (h : replyCallerFinalisable st x r c t = true) :
    finaliseReplyCancel st r c t = cancelIpcBlockingReclaimed c t st := by
  unfold finaliseReplyCancel
  rcases replyCallerFinalisable_cases hX h with ⟨hHd, hD⟩ | ⟨s, -, -, -, hN, -⟩
  · rw [hHd, cancelIpcBlockingReclaimed_of_no_donation c t st hD]; rfl
  · rw [hN]; rfl

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

/-- **A reply-blocked caller's cancel**: the donation return, then the splice,
the restore, the consume and the unlink. -/
theorem cancelIpcBlocking_replyArm_unfold (st : SystemState) (c : SeLe4n.ThreadId)
    (t : TCB) {ep : SeLe4n.ObjId} {rt : Option SeLe4n.ThreadId}
    (hB : t.ipcState = .blockedOnReply ep rt) :
    Lifecycle.Suspend.cancelIpcBlocking st c t =
      SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled
            (spliceThreadReplyFrameOut (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) t)
            c) c t)
        c t.blockingServer? := by
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]

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

/-- A thread code `t + 1` decodes to `t`. -/
theorem threadOfOptCode_succ (t : SeLe4n.ThreadId) :
    SeLe4n.ThreadId.ofOptCode (t.val + 1) = some t := by
  have := SeLe4n.ThreadId.ofOptCode_optCode (some t)
  exact this

/-- **A property the unstack keeps holds after it.** -/
theorem finaliseSchedContextUnstack_closed (P : SystemState → Prop) (hUn : FinaliseUnstackStep P)
    (x : SeLe4n.ObjId) (s₀ : SystemState) (h₀ : P s₀) (hA : schedContextFinaliseAdmitted s₀ x = true)
    (st : SystemState) (hS₀ : st = finaliseSchedContextUnbind (finaliseSchedContextDeschedule s₀ x) x)
    (h : P st) : P (finaliseSchedContextUnstack st x) := by
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
            exact hUn st s1 x sc rid r h hSc hR hRr (replyStackLinkHeads_spec hH) hS s₀ h₀ hA hS₀
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
          simp only [beq_iff_eq] at hG
          have hS := hG
          split
          · rename_i s' hOk
            refine hRel st s' _ t sc x h hT hS ?_ ?_ hOk
            · have hO : st.objects[x]? = some (.schedContext sc) := by rw [← hX]; simp
              unfold SystemState.getSchedContext?
              rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl, hO]
            · simp only [beq_iff_eq] at hB0
              show _ = _ - 1 + 1; omega
          · exact h
        · exact h
      · exact h
  · exact h

/-- **A property every deschedule keeps holds after
`finaliseSchedContextDeschedule`**, whatever thread it takes off. -/
theorem finaliseSchedContextDeschedule_closed_any (P : SystemState → Prop)
    (hDes : ∀ s t, P s → P (descheduleAtPlacement s t)) (st : SystemState) (x : SeLe4n.ObjId)
    (h : P st) : P (finaliseSchedContextDeschedule st x) := by
  unfold finaliseSchedContextDeschedule
  split
  · split
    · exact h
    · dsimp only
      split
      · split
        · exact hDes _ _ h
        · exact h
      · exact h
  · exact h

/-- **A property the deschedule keeps holds after
`finaliseSchedContextDeschedule`**, on a state whose admission admits the
context: the admission reads the holder as no core's idle thread. -/
theorem finaliseSchedContextDeschedule_closed (P : SystemState → Prop)
    (hDes : FinaliseScDescheduleStep P) (st : SystemState) (x : SeLe4n.ObjId)
    (hA : schedContextFinaliseAdmitted st x = true) (h : P st) :
    P (finaliseSchedContextDeschedule st x) := by
  unfold schedContextFinaliseAdmitted at hA
  unfold finaliseSchedContextDeschedule
  split
  · rename_i sc hO
    rw [hO] at hA
    dsimp only at hA
    split
    · exact h
    · rename_i h0
      rw [if_neg h0] at hA
      dsimp only at hA ⊢
      split
      · rename_i t hT
        rw [hT] at hA
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hA
        split
        · rename_i hG
          simp only [Bool.and_eq_true, beq_iff_eq] at hG
          exact hDes st _ t h hT hG.1 hG.2 hA.2.1.2
        · exact h
      · exact h
  · exact h

/-- The deschedule of a context's holder writes nothing off the run-queue links. -/
theorem finaliseSchedContextDeschedule_objectsAgreeOffRunLinks (st : SystemState)
    (x : SeLe4n.ObjId) :
    (finaliseSchedContextDeschedule st x).objectsAgreeOffRunLinks st :=
  finaliseSchedContextDeschedule_closed_any (fun s => s.objectsAgreeOffRunLinks st)
    (fun s t h => (descheduleAtPlacement_objectsAgreeOffRunLinks s t).trans h) st x
    (.refl st)

/-- **An admitted context is bound to no thread once its holder is unbound**:
the admission names a holder bound back to it, the deschedule keeps the
binding, and the in-place unbind of the holder read
as the context's own (`cancelBoundDonationOnCore` on a `.bound` view) always
runs and clears the context's binding.  So the unstack that follows runs on a
context no thread holds, as its own or on loan, and lent from no one: an
admitted context bound to nothing records no lender, and the unbind clears the
lender with the binding. -/
theorem finaliseSchedContextUnbind_released {st : SystemState} {x : SeLe4n.ObjId}
    (hInv : st.objects.invExt) (hA : schedContextFinaliseAdmitted st x = true)
    {sc : SchedContext}
    (hSc : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).getSchedContext?
      ⟨x.val⟩ = some sc) :
    sc.boundThreadCode = 0 ∧ sc.donationOrigin = none := by
  have hD := finaliseSchedContextDeschedule_objectsAgreeOffRunLinks st x
  have hInv1 : (finaliseSchedContextDeschedule st x).objects.invExt :=
    finaliseSchedContextDeschedule_closed_any (fun s => s.objects.invExt)
      (fun s t h => descheduleAtPlacement_preserves_objects_invExt s t h) st x hInv
  generalize finaliseSchedContextDeschedule st x = s1 at hD hInv1 hSc
  unfold schedContextFinaliseAdmitted at hA
  obtain ⟨sc0, hO, hB⟩ : ∃ sc0, st.objects[x]? = some (.schedContext sc0) ∧
      (if sc0.boundThreadCode == 0 then sc0.donationOrigin.isNone
       else
        match st.getTcb? ⟨sc0.boundThreadCode - 1⟩ with
        | some t =>
          t.scBindingScCode == x.val + 1 && !isIdleThreadId ⟨sc0.boundThreadCode - 1⟩ &&
          ((t.ipcStateCode == 0 && t.ipcObjectCode == 0) ||
            (t.runCoreCode == 0 && !threadCurrentOnSomeCore st ⟨sc0.boundThreadCode - 1⟩))
        | none => false) = true := by
    split at hA
    · rename_i sc0 hO
      simp only [Bool.and_eq_true] at hA
      exact ⟨sc0, by rw [← SystemState.getObject?_eq_getElem]; exact hO, hA.2⟩
    · cases hA
  have hO1 : s1.objects[x]? = some (.schedContext sc0) := hD.get_schedContext_iff.mpr hO
  unfold finaliseSchedContextUnbind at hSc
  rw [SystemState.getObject?_eq_getElem, hO1] at hSc
  dsimp only at hSc
  by_cases hb : sc0.boundThreadCode = 0
  · rw [if_pos (by rw [hb]; rfl)] at hSc
    rw [SystemState.getSchedContext?_eq_some_iff] at hSc
    rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl, hO1] at hSc
    rw [if_pos (by rw [hb]; rfl)] at hB
    cases hSc; exact ⟨hb, Option.isNone_iff_eq_none.mp hB⟩
  rw [if_neg (by simpa using hb)] at hSc
  rw [if_neg (by simpa using hb)] at hB
  try dsimp only at hSc
  generalize hTid : (⟨sc0.boundThreadCode - 1⟩ : SeLe4n.ThreadId) = tid at hB hSc
  cases hT : st.getTcb? tid with
  | none => rw [hT] at hB; cases hB
  | some t =>
  rw [hT] at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨hS, -⟩, -⟩ := hB
  have hT1 := hD.getTcb? tid
  rw [hT] at hT1
  cases hT1' : s1.getTcb? tid with
  | none => rw [hT1'] at hT1; cases hT1
  | some t' =>
  rw [hT1'] at hT1
  simp only [Option.map_some, Option.some.injEq] at hT1
  have hS' : t'.scBindingScCode = x.val + 1 := by
    rw [← hS]; exact TCB.proj_eq_of_withoutRunLinks_eq (·.scBindingScCode) hT1
  rw [hT1'] at hSc
  dsimp only at hSc
  rw [if_pos (show (t'.scBindingScCode == x.val + 1) = true by simp [hS'])] at hSc
  have hBind := schedContextBinding_ownerCleared (t := t') hS'
  rw [cancelBoundDonationOnCore_of_bound _ _ _ _ hBind] at hSc
  dsimp only at hSc
  have hOk := cancelBoundDonationOnCore_of_bound s1 tid { t' with scBindingOwnerCode := 0 }
    _ hBind
  have hObj := cancelBoundDonationOnCore_objects s1 _ tid _ _ hBind hInv1 hOk
  -- The purge writes the context's release fields alone, which neither read
  -- below is about.
  obtain ⟨sc₁, hSc₁, hE⟩ := hObj.getSchedContext?_some' hSc
  rw [SystemState.getSchedContext?_eq_some_iff, show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x
    from rfl] at hSc₁
  have hNe : tid.toObjId ≠ x := by
    intro e
    have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT1'
    rw [e, hO1] at this; cases this
  have hG : s1.getSchedContext? ⟨x.val⟩ = some sc0 := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO1
  rw [SystemState.updateTcb_objects_ne _ _ _ _ hNe
    (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv1),
    SystemState.updateSchedContext_eq_of_some hG] at hSc₁
  dsimp only at hSc₁
  rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
    RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv1] at hSc₁
  cases hSc₁
  exact ⟨SchedContext.proj_eq_of_withoutRelease_eq (·.boundThreadCode) hE,
    SchedContext.proj_eq_of_withoutRelease_eq (·.donationOrigin) hE⟩

/-- **An admitted context is bound to no thread once its holder is unbound**
(`finaliseSchedContextUnbind_released`). -/
theorem finaliseSchedContextUnbind_unbound {st : SystemState} {x : SeLe4n.ObjId}
    (hInv : st.objects.invExt) (hA : schedContextFinaliseAdmitted st x = true)
    {sc : SchedContext}
    (hSc : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).getSchedContext?
      ⟨x.val⟩ = some sc) :
    sc.boundThreadCode = 0 :=
  (finaliseSchedContextUnbind_released hInv hA hSc).1

/-- **A property the deschedule, the release and the unstack keep holds after
the scheduling-context finalisation.** -/
theorem finaliseSchedContext_closed (P : SystemState → Prop) (hDes : FinaliseScDescheduleStep P)
    (hRel : FinaliseScReleaseStep P)
    (hUn : FinaliseUnstackStep P) (hYield : FinaliseYieldStep P) (x : SeLe4n.ObjId)
    (st : SystemState) (h : P st) :
    P (finaliseSchedContext x st) := by
  rw [finaliseSchedContext_eq]
  split
  · rename_i hA
    exact hYield.schedContextCleanup _ x
      (finaliseSchedContextUnstack_closed P hUn x st h hA _ rfl (finaliseSchedContextUnbind_closed P hRel _ x
        (finaliseSchedContextDeschedule_closed P hDes st x hA h)))
  · exact h

/-- **A property the suspend keeps holds after `finaliseThreadSuspend`.** -/
theorem finaliseThreadSuspend_closed (P : SystemState → Prop) (hSuspend : FinaliseSuspendStep P)
    (s : SystemState) (tid : SeLe4n.ThreadId) (h : P s) : P (finaliseThreadSuspend s tid) := by
  unfold finaliseThreadSuspend
  split
  · rename_i t hT
    split
    · rename_i hG
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true'] at hG
      obtain ⟨⟨⟨hS, hO⟩, hI⟩, hId⟩ := hG
      exact hSuspend s tid t h hT hS hO hI hId
    · exact h
  · exact h

/-- **A property the reply cancel keeps holds after a reply-blocked caller's
cancel** (`finaliseReplyCallerCancel`): the reply finalisation's own step, at the
reply the caller waits on. -/
theorem finaliseReplyCallerCancel_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (s : SystemState) (c : SeLe4n.ThreadId) (t : TCB) (h : P s) (hT : s.getTcb? c = some t) :
    P (finaliseReplyCallerCancel s c t) := by
  unfold finaliseReplyCallerCancel
  split
  · rename_i r hX
    split
    · rename_i hG
      simp only [Bool.and_eq_true, beq_iff_eq] at hG
      obtain ⟨⟨hC, hF⟩, -⟩ := hG
      rw [finaliseReplyCancel_eq hX hF]
      exact hRep s _ r c t h hX hC hT hF
    · exact h
  · exact h

/-- **A property the reply cancel and the suspend keep holds after a waiter's
end** (`finaliseReplyWaiter`). -/
theorem finaliseReplyWaiter_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (hSuspend : FinaliseSuspendStep P) (s : SystemState) (w : SeLe4n.ThreadId) (t : TCB)
    (h : P s) (hT : s.getTcb? w = some t) : P (finaliseReplyWaiter s w t) :=
  finaliseThreadSuspend_closed P hSuspend _ w (finaliseReplyCallerCancel_closed P hRep s w t h hT)

/-- ...so after the loan return (`finaliseThreadReturnLoan`). -/
theorem finaliseThreadReturnLoan_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (hSuspend : FinaliseSuspendStep P) (s : SystemState) (x : SeLe4n.ThreadId) (h : P s) :
    P (finaliseThreadReturnLoan s x) := by
  unfold finaliseThreadReturnLoan
  split
  · split
    · exact h
    · split
      · rename_i tl hT
        split
        · exact finaliseReplyWaiter_closed P hRep hSuspend s _ tl h hT
        · exact h
      · exact h
  · exact h

/-- ...and after the walk over a server's waiters (`finaliseReplyWaiters`), by
induction on the fuel. -/
theorem finaliseReplyWaiters_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (hSuspend : FinaliseSuspendStep P) (x : SeLe4n.ThreadId) :
    ∀ (fuel : Nat) (s : SystemState), P s → P (finaliseReplyWaiters x fuel s)
  | 0, s, h => h
  | fuel + 1, s, h => by
    unfold finaliseReplyWaiters
    split
    · split
      · exact h
      · split
        · rename_i t hT
          split
          · exact finaliseReplyWaiters_closed P hRep hSuspend x fuel _
              (finaliseReplyWaiter_closed P hRep hSuspend s _ t h hT)
          · exact h
        · exact h
    · exact h

/-- ...so after `finaliseThreadEndWaiters`. -/
theorem finaliseThreadEndWaiters_closed (P : SystemState → Prop) (hRep : FinaliseReplyStep P)
    (hSuspend : FinaliseSuspendStep P) (s : SystemState) (x : SeLe4n.ThreadId) (h : P s) :
    P (finaliseThreadEndWaiters s x) := by
  unfold finaliseThreadEndWaiters
  split
  · exact finaliseReplyWaiters_closed P hRep hSuspend x _ s h
  · exact h

/-- **The thread finalisation's admission admits its notification unbind**: it
reads `notificationUnbindAdmitted` of the thread it finds. -/
theorem threadFinaliseAdmitted_notificationUnbind {st : SystemState} {x : SeLe4n.ObjId}
    (hA : threadFinaliseAdmitted st x = true) :
    ∃ t, st.getTcb? ⟨x.val⟩ = some t ∧ notificationUnbindAdmitted st ⟨x.val⟩ t = true := by
  unfold threadFinaliseAdmitted at hA
  rw [SystemState.getObject?_eq_getElem] at hA
  split at hA
  rotate_left
  · cases hA
  rename_i t hO
  dsimp only at hA
  simp only [Bool.and_eq_true] at hA
  exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hA.1.2⟩

/-- **An admitted unbind of a bound thread finds its notification.** -/
theorem notificationUnbindAdmitted_notification {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hG : notificationUnbindAdmitted st tid t = true) (h0 : t.boundNotificationCode ≠ 0) :
    ∃ n, st.getNotification? ⟨t.boundNotificationCode - 1⟩ = some n := by
  unfold notificationUnbindAdmitted at hG
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at hG
  revert hG
  cases st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
  | none => intro hG; cases hG.1
  | some n => intro _; exact ⟨n, rfl⟩

/-- **A property the notification unbind keeps holds after
`finaliseThreadUnbindNotification`**, on a state whose admission admits the
unbind (`notificationUnbindAdmitted`). -/
theorem finaliseThreadUnbindNotification_closed (P : SystemState → Prop)
    (hUnbind : FinaliseUnbindStep P) (st : SystemState) (tid : SeLe4n.ThreadId) {t : TCB}
    (hT : st.getTcb? tid = some t) (hG : notificationUnbindAdmitted st tid t = true)
    (h : P st) :
    P (finaliseThreadUnbindNotification st tid) := by
  have hc : boundNotificationCodeOf st tid = t.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hT]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact h
  · rename_i h0
    unfold notificationUnbindAdmitted at hG
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hG h0
    rcases hG with hz | ⟨hB, hIn⟩
    · exact absurd hz h0
    · revert hB
      cases hN : st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
      | none => intro hB; cases hB
      | some n =>
        intro hB
        simp only [beq_iff_eq] at hB
        refine hUnbind _ st n tid h hN ?_ ?_ hIn
        · unfold Notification.boundTCB; rw [hB]; exact threadOfOptCode_succ tid
        · rw [hc]; simp only [SeLe4n.ObjId.val]; omega

/-- **A property the notification and endpoint cancels and the reply cancel keep
holds after `finaliseThreadCancel`.** -/
theorem finaliseThreadCancel_closed (P : SystemState → Prop)
    (hCancel : FinaliseNotificationCancelStep P) (hEndpoint : FinaliseEndpointCancelStep P)
    (hRep : FinaliseReplyStep P) (s : SystemState) (tid : SeLe4n.ThreadId) (h1 : P s) :
    P (finaliseThreadCancel s tid) := by
  unfold finaliseThreadCancel
  split
  · rename_i t hT
    have hEp : ∀ e q, P (cancelEndpointBlocked s e q tid t) := by
      intro e q
      unfold cancelEndpointBlocked
      split
      · rename_i ep hE
        split
        · rename_i hG
          exact hEndpoint s e q tid ep t h1 hT hE hG
        · exact h1
      · exact h1
    split
    · rename_i n hI
      split
      · rename_i ntfn hN
        split
        · rename_i hG
          exact hCancel s n tid t ntfn h1 hT hI hN hG
        · exact h1
      · exact h1
    all_goals first
      | exact hEp _ _
      | exact finaliseReplyCallerCancel_closed P hRep s tid t h1 hT
      | exact h1
  · exact h1

/-- **A property the reservation unbind keeps holds after
`finaliseThreadUnbindSchedContext`.** -/
theorem finaliseThreadUnbindSchedContext_closed (P : SystemState → Prop)
    (hSc : FinaliseScUnbindStep P) (s : SystemState) (tid : SeLe4n.ThreadId) (h4 : P s) :
    P (finaliseThreadUnbindSchedContext s tid) := by
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
        obtain ⟨⟨⟨⟨hS, hO⟩, hR⟩, hH⟩, hM'⟩ := hG
        split
        · rename_i s' hOk
          exact hSc s s' tid t sc h4 hT hS hO hR hH hM hM' hOk
        · exact h4
      · exact h4
  · exact h4

/-- **A property the thread finalisation's steps keep holds after it.** -/
theorem finaliseThread_closed (P : SystemState → Prop) (hUnbind : FinaliseUnbindStep P)
    (hSc : FinaliseScUnbindStep P) (hCancel : FinaliseNotificationCancelStep P)
    (hEndpoint : FinaliseEndpointCancelStep P)
    (hSuspend : FinaliseSuspendStep P) (hRelease : FinaliseReleaseStep P)
    (hRep : FinaliseReplyStep P) (hYield : FinaliseYieldStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) :
    P (finaliseThread x st) := by
  unfold finaliseThread; dsimp only
  split
  · rename_i hA
    obtain ⟨t, hT, hG⟩ := threadFinaliseAdmitted_notificationUnbind hA
    refine hYield.completeHeldYield _ _ ?_
    exact finaliseThreadUnbindSchedContext_closed P hSc _ _ (hRelease _ _ (hYield.cancel _ _
      (finaliseThreadSuspend_closed P hSuspend _ _
        (finaliseThreadEndWaiters_closed P hRep hSuspend _ _
          (finaliseThreadReturnLoan_closed P hRep hSuspend _ _
            (finaliseThreadCancel_closed P hCancel hEndpoint hRep _ _
              (finaliseThreadUnbindNotification_closed P hUnbind _ _ hT hG h)))))))
  · exact h

/-- **A property the stash clear keeps holds after `finaliseReplyUnstash`.** -/
theorem finaliseReplyUnstash_closed (P : SystemState → Prop) (hSt : FinaliseUnstashStep P)
    (x : SeLe4n.ObjId) (r : Reply) (st : SystemState) (h : P st) :
    P (finaliseReplyUnstash st x r) := by
  unfold finaliseReplyUnstash
  split
  · exact h
  · split
    · rename_i t hT
      split
      · rename_i hC
        exact hSt st _ x _ t h hT (by simpa using hC) rfl
      · exact h
    · exact h

/-- **The delete's unstash clears the thread the retired scan would find.**  On
a state whose stashes are all recorded (`pendingReceiveReplyWellFormed`'s third
clause), a thread that stashes the reply at `rid` is the one the Reply records,
so the `O(1)` unstash (`finaliseReplyUnstash`, one field read and the named
thread's stash re-checked) clears exactly that thread's stash, the one a scan
of every thread for this stash would find (and the only one, by the second
clause). -/
theorem finaliseReplyUnstash_eq_of_stasher {st : SystemState}
    (h : pendingReceiveReplyWellFormed st) {rid : SeLe4n.ReplyId} {r : Reply}
    (hR : st.getReply? rid = some r) {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hT : st.getTcb? tid = some tcb) (hP : tcb.pendingReceiveReply = some rid) :
    finaliseReplyUnstash st rid.toObjId r = st.updateTcb tid TCB.stashCleared := by
  obtain ⟨r', hR', hS⟩ := h.2.2 tid tcb rid hT hP
  rw [hR] at hR'; cases hR'
  have hCode : tcb.pendingReceiveReplyCode = rid.val + 1 := by
    have e := congrArg SeLe4n.ReplyId.optCode hP
    simp only [TCB.pendingReceiveReply, SeLe4n.ReplyId.optCode_ofOptCode] at e
    exact e
  unfold finaliseReplyUnstash
  rw [hS]
  dsimp only
  rw [show (⟨tid.val⟩ : SeLe4n.ThreadId) = tid from rfl, hT]
  dsimp only
  rw [if_pos (by rw [hCode]; exact beq_self_eq_true _)]

/-- **…and leaves the state when no thread stashes the reply**, as the scan
finding no stasher would. -/
theorem finaliseReplyUnstash_eq_self_of_no_stasher {st : SystemState}
    {rid : SeLe4n.ReplyId} {r : Reply}
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
      tcb.pendingReceiveReply ≠ some rid) :
    finaliseReplyUnstash st rid.toObjId r = st := by
  unfold finaliseReplyUnstash
  split
  · rfl
  · rename_i k _
    split
    · rename_i t hT
      split
      · rename_i hC
        exfalso
        apply hNone ⟨k⟩ t hT
        have e : t.pendingReceiveReplyCode = rid.val + 1 := by
          have := beq_iff_eq.mp hC
          rw [this]; rfl
        simp only [TCB.pendingReceiveReply, e]
        rfl
      · rfl
    · rfl

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
    · exact finaliseReplyUnstash_closed P hSt x r st h
    · rename_i h0
      dsimp only
      split
      · rename_i t hT
        split
        · rename_i hG
          rw [finaliseReplyCancel_eq hX hG]
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
    (hCancel : FinaliseNotificationCancelStep P) (hEndpoint : FinaliseEndpointCancelStep P)
    (hSuspend : FinaliseSuspendStep P)
    (hRelease : FinaliseReleaseStep P) (hUn : FinaliseUnstackStep P) (hRep : FinaliseReplyStep P)
    (hSt : FinaliseUnstashStep P) (hYield : FinaliseYieldStep P)
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
    · exact finaliseThread_closed P hUnbind hRel.scUnbind hCancel hEndpoint hSuspend hRelease hRep
        hYield _ st h
    · exact finaliseSchedContext_closed P hDes hRel hUn hYield _ st h
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
theorem kind {st st' : SystemState} (h : finaliseWrite st st') :
    kindPreservingWriteUpToBindings st st' := by
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

/-- **…and a lent-context write**: no reply is written, and a thread's reply
link and loan are no notification link. -/
theorem loanWrite.of_ntfnUnlinkReach {st st' : SystemState} (h : ntfnUnlinkReach st st') :
    loanWrite st st' := by
  intro oid
  rcases h.2 oid with e | ⟨n, n', hn, hn', -⟩ | ⟨t, t', ht, ht', ⟨np, nn, rfl⟩⟩
  · exact Or.inl e
  · exact Or.inr ⟨.notification n, .notification n', hn, hn',
      objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e)⟩
  · exact Or.inr ⟨.tcb t, .tcb _, ht, ht', objectLoanKept_tcb ⟨rfl, fun _ _ h => h⟩⟩

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
and the cores' hold records changed, the object table well formed, a
finalisation write, and a write that keeps every thread's reply link and loan
(or gives the loan up) and every reply-stack head (`loanWrite`). -/
structure FinaliseFrame (st st' : SystemState) : Prop where
  rest : onlyObjectsSchedulerCoreHoldsDiffer st' st
  invExt : st'.objects.invExt
  write : finaliseWrite st st'
  loan : loanWrite st st'

namespace FinaliseFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : FinaliseFrame st st :=
  ⟨.refl st, hInv, .refl st, .refl st⟩

theorem trans {a b c : SystemState} (h₁ : FinaliseFrame a b) (h₂ : FinaliseFrame b c) :
    FinaliseFrame a c :=
  ⟨h₂.rest.trans h₁.rest, h₂.invExt, h₁.write.trans h₂.write, h₁.loan.trans h₂.loan⟩

theorem kind {st st' : SystemState} (h : FinaliseFrame st st') :
    kindPreservingWriteUpToBindings st st' :=
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

theorem kind {st st' : SystemState} (h : finaliseWriteAny st st') :
    kindPreservingWriteUpToBindings st st' := by
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

/-- WS-ZA ZA6.3: a write of the contexts' release-queue fields alone is a
finalisation write — a context stays a context with its reply-stack head. -/
theorem finaliseWrite.of_agreeOffReleaseLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffReleaseLinks st) : finaliseWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨sc, sc', hp, hq, hE⟩
  · exact Or.inl e
  · exact Or.inr ⟨.schedContext sc, .schedContext sc', hp, hq, rfl, rfl,
      congrArg some (SchedContext.proj_eq_of_withoutRelease_eq (·.scReply) hE),
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- ...and lends no context and lets go of no reply link. -/
theorem loanWrite.of_agreeOffReleaseLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffReleaseLinks st) : loanWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨sc, sc', hp, hq, -⟩
  · exact Or.inl e
  · refine Or.inr ⟨.schedContext sc, .schedContext sc', hp, hq, ?_, ?_⟩
    · intro _ hx; cases hx
    · intro _ _ hr; cases hr

/-- WS-ZA ZA6.3: a release-queue edit (`SystemState.releaseOnlyWrite`, the
objects agreeing off the release fields) is a finalisation step. -/
theorem FinaliseFrame.of_releaseOnlyWrite {st st' : SystemState}
    (hW : st'.releaseOnlyWrite st) (hA : st'.objectsAgreeOffReleaseLinks st)
    (hI : st'.objects.invExt) : FinaliseFrame st st' :=
  ⟨.of_onlyObjectsSchedulerDiffer hW.1, hI, .of_agreeOffReleaseLinks hA,
    .of_agreeOffReleaseLinks hA⟩

namespace FinaliseFrameAny

theorem refl {st : SystemState} (hInv : st.objects.invExt) : FinaliseFrameAny st st :=
  ⟨rfl, rfl, hInv, .refl st⟩

theorem trans {a b c : SystemState} (h₁ : FinaliseFrameAny a b) (h₂ : FinaliseFrameAny b c) :
    FinaliseFrameAny a c :=
  ⟨h₂.cdt.trans h₁.cdt, h₂.asidTable.trans h₁.asidTable, h₂.invExt, h₁.write.trans h₂.write⟩

theorem kind {st st' : SystemState} (h : FinaliseFrameAny st st') : kindPreservingWriteUpToBindings st st' :=
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
      intro _; exact ⟨rfl, rfl⟩)
    (hL : ∀ x, TCB.loanKept (f x) x := by intro _; exact ⟨rfl, fun _ _ h => h⟩) :
    FinaliseFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl hPre
        (finaliseWritable_tcb x) rfl (by simp only [KernelObject.tcbSlots, (hf x).1, (hf x).2]),
      loanWrite.of_insert hInv rfl hPre (objectLoanKept_tcb (hL x))⟩

/-- An object rewritten in its slot by an update that keeps every object, or
keeps a writable one's kind and slots. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt)
    (hf : ∀ o, f o = o ∨ ((f o).objectType = o.objectType ∧ (f o).tcbSlots = o.tcbSlots ∧
      schedContextStackHead? (some (f o)) = schedContextStackHead? (some o) ∧
      finaliseWritable o ∧ o.objectType ≠ .tcb)) :
    FinaliseFrame st (st.modifyObject k f) := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    rw [e]; exact .refl hInv
  | some o =>
    rw [RobinHood.RHTable.modify_of_get? hG]
    rcases hf o with e | ⟨hT, hS, hH, hW, hNT⟩
    · rw [e]
      have hK : ∀ oid : SeLe4n.ObjId, (st.objects.insert k o)[oid]? = st.objects[oid]? := by
        intro oid
        by_cases h : oid = k
        · subst h; exact (RobinHood.RHTable.getElem?_insert_self st.objects oid o hInv).trans hG.symm
        · exact RobinHood.RHTable.getElem?_insert_ne st.objects k oid o
            (by intro h'; exact h (eq_of_beq h').symm) hInv
      exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv, fun oid => Or.inl (hK oid),
        fun oid => Or.inl (hK oid)⟩
    · refine ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
        finaliseWrite.of_insert hInv rfl hG hW hT hS hH, loanWrite.of_insert hInv rfl hG ?_⟩
      refine objectLoanKept_of_inert (fun t e => hNT ?_) (fun r e => ?_)
      · rw [← hT, e]; rfl
      · subst e; rcases hW with h | h | h | h <;> cases h

/-- The wake: a run-queue insert and the `.ready` mark, on threads only. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  refine ⟨.of_onlyObjectsSchedulerDiffer (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c t),
    enqueueRunnableOnCore_preserves_objects_invExt st c t hInv, ?_, ?_⟩ <;>
  cases hT : st.getTcb? t with
  | none =>
    simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    first | exact .refl _ | exact loanWrite.refl _
  | some tcb =>
    cases hD : wakeDeclines st c t with
    | true =>
      simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD,
        if_true]
      first | exact .refl _ | exact loanWrite.refl _
    | false =>
      first
      | exact (finaliseWrite.of_insert
          (st' := { st with objects := st.objects.insert t.toObjId (.tcb (tcb.setIpcState .ready)) })
          hInv rfl ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT) (finaliseWritable_tcb tcb)
          rfl rfl).trans
          (finaliseWrite.of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD))
      | exact (loanWrite.of_insert
          (st' := { st with objects := st.objects.insert t.toObjId (.tcb (tcb.setIpcState .ready)) })
          hInv rfl ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT)
          (objectLoanKept_tcb ⟨rfl, fun _ _ h => h⟩)).trans
          (loanWrite.of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD))

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
        split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
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

/-- The removal of a waiter from anywhere in an endpoint queue, each write in
its slot: the endpoint's ends, the neighbours' links and the waiter's. -/
theorem storeQueueRemove (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeQueueRemove st endpointId isReceiveQ tid ep tcb) := by
  have hHead : ∀ (s : SystemState) (c : Nat), s.objects.invExt →
      FinaliseFrame s (s.modifyObject endpointId (headAdvancedEndpoint isReceiveQ c)) :=
    fun s c hI => modifyObject s endpointId _ hI (fun o => by
      cases o with
      | endpoint e =>
        right; simp only [headAdvancedEndpoint]
        split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
      | _ => exact Or.inl rfl)
  have hEnds : ∀ (s : SystemState) (h t : Nat), s.objects.invExt →
      FinaliseFrame s (s.modifyObject endpointId (endsSetEndpoint isReceiveQ h t)) :=
    fun s h t hI => modifyObject s endpointId _ hI (fun o => by
      cases o with
      | endpoint e =>
        right; simp only [endsSetEndpoint]
        split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
      | _ => exact Or.inl rfl)
  have h1 : FinaliseFrame st (match tcb.queuePPrev with
      | some .endpointHead =>
        st.modifyObject endpointId (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) := by
    split
    · exact hHead st _ hInv
    · exact updateTcb st _ _ hInv
    · exact .refl hInv
  have hFin : ∀ (s2 : SystemState) (h t : Nat), FinaliseFrame st s2 →
      FinaliseFrame st ((s2.modifyObject endpointId (endsSetEndpoint isReceiveQ h t)).updateTcb
        tid tcbOffQueue) := fun s2 h t h2 =>
    have h3 := h2.trans (hEnds s2 h t h2.invExt)
    h3.trans (updateTcb _ tid tcbOffQueue h3.invExt)
  have hNext : ∀ (s1 : SystemState), FinaliseFrame st s1 →
      FinaliseFrame st (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1) := by
    intro s1 h1
    split
    · exact h1.trans (updateTcb s1 _ _ h1.invExt)
    · exact h1
  unfold SeLe4n.Kernel.storeQueueRemove
  exact hFin _ _ _ (hNext _ h1)

/-- A thread's endpoint cancel: the removal, then its IPC ended. -/
theorem storeEndpointBlockedCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hInv : st.objects.invExt) :
    FinaliseFrame st
      (SeLe4n.Kernel.storeEndpointBlockedCancelled st endpointId isReceiveQ tid ep tcb) := by
  unfold SeLe4n.Kernel.storeEndpointBlockedCancelled
  have h1 := storeQueueRemove st endpointId isReceiveQ tid ep tcb hInv
  exact h1.trans (updateTcb _ tid cancelledEndpointWaiterTcb h1.invExt)

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
    exact ⟨by rw [e]; rfl, hR.1, finaliseWrite.of_ntfnUnlinkReach hR, loanWrite.of_ntfnUnlinkReach hR⟩
  exact h1.trans (updateTcb _ _ _ h1.invExt)

/-- The unbind, each side in its slot. -/
theorem storeUnbindNotification (st : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeUnbindNotification st t n) := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  have h1 := updateTcb st t (fun x => { x with boundNotificationCode := 0 }) hInv
  exact h1.trans (modifyObject _ n _ h1.invExt (fun o => by
    cases o with
    | notification m => exact Or.inr ⟨rfl, rfl, rfl, Or.inr (Or.inr (Or.inl rfl)), by simp [KernelObject.objectType]⟩
    | _ => exact Or.inl rfl))

/-- A step that writes the scheduler alone. -/
theorem of_objects_eq {st st' : SystemState} (hR : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hO : st'.objects = st.objects) (hInv : st.objects.invExt) : FinaliseFrame st st' :=
  ⟨.of_onlyObjectsSchedulerDiffer hR, hO ▸ hInv, fun oid => Or.inl (by rw [hO]),
    loanWrite.of_objects_eq hO⟩

/-- A scheduling context rewritten in its slot, its reply-stack head kept. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).scReply = x.scReply) :
    FinaliseFrame st (st.updateSchedContext scId f) := by
  cases hG : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    have hPre := (SystemState.getSchedContext?_eq_some_iff st scId x).mp hG
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl hPre
        (finaliseWritable_schedContext x) rfl rfl (by simp [schedContextStackHead?, hf x]),
      loanWrite.of_insert hInv rfl hPre
        (objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e))⟩

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
    (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.cancelBoundDonationOnCore st t tcb = .ok st') : FinaliseFrame st st' := by
  unfold SeLe4n.Kernel.cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    injection h with h; subst h
    have h1 := updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      hInv (fun _ => rfl)
    generalize st.updateSchedContext scId _ = st1 at h1 ⊢
    have h2 := h1.trans (FinaliseFrame.of_releaseOnlyWrite
      (SchedContextOps.purgeReplenishment_releaseOnlyWrite st1 scId)
      (SchedContextOps.purgeReplenishment_agree st1 scId)
      (SchedContextOps.purgeReplenishment_objects_invExt st1 scId h1.invExt))
    have h3 := h2.trans (updateTcb _ t
      (fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) h2.invExt
      (hL := fun _ => TCB.loanKept_of_bindingCleared rfl rfl))
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
      finaliseWrite.of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c),
      loanWrite.of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)⟩

/-- **A finalised thread's suspend**: the deschedule, then the `.Inactive` mark,
the thread's message dropped. -/
theorem suspend (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st ((descheduleAtPlacement st t).updateTcb t finalisedSuspendMark) := by
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
  · exact loanWrite.of_objects_eq hO

/-- The release step, as the closure asks it. -/
theorem releaseStep (st : SystemState) : FinaliseScReleaseStep (FinaliseFrame st) := by
  intro s s' _ _ _ _ h _ _ _ _ hOk
  exact h.trans (cancelBoundDonationOnCore h.invExt hOk)

/-- **The priority-inheritance walk**: boosts and run-queue moves, threads
rewritten keeping their slots. -/
theorem propagatePip (st : SystemState) (s : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    FinaliseFrame st (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 := by
  refine ⟨.of_onlyObjectsSchedulerDiffer (propagatePipChainCrossCore_onlyObjectsSchedulerDiffer fuel st s ec),
    PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st s ec fuel hInv,
    fun oid => ?_, fun oid => ?_⟩
  · rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv oid with
      e | ⟨pre, post, hp, hq, hC, hL, -⟩
    · exact Or.inl e
    · exact Or.inr ⟨.tcb pre, .tcb post, hp, hq, rfl, by simp [KernelObject.tcbSlots, hC, hL], rfl,
        finaliseWritable_tcb pre⟩
  · -- The walk rewrites threads only, their pip boost and run links: reply
    -- links and loans are kept.
    rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv oid with
      e | ⟨pre, post, hp, hq, -, -, -⟩
    · exact Or.inl e
    · obtain ⟨ty, p, hy, hE⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st s ec
        fuel hInv ⟨oid.val⟩ post hq
      rw [show (⟨oid.val⟩ : SeLe4n.ThreadId).toObjId = oid from rfl, hp] at hy
      cases hy
      refine Or.inr ⟨.tcb pre, .tcb post, hp, hq, objectLoanKept_tcb ⟨?_, fun s o hb => ?_⟩⟩
      · exact TCB.proj_eq_of_withoutRunLinks_eq (·.replyObjectCode) hE
      · rw [← TCB.proj_eq_of_withoutRunLinks_eq (·.schedContextBinding) hE]; exact hb

/-- The revert of a finalised reply's caller's boost. -/
theorem finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.finaliseReplyRevert st server?) := by
  cases server? with
  | none => exact .refl hInv
  | some s => exact propagatePip st s _ _ hInv

/-- A thread's yield link cancelled: its context's end then its own cleared. -/
theorem cancelYieldTo (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.cancelYieldTo st t) := by
  unfold SeLe4n.Kernel.cancelYieldTo
  split
  · split
    · exact .refl hInv
    · rename_i k _
      have h1 := updateSchedContext st ⟨k⟩ SeLe4n.Kernel.SchedContext.yieldCleared hInv (fun _ => rfl)
      exact h1.trans (updateTcb _ t _ h1.invExt)
  · exact .refl hInv

/-- A context's consumed time handed to a thread's registers. -/
theorem setConsumed (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.setConsumed st s t) := by
  unfold SeLe4n.Kernel.setConsumed
  split
  · have h1 := updateSchedContext st s SchedContext.updateConsumed hInv (fun _ => rfl)
    exact h1.trans (updateTcb _ t _ h1.invExt)
  · exact .refl hInv

/-- A context's yield link cancelled: its own end then its yielder's cleared. -/
theorem cancelYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.cancelYieldFrom st s) := by
  unfold SeLe4n.Kernel.cancelYieldFrom
  split
  · split
    · exact .refl hInv
    · rename_i k _
      have h1 := updateSchedContext st s SeLe4n.Kernel.SchedContext.yieldCleared hInv (fun _ => rfl)
      exact h1.trans (updateTcb _ ⟨k⟩ _ h1.invExt)
  · exact .refl hInv

/-- The completion of the yield a context records. -/
theorem completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.completeYieldFrom st s) := by
  unfold SeLe4n.Kernel.completeYieldFrom
  split
  · split
    · exact .refl hInv
    · rename_i k _
      have h1 := setConsumed st s ⟨k⟩ hInv
      exact h1.trans (cancelYieldFrom _ s h1.invExt)
  · exact .refl hInv
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

/-- **The pop's two reply stores**: the head's links cleared, then the frame
below re-headed. -/
theorem storeDonationHeadPop {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.storeDonationHeadPop scId head? st = .ok st') : FinaliseFrameAny st st' := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact .refl hInv
  · have f1 : FinaliseFrameAny st s1 := by
      rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid0, r0, _, hRead, hS0⟩
      · exact .refl hInv
      · exact storeObject hInv hRead (finaliseWritableAny_reply r0) hS0 rfl rfl
    refine f1.trans ?_
    rcases storeReplyReHead_cases hReHead with rfl | ⟨b, rb, _, hReadB, hS2⟩
    · exact .refl f1.invExt
    · exact storeObject f1.invExt hReadB (finaliseWritableAny_reply rb) hS2 rfl rfl

/-- **The donation return**: the context's store, the pop's two reply stores,
then the recipient's and the holder's binding rewrites. -/
theorem returnDonatedSchedContext {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    FinaliseFrameAny st st' := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4, hSc, -, -, -, hS1, hClear, hL1, hS3,
    hL2, hS4, hEq⟩ := returnDonatedSchedContext_ok_storeChain _ _ serverTid scId originalOwner
      newOwner? h
  have f1 := storeObject hInv hSc (Or.inl (finaliseWritable_schedContext sc)) hS1 rfl rfl
  have f2 := f1.trans (storeDonationHeadPop f1.invExt hClear)
  have f3 := f2.trans (storeObject f2.invExt (lookupTcb_some_objects _ _ _ hL1)
    (Or.inl (finaliseWritable_tcb _)) hS3 rfl rfl)
  have f4 := f3.trans (storeObject f3.invExt (lookupTcb_some_objects _ _ _ hL2)
    (Or.inl (finaliseWritable_tcb _)) hS4 rfl rfl)
  have eO : st'.objects = s4.objects := by rw [hEq]
  have eC : st'.cdt = s4.cdt := by rw [hEq]
  have eA : st'.asidTable = s4.asidTable := by rw [hEq]
  exact ⟨eC.trans f4.cdt, eA.trans f4.asidTable, eO ▸ f4.invExt,
    fun k => by rw [eO]; exact f4.write k⟩

/-- **A cancelled caller's donation return**: the pop, or nothing when it
declines. -/
theorem returnDonationToCancelledCaller (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    FinaliseFrameAny st (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact returnDonatedSchedContext hInv hPop
    · exact .refl hInv
  · exact .refl hInv

/-- **A reply-blocked caller's cancel**: the donation return, the splice, the
restore, the consume and the unlink (`cancelIpcBlocking`'s reply arm). -/
theorem replyCancel (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) {ep : SeLe4n.ObjId}
    {rt : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hB : t.ipcState = .blockedOnReply ep rt) :
    FinaliseFrameAny st (Lifecycle.Suspend.cancelIpcBlocking st c t) := by
  rw [cancelIpcBlocking_replyArm_unfold st c t hB]
  have f0 := returnDonationToCancelledCaller st c t hInv
  have f1 := f0.trans (spliceThreadReplyFrameOut _ t f0.invExt)
  have f2 := f1.trans (show FinaliseFrameAny _ (Lifecycle.Suspend.restoreToReadyCancelled _ c) by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact (FinaliseFrame.updateTcb _ c _ f1.invExt).any)
  have f3 := f2.trans (consumeReplyLink _ c t f2.invExt)
  exact f3.trans (unlinkReplyWaiterOpt _ c _ f3.invExt)

/-- **The migration of a returned context's replenishments** writes only the
release queues and the contexts' release fields. -/
theorem cancelIpcBlockingMigrated (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : (Lifecycle.Suspend.cancelIpcBlocking st c t).objects.invExt) :
    FinaliseFrameAny (Lifecycle.Suspend.cancelIpcBlocking st c t)
      (SeLe4n.Kernel.cancelIpcBlockingMigrated c t st) := by
  unfold SeLe4n.Kernel.cancelIpcBlockingMigrated
  split
  · exact (FinaliseFrame.of_releaseOnlyWrite
      (migrateSchedContextReplenishment_releaseOnlyWrite _ _ _ _)
      (migrateSchedContextReplenishment_agree _ _ _ _)
      (migrateSchedContextReplenishment_preserves_objects_invExt _ _ _ _ hInv)).any
  · exact .refl hInv

/-- **A reply-blocked caller's cancel with its reservation handed back**: the
cancel, the replenishment migration, and the holder taken off its core. -/
theorem cancelIpcBlockingReclaimed (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    {ep : SeLe4n.ObjId} {rt : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hB : t.ipcState = .blockedOnReply ep rt) :
    FinaliseFrameAny st (SeLe4n.Kernel.cancelIpcBlockingReclaimed c t st) := by
  have f1 := replyCancel st c t hInv hB
  have f2 := f1.trans (cancelIpcBlockingMigrated st c t f1.invExt)
  unfold SeLe4n.Kernel.cancelIpcBlockingReclaimed descheduleUnboundHolder
  split
  · exact f2
  · exact f2.trans (FinaliseFrame.descheduleAt _ _ _ f2.invExt).any

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
  intro s s1 x sc rid r h _ _ hR _ hS _ _ _ _
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

namespace FinaliseFrameAny

/-- The notification unbind, as the closure asks it. -/
theorem unbindStep (st : SystemState) : FinaliseUnbindStep (FinaliseFrameAny st) :=
  fun _ _ _ _ h _ _ _ _ => h.trans (FinaliseFrame.storeUnbindNotification _ _ _ h.invExt).any

/-- A context's deschedule of its holder, as the closure asks it. -/
theorem scDescheduleStep (st : SystemState) : FinaliseScDescheduleStep (FinaliseFrameAny st) :=
  fun s t _ h _ _ _ _ => h.trans (FinaliseFrame.descheduleAt s t _ h.invExt).any

/-- A context's release of its holder, as the closure asks it. -/
theorem scReleaseStep (st : SystemState) : FinaliseScReleaseStep (FinaliseFrameAny st) :=
  fun s s' t tcb sc x h hT hS hSc hB hOk =>
    h.trans (FinaliseFrame.releaseStep s s s' t tcb sc x (.refl h.invExt) hT hS hSc hB hOk).any

/-- A thread's notification cancel, as the closure asks it. -/
theorem notificationCancelStep (st : SystemState) :
    FinaliseNotificationCancelStep (FinaliseFrameAny st) :=
  fun s n t tcb _ h _ hI _ _ => h.trans (FinaliseFrame.notificationCancel s t tcb n h.invExt hI).any

/-- A thread's endpoint cancel, as the closure asks it. -/
theorem endpointCancelStep (st : SystemState) : FinaliseEndpointCancelStep (FinaliseFrameAny st) :=
  fun s e q t ep tcb h _ _ _ =>
    h.trans (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.invExt).any

/-- A finalised thread's suspend, as the closure asks it. -/
theorem suspendStep (st : SystemState) : FinaliseSuspendStep (FinaliseFrameAny st) :=
  fun s t _ h _ _ _ _ _ => h.trans (FinaliseFrame.suspend s t h.invExt).any

/-- The release of the cores' holds, as the closure asks it. -/
theorem releaseStep (st : SystemState) : FinaliseReleaseStep (FinaliseFrameAny st) :=
  fun s t h => h.trans (FinaliseFrame.releaseCores s t h.invExt).any

/-- A reply-blocked caller's cancel with its boost reverted, as the closure asks
it. -/
theorem replyStep (st : SystemState) : FinaliseReplyStep (FinaliseFrameAny st) := by
  intro s x r c t h hX hC _ hG
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hG
  have h1 := FinaliseFrameAny.cancelIpcBlockingReclaimed s c t h.invExt hB
  exact h.trans (h1.trans (FinaliseFrame.finaliseReplyRevert _ _ h1.invExt).any)

/-- The yield steps, as the closure asks them. -/
theorem yieldStep (st : SystemState) : FinaliseYieldStep (FinaliseFrameAny st) :=
  ⟨fun s t h => h.trans (FinaliseFrame.cancelYieldTo s t h.invExt).any,
   fun s c h => h.trans (FinaliseFrame.completeYieldFrom s c h.invExt).any⟩

end FinaliseFrameAny

/-- **The finalisation's write frame.** -/
theorem finaliseFinalObject_frame (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (finaliseFinalObject target st) :=
  finaliseFinalObject_closed (FinaliseFrameAny st)
    (fun _ _ _ _ _ _ h _ _ _ _ => h.trans (FinaliseFrame.storeEndpointWaiterCancelled _ _ _ _ _ h.invExt).any)
    (fun _ s _ t tcb h _ _ _ hC =>
      have h1 := FinaliseFrame.notificationCancel s t tcb _ h.invExt
        (notificationWaiterCancellable_blocked hC)
      h.trans (h1.trans (.wakeCancelledWaiter _ _ h1.invExt)).any)
    (FinaliseFrameAny.unbindStep st) (FinaliseFrameAny.scDescheduleStep st)
    (FinaliseFrameAny.scReleaseStep st) (FinaliseFrameAny.notificationCancelStep st)
    (FinaliseFrameAny.endpointCancelStep st) (FinaliseFrameAny.suspendStep st)
    (FinaliseFrameAny.releaseStep st) (FinaliseFrameAny.unstackStep st)
    (FinaliseFrameAny.replyStep st)
    (fun s _ _ tid _ h _ _ e => e ▸ h.trans (FinaliseFrame.updateTcb s tid _ h.invExt).any)
    (FinaliseFrameAny.yieldStep st) target st (.refl hInv)

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
  have hQR : ∀ (s : SystemState) (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId)
      (ep : Endpoint) (tcb : TCB), SystemState.onlyObjectsSchedulerDiffer
        (SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb) s := by
    intro s e q t ep tcb
    unfold SeLe4n.Kernel.storeEndpointBlockedCancelled SeLe4n.Kernel.storeQueueRemove
    refine (hU _ _ _).trans ((hU _ _ _).trans ((hM _ _ _).trans ?_))
    split
    · refine (hU _ _ _).trans ?_
      split
      · exact hM _ _ _
      · exact hU _ _ _
      · rfl
    · split
      · exact hM _ _ _
      · exact hU _ _ _
      · rfl
  have hC : ∀ {a b : SystemState}, SystemState.onlyObjectsSchedulerDiffer a b → a.cdt = b.cdt := by
    intro a b e; unfold SystemState.onlyObjectsSchedulerDiffer at e; rw [e]
  have hSt : ∀ {a b : SystemState} {k : SeLe4n.ObjId} {o : KernelObject},
      SeLe4n.Model.storeObject k o a = .ok ((), b) → b.cdt = a.cdt :=
    fun e => storeObject_cdt_eq _ _ _ _ e
  refine finaliseFinalObject_closed (fun s => s.cdt = st.cdt)
    (fun _ _ s _ t _ h _ _ _ _ => ?_) (fun _ s _ t tcb h _ _ _ hC' => ?_)
    (fun _ s _ t h _ _ _ _ => ?_)
    (fun s t _ h _ _ _ _ => (hC (descheduleAtPlacement_onlyObjectsSchedulerDiffer s t)).trans h)
    (fun s s' t tcb _ x h _ _ _ _ hOk => ?_)
    (fun s n t tcb _ h _ hI _ _ => (hC (hNc s t tcb n hI)).trans h)
    (fun s e q t ep tcb h _ _ _ => (hC (hQR s e q t ep tcb)).trans h)
    (fun s t _ h _ _ _ _ _ => (hC ((hU _ t _).trans
      (descheduleAtPlacement_onlyObjectsSchedulerDiffer s t))).trans h)
    (fun s t h => (onlyObjectsSchedulerCoreHoldsDiffer.releaseCores s t).cdt.trans h)
    (fun s s1 x _ _ _ h _ _ _ _ hSt1 _ _ _ _ => ?_)
    (fun s x r c t h hX hCc _ hG => ?_) (fun s _ _ tid _ h _ _ e => e ▸ (hC (hU s tid _)).trans h)
    ⟨fun s t h => by rw [SystemState.cancelYieldTo_eq_objects]; exact h,
     fun s c h => by rw [SystemState.completeYieldFrom_eq_objects]; exact h⟩
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
      have h2 : SystemState.onlyObjectsSchedulerDiffer
          (SchedContextOps.purgeReplenishment s1 scId) s :=
        SystemState.onlyObjectsSchedulerDiffer.trans
          (SchedContextOps.purgeReplenishment_releaseOnlyWrite s1 scId).1 h1
      exact (hC ((hK _ _ _).trans ((hU _ _ _).trans h2))).trans h
    · cases hOk
  · exact (hC (hS s1 _ _)).trans ((hSt hSt1).trans h)
  · obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hG
    have hRev : ∀ (a : SystemState) (sv : Option SeLe4n.ThreadId),
        (finaliseReplyRevert a sv).cdt = a.cdt := by
      intro a sv; cases sv with
      | none => rfl
      | some v => exact PriorityInheritance.propagatePipChainCrossCore_cdt _ a v _
    have hRecl : (cancelIpcBlockingReclaimed c t s).cdt =
        (Lifecycle.Suspend.cancelIpcBlocking s c t).cdt := by
      unfold cancelIpcBlockingReclaimed
      refine (hC (descheduleUnboundHolder_onlyObjectsSchedulerDiffer _ _ _ _)).trans ?_
      unfold cancelIpcBlockingMigrated
      split
      · exact migrateSchedContextReplenishment_cdt _ _ _ _
      · rfl
    have hRet : (Lifecycle.Suspend.returnDonationToCancelledCaller s c t).cdt = s.cdt := by
      unfold Lifecycle.Suspend.returnDonationToCancelledCaller
      split
      · split
        · rename_i hOk
          obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
          obtain ⟨_, _, _, _, s1, s2, s3, s4, -, -, -, -, hS1, hClear, -, hS3, -, hS4, hEq⟩ :=
            returnDonatedSchedContext_ok_storeChain _ _ _ _ _ n hPop
          have eC := congrArg SystemState.cdt hEq
          exact eC.trans ((hSt hS4).trans ((hSt hS3).trans ((storeDonationHeadPop_cdt_eq hClear).trans
            (hSt hS1))))
        · rfl
      · rfl
    rw [hRev, hRecl, cancelIpcBlocking_replyArm_unfold s c t hB]
    replace h : (Lifecycle.Suspend.returnDonationToCancelledCaller s c t).cdt = st.cdt :=
      hRet.trans h
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
        (Lifecycle.Suspend.restoreToReadyCancelled
          (spliceThreadReplyFrameOut (Lifecycle.Suspend.returnDonationToCancelledCaller s c t) t)
          c) c t)
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

/-- **WS-ZA ZA5.5: a revocation is a finalisation write**: it writes one
endpoint's service record, and keeps the derivation tree and the ASID table. -/
theorem revokeService_finaliseFrameAny {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt) :
    FinaliseFrameAny st st' := by
  have hRw := revokeService_serviceRecordRewrite h
  obtain ⟨_, _, _, rfl⟩ := revokeService_ok h
  refine ⟨rfl, rfl, hRw.invExt hInv, fun oid => ?_⟩
  rcases hRw.lookup hInv oid with e | ⟨ep, c, hE, hE'⟩
  · exact Or.inl e
  · exact Or.inr ⟨_, _, hE, hE', rfl, rfl, Or.inl (Or.inr (Or.inl rfl))⟩

/-- **What a revocation keeps**: every object but an endpoint, read either way. -/
theorem revokeService_back {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt)
    {k : SeLe4n.ObjId} {o : KernelObject} (ho : st'.objects[k]? = some o)
    (hN : ∀ ep, o ≠ .endpoint ep) : st.objects[k]? = some o := by
  rcases (revokeService_serviceRecordRewrite h).lookup hInv k with e | ⟨ep, c, h0, h1⟩
  · rw [← e]; exact ho
  · rw [h1] at ho; cases ho; exact absurd rfl (hN _)

theorem revokeService_fwd {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt)
    {k : SeLe4n.ObjId} {o : KernelObject} (ho : st.objects[k]? = some o)
    (hN : ∀ ep, o ≠ .endpoint ep) : st'.objects[k]? = some o := by
  rcases (revokeService_serviceRecordRewrite h).lookup hInv k with e | ⟨ep, c, h0, h1⟩
  · rw [e]; exact ho
  · rw [h0] at ho; cases ho; exact absurd rfl (hN _)

/-- ...so it keeps every thread. -/
theorem revokeService_getTcb? {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt)
    (t : SeLe4n.ThreadId) : st'.getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?
  rcases (revokeService_serviceRecordRewrite h).lookup hInv t.toObjId with e | ⟨ep, c, h0, h1⟩
  · rw [e]
  · rw [h0, h1]

/-- **A revocation lets go of no loan**: the one object it writes is an
endpoint, before and after. -/
theorem revokeService_loanWrite {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt) :
    loanWrite st st' := fun oid => by
  rcases (revokeService_serviceRecordRewrite h).lookup hInv oid with e | ⟨ep, c, h0, h1⟩
  · exact Or.inl e
  · exact Or.inr ⟨_, _, h0, h1, fun _ hx => KernelObject.noConfusion hx,
      fun _ _ hx => KernelObject.noConfusion hx⟩

/-- **The release of a final endpoint's registration is a finalisation write.** -/
theorem releaseFinalRegistration_frame (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) : FinaliseFrameAny st (releaseFinalRegistration target st) := by
  rcases releaseFinalRegistration_cases target st with hE | ⟨_, _, _, _, hR⟩
  · rw [hE]; exact .refl hInv
  · exact revokeService_finaliseFrameAny hR hInv

/-- **The release keeps the derivation tree**, on any state. -/
theorem releaseFinalRegistration_cdt (target : Nat) (st : SystemState) :
    (releaseFinalRegistration target st).cdt = st.cdt := by
  rcases releaseFinalRegistration_cases target st with hE | ⟨_, _, _, _, hR⟩
  · rw [hE]
  · obtain ⟨_, _, _, hEq⟩ := revokeService_ok hR
    rw [hEq]

/-- **The release and the finalisation after it are one finalisation write.** -/
theorem finaliseReleased_frame (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (finaliseFinalObject target (releaseFinalRegistration target st)) :=
  have h0 := releaseFinalRegistration_frame target st hInv
  h0.trans (finaliseFinalObject_frame target _ h0.invExt)

/-- **The retire after the finalisation keeps the teardown's well-formedness and
only shrinks the roots**: the release's, the finalisation's, then the retire's
(`retireFinalObject_preserves_teardownWellFormed`). -/
theorem retireFinalisedObject_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hW : teardownWellFormed st) :
    teardownWellFormed (retireFinalisedObject ec target recorder st) ∧
      vspaceRootsShrink st (retireFinalisedObject ec target recorder st) := by
  obtain ⟨h0, s0⟩ := (releaseFinalRegistration_frame target st hW.1).preserves_teardownWellFormed hW
  obtain ⟨h1, s1⟩ := finaliseFinalObject_preserves_teardownWellFormed target _ h0
  obtain ⟨h2, s2⟩ := retireFinalObject_preserves_teardownWellFormed ec target recorder _ h1
  exact ⟨h2, s0.trans (s1.trans s2)⟩

end SeLe4n.Kernel
