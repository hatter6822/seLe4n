/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.FinaliseThreadFrames
import SeLe4n.Kernel.RobinHood.Invariant.InPlaceCommute

/-!
# The thread finalisation's admission, carried across its steps

WS-ZA ZA5.4 part 34: a thread's finalisation (`finaliseThread`) is admitted on
the pre-state (`threadFinaliseAdmitted`) and then runs its steps, each of which
re-reads its own guard on the state the steps before it left.  This module
proves the carriage: on a state carrying the finalisation's invariant, the
pre-state admission implies each later step's guard where that step runs, so no
step's guard can refuse after an earlier step has written — the
checks-before-writes property of the thread finalisation.

* **The cancel's admission after the notification unbind**
  (`threadIpcCancelAdmitted_after_unbind`): the unbind rewrites the thread's
  bound-notification code and the notification's bound-thread code, neither of
  which the cancel's admission reads (`CancelReadsKept`).
* **The thread's context bound back after the cancel**
  (`finaliseThreadCancel_carries`): a notification or endpoint cancel writes no
  binding, and a reply cancel's own head pop hands the context back to the
  thread as its own — what the context unbind's guard reads
  (`finaliseThreadUnbindSchedContext`).  The walk over the thread's waiters
  needs no admission: it orphans each (`finaliseThreadOrphanWaiters_endsAll`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  What the notification unbind keeps of the cancel's reads
-- ============================================================================

/-- **A thread with its bound-notification code cleared**: the one field of a
thread the notification unbind writes. -/
@[inline] def _root_.SeLe4n.Model.TCB.notificationUnbound (t : TCB) : TCB := { t with boundNotificationCode := 0 }

/-- Two threads equal off their bound-notification codes differ in that code
alone. -/
theorem _root_.SeLe4n.Model.TCB.eq_of_notificationUnbound {t t' : TCB}
    (h : t'.notificationUnbound = t.notificationUnbound) :
    t' = { t with boundNotificationCode := t'.boundNotificationCode } := by
  cases t; cases t'
  simp only [TCB.notificationUnbound, TCB.mk.injEq] at h ⊢
  simp only [h, and_self]

/-- **What the cancel's admission reads of a state, kept**: every endpoint,
scheduling context and reply as it was, a notification wherever there was one,
every thread up to its bound-notification code, every in-place question and
store-locality answer, and the scheduler. -/
structure CancelReadsKept (s' s : SystemState) : Prop where
  endpoint : ∀ e, s'.getEndpoint? e = s.getEndpoint? e
  schedContext : ∀ c, s'.getSchedContext? c = s.getSchedContext? c
  reply : ∀ (k : SeLe4n.ObjId) (r : Reply), s'.objects[k]? = some (KernelObject.reply r) ↔ s.objects[k]? = some (KernelObject.reply r)
  notification : ∀ m, (s'.getNotification? m).isSome = (s.getNotification? m).isSome
  tcb : tcbProjKept TCB.notificationUnbound s' s
  finds : ∀ k, s'.objects.findsInPlace k = s.objects.findsInPlace k
  leaves : ∀ id ty, storeLeavesIndexAndTypes s' id ty = storeLeavesIndexAndTypes s id ty
  scheduler : s'.scheduler = s.scheduler

namespace CancelReadsKept

variable {s s' : SystemState} (h : CancelReadsKept s' s)
include h

theorem getReply? (r : SeLe4n.ReplyId) : s'.getReply? r = s.getReply? r := by
  unfold SystemState.getReply?
  cases e : s.objects[r.toObjId]? with
  | some o =>
    cases o with
    | reply rr => rw [(h.reply _ rr).mpr e]
    | _ =>
      cases e' : s'.objects[r.toObjId]? with
      | none => rfl
      | some o' =>
        cases o' with
        | reply rr => rw [(h.reply _ rr).mp e'] at e; cases e
        | _ => rfl
  | none =>
    cases e' : s'.objects[r.toObjId]? with
    | none => rfl
    | some o' =>
      cases o' with
      | reply rr => rw [(h.reply _ rr).mp e'] at e; cases e
      | _ => rfl

/-- A thread is read in `s'` as in `s` up to its bound-notification code. -/
theorem getTcb? (y : SeLe4n.ThreadId) :
    (s.getTcb? y = none ∧ s'.getTcb? y = none) ∨
      ∃ t b, s.getTcb? y = some t ∧
        s'.getTcb? y = some { t with boundNotificationCode := b } := by
  have e := h.tcb y
  cases hs : s.getTcb? y with
  | none =>
    rw [hs] at e
    cases hs' : s'.getTcb? y with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some _ => rw [hs'] at e; cases e
  | some t =>
    rw [hs] at e
    cases hs' : s'.getTcb? y with
    | none => rw [hs'] at e; cases e
    | some t' =>
      rw [hs'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact Or.inr ⟨t, t'.boundNotificationCode, rfl, by rw [TCB.eq_of_notificationUnbound e]⟩

theorem lookupTcb_isSome (y : SeLe4n.ThreadId) :
    (lookupTcb s' y).isSome = (lookupTcb s y).isSome := by
  unfold lookupTcb
  split
  · rfl
  · rcases h.getTcb? y with ⟨e1, e2⟩ | ⟨t, b, e1, e2⟩ <;> simp [e1, e2]

end CancelReadsKept

/-- **What a write keeps, pointwise, for the cancel's reads**: the same object,
a thread with only its bound-notification code moved, or a notification. -/
def cancelReadsPointwise (o' o : Option KernelObject) : Prop :=
  o' = o ∨ (∃ t b, o = some (.tcb t) ∧ o' = some (.tcb { t with boundNotificationCode := b })) ∨
    (∃ m m', o = some (.notification m) ∧ o' = some (.notification m'))

/-- A write keeping the cancel's reads pointwise, every in-place question, the
index, the kinds' table and the scheduler keeps the cancel's reads. -/
theorem CancelReadsKept.of_pointwise {s s' : SystemState}
    (hP : ∀ k : SeLe4n.ObjId, cancelReadsPointwise s'.objects[k]? s.objects[k]?)
    (hF : ∀ k : SeLe4n.ObjId, s'.objects.findsInPlace k = s.objects.findsInPlace k)
    (hI : s'.objectIndexSet = s.objectIndexSet) (hL : s'.lifecycle = s.lifecycle)
    (hS : s'.scheduler = s.scheduler) : CancelReadsKept s' s := by
  refine ⟨fun e => ?_, fun c => ?_, fun k r => ?_, fun m => ?_, fun y => ?_, hF, fun id ty => ?_, hS⟩
  · unfold SystemState.getEndpoint?
    rcases hP e with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩ <;> simp [*]
  · unfold SystemState.getSchedContext?
    rcases hP c.toObjId with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩ <;> simp [*]
  · rcases hP k with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩ <;> simp [*]
  · unfold SystemState.getNotification?
    rcases hP m with h | ⟨t, b, h1, h2⟩ | ⟨n, n', h1, h2⟩ <;> simp [*]
  · unfold SystemState.getTcb?
    rcases hP y.toObjId with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩
    · rw [h]
    · rw [h1, h2]; rfl
    · rw [h1, h2]
  · unfold storeLeavesIndexAndTypes
    rw [hI, hL]
    rcases hP id with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩
    · rw [h]
    · rw [h1, h2]
    · rw [h1, h2]

/-- **The notification unbind keeps the cancel's reads** (`CancelReadsKept`): it
writes the thread's bound-notification code in place (its admission finds the
thread's slot in place, `unbindNotificationInPlace`) and then a notification's
bound-thread code, under no resize, so every in-place question is answered as
before. -/
theorem CancelReadsKept.storeUnbindNotification (s : SystemState) (x : SeLe4n.ThreadId)
    (n : SeLe4n.ObjId) (hInv : s.objects.invExt) (hIn : unbindNotificationInPlace s x = true) :
    CancelReadsKept (SeLe4n.Kernel.storeUnbindNotification s x n) s := by
  have hFx : s.objects.findsInPlace x.toObjId = true := by
    unfold unbindNotificationInPlace at hIn
    simp only [Bool.and_eq_true] at hIn
    exact hIn.1.1.2
  unfold SeLe4n.Kernel.storeUnbindNotification
  generalize hf : (fun t : TCB => { t with boundNotificationCode := 0 }) = f
  have hInv1 := SystemState.updateTcb_preserves_objects_invExt s x f hInv
  have hF1 : ∀ k, (s.updateTcb x f).objects.findsInPlace k = s.objects.findsInPlace k :=
    updateTcb_findsInPlace_of_key f hFx
  have hNo : (s.updateTcb x f).objects.noResizeDue :=
    RobinHood.RHTable.noResizeDue_of_findsInPlace ((hF1 x.toObjId).trans hFx)
  have hP1 : ∀ k : SeLe4n.ObjId, cancelReadsPointwise (s.updateTcb x f).objects[k]? s.objects[k]? := by
    intro k
    by_cases hk : x.toObjId = k
    · subst hk
      cases hT : s.getTcb? x with
      | none => exact Or.inl (by rw [SystemState.updateTcb_eq_self_of_none hT])
      | some t =>
        refine Or.inr (Or.inl ⟨t, 0, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, ?_⟩)
        rw [← SystemState.getTcb?_eq_some_iff, SystemState.updateTcb_getTcb?_self s x f hInv, hT, ← hf]
        rfl
    · exact Or.inl (SystemState.updateTcb_objects_ne s x f k hk hInv)
  refine CancelReadsKept.of_pointwise (fun k => ?_) (fun k => ?_)
    (SystemState.updateTcb_objectIndexSet s x f) (SystemState.updateTcb_lifecycle s x f)
    (SystemState.updateTcb_scheduler s x f)
  · rw [modifyObject_objects_getElem hInv1 k]
    split
    · rename_i hnk
      subst hnk
      rcases hP1 n with h | ⟨t, b, h1, h2⟩ | ⟨m, m', h1, h2⟩
      · rw [h]
        cases hO : s.objects[n]? with
        | none => exact Or.inl rfl
        | some o =>
          cases o with
          | notification m => exact Or.inr (Or.inr ⟨m, _, rfl, rfl⟩)
          | _ => exact Or.inl rfl
      · rw [h2]; exact Or.inr (Or.inl ⟨t, b, h1, rfl⟩)
      · rw [h2]; exact Or.inr (Or.inr ⟨m, _, h1, rfl⟩)
    · exact hP1 k
  · show ((s.updateTcb x f).objects.modify n _).findsInPlace k = _
    rw [RobinHood.RHTable.modify_eq_mapValueAt _ _ hNo, RobinHood.RHTable.findsInPlace_mapValueAt]
    exact hF1 k

-- ============================================================================
-- §2  The cancel's admission reads only what the unbind keeps
-- ============================================================================

namespace CancelReadsKept

variable {s s' : SystemState} (h : CancelReadsKept s' s)
include h

theorem queueRemoveInPlace_eq (e : SeLe4n.ObjId) (q : Bool) (x : SeLe4n.ThreadId) (ep : Endpoint)
    (t : TCB) : queueRemoveInPlace s' e q x ep t = queueRemoveInPlace s e q x ep t := by
  unfold queueRemoveInPlace
  simp only [h.leaves, h.finds]
  congr 1
  · congr 1
    cases t.queuePPrev with
    | none => rfl
    | some pp =>
      cases pp with
      | endpointHead => rfl
      | tcbNext p =>
        dsimp only
        rcases h.getTcb? p with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> rw [e1, e2] <;> rfl
  · cases t.queueNext with
    | none => rfl
    | some nx =>
      dsimp only
      rcases h.getTcb? nx with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> rw [e1, e2] <;> rfl

theorem endpointBlockedCancellable_eq (e : SeLe4n.ObjId) (q : Bool) (x : SeLe4n.ThreadId)
    (ep : Endpoint) (t : TCB) :
    endpointBlockedCancellable s' e q x ep t = endpointBlockedCancellable s e q x ep t := by
  unfold endpointBlockedCancellable
  rw [h.queueRemoveInPlace_eq]
  congr 1
  cases t.queueNext with
  | some _ => rfl
  | none =>
    cases t.queuePPrev with
    | none => rfl
    | some pp =>
      cases pp with
      | endpointHead => rfl
      | tcbNext p =>
        dsimp only
        rcases h.getTcb? p with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> rw [e1, e2] <;> rfl

theorem endpointCancelAdmitted_eq (e : SeLe4n.ObjId) (q : Bool) (x : SeLe4n.ThreadId) (t : TCB) :
    endpointCancelAdmitted s' e q x t = endpointCancelAdmitted s e q x t := by
  unfold endpointCancelAdmitted
  rw [h.endpoint e]
  cases s.getEndpoint? e with
  | none => rfl
  | some ep => dsimp only; rw [h.endpointBlockedCancellable_eq]

theorem notificationWaiterCancellable_eq (n : SeLe4n.ObjId) (x : SeLe4n.ThreadId) (t : TCB) :
    notificationWaiterCancellable s' n x t = notificationWaiterCancellable s n x t := by
  unfold notificationWaiterCancellable cancelledWaiterWakeable runningOnSomeCore
  rw [h.scheduler]

theorem donationHeadOf?_eq (c : SeLe4n.SchedContextId) (sc : SchedContext) :
    donationHeadOf? s' c sc = donationHeadOf? s c sc := by
  unfold donationHeadOf?; simp only [h.getReply?]

theorem replyStackOuterCaller?_eq (c : SeLe4n.SchedContextId) :
    replyStackOuterCaller? s' c = replyStackOuterCaller? s c := by
  unfold replyStackOuterCaller?; simp only [h.schedContext, h.donationHeadOf?_eq, h.getReply?]

theorem outerCallerAcceptable_eq (srv own : SeLe4n.ThreadId) (o : Option SeLe4n.ThreadId) :
    outerCallerAcceptable s' srv own o = outerCallerAcceptable s srv own o := by
  cases o with
  | none => rfl
  | some outer =>
    unfold outerCallerAcceptable
    dsimp only
    rcases h.getTcb? outer with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> rw [e1, e2] <;> rfl

theorem donationRecipientAcceptable_eq (own : SeLe4n.ThreadId) :
    donationRecipientAcceptable s' own = donationRecipientAcceptable s own := by
  unfold donationRecipientAcceptable lookupTcb
  cases own.isReserved
  · rcases h.getTcb? own with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> simp only [e1, e2] <;> rfl
  · rfl

theorem donatedReturnCommits_eq (srv : SeLe4n.ThreadId) (c : SeLe4n.SchedContextId)
    (own : SeLe4n.ThreadId) : donatedReturnCommits s' srv c own = donatedReturnCommits s srv c own := by
  unfold donatedReturnCommits
  simp only [h.replyStackOuterCaller?_eq, h.schedContext, h.outerCallerAcceptable_eq,
    h.donationRecipientAcceptable_eq, h.lookupTcb_isSome]


theorem replyHeadPopCommits_eq (x : SeLe4n.ObjId) (r : Reply) (c : SeLe4n.ThreadId) :
    replyHeadPopCommits s' x r c = replyHeadPopCommits s x r c := by
  unfold replyHeadPopCommits
  cases r.next with
  | none => rfl
  | some l =>
    cases l with
    | frame _ => rfl
    | head sc =>
      dsimp only
      rw [h.schedContext]
      cases s.getSchedContext? sc with
      | none => rfl
      | some v =>
        dsimp only
        cases v.boundThreadCode with
        | zero => rfl
        | succ k =>
          dsimp only
          rw [h.donatedReturnCommits_eq]
          rcases h.getTcb? ⟨k⟩ with ⟨e1, e2⟩ | ⟨u, b, e1, e2⟩ <;> rw [e1, e2] <;> rfl

theorem replyCallerFinalisable_eq (x : SeLe4n.ObjId) (r : Reply) (c : SeLe4n.ThreadId) (t : TCB) :
    replyCallerFinalisable s' x r c t = replyCallerFinalisable s x r c t := by
  unfold replyCallerFinalisable; rw [h.replyHeadPopCommits_eq]

theorem replyHeadHeldByServer_eq (r : Reply) (t : TCB) :
    replyHeadHeldByServer s' r t = replyHeadHeldByServer s r t := by
  unfold replyHeadHeldByServer; simp only [h.schedContext]

theorem replyCallerCancelAdmitted_eq (c : SeLe4n.ThreadId) (t : TCB) :
    replyCallerCancelAdmitted s' c t = replyCallerCancelAdmitted s c t := by
  unfold replyCallerCancelAdmitted
  simp only [SystemState.getObject?_eq_getElem]
  cases e : s.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
  | some o =>
    cases o with
    | reply r =>
      rw [(h.reply _ r).mpr e]; dsimp only
      rw [h.replyCallerFinalisable_eq, h.replyHeadHeldByServer_eq]
    | _ =>
      cases e' : s'.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
      | none => rfl
      | some o' =>
        cases o' with
        | reply rr => rw [(h.reply _ rr).mp e'] at e; cases e
        | _ => rfl
  | none =>
    cases e' : s'.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
    | none => rfl
    | some o' =>
      cases o' with
      | reply rr => rw [(h.reply _ rr).mp e'] at e; cases e
      | _ => rfl


/-- **The cancel's admission reads only what the unbind keeps.** -/
theorem threadIpcCancelAdmitted_eq (x : SeLe4n.ThreadId) (t : TCB) :
    threadIpcCancelAdmitted s' x t = threadIpcCancelAdmitted s x t := by
  unfold threadIpcCancelAdmitted
  split
  · split
    · rfl
    · exact h.endpointCancelAdmitted_eq _ _ _ _
  · exact h.endpointCancelAdmitted_eq _ _ _ _
  · congr 1
    have e := h.notification ⟨t.ipcObjectCode⟩
    cases e1 : s.getNotification? ⟨t.ipcObjectCode⟩ with
    | none =>
      rw [e1] at e
      cases e2 : s'.getNotification? ⟨t.ipcObjectCode⟩ with
      | none => rfl
      | some _ => rw [e2] at e; cases e
    | some _ =>
      rw [e1] at e
      cases e2 : s'.getNotification? ⟨t.ipcObjectCode⟩ with
      | none => rw [e2] at e; cases e
      | some _ => dsimp only; exact h.notificationWaiterCancellable_eq _ _ _
  · exact h.endpointCancelAdmitted_eq _ _ _ _
  · exact h.replyCallerCancelAdmitted_eq _ _

end CancelReadsKept

/-- Every state keeps its own cancel reads. -/
theorem CancelReadsKept.refl (s : SystemState) : CancelReadsKept s s :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl, fun _ => rfl, tcbProjKept.of_objects rfl,
    fun _ => rfl, fun _ _ => rfl, rfl⟩

/-- **The notification unbind keeps the cancel's reads**, on a state whose
admission admits it (`notificationUnbindAdmitted`): with no binding it writes
nothing, and otherwise it is the in-place unbind the admission reads. -/
theorem finaliseThreadUnbindNotification_readsKept (st : SystemState) (x : SeLe4n.ThreadId)
    {t : TCB} (hInv : st.objects.invExt) (hX : st.getTcb? x = some t)
    (hG : notificationUnbindAdmitted st x t = true) :
    CancelReadsKept (finaliseThreadUnbindNotification st x) st := by
  have hc : boundNotificationCodeOf st x = t.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hX]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact .refl st
  · rename_i h0
    unfold notificationUnbindAdmitted at hG
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hG h0
    rcases hG with hz | ⟨-, hIn⟩
    · exact absurd hz h0
    · exact CancelReadsKept.storeUnbindNotification st x _ hInv hIn

-- ============================================================================
-- §3  The admission's parts, and the cancel's admission after the unbind
-- ============================================================================

/-- **What the thread finalisation's admission reads**, as facts: the thread
stored under its own id, no reserved or idle thread, unlinked from every
reply-waiter queue unless blocked on a reply, holding no timeout budget, its
cancel's admission, and its two bindings bound back (a thread naming no context
naming no lender). -/
theorem threadFinaliseAdmitted_parts {st : SystemState} {x : SeLe4n.ObjId}
    (hA : threadFinaliseAdmitted st x = true) :
    ∃ tx, st.getTcb? ⟨x.val⟩ = some tx ∧ tx.tid.val = x.val ∧
      (⟨x.val⟩ : SeLe4n.ThreadId).isReserved = false ∧ isIdleThreadId ⟨x.val⟩ = false ∧
      (4 ≤ tx.ipcStateCode ∨
        tx.replyWaiterNextCode = 0 ∧ tx.replyWaiterPrevCode = 0 ∧ tx.replyObjectCode = 0) ∧
      tx.timeoutBudget = none ∧
      threadIpcCancelAdmitted st ⟨x.val⟩ tx = true ∧
      (tx.replyObjectCode = 0 ∨ replyHeadPopsOwn st tx = true) ∧
      notificationUnbindAdmitted st ⟨x.val⟩ tx = true ∧
      (tx.scBindingScCode = 0 ∧ tx.scBindingOwnerCode = 0 ∨
        tx.scBindingScCode ≠ 0 ∧ ∃ sc, st.getSchedContext? ⟨tx.scBindingScCode - 1⟩ = some sc ∧
          sc.boundThreadCode = x.val + 1) := by
  unfold threadFinaliseAdmitted at hA
  rw [SystemState.getObject?_eq_getElem] at hA
  split at hA
  rotate_left
  · cases hA
  rename_i tx hO
  dsimp only at hA
  simp only [Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hTid, hRes⟩, hIdle⟩, hRw⟩, hTB⟩, hC⟩, hP⟩, hN⟩, hS⟩ := hA
  refine ⟨tx, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, by simpa using hTid,
    by simpa using hRes, by simpa using hIdle, ?_, by simpa using hTB, hC,
    by simpa only [Bool.or_eq_true, beq_iff_eq] using hP, hN, ?_⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hRw
    rcases hRw with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hS
    rcases hS with h | ⟨h0, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨h0, ?_⟩
      revert h
      cases st.getSchedContext? ⟨tx.scBindingScCode - 1⟩ with
      | none => intro h; cases h
      | some sc => intro h; exact ⟨sc, rfl, by simpa using h⟩

/-- **The cancel's admission after the notification unbind** (part 34): on a
state the finalisation admits, the cancel's admission holds of the thread the
notification unbind leaves — the unbind writes nothing the admission reads
(`finaliseThreadUnbindNotification_readsKept`, `CancelReadsKept.threadIpcCancelAdmitted_eq`),
and the thread it leaves differs from the pre-state's in its bound-notification
code alone. -/
theorem threadIpcCancelAdmitted_after_unbind {st : SystemState} {x : SeLe4n.ObjId}
    (hInv : st.objects.invExt) (hA : threadFinaliseAdmitted st x = true) :
    ∀ t1, (finaliseThreadUnbindNotification st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t1 →
      threadIpcCancelAdmitted (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩ t1 = true := by
  obtain ⟨tx, hX, -, -, -, -, -, hC, -, hBnc, -⟩ := threadFinaliseAdmitted_parts hA
  intro t1 h1
  rw [finaliseThreadUnbindNotification_self hInv hX] at h1
  cases h1
  rw [(finaliseThreadUnbindNotification_readsKept st _ hInv hX hBnc).threadIpcCancelAdmitted_eq]
  exact hC

-- ============================================================================
-- §4  What the finalisation keeps of the thread's own binding
-- ============================================================================

/-- **The thread `x`'s context is bound back to it**: a zero context code names
no lender either, and a nonzero one names a context whose bound-thread code is
`x`'s — what the context unbind's guard reads (`finaliseThreadUnbindSchedContext`),
and what leaves the thread with no binding after it. -/
def bindingBack (s : SystemState) (x : SeLe4n.ThreadId) : Prop :=
  ∀ tx, s.getTcb? x = some tx → (tx.scBindingScCode = 0 → tx.scBindingOwnerCode = 0) ∧
    (tx.scBindingScCode ≠ 0 →
      ∃ sc, s.getSchedContext? ⟨tx.scBindingScCode - 1⟩ = some sc ∧ sc.boundThreadCode = x.val + 1)

/-- A step agreeing on the bindings keeps a context bound back. -/
theorem bindingBack.transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : bindingLinksAgree s s') (hB : bindingBack s x) : bindingBack s' x := by
  intro tx' hX'
  obtain ⟨tx, hX, e1, e2⟩ := h.getTcb?_back hX'
  obtain ⟨hz, hB'⟩ := hB tx hX
  refine ⟨fun h0 => e2.trans (hz (e1 ▸ h0)), fun hc => ?_⟩
  obtain ⟨sc, hS, hb⟩ := hB' (by rw [← e1]; exact hc)
  obtain ⟨sc', hS', hb'⟩ := h.getSchedContext?_fwd hS
  exact ⟨sc', by rw [e1]; exact hS', hb'.trans hb⟩

/-- **What the donation return writes of the two threads**: the thread the
context is taken from gets no binding, and the thread it is handed to the binding
the return names (`donationReturnBinding`). -/
theorem returnDonatedSchedContext_codes {st st' : SystemState} {hd c : SeLe4n.ThreadId}
    {s : SeLe4n.SchedContextId} {n : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : returnDonatedSchedContext st hd s c n = .ok st') (hne : c ≠ hd) :
    (∃ th, st'.objects[hd.toObjId]? = some (.tcb th) ∧ th.scBindingScCode = 0 ∧
      th.scBindingOwnerCode = 0) ∧
    (∃ tc, st'.objects[c.toObjId]? = some (.tcb tc) ∧
      tc.scBindingScCode = (donationReturnBinding s n).scCode ∧
      tc.scBindingOwnerCode = (donationReturnBinding s n).ownerCode) := by
  obtain ⟨_, _, clientTcb, serverTcb, s1, s2, s3, s4, _, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' hd s c n h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  rw [hEq]
  exact ⟨⟨_, storeObject_objects_eq' s3 hd.toObjId _ _ hInv3 hS4, rfl, rfl⟩,
    ⟨_, (storeObject_objects_ne s3 s4 hd.toObjId c.toObjId _
      (SeLe4n.Kernel.threadId_toObjId_ne hne.symm) hInv3 hS4).trans
      (storeObject_objects_eq' s2 c.toObjId _ _ hInv2 hS3), rfl, rfl⟩⟩

/-- **An admitted head reply's cancel is a committed pop, then writes no
binding**: the cancel of `c` (its TCB `t`), whose reply heads the stack of `s`,
admitted by its guard, runs the donation return of `s` from the thread `hd`
holding it to `c`, resolving the outer caller `n`, and every write after it —
the splice, restore, consume and unlink, the migration, the holder's deschedule
and the revert — keeps every binding (`bindingLinksAgree`). -/
theorem finaliseReplyCallerCancel_pop (st : SystemState) (hInv : st.objects.invExt)
    {c : SeLe4n.ThreadId} {t : TCB} {r : Reply} {s : SeLe4n.SchedContextId}
    (hT : st.getTcb? c = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r)) (hN : r.next = some (.head s))
    (hE : replyCallerCancelAdmitted st c t = true) :
    ∃ (hd : SeLe4n.ThreadId) (n : Option SeLe4n.ThreadId) (P : SystemState),
      replyStackOuterCaller? st s = .ok n ∧ c ≠ hd ∧
      replyCallerServerCode t = hd.val + 1 ∧
      returnDonatedSchedContext st hd s c n = .ok P ∧
      bindingLinksAgree P (finaliseReplyCallerCancel st c t) := by
  unfold replyCallerCancelAdmitted at hE
  rw [hR] at hE
  dsimp only at hE
  have hG := hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨⟨hC, hF⟩, hH⟩ := hE
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
  rcases replyCallerFinalisable_cases hR hF with ⟨hNH, -⟩ |
      ⟨s', sc, hd, ht, hN', hSc, -, hBt, hHt, hBind, hCm, hDon⟩
  · rw [hN] at hNH; cases hNH
  rw [hN] at hN'; cases hN'
  have hSrv : replyCallerServerCode t = hd.val + 1 := by
    unfold replyHeadHeldByServer at hH
    rw [hN] at hH
    simp only [hSc, beq_iff_eq] at hH
    rw [← hH]
    exact (SeLe4n.ThreadId.ofOptCode_eq_some_iff _ _).mp hBt
  obtain ⟨P, hOk⟩ := returnDonatedSchedContextResolved_ok_of_commits hInv hCm
  obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
  have hne : c ≠ hd := returnDonatedSchedContext_ok_recipient_ne_server st P hd s c n ht hHt
    (by rw [hBind]; exact fun e => by cases e) hPop
  have hRet : Lifecycle.Suspend.returnDonationToCancelledCaller st c t = P := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hDon, hT]
    dsimp only
    rw [hOk]
  have hCancel : finaliseReplyCallerCancel st c t =
      finaliseReplyRevert (cancelIpcBlockingReclaimed c t st) t.blockingServer? := by
    unfold finaliseReplyCallerCancel finaliseReplyCancel
    rw [hR]
    dsimp only
    rw [if_pos hG, hN]
    rfl
  refine ⟨hd, n, P, hRes, hne, hSrv, hPop, ?_⟩
  rw [hCancel]
  have hIP : P.objects.invExt :=
    returnDonatedSchedContext_preserves_objects_invExt st P hd s c hInv n hPop
  have F := SchedLinkFrame.replyCancelTail P c t hIP
  rw [← hRet, ← cancelIpcBlocking_replyArm_unfold st c t hB] at F
  have hInvC : (Lifecycle.Suspend.cancelIpcBlocking st c t).objects.invExt :=
    (FinaliseFrameAny.replyCancel st c t hInv hB).invExt
  have FD : SchedLinkFrame (cancelIpcBlockingMigrated c t st) (cancelIpcBlockingReclaimed c t st) :=
    SchedLinkFrame.of_agreeOffRunLinks
      (descheduleUnboundHolder_objectsAgreeOffRunLinks st (cancelIpcBlockingMigrated c t st) c t)
      (by unfold cancelIpcBlockingReclaimed descheduleUnboundHolder; split; rfl
          exact descheduleAtPlacement_releaseSlots _ _)
  have FR := SchedLinkFrame.finaliseReplyRevert _ t.blockingServer?
    (cancelIpcBlockingReclaimed_objects_invExt c t st hInvC)
  rw [hRet] at F
  exact ((bindingLinksAgree.trans F.binding (fun o => proj_eq_of_map_eq _ _
    (fun x => by cases x <;> rfl) (cancelIpcBlockingMigrated_agree c t st o))).trans
    FD.binding).trans FR.binding

-- ============================================================================
-- §5  The cancel carries the binding
-- ============================================================================

/-- **A context heads a stack of one frame**: its head reply links down to
nothing, so it has no outer caller. -/
theorem replyStackOuterCaller?_of_prev_none {st : SystemState} {s : SeLe4n.SchedContextId}
    {sc : SchedContext} {rid : SeLe4n.ReplyId} {r : Reply} (hSc : st.getSchedContext? s = some sc)
    (hRp : sc.scReply = some rid) (hGR : st.getReply? rid = some r) (hN : r.next = some (.head s))
    (hP : r.prev = none) : replyStackOuterCaller? st s = .ok none := by
  unfold replyStackOuterCaller? donationHeadOf?
  rw [hSc]
  dsimp only
  rw [hRp]
  dsimp only
  rw [hGR]
  dsimp only
  rw [hN]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [hP]

/-- **An endpoint cancel writes no binding.** -/
theorem cancelEndpointBlocked_bindings (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (x : SeLe4n.ThreadId) (t : TCB) (hInv : s.objects.invExt) :
    bindingLinksAgree s (cancelEndpointBlocked s e q x t) := by
  unfold cancelEndpointBlocked
  split
  · split
    · exact (SchedLinkFrame.storeEndpointBlockedCancelled s e q x _ t hInv).binding
    · exact fun _ => rfl
  · exact fun _ => rfl

/-- **A reply-blocked thread's own cancel keeps its context bound back**, on a
state the finalisation admits: a reply heading no stack is removed writing no
binding; a head reply is the thread's own pop, which hands its context back to
it as its own (`replyHeadPopsOwn`), bound back to it. -/
theorem finaliseReplyCallerCancel_carries (s : SystemState) (x : SeLe4n.ThreadId) (t : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some t)
    (hA : replyCallerCancelAdmitted s x t = true) (hP : replyHeadPopsOwn s t = true) :
    bindingBack s x → bindingBack (finaliseReplyCallerCancel s x t) x := by
  have hInv := h.2.1
  have hA0 := hA
  unfold replyCallerCancelAdmitted at hA0
  cases hR : s.getObject? ⟨t.replyObjectCode - 1⟩ with
  | none => rw [hR] at hA0; cases hA0
  | some o =>
    cases o with
    | reply r =>
      rw [hR] at hA0
      dsimp only at hA0
      simp only [Bool.and_eq_true, beq_iff_eq] at hA0
      obtain ⟨⟨hC, hF⟩, -⟩ := hA0
      have noHead : replyStackLinkIsHead r.next = false →
          bindingBack s x → bindingBack (finaliseReplyCallerCancel s x t) x := fun hNH =>
        bindingBack.transport
          (finaliseReplyCallerCancel_noHead_schedLinkFrame s hInv hR hNH hA).1.binding
      cases hN : r.next with
      | none => exact noHead (by rw [hN]; rfl)
      | some l =>
        cases l with
        | frame a => exact noHead (by rw [hN]; rfl)
        | head sid =>
          obtain ⟨hd, n, P, hRes, hne, -, hPop, hAg⟩ := finaliseReplyCallerCancel_pop s hInv hX hR hN hA
          -- The pop resolves no outer caller.
          have hn : n = none := by
            rcases replyCallerFinalisable_cases hR hF with ⟨hNH, -⟩ |
                ⟨s', sc, -, -, hN', hSc, hRp, -⟩
            · rw [hN] at hNH; cases hNH
            rw [hN] at hN'; cases hN'
            have hPv : r.prev = none := by
              unfold replyHeadPopsOwn at hP; rw [hR] at hP
              simp only [hN, Option.isNone_iff_eq_none] at hP; exact hP
            have hGR : s.getReply? ⟨t.replyObjectCode - 1⟩ = some r :=
              (SystemState.getReply?_eq_some_iff _ _ _).mpr hR
            rw [replyStackOuterCaller?_of_prev_none hSc hRp hGR hN hPv] at hRes
            cases hRes; rfl
          subst hn
          obtain ⟨-, tc, htc, hc1, hc2⟩ := returnDonatedSchedContext_codes hInv hPop hne
          obtain ⟨tx', hX', e1, e2⟩ := hAg.getTcb?_fwd ((SystemState.getTcb?_eq_some_iff _ _ _).mpr htc)
          have hOwn' : ∀ t', (finaliseReplyCallerCancel s x t).getTcb? x = some t' →
              t'.scBindingOwnerCode = 0 := by
            intro t' ht'; rw [hX'] at ht'; cases ht'; rw [e2, hc2]; rfl
          intro _ t' ht'
          refine ⟨fun _ => hOwn' t' ht', fun hz => ?_⟩
          rw [hX'] at ht'; cases ht'
          obtain ⟨sc', hS', hB'⟩ := returnDonatedSchedContext_post_boundThread s P hd sid x hInv none hPop
          obtain ⟨sc'', hS'', hB''⟩ := hAg.getSchedContext?_fwd hS'
          refine ⟨sc'', ?_, hB''.trans ((SeLe4n.ThreadId.ofOptCode_eq_some_iff _ _).mp hB')⟩
          rw [e1, hc1]; exact hS''
    | _ => rw [hR] at hA0; cases hA0

/-- **The finalisation's cancel keeps `x`'s context bound back** (part 34), on a
state carrying the finalisation's invariant whose cancel the admission admits,
whatever `x` was blocked on: a notification or endpoint cancel writes no
binding, and a reply cancel carries it (`finaliseReplyCallerCancel_carries`). -/
theorem finaliseThreadCancel_carries (s : SystemState) (x : SeLe4n.ThreadId) (t : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some t)
    (hA : threadIpcCancelAdmitted s x t = true)
    (hP : t.replyObjectCode = 0 ∨ replyHeadPopsOwn s t = true) :
    bindingBack s x → bindingBack (finaliseThreadCancel s x) x := by
  have hInv := h.2.1
  have hEp : ∀ e q, bindingBack s x → bindingBack (cancelEndpointBlocked s e q x t) x :=
    fun e q => bindingBack.transport (cancelEndpointBlocked_bindings s e q x t hInv)
  unfold threadIpcCancelAdmitted at hA
  unfold finaliseThreadCancel
  rw [hX]
  dsimp only
  have hI : t.ipcState = ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode := rfl
  rcases hc : t.ipcStateCode with _ | _ | _ | _ | k
  · cases ho : t.ipcObjectCode with
    | zero =>
      have hR : t.ipcState = .ready := by rw [hI, hc, ho]; rfl
      rw [hR]; exact id
    | succ o =>
      have hR : t.ipcState = .blockedOnSend ⟨o⟩ := by rw [hI, hc, ho]; rfl
      rw [hR]; exact hEp _ _
  · have hR : t.ipcState = .blockedOnReceive ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]; exact hEp _ _
  · have hR : t.ipcState = .blockedOnNotification ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    dsimp only
    cases s.getNotification? ⟨t.ipcObjectCode⟩ with
    | none => exact id
    | some ntfn =>
      dsimp only
      split
      · exact bindingBack.transport (SchedLinkFrame.notificationCancel s x t _ hInv hR).binding
      · exact id
  · have hR : t.ipcState = .blockedOnCall ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]; exact hEp _ _
  · have hR : t.ipcState = .blockedOnReply ⟨t.ipcObjectCode⟩ (SeLe4n.ThreadId.ofOptCode k) := by
      rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    have hP' : replyHeadPopsOwn s t = true := by
      rcases hP with e | e
      · unfold replyHeadPopsOwn
        unfold replyCallerCancelAdmitted at hA
        cases hO : s.getObject? ⟨t.replyObjectCode - 1⟩ with
        | none => rfl
        | some o =>
          cases o with
          | reply r =>
            rw [hO] at hA
            simp only [Bool.and_eq_true, beq_iff_eq] at hA
            obtain ⟨-, -, -, -, -, hRO, -, -, -⟩ := replyCallerFinalisable_parts hA.1.2
            unfold TCB.replyObject at hRO; rw [e] at hRO; cases hRO
          | _ => rfl
      · exact e
    exact finaliseReplyCallerCancel_carries s x t h hX hA hP'


-- ============================================================================
-- §6  The notification unbind carries the admission's reads
-- ============================================================================

/-- **The notification unbind keeps every reply, both ways**, on a state whose
admission admits it (`finaliseThreadUnbindNotification_readsKept`). -/
theorem finaliseThreadUnbindNotification_replies (st : SystemState) (x : SeLe4n.ThreadId)
    {t : TCB} (hInv : st.objects.invExt) (hX : st.getTcb? x = some t)
    (hG : notificationUnbindAdmitted st x t = true) (k : SeLe4n.ObjId) (r : Reply) :
    (finaliseThreadUnbindNotification st x).objects[k]? = some (.reply r) ↔
      st.objects[k]? = some (.reply r) :=
  (finaliseThreadUnbindNotification_readsKept st x hInv hX hG).reply k r

/-- A read of one reply answers alike on two states keeping every reply, both
ways: the head pop's hand-back question. -/
theorem replyHeadPopsOwn_of_replies {s s' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (r : Reply), s'.objects[k]? = some (KernelObject.reply r) ↔
      s.objects[k]? = some (KernelObject.reply r))
    (t : TCB) : replyHeadPopsOwn s' t = replyHeadPopsOwn s t := by
  unfold replyHeadPopsOwn SystemState.getObject?
  cases e : s.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
  | some o =>
    cases o with
    | reply rr => rw [(h _ rr).mpr e]
    | _ =>
      cases e' : s'.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
      | none => rfl
      | some o' =>
        cases o' with
        | reply rr => rw [(h _ rr).mp e'] at e; cases e
        | _ => rfl
  | none =>
    cases e' : s'.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ObjId)]? with
    | none => rfl
    | some o' =>
      cases o' with
      | reply rr => rw [(h _ rr).mp e'] at e; cases e
      | _ => rfl

end SeLe4n.Kernel
