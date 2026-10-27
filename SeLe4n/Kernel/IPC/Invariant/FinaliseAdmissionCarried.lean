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
waiters' and its cancel's admissions, and its two bindings bound back. -/
theorem threadFinaliseAdmitted_parts {st : SystemState} {x : SeLe4n.ObjId}
    (hA : threadFinaliseAdmitted st x = true) :
    ∃ tx, st.getTcb? ⟨x.val⟩ = some tx ∧ tx.tid.val = x.val ∧
      (⟨x.val⟩ : SeLe4n.ThreadId).isReserved = false ∧ isIdleThreadId ⟨x.val⟩ = false ∧
      (4 ≤ tx.ipcStateCode ∨
        tx.replyWaiterNextCode = 0 ∧ tx.replyWaiterPrevCode = 0 ∧ tx.replyObjectCode = 0) ∧
      tx.timeoutBudget = none ∧ replyWaitersAdmitted st ⟨x.val⟩ tx = true ∧
      threadIpcCancelAdmitted st ⟨x.val⟩ tx = true ∧
      (tx.replyObjectCode = 0 ∨ replyHeadPopsOwn st tx = true) ∧
      notificationUnbindAdmitted st ⟨x.val⟩ tx = true ∧
      (tx.scBindingScCode = 0 ∨ ∃ sc, st.getSchedContext? ⟨tx.scBindingScCode - 1⟩ = some sc ∧
        sc.boundThreadCode = x.val + 1) := by
  unfold threadFinaliseAdmitted at hA
  rw [SystemState.getObject?_eq_getElem] at hA
  split at hA
  rotate_left
  · cases hA
  rename_i tx hO
  dsimp only at hA
  simp only [Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hTid, hRes⟩, hIdle⟩, hRw⟩, hTB⟩, hW⟩, hC⟩, hP⟩, hN⟩, hS⟩ := hA
  refine ⟨tx, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, by simpa using hTid,
    by simpa using hRes, by simpa using hIdle, ?_, by simpa using hTB, hW, hC,
    by simpa only [Bool.or_eq_true, beq_iff_eq] using hP, hN, ?_⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hRw
    rcases hRw with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  · simp only [Bool.or_eq_true, beq_iff_eq] at hS
    rcases hS with h | h
    · exact Or.inl h
    · refine Or.inr ?_
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
  obtain ⟨tx, hX, -, -, -, -, -, -, hC, -, hBnc, -⟩ := threadFinaliseAdmitted_parts hA
  intro t1 h1
  rw [finaliseThreadUnbindNotification_self hInv hX] at h1
  cases h1
  rw [(finaliseThreadUnbindNotification_readsKept st _ hInv hX hBnc).threadIpcCancelAdmitted_eq]
  exact hC

/-- **What the finalised thread's unbind and cancel keep of another thread**,
compared: its two IPC codes, its reply link, its timeout budget and its id, a
zero run-core code kept zero, and a thread linked into no endpoint queue kept
so — what a plain waiter's guard reads of its TCB (`plainWaiterOk`). -/
def TCB.cancelKeptBy (t' t : TCB) : Prop :=
  t'.ipcObjectCode = t.ipcObjectCode ∧ t'.ipcStateCode = t.ipcStateCode ∧
    t'.replyObjectCode = t.replyObjectCode ∧ t'.timeoutBudget = t.timeoutBudget ∧ t'.tid = t.tid ∧
    (t.runCoreCode = 0 → t'.runCoreCode = 0) ∧
    (t.queueNextCode = 0 → t.queuePrevCode = 0 → t'.queueNextCode = 0 ∧ t'.queuePrevCode = 0)

theorem TCB.cancelKeptBy.refl (t : TCB) : TCB.cancelKeptBy t t :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, fun a b => ⟨a, b⟩⟩

theorem TCB.cancelKeptBy.trans {a b c : TCB} (h₁ : TCB.cancelKeptBy a b)
    (h₂ : TCB.cancelKeptBy b c) : TCB.cancelKeptBy a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h₂
  refine ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, fun z => a6 (b6 z),
    fun n p => ?_⟩
  obtain ⟨n', p'⟩ := b7 n p
  exact a7 n' p'

/-- A thread whose key a plain waiter's guard reads is kept is kept so. -/
theorem TCB.cancelKeptBy.of_waiterKeyEq {a b : TCB} (h : TCB.waiterKeyEq a b)
    (hz : b.runCoreCode = 0 → a.runCoreCode = 0) : TCB.cancelKeptBy a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, hz,
    fun n p => ⟨h.2.2.2.1.trans n, h.2.2.2.2.1.trans p⟩⟩

/-- **A step that keeps every plain waiter of a server `x` but `x` itself**:
every other thread kept as `TCB.cancelKeptBy` reads it, and back with its two
IPC codes; and every reply heading no stack whose caller is not `x` kept heading
none, with its caller — its `prev` may move, which no guard of a plain waiter
reads. -/
structure CancelFrame (s s' : SystemState) (x : SeLe4n.ThreadId) : Prop where
  fwd : ∀ (v : SeLe4n.ThreadId) (t : TCB), v ≠ x → s.getTcb? v = some t →
    ∃ t', s'.getTcb? v = some t' ∧ TCB.cancelKeptBy t' t
  bwd : ∀ (v : SeLe4n.ThreadId) (t' : TCB), v ≠ x → s'.getTcb? v = some t' →
    ∃ t, s.getTcb? v = some t ∧ t'.ipcObjectCode = t.ipcObjectCode ∧
      t'.ipcStateCode = t.ipcStateCode
  reply : ∀ (k : SeLe4n.ObjId) (r : Reply), s.getObject? k = some (.reply r) → r.next = none →
    r.callerCode ≠ x.val + 1 →
    ∃ r', s'.getObject? k = some (.reply r') ∧ r'.callerCode = r.callerCode ∧ r'.next = none

namespace CancelFrame

theorem refl (s : SystemState) (x : SeLe4n.ThreadId) : CancelFrame s s x :=
  ⟨fun _ t _ h => ⟨t, h, .refl t⟩, fun _ t _ h => ⟨t, h, rfl, rfl⟩,
    fun _ r h _ _ => ⟨r, h, rfl, by assumption⟩⟩

theorem trans {a b c : SystemState} {x : SeLe4n.ThreadId} (h₁ : CancelFrame a b x)
    (h₂ : CancelFrame b c x) : CancelFrame a c x := by
  refine ⟨fun v t hv ht => ?_, fun v t hv ht => ?_, fun k r hk hn hc => ?_⟩
  · obtain ⟨m, hm, km⟩ := h₁.fwd v t hv ht
    obtain ⟨n, hn, kn⟩ := h₂.fwd v m hv hm
    exact ⟨n, hn, kn.trans km⟩
  · obtain ⟨m, hm, m1, m2⟩ := h₂.bwd v t hv ht
    obtain ⟨n, hn, n1, n2⟩ := h₁.bwd v m hv hm
    exact ⟨n, hn, m1.trans n1, m2.trans n2⟩
  · obtain ⟨m, hm, mc, mn⟩ := h₁.reply k r hk hn hc
    obtain ⟨n, hn', nc, nn⟩ := h₂.reply k m hm mn (by rw [mc]; exact hc)
    exact ⟨n, hn', nc.trans mc, nn⟩

/-- A frame that keeps every plain waiter but `x` is a cancel frame at `x`. -/
theorem of_waiterFrame {a b : SystemState} {x : SeLe4n.ThreadId} (h : WaiterFrame a b (· = x)) :
    CancelFrame a b x := by
  refine ⟨fun v t hv ht => ?_, fun v t hv ht => ?_, fun k r hk hn hc => ?_⟩
  · obtain ⟨t', h', k, z⟩ := h.fwd v t hv ht
    exact ⟨t', h', .of_waiterKeyEq k z⟩
  · obtain ⟨t0, h0, k⟩ := h.bwd v t hv ht
    exact ⟨t0, h0, k.1, k.2.1⟩
  · exact ⟨r, h.reply k r hk hn (fun e he => he ▸ hc), rfl, hn⟩

/-- A frame keeping every other object is one. -/
theorem of_objects_eq {a b : SystemState} (x : SeLe4n.ThreadId) (h : b.objects = a.objects) :
    CancelFrame a b x :=
  of_waiterFrame (WaiterFrame.of_objects_eq _ h)

/-- **A plain waiter of `x` other than `x` stays one across a cancel frame.** -/
theorem ready {a b : SystemState} {x v : SeLe4n.ThreadId} (h : CancelFrame a b x)
    (hv : v ≠ x) (hR : plainWaiterReady a x v) : plainWaiterReady b x v := by
  obtain ⟨t, r, ht, hr, hok⟩ := hR
  obtain ⟨t', ht', k1, k2, k3, k4, -, k6, k7⟩ := h.fwd v t hv ht
  obtain ⟨hvx, hS, hC, hN, hRes, hId, hRun, hIpc, hRO, hQN, hQP, hTB⟩ := hok
  have hcx : r.callerCode ≠ x.val + 1 := by
    rw [hC]; intro e; exact hvx (by omega)
  obtain ⟨r', hr', hc', hn'⟩ := h.reply _ r hr hN hcx
  have hS' : t'.blockingServer? = some x := by
    have e : t'.ipcState = t.ipcState := by
      show ThreadIpcState.ofCodes t'.ipcObjectCode t'.ipcStateCode =
        ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode
      rw [k1, k2]
    unfold TCB.blockingServer?; rw [e]; exact hS
  obtain ⟨q1, q2⟩ := k7 hQN hQP
  exact ⟨t', r', ht', by rw [k3]; exact hr', hvx, hS', hc'.trans hC, hn', hRes, hId, k6 hRun,
    k2 ▸ hIpc, k3 ▸ hRO, q1, q2, k4 ▸ hTB⟩

/-- **A waiter of `x` after the frame waited on `x` before it.** -/
theorem waiterOf_back {a b : SystemState} {x v : SeLe4n.ThreadId} (h : CancelFrame a b x)
    (hv : v ≠ x) (hW : ReplyViews.waiterOf b.replyViews v x) :
    ReplyViews.waiterOf a.replyViews v x := by
  obtain ⟨t', ht', hs'⟩ := waiterOf_iff.mp hW
  obtain ⟨t, ht, e1, e2⟩ := h.bwd v t' hv ht'
  refine waiterOf_iff.mpr ⟨t, ht, ?_⟩
  have e : t'.ipcState = t.ipcState := by
    show ThreadIpcState.ofCodes t'.ipcObjectCode t'.ipcStateCode =
      ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode
    rw [e1, e2]
  unfold TCB.blockingServer? at hs' ⊢; rw [← e]; exact hs'

end CancelFrame

-- ============================================================================
-- §5  What the unbind and the cancel keep of the lender's guard
-- ============================================================================

/-- **A step that keeps what a lender's guard reads of the store**: every
thread's two binding codes, every scheduling context, and every reply `K`
admits. -/
structure LoanKept (s s' : SystemState) (K : SeLe4n.ObjId → Reply → Prop) : Prop where
  bind : ∀ (v : SeLe4n.ThreadId) (t : TCB), s.getTcb? v = some t →
    ∃ t', s'.getTcb? v = some t' ∧ t'.scBindingScCode = t.scBindingScCode ∧
      t'.scBindingOwnerCode = t.scBindingOwnerCode
  sc : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext), s.getSchedContext? c = some sc →
    s'.getSchedContext? c = some sc
  reply : ∀ (k : SeLe4n.ObjId) (r : Reply), s.getObject? k = some (.reply r) → K k r →
    s'.getObject? k = some (.reply r)

namespace LoanKept

variable {K : SeLe4n.ObjId → Reply → Prop}

theorem refl (s : SystemState) (K : SeLe4n.ObjId → Reply → Prop) : LoanKept s s K :=
  ⟨fun _ t h => ⟨t, h, rfl, rfl⟩, fun _ _ h => h, fun _ _ h _ => h⟩

theorem trans {a b c : SystemState} (h₁ : LoanKept a b K) (h₂ : LoanKept b c K) :
    LoanKept a c K := by
  refine ⟨fun v t ht => ?_, fun c sc h => h₂.sc c sc (h₁.sc c sc h),
    fun k r hk hK => h₂.reply k r (h₁.reply k r hk hK) hK⟩
  obtain ⟨m, hm, m1, m2⟩ := h₁.bind v t ht
  obtain ⟨n, hn, n1, n2⟩ := h₂.bind v m hm
  exact ⟨n, hn, n1.trans m1, n2.trans m2⟩

theorem mono {a b : SystemState} {K' : SeLe4n.ObjId → Reply → Prop} (h : LoanKept a b K)
    (hK : ∀ k r, K' k r → K k r) : LoanKept a b K' :=
  ⟨h.bind, h.sc, fun k r hk h' => h.reply k r hk (hK k r h')⟩

theorem of_objects_eq {a b : SystemState} (K : SeLe4n.ObjId → Reply → Prop)
    (h : b.objects = a.objects) : LoanKept a b K := by
  have hT : ∀ v, b.getTcb? v = a.getTcb? v := fun v => by unfold SystemState.getTcb?; rw [h]
  refine ⟨fun v t ht => ⟨t, (hT v).trans ht, rfl, rfl⟩, fun c sc hc => ?_, fun k r hk _ => ?_⟩
  · unfold SystemState.getSchedContext? at hc ⊢; rw [h]; exact hc
  · unfold SystemState.getObject? at hk ⊢; rw [h]; exact hk

end LoanKept

/-- **A reply no guard of `x`'s lender reads as `x`'s**: its caller is not `x`,
and a frame it links up to is a reply whose caller is not `x`. -/
def notServerReply (s : SystemState) (x : SeLe4n.ThreadId) (r : Reply) : Prop :=
  r.callerCode ≠ x.val + 1 ∧ ∀ (a : SeLe4n.ReplyId) (ra : Reply), r.next = some (.frame a) →
    s.getObject? a.toObjId = some (.reply ra) → ra.callerCode ≠ x.val + 1

/-- **The replies a step keeps for `x`'s lender**: every reply that is no
reply of `x`'s (`notServerReply`) is one `K` admits. -/
def LoanReplies (s : SystemState) (x : SeLe4n.ThreadId) (K : SeLe4n.ObjId → Reply → Prop) :
    Prop :=
  ∀ (k : SeLe4n.ObjId) (r : Reply), s.getObject? k = some (.reply r) → notServerReply s x r →
    K k r

/-- A reply read through `getReply?` that `K` admits is kept. -/
theorem LoanKept.getReply? {s s' : SystemState} {K : SeLe4n.ObjId → Reply → Prop}
    (h : LoanKept s s' K) {rid : SeLe4n.ReplyId} {r : Reply} (hR : s.getReply? rid = some r)
    (hK : K rid.toObjId r) : s'.getReply? rid = some r := by
  have hO := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hO' := h.reply rid.toObjId r (by unfold SystemState.getObject?; exact hO) hK
  unfold SystemState.getObject? at hO'
  exact (SystemState.getReply?_eq_some_iff _ _ _).mpr hO'

/-- A reply whose caller is the thread `o` has the code `o + 1`. -/
theorem Reply.callerCode_of_caller {r : Reply} {o : SeLe4n.ThreadId} (h : r.caller = some o) :
    r.callerCode = o.val + 1 :=
  (SeLe4n.ThreadId.ofOptCode_eq_some_iff _ _).mp h

/-- **The outer-caller resolution of a context's stack is kept** by a step
keeping the lender's reads: the head reply and the frame below it are no
replies of `x`'s — the head's caller is not `x` (`hHead`) and the frame below
has the outer caller as its caller, not `x` (`hOut`). -/
theorem replyStackOuterCaller?_transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    {K : SeLe4n.ObjId → Reply → Prop} (Lk : LoanKept s s' K) (hK : LoanReplies s x K)
    {c : SeLe4n.SchedContextId} {n : Option SeLe4n.ThreadId}
    (h : replyStackOuterCaller? s c = .ok n)
    (hHead : ∀ (sc : SchedContext) (rid : SeLe4n.ReplyId) (r0 : Reply),
      s.getSchedContext? c = some sc → sc.scReply = some rid → s.getReply? rid = some r0 →
      r0.callerCode ≠ x.val + 1)
    (hOut : ∀ o, n = some o → o ≠ x) :
    replyStackOuterCaller? s' c = .ok n := by
  unfold replyStackOuterCaller? at h ⊢
  cases hS : s.getSchedContext? c with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    rw [Lk.sc c sc hS]
    dsimp only at h ⊢
    unfold donationHeadOf? at h ⊢
    cases hRp : sc.scReply with
    | none => rw [hRp] at h; exact h
    | some rid =>
      rw [hRp] at h
      dsimp only at h ⊢
      cases hR : s.getReply? rid with
      | none => rw [hR] at h; cases h
      | some r0 =>
        rw [hR] at h
        dsimp only at h
        have hn0 : r0.next = some (.head c) := by
          by_cases hne : r0.next = some (.head c)
          · exact hne
          · simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true] at h
            cases h
        have hR0 : (SystemState.getObject? s rid.toObjId) = some (.reply r0) := by
          unfold SystemState.getObject?; exact (SystemState.getReply?_eq_some_iff _ _ _).mp hR
        have hR' := Lk.getReply? hR (hK _ r0 hR0 ⟨hHead sc rid r0 hS hRp hR,
          fun a ra e _ => by rw [hn0] at e; cases e⟩)
        rw [hR']
        simp only [hn0, bne_self_eq_false, Bool.false_eq_true, if_false] at h ⊢
        cases hP : r0.prev with
        | none => rw [hP] at h; exact h
        | some below =>
          rw [hP] at h
          dsimp only at h ⊢
          cases hB : s.getReply? below with
          | none => rw [hB] at h; cases h
          | some b =>
            rw [hB] at h
            dsimp only at h
            have hbn : b.next = some (.frame rid) := by
              by_cases hne : b.next = some (.frame rid)
              · exact hne
              · simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true] at h
                cases h
            simp only [hbn, bne_self_eq_false, Bool.false_eq_true, if_false] at h
            cases hC : b.caller with
            | none => rw [hC] at h; cases h
            | some outer =>
              rw [hC] at h
              cases h
              have hB0 : (SystemState.getObject? s below.toObjId) = some (.reply b) := by
                unfold SystemState.getObject?; exact (SystemState.getReply?_eq_some_iff _ _ _).mp hB
              have hcb : b.callerCode ≠ x.val + 1 := by
                rw [Reply.callerCode_of_caller hC]
                intro e; exact hOut outer rfl (by cases outer; cases x; simp at e; subst e; rfl)
              have hB' := Lk.getReply? hB (hK _ b hB0 ⟨hcb, fun a ra e hra => by
                rw [hbn] at e; cases e
                rw [hR0] at hra; cases hra
                exact hHead sc rid r0 hS hRp hR⟩)
              rw [hB']
              simp only [hbn, bne_self_eq_false, Bool.false_eq_true, if_false, hC]

/-- A thread kept with its two IPC codes is read as blocked on the same
server. -/
theorem replyCallerServerCode_of_codes {t t' : TCB} (h1 : t'.ipcObjectCode = t.ipcObjectCode)
    (h2 : t'.ipcStateCode = t.ipcStateCode) : replyCallerServerCode t' = replyCallerServerCode t := by
  have e : t'.ipcState = t.ipcState := by
    show ThreadIpcState.ofCodes t'.ipcObjectCode t'.ipcStateCode =
      ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode
    rw [h1, h2]
  unfold replyCallerServerCode TCB.blockingServer?; rw [e]

/-- Two reads of one thread are one TCB. -/
theorem getTcb?_some_inj {s : SystemState} {v : SeLe4n.ThreadId} {a b : TCB}
    (ha : s.getTcb? v = some a) (hb : s.getTcb? v = some b) : a = b := by
  rw [ha] at hb; cases hb; rfl

/-- **The donation return's decision is kept** for the server `x` handing a
context back to a caller `w` other than `x`, by a step keeping the lender's
reads, when the reply heading the context is no reply of `x`'s (`hHead`). -/
theorem donatedReturnCommits_transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    {K : SeLe4n.ObjId → Reply → Prop} (C : CancelFrame s s' x) (Lk : LoanKept s s' K)
    (hK : LoanReplies s x K) {c : SeLe4n.SchedContextId} {w : SeLe4n.ThreadId} (hw : w ≠ x)
    (hHead : ∀ (sc : SchedContext) (rid : SeLe4n.ReplyId) (r0 : Reply),
      s.getSchedContext? c = some sc → sc.scReply = some rid → s.getReply? rid = some r0 →
      r0.callerCode ≠ x.val + 1)
    (h : donatedReturnCommits s x c w = true) : donatedReturnCommits s' x c w = true := by
  unfold donatedReturnCommits at h ⊢
  cases hO : replyStackOuterCaller? s c with
  | error e => rw [hO] at h; cases h
  | ok n =>
    rw [hO] at h
    dsimp only at h
    cases hS : s.getSchedContext? c with
    | none => rw [hS] at h; cases h
    | some sc =>
      rw [hS] at h
      dsimp only at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hB, hOut⟩, hRec⟩, hLw⟩, hLx⟩ := h
      have hOutNe : ∀ o, n = some o → o ≠ x := by
        intro o e
        subst e
        unfold outerCallerAcceptable at hOut
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hOut
        exact hOut.1.2
      rw [replyStackOuterCaller?_transport Lk hK hO hHead hOutNe, Lk.sc c sc hS]
      dsimp only
      -- The threads the decision reads: the caller and the server, and the outer caller.
      have hT : ∀ v, v ≠ x → ∀ tv, s.getTcb? v = some tv → ∃ tv', s'.getTcb? v = some tv' ∧
          tv'.schedContextBinding = tv.schedContextBinding ∧ tv'.ipcState = tv.ipcState := by
        intro v hv tv htv
        obtain ⟨tv', h', k⟩ := C.fwd v tv hv htv
        obtain ⟨tv'', h'', b1, b2⟩ := Lk.bind v tv htv
        have e := getTcb?_some_inj h' h''
        subst e
        refine ⟨tv', h', ?_, ?_⟩
        · show SchedContextBinding.ofCodes tv'.scBindingScCode tv'.scBindingOwnerCode =
            SchedContextBinding.ofCodes tv.scBindingScCode tv.scBindingOwnerCode
          rw [b1, b2]
        · show ThreadIpcState.ofCodes tv'.ipcObjectCode tv'.ipcStateCode =
            ThreadIpcState.ofCodes tv.ipcObjectCode tv.ipcStateCode
          rw [k.1, k.2.1]
      have hLook : ∀ v, v ≠ x → (lookupTcb s v).isSome = true → ∃ tv tv',
          lookupTcb s v = some tv ∧ lookupTcb s' v = some tv' ∧
          tv'.schedContextBinding = tv.schedContextBinding := by
        intro v hv hs
        unfold lookupTcb at hs ⊢
        split at hs
        · cases hs
        · rename_i hRes
          rw [if_neg hRes, if_neg hRes]
          cases htv : s.getTcb? v with
          | none => rw [htv] at hs; cases hs
          | some tv =>
            obtain ⟨tv', h', b, -⟩ := hT v hv tv htv
            exact ⟨tv, tv', rfl, h', b⟩
      have hLx' : (lookupTcb s' x).isSome = true := by
        unfold lookupTcb at hLx ⊢
        split at hLx
        · cases hLx
        · rename_i hRes
          rw [if_neg hRes]
          cases htx : s.getTcb? x with
          | none => rw [htx] at hLx; cases hLx
          | some tx =>
            obtain ⟨tx', h', -, -⟩ := Lk.bind x tx htx
            rw [h']; rfl
      obtain ⟨tw, tw', hw1, hw2, hwb⟩ := hLook w hw hLw
      have hRec' : donationRecipientAcceptable s' w = true := by
        unfold donationRecipientAcceptable at hRec ⊢
        rw [hw1] at hRec; rw [hw2]; dsimp only at hRec ⊢; rw [hwb]; exact hRec
      have hOut' : outerCallerAcceptable s' x w n = true := by
        cases n with
        | none => rfl
        | some o =>
          unfold outerCallerAcceptable at hOut ⊢
          simp only [Bool.and_eq_true] at hOut ⊢
          obtain ⟨hne, hM⟩ := hOut
          refine ⟨hne, ?_⟩
          cases hto : s.getTcb? o with
          | none => rw [hto] at hM; cases hM
          | some to =>
            rw [hto] at hM
            obtain ⟨to', h', b, i⟩ := hT o (hOutNe o rfl) to hto
            rw [h']
            dsimp only at hM ⊢
            rw [b, i]; exact hM
      simp only [hB, hOut', hRec', hw2, hLx', Option.isSome_some, Bool.and_self]

/-- **A caller's head pop decision is kept**, for a caller `w` other than `x`
whose reply at `k` names it and whose context the server `x` holds
(`replyHeadHeldByServer`, read with `w`'s server code `x + 1`). -/
theorem replyHeadPopCommits_transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    {K : SeLe4n.ObjId → Reply → Prop} (C : CancelFrame s s' x) (Lk : LoanKept s s' K)
    (hK : LoanReplies s x K) {k : SeLe4n.ObjId} {r : Reply} {w : SeLe4n.ThreadId} {t : TCB}
    (hw : w ≠ x) (hRk : s.getObject? k = some (.reply r)) (hcw : r.callerCode = w.val + 1)
    (hSC : replyCallerServerCode t = x.val + 1) (hHeld : replyHeadHeldByServer s r t = true)
    (hP : replyHeadPopCommits s k r w = true) : replyHeadPopCommits s' k r w = true := by
  unfold replyHeadPopCommits at hP ⊢
  unfold replyHeadHeldByServer at hHeld
  cases hn : r.next with
  | none => rfl
  | some l =>
    rw [hn] at hP hHeld
    cases l with
    | frame a => rfl
    | head c =>
      dsimp only at hP hHeld ⊢
      cases hS : s.getSchedContext? c with
      | none => rw [hS] at hP; cases hP
      | some sc =>
        rw [hS] at hP hHeld
        rw [Lk.sc c sc hS]
        dsimp only at hP hHeld ⊢
        rw [hSC] at hHeld
        have hbx : sc.boundThreadCode = x.val + 1 := beq_iff_eq.mp hHeld
        rw [hbx] at hP ⊢
        dsimp only at hP ⊢
        simp only [Bool.and_eq_true] at hP ⊢
        obtain ⟨⟨hRid, hHt⟩, hD⟩ := hP
        have hxx : (⟨x.val⟩ : SeLe4n.ThreadId) = x := rfl
        rw [hxx] at hHt hD ⊢
        refine ⟨⟨hRid, ?_⟩, ?_⟩
        · cases hX : s.getTcb? x with
          | none => rw [hX] at hHt; cases hHt
          | some ht =>
            rw [hX] at hHt
            obtain ⟨ht', h', b1, b2⟩ := Lk.bind x ht hX
            rw [h']; dsimp only at hHt ⊢; rw [b1, b2]; exact hHt
        · refine donatedReturnCommits_transport C Lk hK hw (fun sc' rid r0 hS' hR' hG => ?_) hD
          rw [hS] at hS'; cases hS'
          rw [hR'] at hRid
          dsimp only at hRid
          have hk : rid.toObjId = k := by
            cases rid; cases k; simp only [beq_iff_eq] at hRid; subst hRid; rfl
          have hO := (SystemState.getReply?_eq_some_iff _ _ _).mp hG
          unfold SystemState.getObject? at hRk
          rw [hk, hRk] at hO; cases hO
          rw [hcw]; intro e; exact hw (by cases w; cases x; simp at e; subst e; rfl)

/-- **A caller's guard as `x`'s waiter is kept** by a step keeping every plain
waiter and the lender's reads, for a caller `w` other than `x`, kept as
`TCB.cancelKeptBy` reads it, whose reply links up to no frame. -/
theorem replyWaiterEndable_transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    {K : SeLe4n.ObjId → Reply → Prop} (C : CancelFrame s s' x) (Lk : LoanKept s s' K)
    (hK : LoanReplies s x K) {w : SeLe4n.ThreadId} {t t' : TCB} {r : Reply} (hw : w ≠ x)
    (kt : TCB.cancelKeptBy t' t)
    (hR : s.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r))
    (hN : ∀ a, r.next ≠ some (.frame a)) (hG : replyWaiterEndable s x w t = true) :
    replyWaiterEndable s' x w t' = true := by
  obtain ⟨k1, k2, k3, k4, -, k6, k7⟩ := kt
  have hSC' := replyCallerServerCode_of_codes k1 k2
  unfold replyWaiterEndable replyCallerCancelAdmitted at hG ⊢
  rw [hR] at hG
  dsimp only at hG
  simp only [Bool.and_eq_true] at hG
  obtain ⟨⟨hwx, hsc⟩, ⟨hc, hF⟩, hH⟩ := hG
  have hcw : r.callerCode = w.val + 1 := beq_iff_eq.mp hc
  have hr' : s'.getObject? ⟨t'.replyObjectCode - 1⟩ = some (.reply r) := by
    rw [k3]
    refine Lk.reply _ r hR (hK _ r hR ⟨?_, fun a _ e => absurd e (hN a)⟩)
    rw [hcw]; intro e; exact hw (by cases w; cases x; simp at e; subst e; rfl)
  rw [hr']
  dsimp only
  have hSCx : replyCallerServerCode t = x.val + 1 := beq_iff_eq.mp hsc
  have hH' : replyHeadHeldByServer s' r t' = true := by
    unfold replyHeadHeldByServer at hH ⊢
    cases hn : r.next with
    | none => rfl
    | some l =>
      rw [hn] at hH
      cases l with
      | frame _ => rfl
      | head c =>
        dsimp only at hH ⊢
        cases hS : s.getSchedContext? c with
        | none => rw [hS] at hH; cases hH
        | some sc => rw [hS] at hH; rw [Lk.sc c sc hS, hSC']; exact hH
  have hF' : replyCallerFinalisable s' ⟨t'.replyObjectCode - 1⟩ r w t' = true := by
    rw [k3]
    unfold replyCallerFinalisable at hF ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hP, hRes⟩, hId⟩, hRun⟩, hSt⟩, hRO⟩, hQN⟩, hQP⟩, hTB⟩ := hF
    obtain ⟨q1, q2⟩ := k7 hQN hQP
    exact ⟨⟨⟨⟨⟨⟨⟨⟨replyHeadPopCommits_transport C Lk hK hw hR hcw hSCx hH hP, hRes⟩, hId⟩,
      k6 hRun⟩, k2 ▸ hSt⟩, k3 ▸ hRO⟩, q1⟩, q2⟩, k4 ▸ hTB⟩
  rw [hSC']
  simp only [hwx, hsc, hc, hF', hH', Bool.and_self]

/-- **`x`'s lender stays endable** across a step keeping every plain waiter and
the lender's reads, which keeps `x`'s owner code (`ho`). -/
theorem lenderEndable_transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    {K : SeLe4n.ObjId → Reply → Prop} (C : CancelFrame s s' x) (Lk : LoanKept s s' K)
    (hK : LoanReplies s x K) {tx tx' : TCB}
    (ho : tx'.scBindingOwnerCode = tx.scBindingOwnerCode) (hL : lenderEndable s x tx) :
    lenderEndable s' x tx' := by
  intro o hO
  obtain ⟨tl, r, hT, hRl, hNh, hE⟩ := hL o (ho ▸ hO)
  have hN := lenderEndable.noFrame hNh
  have hLx : (⟨o⟩ : SeLe4n.ThreadId) ≠ x := by
    intro e
    unfold replyWaiterEndable at hE
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hE
    exact hE.1.1 (by rw [← e])
  obtain ⟨tl', hT', kt⟩ := C.fwd _ tl hLx hT
  have hcw : r.callerCode ≠ x.val + 1 := by
    unfold replyWaiterEndable replyCallerCancelAdmitted at hE
    rw [hRl] at hE
    simp only [Bool.and_eq_true, beq_iff_eq] at hE
    rw [hE.2.1.1]; intro e; exact hLx (by cases x; simp at e; subst e; rfl)
  refine ⟨tl', r, hT', ?_, hNh, replyWaiterEndable_transport C Lk hK hLx kt hRl hN hE⟩
  rw [kt.2.2.1]
  exact Lk.reply _ r hRl (hK _ r hRl ⟨hcw, fun a _ e => absurd e (hN a)⟩)

-- ============================================================================
-- §6  The two frames across one write
-- ============================================================================

/-- **A thread update writes nothing of another kind**: an object that is no
thread is kept. -/
theorem updateTcb_keeps_nonTcb (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) {k : SeLe4n.ObjId} {o : KernelObject}
    (hk : st.objects[k]? = some o) (hno : ∀ t, o ≠ .tcb t) :
    (st.updateTcb w f).objects[k]? = some o := by
  by_cases hkw : w.toObjId = k
  · subst hkw
    have hN : st.getTcb? w = none := by
      cases hT : st.getTcb? w with
      | none => rfl
      | some t => rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT] at hk; cases hk; exact absurd rfl (hno t)
    rw [SystemState.updateTcb_eq_self_of_none hN]; exact hk
  · rw [SystemState.updateTcb_objects_ne st w f k hkw hInv]; exact hk

/-- **A thread update keeps both frames**, when it keeps, of a thread other
than `x`, what the cancel frame reads, and of every thread its binding codes. -/
theorem CancelFrame.updateTcb (st : SystemState) (w x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : w ≠ x → ∀ t, st.getTcb? w = some t → TCB.cancelKeptBy (f t) t ∧
      (f t).ipcObjectCode = t.ipcObjectCode ∧ (f t).ipcStateCode = t.ipcStateCode) :
    CancelFrame st (st.updateTcb w f) x := by
  refine ⟨fun v t hv ht => ?_, fun v t' hv ht' => ?_, fun k r hk hn _ => ?_⟩
  · by_cases hvw : v = w
    · subst hvw
      rw [SystemState.updateTcb_getTcb?_self st v f hInv, ht]
      exact ⟨f t, rfl, (hf hv t ht).1⟩
    · rw [SystemState.updateTcb_getTcb?_ne st w f hInv v (SeLe4n.Kernel.threadId_toObjId_ne hvw)]
      exact ⟨t, ht, .refl t⟩
  · by_cases hvw : v = w
    · subst hvw
      rw [SystemState.updateTcb_getTcb?_self st v f hInv] at ht'
      cases ht : st.getTcb? v with
      | none => rw [ht] at ht'; cases ht'
      | some t =>
        rw [ht] at ht'; cases ht'
        obtain ⟨-, e1, e2⟩ := hf hv t ht
        exact ⟨t, rfl, e1, e2⟩
    · rw [SystemState.updateTcb_getTcb?_ne st w f hInv v (SeLe4n.Kernel.threadId_toObjId_ne hvw)] at ht'
      exact ⟨t', ht', rfl, rfl⟩
  · unfold SystemState.getObject? at hk ⊢
    exact ⟨r, updateTcb_keeps_nonTcb st w f hInv hk (fun _ e => KernelObject.noConfusion e), rfl, hn⟩

theorem LoanKept.updateTcb (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (K : SeLe4n.ObjId → Reply → Prop)
    (hb : ∀ t, st.getTcb? w = some t → (f t).scBindingScCode = t.scBindingScCode ∧
      (f t).scBindingOwnerCode = t.scBindingOwnerCode) :
    LoanKept st (st.updateTcb w f) K := by
  refine ⟨fun v t ht => ?_, fun c sc hc => ?_, fun k r hk _ => ?_⟩
  · by_cases hvw : v = w
    · subst hvw
      rw [SystemState.updateTcb_getTcb?_self st v f hInv, ht]
      exact ⟨f t, rfl, hb t ht⟩
    · rw [SystemState.updateTcb_getTcb?_ne st w f hInv v (SeLe4n.Kernel.threadId_toObjId_ne hvw)]
      exact ⟨t, ht, rfl, rfl⟩
  · rw [SystemState.getSchedContext?_eq_some_iff] at hc ⊢
    exact updateTcb_keeps_nonTcb st w f hInv hc (fun _ e => KernelObject.noConfusion e)
  · unfold SystemState.getObject? at hk ⊢
    exact updateTcb_keeps_nonTcb st w f hInv hk (fun _ e => KernelObject.noConfusion e)

/-- **An object write that keeps every thread, reply and scheduling context**:
its function is the identity, or maps an object of none of those kinds to one
of none of them. -/
def keepsThreadReplyContext (f : KernelObject → KernelObject) : Prop :=
  ∀ o, f o = o ∨ ((∀ t, o ≠ .tcb t) ∧ (∀ t, f o ≠ .tcb t) ∧ (∀ r, o ≠ .reply r) ∧
    (∀ r, f o ≠ .reply r) ∧ (∀ sc, o ≠ .schedContext sc) ∧ (∀ sc, f o ≠ .schedContext sc))

/-- An endpoint or notification rewrite keeps every thread, reply and
scheduling context. -/
theorem keepsThreadReplyContext.of_kind {f : KernelObject → KernelObject}
    (hE : ∀ o, (∃ e, o = .endpoint e) ∨ (∃ n, o = .notification n) ∨ f o = o)
    (hK : ∀ o, (∃ e, o = .endpoint e) ∨ (∃ n, o = .notification n) →
      (∃ e, f o = .endpoint e) ∨ (∃ n, f o = .notification n)) :
    keepsThreadReplyContext f := by
  intro o
  rcases hE o with h | h | h
  · refine Or.inr ?_
    obtain ⟨e, rfl⟩ := h
    rcases hK _ (Or.inl ⟨e, rfl⟩) with ⟨e', h'⟩ | ⟨n', h'⟩ <;> rw [h'] <;>
      exact ⟨fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c,
        fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c,
        fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c⟩
  · refine Or.inr ?_
    obtain ⟨n, rfl⟩ := h
    rcases hK _ (Or.inr ⟨n, rfl⟩) with ⟨e', h'⟩ | ⟨n', h'⟩ <;> rw [h'] <;>
      exact ⟨fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c,
        fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c,
        fun _ c => KernelObject.noConfusion c, fun _ c => KernelObject.noConfusion c⟩
  · exact Or.inl h

/-- **Such a write keeps every thread, reply and scheduling context**, read at
any key. -/
theorem modifyObject_keepsKinds (st : SystemState) (k : SeLe4n.ObjId)
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) (hf : keepsThreadReplyContext f)
    (y : SeLe4n.ObjId) {o : KernelObject} (hKind : (∃ t, o = .tcb t) ∨ (∃ r, o = .reply r) ∨
      (∃ sc, o = .schedContext sc)) :
    (st.modifyObject k f).objects[y]? = some o ↔ st.objects[y]? = some o := by
  rw [modifyObject_objects_getElem hInv y]
  split
  · rename_i hky
    subst hky
    cases hO : st.objects[k]? with
    | none => simp
    | some o0 =>
      simp only [Option.map_some, Option.some.injEq]
      rcases hf o0 with e | ⟨h1, h2, h3, h4, h5, h6⟩
      · rw [e]
      · constructor
        · intro e
          rcases hKind with ⟨t, rfl⟩ | ⟨r, rfl⟩ | ⟨sc, rfl⟩
          · exact absurd e (h2 t)
          · exact absurd e (h4 r)
          · exact absurd e (h6 sc)
        · intro e
          rcases hKind with ⟨t, rfl⟩ | ⟨r, rfl⟩ | ⟨sc, rfl⟩
          · exact absurd e (h1 t)
          · exact absurd e (h3 r)
          · exact absurd e (h5 sc)
  · exact Iff.rfl

theorem CancelFrame.modifyObject (st : SystemState) (k : SeLe4n.ObjId) (x : SeLe4n.ThreadId)
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) (hf : keepsThreadReplyContext f) :
    CancelFrame st (st.modifyObject k f) x := by
  have hT : ∀ v t, (st.modifyObject k f).getTcb? v = some t ↔ st.getTcb? v = some t := fun v t => by
    rw [SystemState.getTcb?_eq_some_iff, SystemState.getTcb?_eq_some_iff]
    exact modifyObject_keepsKinds st k hInv hf _ (Or.inl ⟨t, rfl⟩)
  refine ⟨fun v t _ ht => ⟨t, (hT v t).mpr ht, .refl t⟩,
    fun v t _ ht => ⟨t, (hT v t).mp ht, rfl, rfl⟩, fun y r hk hn _ => ⟨r, ?_, rfl, hn⟩⟩
  unfold SystemState.getObject? at hk ⊢
  exact (modifyObject_keepsKinds st k hInv hf _ (Or.inr (Or.inl ⟨r, rfl⟩))).mpr hk

theorem LoanKept.modifyObject (st : SystemState) (k : SeLe4n.ObjId)
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) (hf : keepsThreadReplyContext f)
    (K : SeLe4n.ObjId → Reply → Prop) : LoanKept st (st.modifyObject k f) K := by
  refine ⟨fun v t ht => ⟨t, ?_, rfl, rfl⟩, fun c sc hc => ?_, fun y r hk _ => ?_⟩
  · rw [SystemState.getTcb?_eq_some_iff] at ht ⊢
    exact (modifyObject_keepsKinds st k hInv hf _ (Or.inl ⟨t, rfl⟩)).mpr ht
  · rw [SystemState.getSchedContext?_eq_some_iff] at hc ⊢
    exact (modifyObject_keepsKinds st k hInv hf _ (Or.inr (Or.inr ⟨sc, rfl⟩))).mpr hc
  · unfold SystemState.getObject? at hk ⊢
    exact (modifyObject_keepsKinds st k hInv hf _ (Or.inr (Or.inl ⟨r, rfl⟩))).mpr hk

-- ============================================================================
-- §7  The notification unbind keeps both frames
-- ============================================================================

/-- **A step keeping the cancel's reads keeps the waiters' frame**: it moves a
thread's bound-notification code alone, which no plain waiter's guard reads. -/
theorem CancelReadsKept.cancelFrame {s s' : SystemState} (h : CancelReadsKept s' s)
    (x : SeLe4n.ThreadId) : CancelFrame s s' x := by
  refine ⟨fun v t _ ht => ?_, fun v t' _ ht' => ?_, fun k r hk hn _ => ⟨r, ?_, rfl, hn⟩⟩
  · rcases h.getTcb? v with ⟨e1, -⟩ | ⟨t0, b, e1, e2⟩
    · rw [e1] at ht; cases ht
    · rw [e1] at ht; cases ht
      exact ⟨_, e2, ⟨rfl, rfl, rfl, rfl, rfl, id, fun a b => ⟨a, b⟩⟩⟩
  · rcases h.getTcb? v with ⟨-, e2⟩ | ⟨t0, b, e1, e2⟩
    · rw [e2] at ht'; cases ht'
    · rw [e2] at ht'; cases ht'
      exact ⟨t0, e1, rfl, rfl⟩
  · unfold SystemState.getObject? at hk ⊢
    exact (h.reply k r).mpr hk

/-- **A step keeping the cancel's reads keeps the lender's reads.** -/
theorem CancelReadsKept.loanKept {s s' : SystemState} (h : CancelReadsKept s' s)
    (K : SeLe4n.ObjId → Reply → Prop) : LoanKept s s' K := by
  refine ⟨fun v t ht => ?_, fun c sc hc => by rw [h.schedContext c]; exact hc,
    fun k r hk _ => ?_⟩
  · rcases h.getTcb? v with ⟨e1, -⟩ | ⟨t0, b, e1, e2⟩
    · rw [e1] at ht; cases ht
    · rw [e1] at ht; cases ht
      exact ⟨_, e2, rfl, rfl⟩
  · unfold SystemState.getObject? at hk ⊢
    exact (h.reply k r).mpr hk

/-- **The notification unbind keeps both frames**, on a state whose admission
admits it: it writes nothing a plain waiter's guard or the lender's guard
reads. -/
theorem finaliseThreadUnbindNotification_frames (st : SystemState) (x : SeLe4n.ThreadId)
    {t : TCB} (hInv : st.objects.invExt) (hX : st.getTcb? x = some t)
    (hG : notificationUnbindAdmitted st x t = true) (K : SeLe4n.ObjId → Reply → Prop) :
    CancelFrame st (finaliseThreadUnbindNotification st x) x ∧
      LoanKept st (finaliseThreadUnbindNotification st x) K :=
  have h := finaliseThreadUnbindNotification_readsKept st x hInv hX hG
  ⟨h.cancelFrame x, h.loanKept K⟩

-- ============================================================================
-- §8  The notification and endpoint cancels keep both frames
-- ============================================================================

/-- **A step keeping every reply and scheduling context**, read at any key. -/
def replyContextKept (s s' : SystemState) : Prop :=
  ∀ (k : SeLe4n.ObjId) (o : KernelObject), s.objects[k]? = some o →
    ((∃ r, o = .reply r) ∨ ∃ sc, o = .schedContext sc) → s'.objects[k]? = some o

namespace replyContextKept

theorem refl (s : SystemState) : replyContextKept s s := fun _ _ h _ => h

theorem trans {a b c : SystemState} (h₁ : replyContextKept a b) (h₂ : replyContextKept b c) :
    replyContextKept a c := fun k o h hk => h₂ k o (h₁ k o h hk) hk

theorem updateTcb (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : replyContextKept st (st.updateTcb w f) := by
  intro k o h hk
  refine updateTcb_keeps_nonTcb st w f hInv h (fun t e => ?_)
  rcases hk with ⟨r, rfl⟩ | ⟨sc, rfl⟩ <;> cases e

theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt) (hf : keepsThreadReplyContext f) :
    replyContextKept st (st.modifyObject k f) := by
  intro y o h hk
  refine (modifyObject_keepsKinds st k hInv hf y ?_).mpr h
  rcases hk with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

end replyContextKept

/-- **A step keeping every scheduling context and every reply `K` admits.** -/
def replyContextKeptBy (K : SeLe4n.ObjId → Reply → Prop) (s s' : SystemState) : Prop :=
  ∀ (k : SeLe4n.ObjId) (o : KernelObject), s.objects[k]? = some o →
    ((∃ r, o = .reply r ∧ K k r) ∨ ∃ sc, o = .schedContext sc) → s'.objects[k]? = some o

theorem replyContextKeptBy.trans {K : SeLe4n.ObjId → Reply → Prop} {a b c : SystemState}
    (h₁ : replyContextKeptBy K a b) (h₂ : replyContextKeptBy K b c) : replyContextKeptBy K a c :=
  fun k o h hk => h₂ k o (h₁ k o h hk) hk

/-- A step keeping every reply keeps every reply `K` admits. -/
theorem replyContextKept.by {s s' : SystemState} (h : replyContextKept s s')
    (K : SeLe4n.ObjId → Reply → Prop) : replyContextKeptBy K s s' := by
  intro k o ho hk
  refine h k o ho ?_
  rcases hk with ⟨r, e, -⟩ | e
  · exact Or.inl ⟨r, e⟩
  · exact Or.inr e

/-- **A step writing none of the scheduling links and keeping every reply and
context keeps the lender's reads.** -/
theorem LoanKept.of_schedLinkFrame {s s' : SystemState} {K : SeLe4n.ObjId → Reply → Prop}
    (F : SchedLinkFrame s s') (hk : replyContextKeptBy K s s') : LoanKept s s' K := by
  refine ⟨fun v t ht => ?_, fun c sc hc => ?_, fun k r hr hK => ?_⟩
  · have e := F.binding v.toObjId
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp ht] at e
    cases h' : s'.objects[v.toObjId]? with
    | none => rw [h'] at e; cases e
    | some o =>
      rw [h'] at e
      cases o with
      | tcb t' =>
        simp only [schedBindingLinksOf, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
        exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h', e.1, e.2⟩
      | schedContext _ => cases e
      | _ => cases e
  · rw [SystemState.getSchedContext?_eq_some_iff] at hc ⊢
    exact hk _ _ hc (Or.inr ⟨sc, rfl⟩)
  · unfold SystemState.getObject? at hr ⊢
    exact hk _ _ hr (Or.inl ⟨r, rfl, hK⟩)

/-- **A notification-queue unlink keeps both frames**: it rewrites
notifications and the threads' notification links alone. -/
theorem ntfnUnlinkReach_frames {s s' : SystemState} (h : ntfnUnlinkReach s s')
    (x : SeLe4n.ThreadId) : CancelFrame s s' x ∧ replyContextKept s s' := by
  have hKind : replyContextKept s s' := by
    intro k o hk hko
    rcases h.2 k with e | ⟨n, n', h0, -, -⟩ | ⟨t, t', h0, -, -⟩
    · rw [e]; exact hk
    · rw [hk] at h0; cases h0
      rcases hko with ⟨_, e⟩ | ⟨_, e⟩ <;> cases e
    · rw [hk] at h0; cases h0
      rcases hko with ⟨_, e⟩ | ⟨_, e⟩ <;> cases e
  refine ⟨⟨fun v t _ ht => ?_, fun v t' _ ht' => ?_, fun k r hk hn _ => ⟨r, ?_, rfl, hn⟩⟩, hKind⟩
  · have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    rcases h.2 v.toObjId with e | ⟨n, n', h0, -, -⟩ | ⟨t0, t1, h0, h1, np, nn, e⟩
    · exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (e.trans hO), .refl t⟩
    · rw [hO] at h0; cases h0
    · rw [hO] at h0; cases h0
      exact ⟨t1, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h1, by
        subst e; exact ⟨rfl, rfl, rfl, rfl, rfl, id, fun a b => ⟨a, b⟩⟩⟩
  · have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht'
    rcases h.2 v.toObjId with e | ⟨n, n', -, h1, -⟩ | ⟨t0, t1, h0, h1, np, nn, e⟩
    · exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr (e.symm.trans hO), rfl, rfl⟩
    · rw [hO] at h1; cases h1
    · rw [hO] at h1; cases h1
      exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0, by subst e; rfl, by subst e; rfl⟩
  · unfold SystemState.getObject? at hk ⊢
    exact hKind k _ hk (Or.inl ⟨r, rfl⟩)

/-- **The notification cancel keeps both frames**: the unlink, then the
cancelled thread's own restore. -/
theorem notificationCancel_frames (st : SystemState) (x : SeLe4n.ThreadId) (tcb : TCB)
    (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (hB : tcb.ipcState = .blockedOnNotification n) (K : SeLe4n.ObjId → Reply → Prop) :
    CancelFrame st (Lifecycle.Suspend.cancelIpcBlocking st x tcb) x ∧
      LoanKept st (Lifecycle.Suspend.cancelIpcBlocking st x tcb) K := by
  have F := SchedLinkFrame.notificationCancel st x tcb n hInv hB
  have hEq : Lifecycle.Suspend.cancelIpcBlocking st x tcb =
      Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue st x) x := by
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  rw [hEq] at F ⊢
  have hR := removeFromNotificationWaitQueue_reach st x hInv
  obtain ⟨C1, k1⟩ := ntfnUnlinkReach_frames hR x
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging at F ⊢
  refine ⟨C1.trans (CancelFrame.updateTcb _ x x _ hR.1 (fun h => absurd rfl h)),
    LoanKept.of_schedLinkFrame F ((k1.trans (replyContextKept.updateTcb _ x _ hR.1)).by K)⟩

/-- An endpoint rewrite keeps every thread, reply and scheduling context. -/
theorem keepsThreadReplyContext.endpoint {f : KernelObject → KernelObject}
    (hE : ∀ e, ∃ e', f (.endpoint e) = .endpoint e')
    (hO : ∀ o, (∀ e, o ≠ .endpoint e) → f o = o) : keepsThreadReplyContext f :=
  keepsThreadReplyContext.of_kind
    (fun o => by
      by_cases h : ∃ e, o = .endpoint e
      · exact Or.inl h
      · exact Or.inr (Or.inr (hO o (fun e he => h ⟨e, he⟩))))
    (fun o h => by
      rcases h with ⟨e, rfl⟩ | ⟨n, rfl⟩
      · exact Or.inl (hE e)
      · exact Or.inr ⟨n, hO _ (fun _ e => by cases e)⟩)

/-- **The removal of `x` from an endpoint queue keeps both frames**: it writes
the endpoint, `x`, and `x`'s two neighbours' queue links — a neighbour linked to
`x` (the removal's own check for the predecessor, the queue's link integrity
for the successor), so linked into a queue, which no plain waiter is. -/
theorem storeQueueRemove_frames (st : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (x : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt)
    (hL : tcbQueueLinkIntegrity st) (hX : st.getTcb? x = some tcb)
    (hG : queueRemoveInPlace st e q x ep tcb = true) :
    CancelFrame st (storeQueueRemove st e q x ep tcb) x ∧
      replyContextKept st (storeQueueRemove st e q x ep tcb) := by
  have hKE : ∀ c, keepsThreadReplyContext (headAdvancedEndpoint q c) := fun c =>
    keepsThreadReplyContext.endpoint (fun e => by simp only [headAdvancedEndpoint]; exact ⟨_, rfl⟩)
      (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _))
  have hKS : ∀ h t, keepsThreadReplyContext (endsSetEndpoint q h t) := fun h t =>
    keepsThreadReplyContext.endpoint (fun e => by simp only [endsSetEndpoint]; exact ⟨_, rfl⟩)
      (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _))
  -- The predecessor's write.
  have h1 : (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st).objects.invExt ∧
      CancelFrame st (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) x ∧
      replyContextKept st (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) ∧
      ∀ (v : SeLe4n.ThreadId) (t : TCB), (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st).getTcb? v = some t →
        ∃ t0, st.getTcb? v = some t0 ∧ t.queuePrevCode = t0.queuePrevCode := by
    split
    · refine ⟨modifyObject_preserves_objects_invExt hInv,
        CancelFrame.modifyObject st e x hInv (hKE _), replyContextKept.modifyObject st e hInv (hKE _),
        fun v t ht => ⟨t, ?_, rfl⟩⟩
      rw [SystemState.getTcb?_eq_some_iff] at ht ⊢
      exact (modifyObject_keepsKinds st e hInv (hKE _) _ (Or.inl ⟨t, rfl⟩)).mp ht
    · rename_i p hP
      have hPre : ∃ pt, st.getTcb? p = some pt ∧ pt.queueNext = some x := by
        unfold queueRemoveInPlace at hG
        rw [hP] at hG
        simp only [Bool.and_eq_true] at hG
        have h' := hG.1.2.2.2
        cases hp : st.getTcb? p with
        | none => rw [hp] at h'; cases h'
        | some pt => rw [hp] at h'; exact ⟨pt, rfl, by simpa using h'⟩
      obtain ⟨pt, hpt, hpn⟩ := hPre
      refine ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv,
        CancelFrame.updateTcb st p x _ hInv (fun _ t ht => ?_), replyContextKept.updateTcb st p _ hInv,
        fun v t ht => ?_⟩
      · rw [hpt] at ht; cases ht
        have hc : pt.queueNextCode = x.val + 1 := by
          have := congrArg SeLe4n.ThreadId.optCode hpn
          rw [TCB.optCode_queueNext] at this; exact this
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl, id, fun a _ => absurd a (by rw [hc]; omega)⟩, rfl, rfl⟩
      · by_cases hvp : v = p
        · subst hvp
          rw [SystemState.updateTcb_getTcb?_self st v _ hInv, hpt] at ht; cases ht
          exact ⟨pt, hpt, rfl⟩
        · rw [SystemState.updateTcb_getTcb?_ne st p _ hInv v
            (SeLe4n.Kernel.threadId_toObjId_ne hvp)] at ht
          exact ⟨t, ht, rfl⟩
    · exact ⟨hInv, .refl st x, .refl st, fun v t ht => ⟨t, ht, rfl⟩⟩
  -- The successor's write.
  have h2 : ∀ s1 : SystemState, s1.objects.invExt → CancelFrame st s1 x → replyContextKept st s1 →
      (∀ (v : SeLe4n.ThreadId) (t : TCB), s1.getTcb? v = some t →
        ∃ t0, st.getTcb? v = some t0 ∧ t.queuePrevCode = t0.queuePrevCode) →
      (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1).objects.invExt ∧
      CancelFrame st (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1) x ∧
      replyContextKept st (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1) := by
    intro s1 i1 c1 k1 b1
    split
    · rename_i n hn
      obtain ⟨tn, htn, hnp⟩ := hL.1 x tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX) n hn
      refine ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ i1,
        c1.trans (CancelFrame.updateTcb s1 n x _ i1 (fun _ t ht => ?_)),
        k1.trans (replyContextKept.updateTcb s1 n _ i1)⟩
      obtain ⟨t0, h0, e0⟩ := b1 n t ht
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr htn] at h0; cases h0
      have hc : t.queuePrevCode = x.val + 1 := by
        rw [e0]
        have := congrArg SeLe4n.ThreadId.optCode hnp
        rw [TCB.optCode_queuePrev] at this; exact this
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, id, fun _ b => absurd b (by rw [hc]; omega)⟩, rfl, rfl⟩
    · exact ⟨i1, c1, k1⟩
  have hFin : ∀ (s2 : SystemState) (h t : Nat), s2.objects.invExt → CancelFrame st s2 x →
      replyContextKept st s2 →
      CancelFrame st ((s2.modifyObject e (endsSetEndpoint q h t)).updateTcb x tcbOffQueue) x ∧
        replyContextKept st ((s2.modifyObject e (endsSetEndpoint q h t)).updateTcb x tcbOffQueue) := by
    intro s2 h t i2 c2 k2
    have i3 := modifyObject_preserves_objects_invExt (k := e) (f := endsSetEndpoint q h t) i2
    exact ⟨(c2.trans (CancelFrame.modifyObject s2 e x i2 (hKS _ _))).trans
        (CancelFrame.updateTcb _ x x _ i3 (fun h => absurd rfl h)),
      (k2.trans (replyContextKept.modifyObject s2 e i2 (hKS _ _))).trans
        (replyContextKept.updateTcb _ x _ i3)⟩
  obtain ⟨i1, c1, k1, b1⟩ := h1
  have r := h2 _ i1 c1 k1 b1
  unfold storeQueueRemove
  exact hFin _ _ _ r.1 r.2.1 r.2.2

/-- **The endpoint cancel keeps both frames**: the removal, then the cancelled
thread's own rewrite. -/
theorem storeEndpointBlockedCancelled_frames (st : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (x : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt)
    (hL : tcbQueueLinkIntegrity st) (hX : st.getTcb? x = some tcb)
    (hG : queueRemoveInPlace st e q x ep tcb = true) (K : SeLe4n.ObjId → Reply → Prop) :
    CancelFrame st (storeEndpointBlockedCancelled st e q x ep tcb) x ∧
      LoanKept st (storeEndpointBlockedCancelled st e q x ep tcb) K := by
  obtain ⟨C, k⟩ := storeQueueRemove_frames st e q x ep tcb hInv hL hX hG
  have I := (FinaliseFrame.storeQueueRemove st e q x ep tcb hInv).invExt
  have F := SchedLinkFrame.storeEndpointBlockedCancelled st e q x ep tcb hInv
  unfold storeEndpointBlockedCancelled at F ⊢
  exact ⟨C.trans (CancelFrame.updateTcb _ x x _ I (fun h => absurd rfl h)),
    LoanKept.of_schedLinkFrame F ((k.trans (replyContextKept.updateTcb _ x _ I)).by K)⟩

-- ============================================================================
-- §9  What the finalisation keeps of the thread's own binding
-- ============================================================================

/-- **The thread `x`'s context is bound back to it**: a nonzero context code
names a context whose bound-thread code is `x`'s. -/
def bindingBack (s : SystemState) (x : SeLe4n.ThreadId) : Prop :=
  ∀ tx, s.getTcb? x = some tx → tx.scBindingScCode ≠ 0 →
    ∃ sc, s.getSchedContext? ⟨tx.scBindingScCode - 1⟩ = some sc ∧ sc.boundThreadCode = x.val + 1

/-- A step agreeing on the bindings keeps a context bound back. -/
theorem bindingBack.transport {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : bindingLinksAgree s s') (hB : bindingBack s x) : bindingBack s' x := by
  intro tx' hX' hc
  obtain ⟨tx, hX, e1, -⟩ := h.getTcb?_back hX'
  obtain ⟨sc, hS, hb⟩ := hB tx hX (by rw [← e1]; exact hc)
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
      (descheduleUnboundHolder_replenishQueueOnCore st (cancelIpcBlockingMigrated c t st) c t)
  have FR := SchedLinkFrame.finaliseReplyRevert _ t.blockingServer?
    (cancelIpcBlockingReclaimed_objects_invExt c t st hInvC)
  rw [hRet] at F
  exact ((bindingLinksAgree.trans F.binding (bindingLinksAgree.of_objects_eq
    (cancelIpcBlockingMigrated_objects c t st))).trans FD.binding).trans FR.binding

/-- **The replies a cancel of `c`'s reply keeps for a lender**: every reply but
`c`'s own (at `rid`) and a frame linking up to it. -/
def offCallerReply (rid : SeLe4n.ReplyId) (k : SeLe4n.ObjId) (r : Reply) : Prop :=
  k ≠ rid.toObjId ∧ r.next ≠ some (.frame rid)

/-- **The restore, consume, unlink and revert of a cancelled caller `c` keep every
context and every reply but `c`'s own**: they write threads, and the consume
`c`'s reply. -/
theorem replyCancelRest_kept (s0 : SystemState) (hI0 : s0.objects.invExt) (c : SeLe4n.ThreadId)
    (t t0 : TCB) {rid : SeLe4n.ReplyId} {r0 : Reply} (hRO : t.replyObject = some rid)
    (hT0 : s0.getTcb? c = some t0) (hR0 : s0.objects[rid.toObjId]? = some (.reply r0))
    (hInvC : (SystemState.unlinkReplyWaiterOpt
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 c) c t)
      c t.blockingServer?).objects.invExt) :
    replyContextKeptBy (offCallerReply rid) s0 (finaliseReplyRevert
      (SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 c) c t)
        c t.blockingServer?) t.blockingServer?) := by
  have hNT : ∀ (k : SeLe4n.ObjId) (o : KernelObject), ((∃ r, o = .reply r ∧ offCallerReply rid k r) ∨
      ∃ sc, o = .schedContext sc) → ∀ tt, o ≠ .tcb tt := fun k o h tt e => by
    subst e; rcases h with ⟨_, e, -⟩ | ⟨_, e⟩ <;> cases e
  have k1 : replyContextKeptBy (offCallerReply rid) s0
      (Lifecycle.Suspend.restoreToReadyCancelled s0 c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact (replyContextKept.updateTcb s0 c _ hI0).by _
  have hI1 : (Lifecycle.Suspend.restoreToReadyCancelled s0 c).objects.invExt :=
    Lifecycle.Suspend.restoreToReadyStaging_invExt s0 c _ hI0
  have hR1 : (Lifecycle.Suspend.restoreToReadyCancelled s0 c).objects[rid.toObjId]? =
      some (.reply r0) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact updateTcb_keeps_nonTcb s0 c _ hI0 hR0 (fun _ e => by cases e)
  have hC1 : ∃ tw, (Lifecycle.Suspend.restoreToReadyCancelled s0 c).objects[c.toObjId]? =
      some (.tcb tw) := by
    have h : ∃ tw, (Lifecycle.Suspend.restoreToReadyCancelled s0 c).getTcb? c = some tw := by
      unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
      rw [SystemState.updateTcb_getTcb?_self s0 c _ hI0, hT0]; exact ⟨_, rfl⟩
    obtain ⟨tw, h⟩ := h
    exact ⟨tw, (SystemState.getTcb?_eq_some_iff _ _ _).mp h⟩
  obtain ⟨tw, hC1⟩ := hC1
  have k2 : replyContextKeptBy (offCallerReply rid) (Lifecycle.Suspend.restoreToReadyCancelled s0 c)
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 c) c t) := by
    intro k o ho hk
    rw [Lifecycle.Suspend.consumeReplyLink_some _ c t rid hRO]
    have hkR : k ≠ rid.toObjId := by
      intro e; subst e
      rw [hR1] at ho; cases ho
      rcases hk with ⟨_, e, hK⟩ | ⟨_, e⟩
      · cases e; exact hK.1 rfl
      · cases e
    have hkC : k ≠ c.toObjId := by
      intro e; subst e
      rw [hC1] at ho; cases ho
      exact hNT _ _ hk tw rfl
    rw [consumeCallerReply_objects_frame _ _ c rid hI1 (SystemState.consumeCallerReply_eq_link _ c rid)
      k hkR hkC]
    exact ho
  have k3 : replyContextKeptBy (offCallerReply rid)
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 c) c t)
      (SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 c) c t)
        c t.blockingServer?) := fun k o ho hk =>
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ c _).get_of_not_tcb
      (hNT k o hk) ho
  have k4 : ∀ (s : SystemState) (sv : Option SeLe4n.ThreadId), s.objects.invExt →
      replyContextKeptBy (offCallerReply rid) s (finaliseReplyRevert s sv) := by
    intro s sv hs k o ho hk
    cases sv with
    | none => exact ho
    | some y =>
      rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise
          s.objectIndex.length s y Concurrency.bootCoreId hs k with e | ⟨pre, -, hp, -⟩
      · show (PriorityInheritance.propagatePipChainCrossCore s y Concurrency.bootCoreId).1.objects[k]? = _
        rw [show PriorityInheritance.propagatePipChainCrossCore s y Concurrency.bootCoreId =
          PriorityInheritance.propagatePipChainCrossCore s y Concurrency.bootCoreId
            s.objectIndex.length from rfl, e]
        exact ho
      · rw [ho] at hp; cases hp; exact absurd rfl (hNT k _ hk pre)
  exact ((k1.trans k2).trans k3).trans (k4 _ _ hInvC)

/-- **The cancel of a reply on no stack keeps the lender's reads**: it writes no
binding (`finaliseReplyCallerCancel_noHead_schedLinkFrame`), and its writes to
replies are the caller's own reply and, at a top cut from the frame below, that
frame, which links up to it (`offCallerReply`). -/
theorem finaliseReplyCallerCancel_unstacked_loanKept (st : SystemState) (hInv : st.objects.invExt)
    {c : SeLe4n.ThreadId} {t : TCB} {r : Reply} (hT : st.getTcb? c = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r)) (hN : r.next = none)
    (hE : replyCallerCancelAdmitted st c t = true) :
    LoanKept st (finaliseReplyCallerCancel st c t) (offCallerReply ⟨t.replyObjectCode - 1⟩) := by
  have hNH : replyStackLinkIsHead r.next = false := by rw [hN]; rfl
  have F := finaliseReplyCallerCancel_noHead_schedLinkFrame st hInv hR hNH hE |>.1
  refine LoanKept.of_schedLinkFrame F ?_
  obtain ⟨⟨ep, rt, hB⟩, -, hRO, hD, hEq⟩ := finaliseReplyCallerCancel_noHead st hR hNH hE
  rw [hEq]
  let rid : SeLe4n.ReplyId := ⟨t.replyObjectCode - 1⟩
  have hRo : st.objects[rid.toObjId]? = some (.reply r) := hR
  have hGR : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hRo
  -- The splice: the identity, or the cut from the frame below.
  have K0 : replyContextKeptBy (offCallerReply rid) st (spliceThreadReplyFrameOut st t) ∧
      ∃ r0, (spliceThreadReplyFrameOut st t).objects[rid.toObjId]? = some (.reply r0) := by
    rcases spliceThreadReplyFrameOut_cases st t with h | ⟨rid', hr', h⟩
    · rw [h]; exact ⟨fun _ _ h _ => h, r, hRo⟩
    rw [hRO] at hr'; cases hr'
    rcases spliceReplyFrameOut_cases h with h' | ⟨r1, above, _, hR1, hN1, _, _, _⟩ |
        ⟨r1, below, b, hR1, hN1, _, hB', hBn, hS⟩
    · rw [h']; exact ⟨fun _ _ h _ => h, r, hRo⟩
    · rw [hGR] at hR1; cases hR1; rw [hN] at hN1; cases hN1
    rw [hGR] at hR1; cases hR1
    obtain ⟨-, hRv, hFrame⟩ := severReplyFrameBelowStores_values hInv hGR hN1 hB' hBn hS
    have hBO := (SystemState.getReply?_eq_some_iff _ _ _).mp hB'
    refine ⟨fun k o ho hk => ?_, _, (SystemState.getReply?_eq_some_iff _ _ _).mp hRv⟩
    have hkB : k ≠ below.toObjId := by
      intro e; subst e
      rw [hBO] at ho; cases ho
      rcases hk with ⟨_, e, hK⟩ | ⟨_, e⟩
      · cases e; exact hK.2 hBn
      · cases e
    have hkR : k ≠ rid.toObjId := by
      intro e; subst e
      rw [hRo] at ho; cases ho
      rcases hk with ⟨_, e, hK⟩ | ⟨_, e⟩
      · cases e; exact hK.1 rfl
      · cases e
    rw [hFrame k hkB hkR]; exact ho
  obtain ⟨K0, r0, hR0⟩ := K0
  have hI0 := spliceThreadReplyFrameOut_preserves_objects_invExt st t hInv
  have hT0 : (spliceThreadReplyFrameOut st t).getTcb? c = some t := by
    rw [spliceThreadReplyFrameOut_getTcb?_eq st t hInv]; exact hT
  have hInvC : (SystemState.unlinkReplyWaiterOpt
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled (spliceThreadReplyFrameOut st t) c) c t)
      c t.blockingServer?).objects.invExt := by
    rw [← cancelIpcBlocking_replyArm_of_noDonation st c t hB hD]
    exact Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st c t hInv
  exact K0.trans (replyCancelRest_kept _ hI0 c t t hRO hT0 hR0 hInvC)

/-- **The splice of a framed reply keeps every other reply heading no stack**,
up to its `prev`: it writes the frame above (its `prev` alone, or its links cut
from the spliced reply), the frame below (linked up to the frame above, so
linking up to a frame before and after), and the spliced reply itself. -/
theorem spliceThreadReplyFrameOut_framed_cancelFrame (st : SystemState) (hInv : st.objects.invExt)
    {c : SeLe4n.ThreadId} {t : TCB} {r : Reply} {rid : SeLe4n.ReplyId}
    (hRO : t.replyObject = some rid) (hRo : st.objects[rid.toObjId]? = some (.reply r))
    (hC : r.callerCode = c.val + 1) :
    CancelFrame st (spliceThreadReplyFrameOut st t) c ∧
      ∃ r0, (spliceThreadReplyFrameOut st t).objects[rid.toObjId]? = some (.reply r0) ∧
        r0.callerCode = r.callerCode := by
  have hGR : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hRo
  have hTcb := spliceThreadReplyFrameOut_getTcb?_eq st t hInv
  have hT : ∀ (v : SeLe4n.ThreadId) (tv : TCB),
      (spliceThreadReplyFrameOut st t).getTcb? v = some tv ↔ st.getTcb? v = some tv := fun v tv => by
    rw [hTcb]
  have mk : (∀ (k : SeLe4n.ObjId) (r' : Reply), st.objects[k]? = some (.reply r') → r'.next = none →
      r'.callerCode ≠ c.val + 1 → ∃ r'', (spliceThreadReplyFrameOut st t).objects[k]? =
        some (.reply r'') ∧ r''.callerCode = r'.callerCode ∧ r''.next = none) →
      CancelFrame st (spliceThreadReplyFrameOut st t) c := fun hRep =>
    ⟨fun v tv _ hv => ⟨tv, (hT v tv).mpr hv, .refl tv⟩, fun v tv _ hv => ⟨tv, (hT v tv).mp hv, rfl, rfl⟩,
      fun k r' hk hn hc => by unfold SystemState.getObject? at hk ⊢; exact hRep k r' hk hn hc⟩
  rcases spliceThreadReplyFrameOut_cases st t with h | ⟨rid', hr', h⟩
  · rw [h]; exact ⟨.refl st c, r, hRo, rfl⟩
  rw [hRO] at hr'; cases hr'
  rcases spliceReplyFrameOut_cases h with h' | ⟨r1, above, a, hR1, hN1, hA, hP, hS⟩ |
      ⟨r1, below, b, hR1, hN1, hPv, hB', hBn, hS⟩
  · rw [h']; exact ⟨.refl st c, r, hRo, rfl⟩
  · rw [hGR] at hR1; cases hR1
    have hAO := (SystemState.getReply?_eq_some_iff _ _ _).mp hA
    have hkR : ∀ (k : SeLe4n.ObjId) (r' : Reply), st.objects[k]? = some (.reply r') →
        r'.callerCode ≠ c.val + 1 → k ≠ rid.toObjId := fun k r' hk hc e => by
      subst e; rw [hRo] at hk; cases hk; exact hc hC
    cases hBelow : spliceFrameBelow? st rid r above with
    | none =>
      obtain ⟨hCut, hAbove, hFrame⟩ := spliceReplyFrameStores_sever_values hInv hBelow hS
      refine ⟨mk (fun k r' hk hn hc => ?_), _, (SystemState.getReply?_eq_some_iff _ _ _).mp hCut, rfl⟩
      have hk1 := hkR k r' hk hc
      by_cases hkA : k = above.toObjId
      · subst hkA
        rw [hAO] at hk; cases hk
        have hAR : above ≠ rid := fun e => hk1 (by rw [e])
        refine ⟨_, (SystemState.getReply?_eq_some_iff _ _ _).mp (hAbove hAR), ?_, ?_⟩ <;>
          rw [Reply.unlinkedFrom_of_next_ne (by rw [hn]; exact fun e => by cases e)]
        all_goals first | rfl | exact hn
      · exact ⟨r', by rw [hFrame k hkA hk1]; exact hk, rfl, hn⟩
    | some pair =>
      obtain ⟨below, b⟩ := pair
      obtain ⟨-, -, hBb, hBn⟩ := spliceFrameBelow?_eq_some hBelow
      obtain ⟨hAv, hBv, hCut, hFrame⟩ := spliceReplyFrameStores_splice_values hInv hGR hN1 hA hP
        hBelow hS
      have hBO := (SystemState.getReply?_eq_some_iff _ _ _).mp hBb
      refine ⟨mk (fun k r' hk hn hc => ?_), _, (SystemState.getReply?_eq_some_iff _ _ _).mp hCut, rfl⟩
      have hk1 := hkR k r' hk hc
      by_cases hkB : k = below.toObjId
      · subst hkB; rw [hBO] at hk; cases hk; rw [hBn] at hn; cases hn
      by_cases hkA : k = above.toObjId
      · subst hkA
        rw [hAO] at hk; cases hk
        exact ⟨_, (SystemState.getReply?_eq_some_iff _ _ _).mp hAv, rfl, hn⟩
      · exact ⟨r', by rw [hFrame k hkA hkB hk1]; exact hk, rfl, hn⟩
  · rw [hGR] at hR1; cases hR1
    obtain ⟨-, hRv, hFrame⟩ := severReplyFrameBelowStores_values hInv hGR hN1 hB' hBn hS
    have hBO := (SystemState.getReply?_eq_some_iff _ _ _).mp hB'
    refine ⟨mk (fun k r' hk hn hc => ?_), _, (SystemState.getReply?_eq_some_iff _ _ _).mp hRv, rfl⟩
    have hkB : k ≠ below.toObjId := fun e => by
      subst e; rw [hBO] at hk; cases hk; rw [hBn] at hn; cases hn
    have hkR : k ≠ rid.toObjId := fun e => by
      subst e; rw [hRo] at hk; cases hk; exact hc hC
    exact ⟨r', by rw [hFrame k hkB hkR]; exact hk, rfl, hn⟩

/-- **The cancel of a framed reply keeps every other plain waiter**
(`CancelFrame`): the splice (`spliceThreadReplyFrameOut_framed_cancelFrame`), then
the restore, the consume, the unlink and the revert, which keep every other
thread and every other reply (`WaiterFrame`). -/
theorem finaliseReplyCallerCancel_noHead_cancelFrame (st : SystemState) (hInv : st.objects.invExt)
    {c : SeLe4n.ThreadId} {t : TCB} {r : Reply} (hT : st.getTcb? c = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r))
    (hNH : replyStackLinkIsHead r.next = false) (hE : replyCallerCancelAdmitted st c t = true) :
    CancelFrame st (finaliseReplyCallerCancel st c t) c := by
  obtain ⟨⟨ep, rt, hB⟩, hC, hRO, hD, hEq⟩ := finaliseReplyCallerCancel_noHead st hR hNH hE
  rw [hEq]
  let rid : SeLe4n.ReplyId := ⟨t.replyObjectCode - 1⟩
  have hRo : st.objects[rid.toObjId]? = some (.reply r) := hR
  obtain ⟨C0, r1, hr1, hc1⟩ := spliceThreadReplyFrameOut_framed_cancelFrame st hInv hRO hRo hC
  have I1 := spliceThreadReplyFrameOut_preserves_objects_invExt st t hInv
  have hT1 : (spliceThreadReplyFrameOut st t).getTcb? c = some t := by
    rw [spliceThreadReplyFrameOut_getTcb?_eq st t hInv]; exact hT
  have hInvC : (SystemState.unlinkReplyWaiterOpt
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled (spliceThreadReplyFrameOut st t) c) c t)
      c t.blockingServer?).objects.invExt := by
    rw [← cancelIpcBlocking_replyArm_of_noDonation st c t hB hD]
    exact Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st c t hInv
  generalize spliceThreadReplyFrameOut st t = s1 at C0 hr1 I1 hT1 hInvC
  have f1 : WaiterFrame s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 c) (· = c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact WaiterFrame.updateTcb s1 c _ I1
  have hI1 : (Lifecycle.Suspend.restoreToReadyCancelled s1 c).objects.invExt :=
    Lifecycle.Suspend.restoreToReadyStaging_invExt s1 c _ I1
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT1
  have hwR : c.toObjId ≠ rid.toObjId := fun e => by rw [e, hr1] at hTo; cases hTo
  have hR1 : (Lifecycle.Suspend.restoreToReadyCancelled s1 c).objects[rid.toObjId]? =
      some (.reply r1) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_objects_ne s1 c _ _ hwR I1]; exact hr1
  have hW1 : ∃ tw, (Lifecycle.Suspend.restoreToReadyCancelled s1 c).getTcb? c = some tw := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_getTcb?_self s1 c _ I1, hT1]; exact ⟨_, rfl⟩
  obtain ⟨tw, hW1⟩ := hW1
  have f2 := WaiterFrame.consumeReplyLink _ c t tw hI1 rid r1 hRO hR1 (hc1.trans hC) hW1
  have f3 := WaiterFrame.of_agreeOffReplyLinks (· = c)
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s1 c) c t) c
      t.blockingServer?)
  obtain ⟨f4, -⟩ := finaliseReplyRevert_frame _ hInvC t.blockingServer? (· = c)
  exact C0.trans (CancelFrame.of_waiterFrame (((f1.trans f2).trans f3).trans f4))

-- ============================================================================
-- §10  The cancel carries the waiters, the lender and the binding
-- ============================================================================

/-- **What a step keeping both frames and every binding carries of `x`**: its
owner code, its lender's endability, and its context bound back. -/
theorem carried_of_frames {s s' : SystemState} {x : SeLe4n.ThreadId} {t : TCB}
    {K : SeLe4n.ObjId → Reply → Prop} (hX : s.getTcb? x = some t) (C : CancelFrame s s' x)
    (Lk : LoanKept s s' K) (hK : LoanReplies s x K) (F : bindingLinksAgree s s') :
    (∀ t', s'.getTcb? x = some t' → t'.scBindingOwnerCode = t.scBindingOwnerCode) ∧
      (lenderEndable s x t → ∀ t', s'.getTcb? x = some t' → lenderEndable s' x t') ∧
      (bindingBack s x → bindingBack s' x) := by
  have ho : ∀ t', s'.getTcb? x = some t' → t'.scBindingOwnerCode = t.scBindingOwnerCode := by
    intro t' ht'
    obtain ⟨t0, h0, -, e⟩ := F.getTcb?_back ht'
    rw [hX] at h0; cases h0; exact e
  exact ⟨ho, fun hL t' ht' => lenderEndable_transport C Lk hK (ho t' ht') hL,
    bindingBack.transport F⟩

/-- Every reply is one a cancel keeps for the lender when the cancel keeps every
reply. -/
theorem LoanReplies.true (s : SystemState) (x : SeLe4n.ThreadId) :
    LoanReplies s x (fun _ _ => True) := fun _ _ _ _ => trivial

/-- **A reply-blocked thread's own reply is no reply of its lender's**
(`offCallerReply`): it is `x`'s, and a frame linking up to it links up to `x`'s. -/
theorem LoanReplies.offCallerReply {s : SystemState} {x : SeLe4n.ThreadId} {r : Reply}
    {rid : SeLe4n.ReplyId} (hR : s.getObject? rid.toObjId = some (.reply r))
    (hC : r.callerCode = x.val + 1) : LoanReplies s x (offCallerReply rid) := by
  intro k r' hk hN
  refine ⟨fun e => ?_, fun e => hN.2 rid r e hR hC⟩
  subst e; rw [hR] at hk; cases hk; exact hN.1 hC

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

/-- **An endpoint cancel admitted by the finalisation keeps both frames and every
binding.** -/
theorem cancelEndpointBlocked_frames (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (x : SeLe4n.ThreadId) (t : TCB) (hInv : s.objects.invExt) (hL : tcbQueueLinkIntegrity s)
    (hX : s.getTcb? x = some t) (hA : endpointCancelAdmitted s e q x t = true) :
    CancelFrame s (cancelEndpointBlocked s e q x t) x ∧
      LoanKept s (cancelEndpointBlocked s e q x t) (fun _ _ => True) ∧
      bindingLinksAgree s (cancelEndpointBlocked s e q x t) := by
  unfold endpointCancelAdmitted at hA
  unfold cancelEndpointBlocked
  cases hE : s.getEndpoint? e with
  | none => rw [hE] at hA; simp at hA
  | some ep =>
    rw [hE] at hA
    simp only [Bool.and_eq_true] at hA
    have hC := hA.2
    dsimp only
    rw [if_pos hC]
    have hG : queueRemoveInPlace s e q x ep t = true := by
      unfold endpointBlockedCancellable at hC
      simp only [Bool.and_eq_true] at hC
      exact hC.1.2
    obtain ⟨C, Lk⟩ := storeEndpointBlockedCancelled_frames s e q x ep t hInv hL hX hG (fun _ _ => True)
    exact ⟨C, Lk, (SchedLinkFrame.storeEndpointBlockedCancelled s e q x ep t hInv).binding⟩

/-- **A reply-blocked thread's own cancel carries its waiters, its lender and its
binding**, on a state the finalisation admits: a reply on no stack keeps both
frames and every binding; a framed reply keeps the waiters' frame and every
binding, and the thread lends nothing (`replyWaitersAdmitted` reads a lender's
loan only with the thread's reply on no stack); a head reply is the thread's own
pop, which hands its context back to it as its own (`replyHeadPopsOwn`), bound
back to it. -/
theorem finaliseReplyCallerCancel_carries (s : SystemState) (x : SeLe4n.ThreadId) (t : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some t)
    (hA : replyCallerCancelAdmitted s x t = true) (hP : replyHeadPopsOwn s t = true)
    (hA1 : t.scBindingOwnerCode ≠ 0 → t.replyObjectCode = 0 ∨ replyCallerReplyUnstacked s t = true) :
    CancelFrame s (finaliseReplyCallerCancel s x t) x ∧
      (∀ t', (finaliseReplyCallerCancel s x t).getTcb? x = some t' →
        t'.scBindingOwnerCode = t.scBindingOwnerCode) ∧
      (lenderEndable s x t → ∀ t', (finaliseReplyCallerCancel s x t).getTcb? x = some t' →
        lenderEndable (finaliseReplyCallerCancel s x t) x t') ∧
      (bindingBack s x → bindingBack (finaliseReplyCallerCancel s x t) x) := by
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
      obtain ⟨-, -, -, -, -, hRO, -, -, -⟩ := replyCallerFinalisable_parts hF
      have hcode : t.replyObjectCode ≠ 0 := by
        intro e; unfold TCB.replyObject at hRO; rw [e] at hRO; cases hRO
      -- On a stacked reply the thread lends nothing.
      have hOwn0 : (∃ l, r.next = some l) → t.scBindingOwnerCode = 0 := by
        intro ⟨l, hl⟩
        rcases Nat.eq_zero_or_pos t.scBindingOwnerCode with h0 | hpos
        · exact h0
        rcases hA1 (by omega) with e | e
        · exact absurd e hcode
        · unfold replyCallerReplyUnstacked at e; rw [hR] at e
          simp only [hl, Option.isNone_some, Bool.false_eq_true] at e
      cases hN : r.next with
      | none =>
        obtain ⟨W, -, -⟩ := finaliseReplyCallerCancel_unframed s hInv h.2.2.2.2.1 hX hR
          (fun a e => by rw [hN] at e; cases e) hA
        have Lk := finaliseReplyCallerCancel_unstacked_loanKept s hInv hX hR hN hA
        have F := finaliseReplyCallerCancel_noHead_schedLinkFrame s hInv hR (by rw [hN]; rfl) hA |>.1
        refine ⟨CancelFrame.of_waiterFrame W, carried_of_frames hX (CancelFrame.of_waiterFrame W) Lk
          (LoanReplies.offCallerReply (rid := ⟨t.replyObjectCode - 1⟩) hR hC) F.binding⟩
      | some l =>
        have hO := hOwn0 ⟨l, hN⟩
        cases l with
        | frame a =>
          have C := finaliseReplyCallerCancel_noHead_cancelFrame s hInv hX hR (by rw [hN]; rfl) hA
          have F : bindingLinksAgree s (finaliseReplyCallerCancel s x t) :=
            (finaliseReplyCallerCancel_noHead_schedLinkFrame s hInv hR (by rw [hN]; rfl) hA).1.binding
          have ho : ∀ t', (finaliseReplyCallerCancel s x t).getTcb? x = some t' →
              t'.scBindingOwnerCode = t.scBindingOwnerCode := by
            intro t' ht'
            obtain ⟨t0, h0, -, e⟩ := F.getTcb?_back ht'
            rw [hX] at h0; cases h0; exact e
          refine ⟨C, ho, fun _ t' ht' o hO' => ?_, bindingBack.transport F⟩
          rw [ho t' ht', hO] at hO'; cases hO'
        | head sid =>
          obtain ⟨W, -, -⟩ := finaliseReplyCallerCancel_unframed s hInv h.2.2.2.2.1 hX hR
            (fun a e => by rw [hN] at e; cases e) hA
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
          refine ⟨CancelFrame.of_waiterFrame W, fun t' ht' => by rw [hOwn' t' ht', hO],
            fun _ t' ht' o hO' => (by rw [hOwn' t' ht'] at hO'; cases hO'), fun _ t' ht' hz => ?_⟩
          rw [hX'] at ht'; cases ht'
          obtain ⟨sc', hS', hB'⟩ := returnDonatedSchedContext_post_boundThread s P hd sid x hInv none hPop
          obtain ⟨sc'', hS'', hB''⟩ := hAg.getSchedContext?_fwd hS'
          refine ⟨sc'', ?_, hB''.trans ((SeLe4n.ThreadId.ofOptCode_eq_some_iff _ _).mp hB')⟩
          rw [e1, hc1]; exact hS''
    | _ => rw [hR] at hA0; cases hA0

/-- **The finalisation's cancel carries the waiters, the lender and the binding**
(part 34): on a state carrying the finalisation's invariant whose cancel the
admission admits, the cancel keeps every plain waiter of `x` but `x`
(`CancelFrame`), keeps `x`'s owner code, keeps `x`'s lender endable, and keeps
`x`'s context bound back — whatever `x` was blocked on. -/
theorem finaliseThreadCancel_carries (s : SystemState) (x : SeLe4n.ThreadId) (t : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some t)
    (hA : threadIpcCancelAdmitted s x t = true)
    (hP : t.replyObjectCode = 0 ∨ replyHeadPopsOwn s t = true)
    (hA1 : t.scBindingOwnerCode ≠ 0 → t.replyObjectCode = 0 ∨ replyCallerReplyUnstacked s t = true) :
    CancelFrame s (finaliseThreadCancel s x) x ∧
      (∀ t', (finaliseThreadCancel s x).getTcb? x = some t' →
        t'.scBindingOwnerCode = t.scBindingOwnerCode) ∧
      (lenderEndable s x t → ∀ t', (finaliseThreadCancel s x).getTcb? x = some t' →
        lenderEndable (finaliseThreadCancel s x) x t') ∧
      (bindingBack s x → bindingBack (finaliseThreadCancel s x) x) := by
  have hInv := h.2.1
  have hL : tcbQueueLinkIntegrity s := h.1.2.1.linkIntegrity
  have hId : CancelFrame s s x ∧
      (∀ t', s.getTcb? x = some t' → t'.scBindingOwnerCode = t.scBindingOwnerCode) ∧
      (lenderEndable s x t → ∀ t', s.getTcb? x = some t' → lenderEndable s x t') ∧
      (bindingBack s x → bindingBack s x) :=
    ⟨.refl s x, fun t' ht' => by rw [hX] at ht'; cases ht'; rfl,
      fun hL t' ht' => by rw [hX] at ht'; cases ht'; exact hL, id⟩
  have hEp : ∀ e q, endpointCancelAdmitted s e q x t = true →
      CancelFrame s (cancelEndpointBlocked s e q x t) x ∧
      (∀ t', (cancelEndpointBlocked s e q x t).getTcb? x = some t' →
        t'.scBindingOwnerCode = t.scBindingOwnerCode) ∧
      (lenderEndable s x t → ∀ t', (cancelEndpointBlocked s e q x t).getTcb? x = some t' →
        lenderEndable (cancelEndpointBlocked s e q x t) x t') ∧
      (bindingBack s x → bindingBack (cancelEndpointBlocked s e q x t) x) := fun e q hE => by
    obtain ⟨C, Lk, F⟩ := cancelEndpointBlocked_frames s e q x t hInv hL hX hE
    exact ⟨C, carried_of_frames hX C Lk (LoanReplies.true s x) F⟩
  unfold threadIpcCancelAdmitted at hA
  unfold finaliseThreadCancel
  rw [hX]
  dsimp only
  have hI : t.ipcState = ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode := rfl
  rcases hc : t.ipcStateCode with _ | _ | _ | _ | k
  · rw [hc] at hA
    cases ho : t.ipcObjectCode with
    | zero =>
      have hR : t.ipcState = .ready := by rw [hI, hc, ho]; rfl
      rw [hR]; exact hId
    | succ o =>
      have hR : t.ipcState = .blockedOnSend ⟨o⟩ := by rw [hI, hc, ho]; rfl
      rw [hR]
      simp only [ho, Nat.add_sub_cancel, Nat.succ_ne_zero, beq_iff_eq, if_false] at hA
      exact hEp _ _ hA
  · have hR : t.ipcState = .blockedOnReceive ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    exact hEp _ _ hA
  · have hR : t.ipcState = .blockedOnNotification ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    dsimp only at hA ⊢
    cases hN : s.getNotification? ⟨t.ipcObjectCode⟩ with
    | none => exact hId
    | some ntfn =>
      rw [hN] at hA
      dsimp only at hA ⊢
      have hC := ((Bool.and_eq_true _ _).mp hA).2
      rw [if_pos hC]
      obtain ⟨C, Lk⟩ := notificationCancel_frames s x t _ hInv hR (fun _ _ => True)
      exact ⟨C, carried_of_frames hX C Lk (LoanReplies.true s x)
        (SchedLinkFrame.notificationCancel s x t _ hInv hR).binding⟩
  · have hR : t.ipcState = .blockedOnCall ⟨t.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    exact hEp _ _ hA
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
    exact finaliseReplyCallerCancel_carries s x t h hX hA hP' hA1


-- ============================================================================
-- §11  The loan return hands the context back
-- ============================================================================

/-- **The loan return leaves `x` lending nothing, its context bound back**
(part 34): on a state carrying the finalisation's invariant, when `x`'s lender,
if any, is endable (`lenderEndable`) — its reply heading a stack — the lender's
pop (`finaliseThreadReturnLoan`) takes the context from `x`: the donation
return writes `x` no binding (`returnDonatedSchedContext_codes`, the pop's
holder being `x`, the server the lender waits on), and every write after it
keeps every binding (`finaliseReplyCallerCancel_pop`,
`SchedLinkFrame.finaliseThreadSuspend`).  With no lender, nothing is written,
so a context bound back stays so. -/
theorem finaliseThreadReturnLoan_unbinds (s : SystemState) (x : SeLe4n.ThreadId) (tx : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some tx) (hL : lenderEndable s x tx)
    (hB : tx.scBindingOwnerCode = 0 → bindingBack s x) :
    (∀ t', (finaliseThreadReturnLoan s x).getTcb? x = some t' → t'.scBindingOwnerCode = 0) ∧
      bindingBack (finaliseThreadReturnLoan s x) x := by
  cases hO : tx.scBindingOwnerCode with
  | zero =>
    have hR : finaliseThreadReturnLoan s x = s := by
      unfold finaliseThreadReturnLoan; rw [hX]; simp only [hO]
    rw [hR]
    refine ⟨fun t' ht' => ?_, hB hO⟩
    rw [hX] at ht'; cases ht'; exact hO
  | succ o =>
    obtain ⟨tl, r, hT, hRl, ⟨c, hNh⟩, hE⟩ := hL o hO
    have hR : finaliseThreadReturnLoan s x = finaliseReplyWaiter s ⟨o⟩ tl := by
      unfold finaliseThreadReturnLoan; rw [hX]; simp only [hO, hT, hE, if_true]
    rw [hR]
    have hE' := hE
    unfold replyWaiterEndable at hE'
    simp only [Bool.and_eq_true, beq_iff_eq] at hE'
    obtain ⟨⟨-, hSx⟩, hG⟩ := hE'
    obtain ⟨hd, n, P, -, hne, hSrv, hRet, hAg⟩ := finaliseReplyCallerCancel_pop s h.2.1 hT hRl hNh hG
    have hdx : hd = x := by
      have e : hd.val = x.val := by omega
      cases hd; cases x; simp only at e; subst e; rfl
    subst hdx
    obtain ⟨⟨th, hth, h1, h2⟩, -⟩ := returnDonatedSchedContext_codes h.2.1 hRet hne
    obtain ⟨-, hI, -⟩ := finaliseReplyCallerCancel_unframed s h.2.1 h.2.2.2.2.1 hT hRl
      (lenderEndable.noFrame ⟨c, hNh⟩) hG
    have F : bindingLinksAgree P (finaliseReplyWaiter s ⟨o⟩ tl) := by
      unfold finaliseReplyWaiter
      exact hAg.trans (SchedLinkFrame.finaliseThreadSuspend _ _ hI).binding
    have hzero : ∀ t', (finaliseReplyWaiter s ⟨o⟩ tl).getTcb? hd = some t' →
        t'.scBindingScCode = 0 ∧ t'.scBindingOwnerCode = 0 := by
      intro t' ht'
      obtain ⟨tp, hp, e1, e2⟩ := F.getTcb?_back ht'
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hth] at hp
      cases hp
      exact ⟨e1.trans h1, e2.trans h2⟩
    exact ⟨fun t' ht' => (hzero t' ht').2, fun t' ht' hc => absurd (hzero t' ht').1 hc⟩


-- ============================================================================
-- §12  The notification unbind carries the admission's reads
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

/-- A read of one reply answers alike on two states keeping every reply, both
ways: the unstacked-reply question. -/
theorem replyCallerReplyUnstacked_of_replies {s s' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (r : Reply), s'.objects[k]? = some (KernelObject.reply r) ↔
      s.objects[k]? = some (KernelObject.reply r))
    (t : TCB) : replyCallerReplyUnstacked s' t = replyCallerReplyUnstacked s t := by
  unfold replyCallerReplyUnstacked SystemState.getObject?
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


/-- A step agreeing on the bindings keeps a thread lending nothing. -/
theorem bindingLinksAgree.ownerZero {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : bindingLinksAgree s s') (hz : ∀ t, s.getTcb? x = some t → t.scBindingOwnerCode = 0) :
    ∀ t', s'.getTcb? x = some t' → t'.scBindingOwnerCode = 0 := by
  intro t' ht'
  obtain ⟨t, ht, -, e⟩ := h.getTcb?_back ht'
  exact e.trans (hz t ht)

end SeLe4n.Kernel
