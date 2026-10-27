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
      (tx.boundNotificationCode == 0 ||
        ((match st.getNotification? ⟨tx.boundNotificationCode - 1⟩ with
          | some n => n.boundTCBCode == x.val + 1
          | none => false) && unbindNotificationInPlace st ⟨x.val⟩)) = true ∧
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
(`CancelReadsKept.storeUnbindNotification`, `CancelReadsKept.threadIpcCancelAdmitted_eq`),
and the thread it leaves differs from the pre-state's in its bound-notification
code alone. -/
theorem threadIpcCancelAdmitted_after_unbind {st : SystemState} {x : SeLe4n.ObjId}
    (hInv : st.objects.invExt) (hA : threadFinaliseAdmitted st x = true) :
    ∀ t1, (finaliseThreadUnbindNotification st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t1 →
      threadIpcCancelAdmitted (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩ t1 = true := by
  obtain ⟨tx, hX, -, -, -, -, -, -, hC, -, hBnc, -⟩ := threadFinaliseAdmitted_parts hA
  intro t1 h1
  rw [finaliseThreadUnbindNotification_self hInv hX hBnc] at h1
  cases h1
  have hT : threadIpcCancelAdmitted st ⟨x.val⟩ { tx with boundNotificationCode := 0 } = true :=
    hC
  have hc : boundNotificationCodeOf st ⟨x.val⟩ = tx.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hX]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  split
  · exact hT
  · split
    · split
      · rename_i hG
        simp only [Bool.and_eq_true] at hG
        rw [(CancelReadsKept.storeUnbindNotification st _ _ hInv hG.2).threadIpcCancelAdmitted_eq]
        exact hT
      · exact hT
    · exact hT

end SeLe4n.Kernel
