/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.FinaliseAdmissionCarried

/-!
# A finalised object's own record is retirable

WS-ZA ZA5.4 part 26: a final delete finalises a thread or a scheduling context
(`finaliseThread`, `finaliseSchedContext`) and then retires it
(`retireFinalObject`), which erases it only when it is retirable
(`schedulingObjectRetirable`).  This module proves that the finalisation, run on
a state its admission admits, always leaves the object's **own record** in the
retirable shape: nothing it holds names another object and nothing it records
keeps it in use.

* **The scheduling context** (`finaliseSchedContext_releases`): bound to no
  thread, lent from no one, heading no reply stack, recording no yielder.
* **The thread** (`finaliseThread_quiesces`): `.Inactive` and `.ready`, linked
  into no queue and heading none, bound to no notification and to no
  scheduling context, holding no reply link or stash and no timeout budget,
  and held by no core — every field `threadLinksQuiescent` reads, the space
  slots aside, which the zombie loop empties after the finalisation.

What the record does not say — that no *other* object still names the
finalised one — follows from the record under the reachable invariants: for the
thread, `threadRetirable.namedByNone`, so the retire reads the thread's own links
alone.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The scheduling context
-- ============================================================================

/-- **A finalised scheduling context's own record is released**: the context
at `x` is stored, bound to no thread, lent from no one, heading no reply
stack and recording no yielder — the record half of `schedContextRetirable`. -/
def schedContextRecordReleased (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∃ sc, st.objects[x]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
    sc.donationOrigin = none ∧ sc.scReply = none ∧ sc.yieldFromCode = 0

/-- **The holder's unbind keeps the context, its reply-stack head and every
reply**: it rewrites the context's binding fields and the holder's TCB alone. -/
theorem finaliseSchedContextUnbind_keeps {s : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} (hInv : s.objects.invExt) (hO : s.objects[x]? = some (.schedContext sc)) :
    (∃ sc', (finaliseSchedContextUnbind s x).objects[x]? = some (.schedContext sc') ∧
      sc'.scReply = sc.scReply) ∧
    ∀ (k : SeLe4n.ObjId) (r : Reply), s.objects[k]? = some (.reply r) →
      (finaliseSchedContextUnbind s x).objects[k]? = some (.reply r) := by
  have hId : ∀ s' : SystemState, s' = s →
      (∃ sc', s'.objects[x]? = some (.schedContext sc') ∧ sc'.scReply = sc.scReply) ∧
      ∀ (k : SeLe4n.ObjId) (r : Reply), s.objects[k]? = some (.reply r) →
        s'.objects[k]? = some (.reply r) := by
    intro s' e; subst e; exact ⟨⟨sc, hO, rfl⟩, fun _ _ h => h⟩
  unfold finaliseSchedContextUnbind
  rw [SystemState.getObject?_eq_getElem, hO]
  dsimp only
  split
  · exact hId _ rfl
  generalize hTid : (⟨sc.boundThreadCode - 1⟩ : SeLe4n.ThreadId) = tid
  cases hT : s.getTcb? tid with
  | none => exact hId _ rfl
  | some t =>
  dsimp only
  split
  rotate_left
  · exact hId _ rfl
  rename_i hG
  simp only [beq_iff_eq] at hG
  have hBind := schedContextBinding_ownerCleared (t := t) hG
  have hOk := cancelBoundDonationOnCore_of_bound s tid { t with scBindingOwnerCode := 0 }
    _ hBind
  rw [hOk]
  dsimp only
  have hObj := cancelBoundDonationOnCore_objects s _ tid _ _ hBind hInv hOk
  have hNe : tid.toObjId ≠ x := by
    intro e
    have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [e, hO] at this; cases this
  have hG' : s.getSchedContext? ⟨x.val⟩ = some sc := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO
  have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt s ⟨x.val⟩
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
  have hMidX : ((s.updateSchedContext ⟨x.val⟩
        (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).updateTcb
        tid (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })).objects[x]? =
      some (.schedContext
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) := by
    rw [SystemState.updateTcb_objects_ne _ _ _ _ hNe hInv1,
      SystemState.updateSchedContext_eq_of_some hG']
    dsimp only
    rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
      RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
  obtain ⟨sc', h1, e⟩ := hObj.getSchedContext?_some (s := ⟨x.val⟩)
    ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hMidX)
  refine ⟨⟨sc', (SystemState.getSchedContext?_eq_some_iff _ _ _).mp h1,
    (congrArg SchedContext.scReply e : _)⟩, fun k r hk => ?_⟩
  · refine hObj.get_of_not_sc (fun _ e => KernelObject.noConfusion e) ?_
    have hkx : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId ≠ k := by
      intro e; rw [← e] at hk; rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
        hO] at hk; cases hk
    have hkt : tid.toObjId ≠ k := by
      intro e
      have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      rw [e, hk] at this; cases this
    rw [SystemState.updateTcb_objects_ne _ _ _ _ hkt hInv1,
      SystemState.updateSchedContext_objects_ne _ _ _ _ hkx hInv]
    exact hk

/-- **The holder's deschedule keeps the context and every reply**: it writes
run-queue links alone. -/
theorem finaliseSchedContextDeschedule_keeps {s : SystemState} {x k : SeLe4n.ObjId}
    {o : KernelObject} (hNot : ∀ t, o ≠ .tcb t) (hk : s.objects[k]? = some o) :
    (finaliseSchedContextDeschedule s x).objects[k]? = some o :=
  (finaliseSchedContextDeschedule_objectsAgreeOffRunLinks s x).get_of_not_tcb hNot hk

/-- **The destroy cleanup releases a released context's yield** (WS-ZA ZA6.6):
on a context bound to no thread, lent from no one and heading no reply stack,
the cleanup completes the yield the context records
(`finaliseSchedContextCleanupImpl`, `completeYieldFrom`), which writes the yield
writes alone and leaves the context recording no yielder. -/
theorem finaliseSchedContextCleanupImpl_releases {s : SystemState} {x : SeLe4n.ObjId}
    (hInv : s.objects.invExt) {sc : SchedContext} (hO : s.objects[x]? = some (.schedContext sc))
    (hB : sc.boundThreadCode = 0) (hD : sc.donationOrigin = none) (hR : sc.scReply = none) :
    schedContextRecordReleased (finaliseSchedContextCleanupImpl s x) x := by
  unfold finaliseSchedContextCleanupImpl
  rw [SystemState.getObject?_eq_getElem, hO]
  simp only [hB, hR, beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
  have hG : s.getSchedContext? (SeLe4n.SchedContextId.ofObjId x) = some sc := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO
  have e := (SystemState.completeYieldFrom_objectsAgreeOffYield s
    (SeLe4n.SchedContextId.ofObjId x) hInv).getSchedContext?_map
    (fun u => (u.boundThreadCode, u.donationOrigin, u.scReply)) (fun _ => rfl)
    (SeLe4n.SchedContextId.ofObjId x)
  rw [hG] at e
  cases hG' : (completeYieldFrom s (SeLe4n.SchedContextId.ofObjId x)).getSchedContext?
      (SeLe4n.SchedContextId.ofObjId x) with
  | none => rw [hG'] at e; cases e
  | some sc' =>
    rw [hG'] at e
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    exact ⟨sc', (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hG', e1.trans hB,
      e2.trans hD, e3.trans hR, SystemState.completeYieldFrom_yieldFromCode_self _ _ hInv hG'⟩

/-- **A finalised scheduling context's own record is released**
(WS-ZA ZA5.4 part 26): on a state its admission admits, the finalisation
leaves the context at `x` bound to no thread and lent from no one — the
holder's unbind clears both (`finaliseSchedContextUnbind_released`) — and
heading no reply stack: the head reply the admission reads still names the
context as its head after the deschedule and the unbind, which write no reply,
so the unstack runs and clears the head; the destroy cleanup then completes
the yield the context records (`finaliseSchedContextCleanupImpl_releases`). -/
theorem finaliseSchedContext_releases (x : SeLe4n.ObjId) (st : SystemState)
    (hInv : st.objects.invExt) (hA : schedContextFinaliseAdmitted st x = true) :
    schedContextRecordReleased (finaliseSchedContext x st) x := by
  rw [finaliseSchedContext_eq, if_pos hA]
  have hInvU := (finaliseSchedContextUnstack_closed (FinaliseFrameAny st)
    (FinaliseFrameAny.unstackStep st) x st (.refl hInv) hA _ rfl
    (finaliseSchedContextUnbind_closed _ (FinaliseFrameAny.scReleaseStep st) _ x
      (finaliseSchedContextDeschedule_closed _ (FinaliseFrameAny.scDescheduleStep st) st x hA
        (.refl hInv)))).invExt
  suffices hU : ∃ sc, (finaliseSchedContextUnstack (finaliseSchedContextUnbind
      (finaliseSchedContextDeschedule st x) x) x).objects[x]? = some (.schedContext sc) ∧
      sc.boundThreadCode = 0 ∧ sc.donationOrigin = none ∧ sc.scReply = none by
    obtain ⟨sc, h1, h2, h3, h4⟩ := hU
    exact finaliseSchedContextCleanupImpl_releases hInvU h1 h2 h3 h4
  have hA0 := hA
  unfold schedContextFinaliseAdmitted at hA0
  obtain ⟨sc0, hO, hRep⟩ : ∃ sc0, st.objects[x]? = some (.schedContext sc0) ∧
      (match sc0.scReply with
        | none => true
        | some rid =>
          match st.getReply? rid with
          | some r => replyStackLinkHeads x r.next
          | none => false) = true := by
    split at hA0
    · rename_i sc0 hO
      simp only [Bool.and_eq_true] at hA0
      exact ⟨sc0, by rw [← SystemState.getObject?_eq_getElem]; exact hO, hA0.1⟩
    · cases hA0
  have hInv1 : (finaliseSchedContextDeschedule st x).objects.invExt :=
    finaliseSchedContextDeschedule_closed_any (fun s => s.objects.invExt)
      (fun s t h => descheduleAtPlacement_preserves_objects_invExt s t h) st x hInv
  have hO1 := finaliseSchedContextDeschedule_keeps (x := x) (fun _ e => KernelObject.noConfusion e) hO
  obtain ⟨⟨sc2, hO2, hR2⟩, hKeep⟩ := finaliseSchedContextUnbind_keeps hInv1 hO1
  have hInv2 : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).objects.invExt :=
    finaliseSchedContextUnbind_closed (fun s => s.objects.invExt)
      (fun s _ _ _ _ _ h _ _ _ _ hOk => (FinaliseFrame.cancelBoundDonationOnCore h hOk).invExt)
      _ x hInv1
  have hG2 : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).getSchedContext?
      ⟨x.val⟩ = some sc2 := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO2
  obtain ⟨hB2, hD2⟩ := finaliseSchedContextUnbind_released hInv hA hG2
  generalize finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x = s2
    at hO2 hKeep hInv2 hG2
  unfold finaliseSchedContextUnstack
  rw [hG2]
  dsimp only
  cases hS : sc2.scReply with
  | none => exact ⟨sc2, hO2, hB2, hD2, hS⟩
  | some rid =>
  dsimp only
  rw [hR2] at hS
  rw [hS] at hRep
  dsimp only at hRep
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRep; cases hRep
  | some r =>
  rw [hR] at hRep
  dsimp only at hRep
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hRo2 := hKeep _ r (finaliseSchedContextDeschedule_keeps
    (fun _ e => KernelObject.noConfusion e) hRo)
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRo2]
  dsimp only
  rw [if_pos hRep]
  obtain ⟨s3, hS3⟩ : ∃ s3, storeObject rid.toObjId (.reply { r with next := none }) s2 = .ok ((), s3) :=
    ⟨_, rfl⟩
  rw [hS3]
  dsimp only
  have hNe : x ≠ rid.toObjId := by intro e; rw [e, hRo2] at hO2; cases hO2
  have hO3 : s3.objects[x]? = some (.schedContext sc2) := by
    rw [storeObject_objects_ne s2 s3 rid.toObjId x _ hNe hInv2 hS3]; exact hO2
  have hInv3 := storeObject_preserves_objects_invExt s2 s3 rid.toObjId _ hInv2 hS3
  have hG3 : s3.getSchedContext? ⟨x.val⟩ = some sc2 := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO3
  refine ⟨{ sc2 with scReply := none }, ?_, hB2, hD2, rfl⟩
  rw [SystemState.updateSchedContext_eq_of_some hG3]
  dsimp only
  rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
    RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv3]

-- ============================================================================
-- §2  The thread
-- ============================================================================

/-- A thread yielded to no context reads as quiescent exactly when its record
with the yield writes cleared does: the quiescence reads no register. -/
theorem threadLinksQuiescent_eq_withoutYieldWrites {t : TCB} (h : t.yieldToCode = 0) :
    threadLinksQuiescent t = threadLinksQuiescent t.withoutYieldWrites := by
  unfold threadLinksQuiescent; rw [h]

open SeLe4n.Kernel.Concurrency (CoreId) in
/-- **A finalised thread's own record is quiesced**: the thread at `x` is stored
under its own id, quiescent but for its space slots (`threadLinksQuiescent`) and
held by no core — the record half of `threadRetirable`, the space slots aside,
which the zombie loop empties after the finalisation. -/
def threadRecordQuiesced (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∃ t, st.objects[x]? = some (.tcb t) ∧ t.tid.val = x.val ∧ threadLinksQuiescent t = true ∧
    threadHeldOnSomeCore st ⟨x.val⟩ = false

/-- **The state a thread's finalisation ends its own IPC on**: its notification
unbound, then its blocked IPC cancelled — where the loan return and the walk
over its waiters run. -/
abbrev finaliseThreadAfterCancel (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  finaliseThreadCancel (finaliseThreadUnbindNotification st tid) tid

/-- **The state a thread's finalisation unbinds its context on**: its waiters
ended, then suspended and released by every core. -/
abbrev finaliseThreadAfterRelease (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  finaliseThreadReleaseCores (cancelYieldTo (finaliseThreadSuspend (finaliseThreadEndWaiters
    (finaliseThreadReturnLoan (finaliseThreadAfterCancel st tid) tid) tid) tid) tid) tid

/-- **The thread finalisation's admission is carried across its own steps**
(WS-ZA ZA5.4 part 34): on a state carrying the finalisation's invariant on which
`threadFinaliseAdmitted` admits the thread, what each later step's guard reads
holds on the state that step runs on, so no step's guard refuses after an
earlier step has written — checks before writes.

* The cancel's admission holds after the notification unbind
  (`threadIpcCancelAdmitted_after_unbind`).
* After the cancel, the lender the thread's binding names is endable, and every
  other thread waiting on it is a plain waiter: the waiters' admission reads
  both on the pre-state (`lenderEndable_of_admitted`, `replyWaitersAdmitted_plain`),
  and the unbind and the cancel keep them (`finaliseThreadUnbindNotification_frames`,
  `finaliseThreadCancel_carries`) — what the loan return's and the walk's guards
  read (`finaliseThreadEndWaiters_returnLoan_endsAll`).
* After the release, the thread lends nothing and its context is bound back to
  it — the context unbind's binding clause: the loan return takes a loan back
  (`finaliseThreadReturnLoan_unbinds`), and the walk, the suspend and the
  release write no binding. -/
theorem finaliseThread_admissionCarried (x : SeLe4n.ObjId) (st : SystemState)
    (hI : finaliseStepInvariant st) (hBd : runCodeBounded st ⟨x.val⟩)
    (hA : threadFinaliseAdmitted st x = true) :
    (∀ t1, (finaliseThreadUnbindNotification st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t1 →
      threadIpcCancelAdmitted (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩ t1 = true) ∧
    (∀ t2, (finaliseThreadAfterCancel st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t2 →
      lenderEndable (finaliseThreadAfterCancel st ⟨x.val⟩) ⟨x.val⟩ t2 ∧
      ∀ v, ReplyViews.waiterOf (finaliseThreadAfterCancel st ⟨x.val⟩).replyViews v ⟨x.val⟩ →
        (∀ o, t2.scBindingOwnerCode = o + 1 → v ≠ ⟨o⟩) →
        plainWaiterReady (finaliseThreadAfterCancel st ⟨x.val⟩) ⟨x.val⟩ v) ∧
    (∀ t6, (finaliseThreadAfterRelease st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t6 →
      t6.scBindingOwnerCode = 0) ∧
    bindingBack (finaliseThreadAfterRelease st ⟨x.val⟩) ⟨x.val⟩ := by
  have hCancel := threadIpcCancelAdmitted_after_unbind hI.2.1 hA
  refine ⟨hCancel, ?_⟩
  unfold finaliseThreadAfterRelease finaliseThreadAfterCancel
  obtain ⟨tx0, hX0, -, -, -, -, -, hWA, -, hPA, hBnc, hSBA⟩ := threadFinaliseAdmitted_parts hA
  -- What the admission reads of the waiters, the lender and the binding.
  have hL0 := lenderEndable_of_admitted hI hX0 hWA
  have hAll0 := replyWaitersAdmitted_plain hI hX0 hWA
  have hA10 : tx0.scBindingOwnerCode ≠ 0 →
      tx0.replyObjectCode = 0 ∨ replyCallerReplyUnstacked st tx0 = true := by
    intro hne
    have hW := hWA
    unfold replyWaitersAdmitted at hW
    cases hOw : tx0.scBindingOwnerCode with
    | zero => exact absurd hOw hne
    | succ o =>
      rw [hOw] at hW
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hW
      exact hW.1.1.2
  have hBB0 : bindingBack st ⟨x.val⟩ := by
    intro t ht hc
    rw [hX0] at ht; cases ht
    rcases hSBA with h0 | h0
    · exact absurd h0 hc
    · exact h0
  -- The notification unbind.
  have C0 := finaliseCarried.start st ⟨x.val⟩ hI hBd
  have hX1 := finaliseThreadUnbindNotification_self hI.2.1 hX0
  have C1 := finaliseThreadUnbindNotification_closed _ (finaliseCarried.unbindStep st ⟨x.val⟩)
    st ⟨x.val⟩ hX0 hBnc C0
  obtain ⟨C01, Lk01⟩ :=
    finaliseThreadUnbindNotification_frames st ⟨x.val⟩ hI.2.1 hX0 hBnc (fun _ _ => True)
  have hRep := finaliseThreadUnbindNotification_replies st ⟨x.val⟩ hI.2.1 hX0 hBnc
  have hL1 : lenderEndable (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩
      { tx0 with boundNotificationCode := 0 } :=
    lenderEndable_transport C01 Lk01 (LoanReplies.true _ _) rfl hL0
  have hP1 : tx0.replyObjectCode = 0 ∨
      replyHeadPopsOwn (finaliseThreadUnbindNotification st ⟨x.val⟩)
        { tx0 with boundNotificationCode := 0 } = true := by
    rw [replyHeadPopsOwn_of_replies hRep]; exact hPA
  have hA11 : tx0.scBindingOwnerCode ≠ 0 → tx0.replyObjectCode = 0 ∨
      replyCallerReplyUnstacked (finaliseThreadUnbindNotification st ⟨x.val⟩)
        { tx0 with boundNotificationCode := 0 } = true := by
    rw [replyCallerReplyUnstacked_of_replies hRep]; exact hA10
  have hBB1 : bindingBack (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩ := by
    intro t ht hc
    rw [hX1] at ht; cases ht
    obtain ⟨sc, hS, hb⟩ := hBB0 tx0 hX0 hc
    exact ⟨sc, Lk01.sc _ _ hS, hb⟩
  generalize finaliseThreadUnbindNotification st ⟨x.val⟩ = s1
    at hX1 C1 hCancel C01 hL1 hP1 hA11 hBB1
  -- The cancel.
  obtain ⟨t2, hX2, k2⟩ := finaliseThreadCancel_quiets C1.1.2.1 hX1 (hCancel _ hX1)
  obtain ⟨C12, ho2, hLe2, hBB2⟩ :=
    finaliseThreadCancel_carries s1 ⟨x.val⟩ _ C1.1 hX1 (hCancel _ hX1) hP1 hA11
  have hL2 := hLe2 hL1 t2 hX2
  have hBB2' := hBB2 hBB1
  have hOw2 := ho2 t2 hX2
  have hRd2 : t2.blockingServer? = none := by
    have hS2 : t2.ipcStateCode = 0 := congrArg (fun k => k.2.1) k2
    have hO2 : t2.ipcObjectCode = 0 := congrArg (fun k => k.1) k2
    have e : t2.ipcState = .ready := by
      show ThreadIpcState.ofCodes t2.ipcObjectCode t2.ipcStateCode = _
      rw [hO2, hS2]; rfl
    unfold TCB.blockingServer?; rw [e]
  have C02 := C01.trans C12
  have hAll2 : ∀ v, ReplyViews.waiterOf (finaliseThreadCancel s1 ⟨x.val⟩).replyViews v ⟨x.val⟩ →
      (∀ o, t2.scBindingOwnerCode = o + 1 → v ≠ ⟨o⟩) →
      plainWaiterReady (finaliseThreadCancel s1 ⟨x.val⟩) ⟨x.val⟩ v := by
    intro v hv hne
    have hvx : v ≠ ⟨x.val⟩ := by
      intro e; subst e
      obtain ⟨tv, htv, hsv⟩ := waiterOf_iff.mp hv
      rw [hX2] at htv; cases htv
      rw [hRd2] at hsv; cases hsv
    exact C02.ready hvx (hAll0 v (C02.waiterOf_back hvx hv) (fun o e => hne o (hOw2.trans e)))
  refine ⟨fun t2' h2' => ?_, ?_⟩
  · rw [hX2] at h2'; cases h2'; exact ⟨hL2, hAll2⟩
  have C2 := finaliseThreadCancel_closed _ (finaliseCarried.notificationCancelStep st ⟨x.val⟩)
    (finaliseCarried.endpointCancelStep st ⟨x.val⟩) (finaliseCarried.replyStep st ⟨x.val⟩)
    s1 ⟨x.val⟩ C1
  generalize finaliseThreadCancel s1 ⟨x.val⟩ = s2 at hX2 C2 hL2 hBB2' hAll2
  -- The loan return and the walk.
  obtain ⟨-, -, hWalkB⟩ :=
    finaliseThreadEndWaiters_returnLoan_endsAll s2 ⟨x.val⟩ t2 C2.1 hX2 hL2 hAll2
  obtain ⟨hOwn3, hBB3⟩ :=
    finaliseThreadReturnLoan_unbinds s2 ⟨x.val⟩ t2 C2.1 hX2 hL2 (fun _ => hBB2')
  have hOwn4 := hWalkB.ownerZero hOwn3
  have hBB4 := bindingBack.transport hWalkB hBB3
  have C4 := finaliseThreadEndWaiters_closed _ (finaliseCarried.replyStep st ⟨x.val⟩)
    (finaliseCarried.suspendStep st ⟨x.val⟩) _ ⟨x.val⟩
    (finaliseThreadReturnLoan_closed _ (finaliseCarried.replyStep st ⟨x.val⟩)
      (finaliseCarried.suspendStep st ⟨x.val⟩) s2 ⟨x.val⟩ C2)
  generalize finaliseThreadEndWaiters (finaliseThreadReturnLoan s2 ⟨x.val⟩) ⟨x.val⟩ = s4
    at C4 hOwn4 hBB4
  -- The suspend, its yield cancel and the release write no binding.
  have F5 := (SchedLinkFrame.finaliseThreadSuspend s4 ⟨x.val⟩ C4.1.2.1).binding
  have C5 := finaliseThreadSuspend_closed _ (finaliseCarried.suspendStep st ⟨x.val⟩) s4 ⟨x.val⟩ C4
  have F5y := (SchedLinkFrame.of_objectsAgreeOffYield
    (SystemState.cancelYieldTo_objectsAgreeOffYield _ ⟨x.val⟩ C5.1.2.1)
    (SystemState.cancelYieldTo_scheduler _ ⟨x.val⟩)).binding
  have F6 : bindingLinksAgree (cancelYieldTo (finaliseThreadSuspend s4 ⟨x.val⟩) ⟨x.val⟩)
      (finaliseThreadReleaseCores (cancelYieldTo (finaliseThreadSuspend s4 ⟨x.val⟩) ⟨x.val⟩)
        ⟨x.val⟩) :=
    bindingLinksAgree.of_objects_eq (finaliseThreadReleaseCores_objects _ ⟨x.val⟩)
  have F := bindingLinksAgree.trans (bindingLinksAgree.trans F5 F5y) F6
  exact ⟨F.ownerZero hOwn4, bindingBack.transport F hBB4⟩

/-- **A finalised thread's own record is quiesced** (WS-ZA ZA5.4 part 26), on a
state carrying the finalisation's invariant, the run queues' agreement and
`currentDequeuedUnique`, on which its admission admits it — read on the
pre-state alone: the admission carries to the state each later step runs on
(`finaliseThread_admissionCarried`, part 34).

The steps: the unbind clears the bound-notification code
(`finaliseThreadUnbindNotification_self`); the cancel leaves the thread ready
off every endpoint queue (`finaliseThreadCancel_quiets`); the loan return and
the walk end every waiter and keep the thread
(`finaliseThreadEndWaiters_returnLoan_endsAll`); the suspend marks
it `.Inactive` on no core (`finaliseThreadSuspend_quiets`, single placement from
`currentDequeuedUnique`), and its yield cancel leaves the thread yielded to no
context (`cancelYieldTo_yieldToCode_self`), writing the yield writes alone; the
release lets every core's hold go; the context unbind clears the binding
(`finaliseThreadUnbindSchedContext_self`) and its completion of the held
context's yield keeps the thread yielded to none
(`completeHeldYield_yieldToCode_zero`); and the invariant, carried along every
step (`finaliseCarried`), reads every other link
off a ready thread nothing waits on (`readyThread_unlinked`). -/
theorem finaliseThread_quiesces (x : SeLe4n.ObjId) (st : SystemState)
    (hI : finaliseStepInvariant st) (hRQ : st.runQueueRefined) (hCD : st.currentDequeuedUnique)
    (hBd : runCodeBounded st ⟨x.val⟩) (hA : threadFinaliseAdmitted st x = true) :
    threadRecordQuiesced (finaliseThread x st) x := by
  obtain ⟨hCancel, hWait, hBind⟩ := finaliseThread_admissionCarried x st hI hBd hA
  unfold finaliseThread; dsimp only; rw [if_pos hA]
  generalize threadHeldContextCode st ⟨x.val⟩ = held
  unfold finaliseThreadAfterRelease at hBind
  unfold finaliseThreadAfterCancel at hWait hBind
  -- The admission's reads of the thread.
  have hA0 := hA
  unfold threadFinaliseAdmitted at hA0
  rw [SystemState.getObject?_eq_getElem] at hA0
  split at hA0
  rotate_left
  · cases hA0
  rename_i tx0 hO
  dsimp only at hA0
  simp only [Bool.and_eq_true] at hA0
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hTid, -⟩, hIdle⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hBnc⟩, -⟩ := hA0
  simp only [beq_iff_eq] at hTid
  simp only [Bool.not_eq_true'] at hIdle
  have hX0 : st.getTcb? ⟨x.val⟩ = some tx0 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO
  -- The notification unbind.
  have C0 := finaliseCarried.start st ⟨x.val⟩ hI hBd
  have hX1 := finaliseThreadUnbindNotification_self hI.2.1 hX0
  have C1 := finaliseThreadUnbindNotification_closed _ (finaliseCarried.unbindStep st ⟨x.val⟩)
    st ⟨x.val⟩ hX0 hBnc C0
  generalize finaliseThreadUnbindNotification st ⟨x.val⟩ = s1 at hX1 C1 hCancel hWait hBind
  -- The cancel.
  obtain ⟨t2, hX2, k2⟩ := finaliseThreadCancel_quiets C1.1.2.1 hX1 (hCancel _ hX1)
  have C2 := finaliseThreadCancel_closed _ (finaliseCarried.notificationCancelStep st ⟨x.val⟩)
    (finaliseCarried.endpointCancelStep st ⟨x.val⟩) (finaliseCarried.replyStep st ⟨x.val⟩)
    s1 ⟨x.val⟩ C1
  generalize finaliseThreadCancel s1 ⟨x.val⟩ = s2 at hX2 C2 hWait hBind
  -- The loan return and the walk.
  obtain ⟨hL2, hAll2⟩ := hWait t2 hX2
  obtain ⟨hNoW4, hK4, -⟩ :=
    finaliseThreadEndWaiters_returnLoan_endsAll s2 ⟨x.val⟩ t2 C2.1 hX2 hL2 hAll2
  obtain ⟨t4, hX4, key4, -⟩ := hK4 t2 hX2
  have C4 := finaliseThreadEndWaiters_closed _ (finaliseCarried.replyStep st ⟨x.val⟩)
    (finaliseCarried.suspendStep st ⟨x.val⟩) _ ⟨x.val⟩
    (finaliseThreadReturnLoan_closed _ (finaliseCarried.replyStep st ⟨x.val⟩)
      (finaliseCarried.suspendStep st ⟨x.val⟩) s2 ⟨x.val⟩ C2)
  generalize finaliseThreadEndWaiters (finaliseThreadReturnLoan s2 ⟨x.val⟩) ⟨x.val⟩ = s4
    at hNoW4 hX4 C4 hBind
  have k4 : t4.cancelKey = TCB.quietKey { tx0 with boundNotificationCode := 0 }.bindKey := by
    refine Eq.trans ?_ k2
    obtain ⟨a1, a2, -, a4, a5, -, a7, a8, a9⟩ := key4
    simp only [TCB.cancelKey, a1, a2, a4, a5, a7, a8, a9]
  have hS4 : t4.ipcStateCode = 0 := congrArg (fun k => k.2.1) k4
  have hO4 : t4.ipcObjectCode = 0 := congrArg (fun k => k.1) k4
  -- The suspend.
  have hRef4 := (C4.2.1.1 hI.2.1 hRQ).2
  have hCD4 := C4.2.1.2 hI.2.1 hRQ hRef4 hCD
  obtain ⟨t5, hX5, kc5, hSus5, hM5, hz5, hCur5⟩ :=
    finaliseThreadSuspend_quiets C4.1.2.1 hCD4 C4.2.2.2 hX4 hS4 hO4 hIdle
  have hNoW5 := noWaiter_of_servers (finaliseThreadSuspend_servers s4 ⟨x.val⟩ C4.1.2.1) hNoW4
  have C5 := finaliseThreadSuspend_closed _ (finaliseCarried.suspendStep st ⟨x.val⟩) s4 ⟨x.val⟩ C4
  generalize finaliseThreadSuspend s4 ⟨x.val⟩ = s5 at hX5 hCur5 hNoW5 C5 hBind
  -- The suspend's yield cancel (seL4-MCS's `suspend` → `schedContext_cancelYieldTo`):
  -- it writes the yield writes alone, and leaves the thread yielded to no context.
  have A5 := SystemState.cancelYieldTo_objectsAgreeOffYield s5 ⟨x.val⟩ C5.1.2.1
  have e5 := A5.getTcb?_map TCB.withoutYieldWrites (fun _ => rfl) ⟨x.val⟩
  rw [hX5] at e5
  cases hX5y : (cancelYieldTo s5 ⟨x.val⟩).getTcb? ⟨x.val⟩ with
  | none => rw [hX5y] at e5; cases e5
  | some t5y =>
  rw [hX5y] at e5
  simp only [Option.map_some, Option.some.injEq] at e5
  have y5 := SystemState.cancelYieldTo_yieldToCode_self _ _ C5.1.2.1 hX5y
  have kc5y : t5y.cancelKey = t5.cancelKey := by have e := congrArg TCB.cancelKey e5; exact e
  have hz5y : t5y.runCoreCode = 0 := (congrArg TCB.runCoreCode e5).trans hz5
  have hCur5y : ∀ c, (cancelYieldTo s5 ⟨x.val⟩).scheduler.currentOnCore c ≠ some ⟨x.val⟩ := by
    rw [SystemState.cancelYieldTo_scheduler]; exact hCur5
  have hNoW5y := noWaiter_of_servers (s := s5)
    (fun y => A5.getTcb?_map TCB.blockingServer? (fun _ => rfl) y) hNoW5
  have C5y := (finaliseCarried.yieldStep st ⟨x.val⟩).cancel s5 ⟨x.val⟩ C5
  generalize cancelYieldTo s5 ⟨x.val⟩ = s5' at hX5y hCur5y hNoW5y C5y hBind
  -- The release.
  have hX6 : (finaliseThreadReleaseCores s5' ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t5y := by
    rw [finaliseThreadReleaseCores_getTcb?]; exact hX5y
  have hHeld6 : threadHeldOnSomeCore (finaliseThreadReleaseCores s5' ⟨x.val⟩) ⟨x.val⟩ = false := by
    obtain ⟨hF, hRs⟩ := finaliseThreadReleaseCores_unheld s5' ⟨x.val⟩
    unfold threadHeldOnSomeCore threadCurrentOnSomeCore
    rw [hF, hRs, finaliseThreadReleaseCores_scheduler]
    simp only [Bool.or_false, List.any_eq_false, beq_iff_eq]
    exact fun c _ => hCur5y c
  have hNoW6 := noWaiter_of_servers (s := s5')
    (tcbProjKept.of_objects (finaliseThreadReleaseCores_objects s5' ⟨x.val⟩)) hNoW5y
  have C6 := finaliseCarried.releaseStep st ⟨x.val⟩ s5' ⟨x.val⟩ C5y
  have hOwn6 := hBind.1 t5y hX6
  have hBd6 := hBind.2 t5y hX6
  generalize finaliseThreadReleaseCores s5' ⟨x.val⟩ = s6 at hX6 hHeld6 hNoW6 C6 hBd6
  -- The context unbind (seL4-MCS's `unbindFromSC`: `unbindTCB`, then the held
  -- context's yield completed).
  obtain ⟨hX7, hOth7, hCur7, hM7⟩ :=
    finaliseThreadUnbindSchedContext_self C6.1.2.1 hX6 hz5y hHeld6 hOwn6 hBd6
  have C7 := finaliseThreadUnbindSchedContext_closed _
    (finaliseCarried.scReleaseStep st ⟨x.val⟩).scUnbind s6 ⟨x.val⟩ C6
  have hNoW7 : ∀ v, ¬ ReplyViews.waiterOf
      (finaliseThreadUnbindSchedContext s6 ⟨x.val⟩).replyViews v ⟨x.val⟩ := by
    refine noWaiter_of_servers (fun y => ?_) hNoW6
    by_cases hy : y.toObjId = (⟨x.val⟩ : SeLe4n.ThreadId).toObjId
    · have hyx := SeLe4n.ThreadId.toObjId_injective _ _ hy
      subst hyx
      rw [hX7, hX6]; rfl
    · rw [hOth7 y hy]
  have hHeld7 : threadHeldOnSomeCore (finaliseThreadUnbindSchedContext s6 ⟨x.val⟩) ⟨x.val⟩ =
      false := by
    rw [← hHeld6]
    unfold threadHeldOnSomeCore threadCurrentOnSomeCore
    rw [hM7]; simp only [hCur7]
  -- The held context's yield completion: it writes the yield writes alone, and
  -- keeps the thread yielded to no context.
  have hInv7 := C7.1.2.1
  have e8 := (SystemState.completeHeldYield_objectsAgreeOffYield _ held hInv7).getTcb?_map
    TCB.withoutYieldWrites (fun _ => rfl) ⟨x.val⟩
  rw [hX7] at e8
  cases hX8 : (completeHeldYield (finaliseThreadUnbindSchedContext s6 ⟨x.val⟩)
      held).getTcb? ⟨x.val⟩ with
  | none => rw [hX8] at e8; cases e8
  | some t8 =>
  rw [hX8] at e8
  simp only [Option.map_some, Option.some.injEq] at e8
  have y8 := SystemState.completeHeldYield_yieldToCode_zero _ held hInv7 ⟨x.val⟩
    (fun t h => by rw [hX7] at h; cases h; exact y5) hX8
  have hHeld8 : threadHeldOnSomeCore (completeHeldYield
      (finaliseThreadUnbindSchedContext s6 ⟨x.val⟩) held) ⟨x.val⟩ = false := by
    rw [SystemState.completeHeldYield_eq_objects]; exact hHeld7
  -- The record's fields.
  have kq := kc5y.trans (kc5.trans k4)
  simp only [TCB.cancelKey, TCB.quietKey, TCB.bindKey, Prod.mk.injEq] at kq
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := kq
  obtain ⟨n1, n2, r1, r2, r3, r4, r5, r6⟩ := readyThread_unlinked C7.1 hX7 q2 q1 hNoW7
  refine ⟨t8, (SystemState.getTcb?_eq_some_iff _ _ _).mp hX8, ?_, ?_, hHeld8⟩
  · have htid : t8.tid = t5y.tid := by have e := congrArg TCB.tid e8; exact e
    rw [htid]
    rw [q7]; exact hTid
  · rw [threadLinksQuiescent_eq_withoutYieldWrites y8, e8]
    simp only [threadLinksQuiescent, TCB.withoutYieldWrites, Bool.and_eq_true, beq_iff_eq,
      Option.isNone_iff_eq_none]
    simp_all

end SeLe4n.Kernel
