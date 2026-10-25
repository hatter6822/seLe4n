/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.FinaliseThreadFrames

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
  thread, lent from no one, heading no reply stack.
* **The thread** (`finaliseThread_quiesces`): `.Inactive` and `.ready`, linked
  into no queue and heading none, bound to no notification and to no
  scheduling context, holding no reply link or stash and no timeout budget,
  and held by no core — every field `threadLinksQuiescent` reads, the space
  slots aside, which the zombie loop empties after the finalisation.

What the record does not say — that no *other* object still names the
finalised one — is the retire's store walk today, and the reciprocity
invariants that replace it are `docs/planning/UNTYPED_RESET_PLAN.md` row 27,
which consumes these theorems.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The scheduling context
-- ============================================================================

/-- **A finalised scheduling context's own record is released**: the context
at `x` is stored, bound to no thread, lent from no one and heading no reply
stack — the record half of `schedContextRetirable`. -/
def schedContextRecordReleased (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∃ sc, st.objects[x]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
    sc.donationOrigin = none ∧ sc.scReply = none

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
    (determineTargetCore s tid) _ hBind
  rw [hOk]
  dsimp only
  have hObj := cancelBoundDonationOnCore_objects s _ tid _ _ _ hBind hOk
  have hNe : tid.toObjId ≠ x := by
    intro e
    have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [e, hO] at this; cases this
  have hG' : s.getSchedContext? ⟨x.val⟩ = some sc := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO
  have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt s ⟨x.val⟩
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
  refine ⟨⟨{ sc with boundThreadCode := 0, isActive := false, donationOrigin := none }, ?_, rfl⟩,
    fun k r hk => ?_⟩
  · rw [hObj, SystemState.updateTcb_objects_ne _ _ _ _ hNe hInv1,
      SystemState.updateSchedContext_eq_of_some hG']
    dsimp only
    rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
      RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
  · have hkx : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId ≠ k := by
      intro e; rw [← e] at hk; rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
        hO] at hk; cases hk
    have hkt : tid.toObjId ≠ k := by
      intro e
      have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      rw [e, hk] at this; cases this
    rw [hObj, SystemState.updateTcb_objects_ne _ _ _ _ hkt hInv1,
      SystemState.updateSchedContext_objects_ne _ _ _ _ hkx hInv]
    exact hk

/-- **The holder's deschedule keeps the context and every reply**: it writes
run-queue links alone. -/
theorem finaliseSchedContextDeschedule_keeps {s : SystemState} {x k : SeLe4n.ObjId}
    {o : KernelObject} (hNot : ∀ t, o ≠ .tcb t) (hk : s.objects[k]? = some o) :
    (finaliseSchedContextDeschedule s x).objects[k]? = some o :=
  (finaliseSchedContextDeschedule_objectsAgreeOffRunLinks s x).get_of_not_tcb hNot hk

/-- **A finalised scheduling context's own record is released**
(WS-ZA ZA5.4 part 26): on a state its admission admits, the finalisation
leaves the context at `x` bound to no thread and lent from no one — the
holder's unbind clears both (`finaliseSchedContextUnbind_released`) — and
heading no reply stack: the head reply the admission reads still names the
context as its head after the deschedule and the unbind, which write no reply,
so the unstack runs and clears the head. -/
theorem finaliseSchedContext_releases (x : SeLe4n.ObjId) (st : SystemState)
    (hInv : st.objects.invExt) (hA : schedContextFinaliseAdmitted st x = true) :
    schedContextRecordReleased (finaliseSchedContext x st) x := by
  rw [finaliseSchedContext_eq, if_pos hA]
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
    finaliseSchedContextDeschedule_closed (fun s => s.objects.invExt)
      (fun s t _ h _ _ _ _ => descheduleAtPlacement_preserves_objects_invExt s t h) st x hInv
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
  finaliseThreadReleaseCores (finaliseThreadSuspend (finaliseThreadEndWaiters
    (finaliseThreadReturnLoan (finaliseThreadAfterCancel st tid) tid) tid) tid) tid

/-- **A finalised thread's own record is quiesced** (WS-ZA ZA5.4 part 26), on a
state carrying the finalisation's invariant, the run queues' agreement and
`currentDequeuedUnique`, on which its admission admits it, and stated on the
states where each later step runs, as part 25's walk theorem is: the cancel's
own admission on the state the notification unbind leaves (`hCancel`), the
waiters' admission on the state the cancel leaves (`hWait`), and the context
unbind's binding clause on the state the release leaves (`hBind`).  That the
pre-state admission carries to those states — so no step's guard refuses after
an earlier step has written, which is what proves checks-before-writes for the
thread finalisation — is `docs/planning/UNTYPED_RESET_PLAN.md` row 27; today
each step and the retire re-check their own guards.

The steps: the unbind clears the bound-notification code
(`finaliseThreadUnbindNotification_self`); the cancel leaves the thread ready
off every endpoint queue (`finaliseThreadCancel_quiets`); the loan return and
the walk end every waiter and keep the thread
(`finaliseThreadEndWaiters_returnLoan_endsAll_of_admitted`); the suspend marks
it `.Inactive` on no core (`finaliseThreadSuspend_quiets`, single placement from
`currentDequeuedUnique`); the release lets every core's hold go; the context
unbind clears the binding (`finaliseThreadUnbindSchedContext_self`); and the
invariant, carried along every step (`finaliseCarried`), reads every other link
off a ready thread nothing waits on (`readyThread_unlinked`). -/
theorem finaliseThread_quiesces (x : SeLe4n.ObjId) (st : SystemState)
    (hI : finaliseStepInvariant st) (hRQ : st.runQueueRefined) (hCD : st.currentDequeuedUnique)
    (hBd : runCodeBounded st ⟨x.val⟩) (hA : threadFinaliseAdmitted st x = true)
    (hCancel : ∀ t1, (finaliseThreadUnbindNotification st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t1 →
      threadIpcCancelAdmitted (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩ t1 = true)
    (hWait : ∀ t2, (finaliseThreadAfterCancel st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t2 →
      replyWaitersAdmitted (finaliseThreadAfterCancel st ⟨x.val⟩) ⟨x.val⟩ t2 = true ∧
        (t2.scBindingOwnerCode ≠ 0 → t2.scBindingScCode ≠ 0))
    (hBind : ∀ t6, (finaliseThreadAfterRelease st ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t6 →
      t6.scBindingOwnerCode = 0 ∧ (t6.scBindingScCode ≠ 0 → ∃ sc,
        (finaliseThreadAfterRelease st ⟨x.val⟩).getSchedContext? ⟨t6.scBindingScCode - 1⟩ = some sc ∧
          sc.boundThreadCode = x.val + 1)) :
    threadRecordQuiesced (finaliseThread x st) x := by
  rw [finaliseThread_eq, if_pos hA]
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
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hTid, -⟩, hIdle⟩, -⟩, -⟩, -⟩, -⟩, hBnc⟩, -⟩ := hA0
  simp only [beq_iff_eq] at hTid
  simp only [Bool.not_eq_true'] at hIdle
  have hX0 : st.getTcb? ⟨x.val⟩ = some tx0 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO
  -- The notification unbind.
  have C0 := finaliseCarried.start st ⟨x.val⟩ hI hBd
  have hX1 := finaliseThreadUnbindNotification_self hI.2.1 hX0 hBnc
  have C1 := finaliseThreadUnbindNotification_closed _ (finaliseCarried.unbindStep st ⟨x.val⟩)
    st ⟨x.val⟩ C0
  generalize finaliseThreadUnbindNotification st ⟨x.val⟩ = s1 at hX1 C1 hCancel hWait hBind
  -- The cancel.
  obtain ⟨t2, hX2, k2⟩ := finaliseThreadCancel_quiets C1.1.2.1 hX1 (hCancel _ hX1)
  have C2 := finaliseThreadCancel_closed _ (finaliseCarried.notificationCancelStep st ⟨x.val⟩)
    (finaliseCarried.endpointCancelStep st ⟨x.val⟩) (finaliseCarried.replyStep st ⟨x.val⟩)
    s1 ⟨x.val⟩ C1
  generalize finaliseThreadCancel s1 ⟨x.val⟩ = s2 at hX2 C2 hWait hBind
  -- The loan return and the walk.
  obtain ⟨hW2, hSc2⟩ := hWait t2 hX2
  obtain ⟨hNoW4, hK4⟩ :=
    finaliseThreadEndWaiters_returnLoan_endsAll_of_admitted s2 ⟨x.val⟩ t2 C2.1 hX2 hSc2 hW2
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
  -- The release.
  have hX6 : (finaliseThreadReleaseCores s5 ⟨x.val⟩).getTcb? ⟨x.val⟩ = some t5 := by
    rw [finaliseThreadReleaseCores_getTcb?]; exact hX5
  have hHeld6 : threadHeldOnSomeCore (finaliseThreadReleaseCores s5 ⟨x.val⟩) ⟨x.val⟩ = false := by
    obtain ⟨hF, hRs⟩ := finaliseThreadReleaseCores_unheld s5 ⟨x.val⟩
    unfold threadHeldOnSomeCore threadCurrentOnSomeCore
    rw [hF, hRs, finaliseThreadReleaseCores_scheduler]
    simp only [Bool.or_false, List.any_eq_false, beq_iff_eq]
    exact fun c _ => hCur5 c
  have hNoW6 := noWaiter_of_servers (s := s5)
    (tcbProjKept.of_objects (finaliseThreadReleaseCores_objects s5 ⟨x.val⟩)) hNoW5
  have C6 := finaliseCarried.releaseStep st ⟨x.val⟩ s5 ⟨x.val⟩ C5
  obtain ⟨hOwn6, hBd6⟩ := hBind t5 hX6
  generalize finaliseThreadReleaseCores s5 ⟨x.val⟩ = s6 at hX6 hHeld6 hNoW6 C6 hBd6
  -- The context unbind.
  obtain ⟨hX7, hOth7, hCur7, hM7⟩ :=
    finaliseThreadUnbindSchedContext_self C6.1.2.1 hX6 hz5 hHeld6 hOwn6 hBd6
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
  -- The record's fields.
  have kq := kc5.trans k4
  simp only [TCB.cancelKey, TCB.quietKey, TCB.bindKey, Prod.mk.injEq] at kq
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := kq
  obtain ⟨n1, n2, r1, r2, r3, r4, r5, r6⟩ := readyThread_unlinked C7.1 hX7 q2 q1 hNoW7
  refine ⟨_, (SystemState.getTcb?_eq_some_iff _ _ _).mp hX7, ?_, ?_, hHeld7⟩
  · show t5.tid.val = x.val
    rw [q7]; exact hTid
  · simp only [threadLinksQuiescent, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none]
    simp_all

end SeLe4n.Kernel
