/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDonatedInPlace
import SeLe4n.Kernel.IPC.Operations.UnheldContextPopInPlace

/-!
# The reply to a caller recording no server, written in place

WS-ZA ZA6.34: a caller whose server was finalised is blocked on its reply with
no server recorded (seL4-MCS's `finaliseCap` → `schedContext_unbindTCB`, which
leaves the callers blocked), and a holder of the reply capability may still
answer it (`doReplyTransfer`).  The reply leg wakes the caller and consumes its
reply object, with no server's reply waiters to leave (`storeReplyLegReady`);
then, where the reply object heads a context no thread holds, `reply_pop` hands
the context to the caller (`returnUnheldSchedContextInPlace`, settled on the
caller's home core).  Every refusal is ruled out before the first write
(`replyUnheldPopsInPlace`), the pop's own gate is carried across the reply leg
(`unheldPopsInPlace_transport`), and the result is proven equal to the
specification (`replyTransferChecked_unheld_inPlace`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyLeg

theorem storeReplyLegReady_noResizeDue (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeReplyLegReady st c rid).objects.noResizeDue := by
  unfold storeReplyLegReady
  dsimp only
  exact updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
    (enqueueRunnableOnCore_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ hNo)))

/-- The reply leg's writes change only the index-free part of the state. -/
theorem storeReplyLegReady_fields (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeReplyLegReady st c rid).objectIndexSet = st.objectIndexSet ∧
      (storeReplyLegReady st c rid).lifecycle = st.lifecycle := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hD := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer (st.updateTcb c receiverReady)
    (determineTargetCore (st.updateTcb c receiverReady) c) c
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo3,
    SystemState.modifyObject_eq_mapValueAt _ _ _ hNo2]
  unfold SystemState.mapTcbInPlace
  dsimp only
  rw [hD, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact ⟨rfl, rfl⟩

/-- **Off the answered caller and its reply object, the reply leg's writes
touch only links.** -/
theorem storeReplyLegReady_agree (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (x : SeLe4n.ObjId) (hxc : x ≠ c.toObjId) (hxr : x ≠ rid.toObjId) :
    ((storeReplyLegReady st c rid).objects[x]?).map KernelObject.withoutRunLinks =
      (st.objects[x]?).map KernelObject.withoutRunLinks := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  rw [objects_updateTcb_ne _ _ _ hNo3 x hxc, objects_modifyObject_ne _ _ _ hNo2 x hxr,
    enqueueRunnableOnCore_agree_of_findsInPlace _ _ c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1 x,
    objects_updateTcb_ne _ _ _ hNo x hxc]

/-- The reply leg's writes keep every key where it is found. -/
theorem storeReplyLegReady_keepsFinds (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue)
    (hFC : st.objects.findsInPlace c.toObjId = true) :
    (storeReplyLegReady st c rid).objectsKeepFinds st := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hK1 : (st.updateTcb c receiverReady).objectsKeepFinds st := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact SystemState.mapTcbInPlace_keepsFinds _ _ _
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo3]
  refine (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans ?_
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo2]
  refine (show SystemState.objectsKeepFinds _ _ from
    fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _).trans ?_
  exact (enqueueRunnableOnCore_keepsFinds _ _ c ((hK1 _).trans hFC)).trans hK1

/-- The reply leg's writes leave its reply object consumed. -/
theorem storeReplyLegReady_reply (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (rp : Reply) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNe : rid.toObjId ≠ c.toObjId) :
    (storeReplyLegReady st c rid).objects[rid.toObjId]? = some (.reply rp.consumed) := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace _
    (determineTargetCore (st.updateTcb c receiverReady) c) c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  rw [objects_updateTcb_ne _ _ _ hNo3 _ hNe, objects_modifyObject_self _ _ _ hNo2,
    hA2.get_reply_iff.mpr (by rw [objects_updateTcb_ne _ _ _ hNo _ hNe]; exact hRp)]
  rfl

/-- The answered caller after the reply leg, off its run-queue links: woken
ready with its reply object released, every other field as it was. -/
theorem storeReplyLegReady_callerView (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (hNe : rid.toObjId ≠ c.toObjId) :
    ∃ t, (storeReplyLegReady st c rid).objects[c.toObjId]? = some (.tcb t) ∧
      t.withoutRunLinks = ({ receiverReady ct with replyObjectCode := 0 } : TCB).withoutRunLinks := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace _
    (determineTargetCore (st.updateTcb c receiverReady) c) c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1
  obtain ⟨t2, h2, e2⟩ := hA2.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1)
  have h3 : ((enqueueRunnableOnCore (st.updateTcb c receiverReady)
      (determineTargetCore (st.updateTcb c receiverReady) c) c).modifyObject rid.toObjId
        replyConsumedObject).getTcb? c = some t2 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by rw [objects_modifyObject_ne _ _ _ hNo2 _ (fun e => hNe e.symm)]; exact h2)
  have h4 := SystemState.updateTcb_eq_mapTcbInPlace _ c (fun t => { t with replyObjectCode := 0 }) hNo3
  refine ⟨{ t2 with replyObjectCode := 0 }, ?_, ?_⟩
  · rw [h4]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mp
      (by rw [SystemState.mapTcbInPlace_getTcb?_self, h3]; rfl)
  · have hR : ∀ t : TCB, ({ t with replyObjectCode := 0 } : TCB).withoutRunLinks =
        { t.withoutRunLinks with replyObjectCode := 0 } := fun _ => rfl
    rw [hR, hR, e2]

end ReplyLeg

section UnheldGate

/-- **A reply to a caller recording no server whose pop may write in place**,
read on the pre-state: the caller `c` an unreserved thread, its slot and its
reply object's local, the reply object heading the stack of context `s` (the
context naming it back), and the unheld pop's own gate passing there
(`unheldPopsInPlace`).  Every read is a code, so the test builds nothing. -/
@[inline] def replyUnheldPopsInPlace (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : Bool :=
  !c.isReserved &&
  storeLeavesIndexAndTypes st c.toObjId .tcb &&
  st.objects.findsInPlace c.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  (match st.getReply? rid with
   | some rp =>
     match rp.next with
     | some (.head s) =>
       (match st.getSchedContext? s with
        | some sc =>
          match sc.scReply with
          | some h => h.val == rid.val
          | none => false
        | none => false) &&
       unheldPopsInPlace st s c
     | _ => false
   | none => false)

/-- **The unheld pop's gate is carried to a state that agrees off a thread and
a reply**: where `T` agrees with `st` off the caller `c` and the reply object
`rid` (up to run-queue links), keeps every slot's index, type and place, keeps
the caller's binding code and the reply object's links, the gate that passes on
`st` passes on `T`. -/
theorem unheldPopsInPlace_transport {st T : SystemState} {s : SeLe4n.SchedContextId}
    {c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {ct : TCB} {rp : Reply}
    (hT : st.getTcb? c = some ct) (hRp : st.getReply? rid = some rp)
    (hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks)
    (hLT : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true)
    (hFT : ∀ k, T.objects.findsInPlace k = st.objects.findsInPlace k)
    (hTC : ∃ t, T.getTcb? c = some t ∧ t.scBindingScCode = ct.scBindingScCode)
    (hTR : ∃ r, T.getReply? rid = some r ∧ r.next = rp.next ∧ r.prev = rp.prev)
    (hHead : rp.next = some (.head s))
    (hG : unheldPopsInPlace st s c = true) : unheldPopsInPlace T s c = true := by
  have hTo : st.objects[c.toObjId]? = some (.tcb ct) := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hRo : st.objects[rid.toObjId]? = some (.reply rp) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hRp
  obtain ⟨t, hTt, hTb⟩ := hTC
  obtain ⟨r, hTr, hRn, hRpv⟩ := hTR
  unfold unheldPopsInPlace at hG ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG ⊢
  obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hLsc⟩, hFsc⟩, hCm⟩, hM⟩ := hG
  refine ⟨⟨⟨⟨⟨hCRes, hLT hLC⟩, hLT hLsc⟩, (hFT _).trans hFsc⟩, ?_⟩, ?_⟩
  · rw [hTt]; rw [hT] at hCm; show (t.scBindingScCode == 0) = true; rw [hTb]; exact hCm
  cases hScg : st.getSchedContext? s with
  | none => rw [hScg] at hM; cases hM
  | some sc =>
  rw [hScg] at hM
  have hScO : st.objects[s.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg
  have hScC : s.toObjId ≠ c.toObjId := fun e => by rw [e, hTo] at hScO; cases hScO
  have hScR : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRo] at hScO; cases hScO
  have hScT : T.getSchedContext? s = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hScC hScR) (fun _ e => by cases e) hScO)
  rw [hScT]
  dsimp only at hM ⊢
  simp only [Bool.and_eq_true] at hM ⊢
  obtain ⟨hBT, hM⟩ := hM
  refine ⟨hBT, ?_⟩
  cases hSr : sc.scReply with
  | none => rw [hSr] at hM; cases hM
  | some h =>
  rw [hSr] at hM
  dsimp only at hM ⊢
  simp only [Bool.and_eq_true] at hM ⊢
  obtain ⟨⟨hLh, hFh⟩, hM⟩ := hM
  refine ⟨⟨hLT hLh, (hFT _).trans hFh⟩, ?_⟩
  -- The head reply on `T`: the answered reply object itself, or untouched.
  obtain ⟨hp, hHp, hpN, hpP⟩ : ∃ hp, st.getReply? h = some hp ∧
      (∃ hp', T.getReply? h = some hp' ∧ hp'.next = hp.next ∧ hp'.prev = hp.prev) ∧ True := by
    cases hHg : st.getReply? h with
    | none => rw [hHg] at hM; cases hM
    | some hp =>
      refine ⟨hp, rfl, ?_, trivial⟩
      by_cases hhr : h = rid
      · subst hhr
        rw [hRp] at hHg; cases hHg
        exact ⟨r, hTr, hRn, hRpv⟩
      · have hHo : st.objects[h.toObjId]? = some (.reply hp) :=
          (SystemState.getReply?_eq_some_iff _ _ _).mp hHg
        have hhc : h.toObjId ≠ c.toObjId := fun e => by rw [e, hTo] at hHo; cases hHo
        have hhr' : h.toObjId ≠ rid.toObjId := fun e => hhr (SeLe4n.ReplyId.toObjId_injective _ _ e)
        exact ⟨hp, (SystemState.getReply?_eq_some_iff _ _ _).mpr
          (agreeAt_of_not_tcb (hView _ hhc hhr') (fun _ e => by cases e) hHo), rfl, rfl⟩
  obtain ⟨hp', hTh, hN', hP'⟩ := hpN
  rw [hHp] at hM
  rw [hTh]
  dsimp only at hM ⊢
  simp only [Bool.and_eq_true] at hM ⊢
  obtain ⟨hMn, hMp⟩ := hM
  rw [hN', hP']
  refine ⟨hMn, ?_⟩
  cases hPv : hp.prev with
  | none => rfl
  | some b =>
  rw [hPv] at hMp
  dsimp only at hMp ⊢
  simp only [Bool.and_eq_true] at hMp ⊢
  obtain ⟨⟨⟨hbne, hLb⟩, hFb⟩, hBm⟩ := hMp
  refine ⟨⟨⟨hbne, hLT hLb⟩, (hFT _).trans hFb⟩, ?_⟩
  cases hBg : st.getReply? b with
  | none => rw [hBg] at hBm; cases hBm
  | some bR =>
  rw [hBg] at hBm
  have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hBg
  have hbc : b.toObjId ≠ c.toObjId := fun e => by rw [e, hTo] at hBO; cases hBO
  -- `b` names a frame above it, and the answered reply object heads a context.
  have hbr : b.toObjId ≠ rid.toObjId := by
    intro e
    have hbe : b = rid := SeLe4n.ReplyId.toObjId_injective _ _ e
    subst hbe
    rw [hRp] at hBg; cases hBg
    dsimp only at hBm
    rw [hHead] at hBm
    simp at hBm
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hbc hbr) (fun _ e => by cases e) hBO)]
  dsimp only at hBm ⊢
  simp only [Bool.and_eq_true] at hBm ⊢
  obtain ⟨⟨hBN, hBC⟩, hOut⟩ := hBm
  refine ⟨⟨hBN, hBC⟩, ?_⟩
  revert hOut
  generalize bR.callerCode = k
  intro hOut
  cases k with
  | zero => rfl
  | succ o =>
    simp only [outerCallerAcceptableCode, Bool.and_eq_true] at hOut ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hOut
    refine ⟨⟨h1, h2⟩, ?_⟩
    have hoc : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ c.toObjId := fun e => by
      have := SeLe4n.ThreadId.toObjId_injective _ _ e
      rw [← this] at h1; simp at h1
    have hor : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ rid.toObjId := fun e => by
      unfold outerTestAt at h3
      rw [(show st.getTcb? ⟨o⟩ = none from by
        unfold SystemState.getTcb?; rw [e, hRo])] at h3
      cases h3
    rw [outerTestAt_of_view (hView _ hoc hor)]; exact h3

end UnheldGate

section UnheldPopMoves

/-- The unheld pop leaves the table's size and capacity alone. -/
theorem returnUnheldSchedContextInPlace_noResizeDue (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    (returnUnheldSchedContextInPlace st owner scId).objects.noResizeDue := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact hNo
  · split
    · exact hNo
    · split
      · exact hNo
      · split
        · exact hNo
        · dsimp only
          rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
          refine updateTcb_noResizeDue _ _ _ ?_
          split <;> (repeat (first | exact hNo | apply modifyObject_noResizeDue |
            apply updateSchedContext_noResizeDue))

/-- **The unheld pop commutes with a delivery**, to the recipient it binds or to
any other thread: the pop reads the recipient's priority, deadline, domain and
budget, none of which a delivery writes. -/
theorem returnUnheldSchedContextInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (owner : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    returnUnheldSchedContextInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) owner scId =
      (returnUnheldSchedContextInPlace st owner scId).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  have hPop : ∀ x : Reply, popOuterCode (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) x =
      popOuterCode st x := by
    intro x; unfold popOuterCode; simp only [SystemState.getReply?_mapTcbInPlace]
  unfold returnUnheldSchedContextInPlace
  simp only [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getReply?_mapTcbInPlace,
    effectiveDeadline_msg, hasSufficientBudget_msg, hPop]
  cases st.getSchedContext? scId with
  | none => rfl
  | some sc =>
    try dsimp only
    cases sc.scReply with
    | none => rfl
    | some hr =>
      try dsimp only
      cases st.getReply? hr with
      | none => rfl
      | some rr =>
        try dsimp only
        rcases getTcb?_msg_cases r ρ μ π st owner with h | ⟨_, h⟩ <;> rw [h] <;>
          cases st.getTcb? owner <;> (try simp only [Option.map_none]) <;>
          try (with_reducible rfl)
        all_goals
          try simp only [Option.map_some, TCB.withMessageSlots_boostedPriority,
            TCB.withMessageSlots_domain, effectiveDeadline_withMessageSlots,
            hasSufficientBudget_withMessageSlots]
          try dsimp only
          cases rr.prev with
          | none =>
            try dsimp only
            rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
              modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (fun o => by cases o <;> rfl),
              updateTcb_msg r ρ μ π _ owner _ ?_ ?_,
              markCandidacyGainFor_msg, markKeyChangeParts_msg]
            all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
              with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))
          | some b =>
            try dsimp only
            rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
              modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (fun o => by cases o <;> rfl),
              modifyObject_msg r ρ μ _ _ _ ?_ (fun o => by cases o <;> rfl),
              updateTcb_msg r ρ μ π _ owner _ ?_ ?_,
              markCandidacyGainFor_msg, markKeyChangeParts_msg]
            all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
              with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))

end UnheldPopMoves

section UnheldReplyDelivered

/-- **The gate carries the pop across the reply leg**: under
`replyUnheldPopsInPlace` the reply object heads the stack of context `scId` (the
code the arm reads), and on the state the reply leg leaves (its writes, the
caller holding message `msg`) the reply's donation step is the in-place unheld
pop, settled on the caller's home core read on the pre-state. -/
theorem replyUnheldPopsInPlace_pop (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hG : replyUnheldPopsInPlace st c rid = true) :
    ∃ rp scId, st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.next = some (.head scId) ∧
      replyHeadContextCode st rid = scId.val + 1 ∧
      c.isReserved = false ∧ st.objects.noResizeDue ∧
      storeLeavesIndexAndTypes st c.toObjId .tcb = true ∧
      st.objects.findsInPlace c.toObjId = true ∧
      storeLeavesIndexAndTypes st rid.toObjId .reply = true ∧
      st.objects.findsInPlace rid.toObjId = true ∧
      replyRecvPopDonation rid c ((storeReplyLegReady st c rid).mapTcbInPlace c (holdMessage msg)) =
        .ok (none, SchedContextOps.settleReturnedContext
          (returnUnheldSchedContextInPlace
            ((storeReplyLegReady st c rid).mapTcbInPlace c (holdMessage msg)) c scId)
          (determineTargetCore st c) scId) ∧
      (∀ cv : SeLe4n.ValidThreadId, cv.val = c →
        applyReplyDonationOnCore
            ((storeReplyLegReady st c rid).mapTcbInPlace c (holdMessage msg)) rid cv
            (replyDonationRecipientHome
              ((storeReplyLegReady st c rid).mapTcbInPlace c (holdMessage msg)) rid c) =
          .ok (SchedContextOps.settleReturnedContext
            (returnUnheldSchedContextInPlace
              ((storeReplyLegReady st c rid).mapTcbInPlace c (holdMessage msg)) c scId)
            (determineTargetCore st c) scId)) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  unfold replyUnheldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hM⟩ := hG
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFC
  cases hRg : st.getReply? rid with
  | none => rw [hRg] at hM; cases hM
  | some rp =>
  rw [hRg] at hM
  dsimp only at hM
  have hRp : st.objects[rid.toObjId]? = some (.reply rp) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hRg
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head scId =>
  rw [hN] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hSm, hU⟩ := hM
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hSm; cases hSm
  | some sc =>
  rw [hScg] at hSm
  dsimp only at hSm
  have hHead : sc.scReply = some rid := by
    revert hSm
    cases sc.scReply with
    | none => intro h; cases h
    | some h =>
      intro e
      have : h = rid := by cases h; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
      rw [this]
  have hBT : sc.boundThreadCode = 0 := by
    have hU' := hU
    unfold unheldPopsInPlace at hU'
    rw [hScg] at hU'
    simp only [Bool.and_eq_true] at hU'
    exact beq_iff_eq.mp hU'.2.1
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg
  refine ⟨rp, scId, hRp, hN, by simp only [replyHeadContextCode, hRg, hN],
    hCRes, hNo, hLC, hFC, hLR, hFR, ?_⟩
  -- The state after the reply leg, against the pre-state.
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  generalize hS1 : storeReplyLegReady st c rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  obtain ⟨hI, hL⟩ := storeReplyLegReady_fields st c rid hNo
  rw [hS1] at hI hL
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [← hTdef, hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by
    rw [← hTdef, hHold _ hRc]; exact hR1
  have hV : ∀ x, notVSpaceRootAt st x = true → notVSpaceRootAt T x = true := by
    intro x hx
    by_cases hxc : x = c.toObjId
    · subst hxc; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hTC]
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hTR]
      · rw [notVSpaceRootAt_of_view (hView x hxc hxr)]; exact hx
  have hLT : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true := fun h => by
    rw [← hTdef]
    exact storeLeavesIndexAndTypes_of_frame (s' := S1.mapTcbInPlace c (holdMessage msg)) hI hL
      (hTdef ▸ hV) h
  have hFT : ∀ k, T.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hTdef]; exact ((SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK) k
  have hRT : T.getReply? rid = some rp.consumed := (SystemState.getReply?_eq_some_iff _ _ _).mpr hTR
  have hNextC : rp.consumed.next = some (.head scId) := by simp only [Reply.consumed, hN]
  have hPrevC : rp.consumed.prev = rp.prev := by simp only [Reply.consumed, hN]
  have hScC : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hScR : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hScC hScR) (fun _ e => by cases e) hScO)
  have hOT : T.getTcb? c = some (holdMessage msg tc1) := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC
  have hBC : (holdMessage msg tc1).scBindingScCode = ct.scBindingScCode := by
    have h := congrArg TCB.scBindingScCode hc1; exact h
  have hUT : unheldPopsInPlace T scId c = true :=
    unheldPopsInPlace_transport hTc hRg hView hLT hFT
      ⟨holdMessage msg tc1, hOT, hBC⟩
      ⟨rp.consumed, hRT, by rw [hNextC, hN], hPrevC⟩ hN hU
  have hCtx : replyFrameHeadContext? T rid = some scId := by
    unfold replyFrameHeadContext?
    rw [hRT]
    simp only [hNextC, hScT, hHead, beq_self_eq_true, ↓reduceIte]
  have hHolder : replyFrameHeadHolder? T rid = none := by
    unfold replyFrameHeadHolder?
    rw [hCtx]
    simp only [hScT, Option.bind_some, SchedContext.boundThread, hBT]
    rfl
  have hDT : determineTargetCore T c = determineTargetCore st c := by
    have e : tc1.cpuAffinity = ct.cpuAffinity := by
      have h := congrArg TCB.cpuAffinity hc1; exact h
    unfold determineTargetCore
    rw [hOT, hTc]
    show (match tc1.cpuAffinity with | some c' => c' | none => bootCoreId) = _
    rw [e]
    rfl
  have hPopT : popUnheldReplyHead T rid c (determineTargetCore T c) =
      .ok (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace T c scId)
        (determineTargetCore st c) scId) := by
    rw [hDT, popUnheldReplyHead_eq_impl]
    unfold popUnheldReplyHeadImpl
    rw [hCtx]
    simp only [hUT, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · unfold replyRecvPopDonation
    rw [hHolder]
    simp only [hPopT]
  intro cv hcv
  subst hcv
  unfold applyReplyDonationOnCore replyDonationRecipientHome
  rw [hHolder]
  simp only []
  exact hPopT

/-- **The reply to a caller recording no server, delivered**: the caller woken
without the message, its reply object consumed, the context its reply object
heads handed to it in place (`returnUnheldSchedContextInPlace`, settled on its
home `home`), then the reply's frame written into the caller's saved registers.
No server's reply waiters to leave and no server's boost to revert: none is
recorded. -/
@[noinline] def performReplyUnheldDelivered (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  let X := SchedContextOps.settleReturnedContext
    (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrameW layout rf len badgeWord badged)
    (fun _ => holdDeliveredBody X c layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- **The checked reply to a caller recording no server, in place**: under the
flow gate and `replyUnheldPopsInPlace`, a reply of at most four words to an
unfaulted caller blocked on it with no server recorded, whose reply object heads
the stack of a context no thread holds, commits `performReplyUnheldDelivered`'s
state, its context the one the reply object heads (`replyHeadContextCode`) and
its home the caller's, both read on the pre-state. -/
theorem replyTransferChecked_unheld_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) (msg : IpcMessage)
    (grant : Bool)
    (hMsg : msg =
      { registers := Architecture.regMessageBody layout rf len, badge := SeLe4n.Badge.opt badgeWord badged })
    (hSz : ¬ Architecture.regMessageLength layout len > maxMessageRegisters)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hX : (!grant || !receiverHasBuffer st ct || (receiveSlot? st ct).isNone) = true)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true) :
    replyTransferOnCoreChecked ctx replier c mi regs msg grant core st =
      .ok ((), performReplyUnheldDelivered st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) layout rf len badgeWord badged) := by
  replace hMsg := hMsg.symm
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, -, hPop⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  have hSz' : ¬ msg.registers.size > maxMessageRegisters := by
    rw [← hMsg, Architecture.regMessageBody_size]; exact hSz
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st replier c none ct ep rid rp msg core hSz' hT hIpc
    hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  have hRec : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyLegReady_noResizeDue st c rid hNo
  have hNoP := returnUnheldSchedContextInPlace_noResizeDue _ c scId hNoS
  have hNoQ := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId hNoP
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte,
    replyTransferCaps_of_inert st replier c grant ct hTc hX, CapTransferSummary.capInfo_empty]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hAns, hcv, SystemState.unlinkReplyWaiterOpt]
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performReplyUnheldDelivered
  subst hMsg
  rw [returnUnheldSchedContextInPlace_msg c id _ id _ c scId hNoS, settleReturnedContext_msg,
    Architecture.regMessageFrameW_eq,
    stageDeliveredMessage_holdMessage _ _ _ hNoQ
      (by rw [Architecture.regMessageBody_size]; exact hSz4),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

end UnheldReplyDelivered

end SeLe4n.Kernel
