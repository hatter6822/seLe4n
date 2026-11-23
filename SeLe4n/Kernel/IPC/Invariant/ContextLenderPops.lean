-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.ContextLenderRemovals

/-!
# The lenders across the donation pop and the donation push

WS-SX SX8 (D27).  The pop moves a context's head down to the frame below it and
takes the old head off: a links shrink (`returnDonatedSchedContext_linksShrink`),
so it carries the lenders' flow with no label hypothesis.  The push makes a frame
on no stack the context's new head: it adds a lender, the pushed frame's caller,
which is the donor (`replyCallerLinkageReciprocal`), so it carries the flow
exactly where the donor flows to the context's label
(`donateSchedContext_preserves_contextLendersFlow`) — the fact the lend
admission (`callLendAdmits`) checks before every lend.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The views read the object store alone. -/
theorem contextStackLinksShrink_of_objects_eq {st st' : SystemState}
    (h : st'.objects = st.objects) : contextStackLinksShrink st st' :=
  contextStackLinksShrink_of_agree (fun _ _ hx => h ▸ hx) (fun _ _ hx => h ▸ hx)

/-! ### The pop -/

theorem storeDonationHeadClear_linksShrink {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : storeDonationHeadClear head? st = .ok st') :
    contextStackLinksShrink st st' := by
  cases head? with
  | none => cases h; exact .refl _
  | some rid =>
    rw [storeDonationHeadClear_some] at h
    cases hR : st.getReply? rid with
    | none => rw [hR] at h; cases h
    | some r =>
      rw [hR] at h; simp only [] at h
      split at h
      · cases h
      · rename_i hS; cases h
        exact contextStackLinksShrink_storeReply hObjInv hR hS (.inl rfl) (.inr rfl)

theorem storeReplyReHead_linksShrink {scId : SeLe4n.SchedContextId}
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : storeReplyReHead scId head? st = .ok st') :
    contextStackLinksShrink st st' := by
  cases head? with
  | none => cases h; exact .refl _
  | some rid =>
    rw [storeReplyReHead_some] at h
    cases hR : st.getReply? rid with
    | none => rw [hR] at h; cases h
    | some r =>
      rw [hR] at h; simp only [] at h
      split at h
      · cases h
      · rename_i hS; cases h
        exact contextStackLinksShrink_storeReply hObjInv hR hS (.inr rfl) (.inr rfl)

theorem storeDonationHeadPop_linksShrink {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : storeDonationHeadPop scId head? st = .ok st') :
    contextStackLinksShrink st st' := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, h1, h2⟩
  · exact .refl _
  · exact (storeDonationHeadClear_linksShrink hObjInv h1).trans
      (storeReplyReHead_linksShrink (storeDonationHeadClear_preserves_objects_invExt hObjInv h1) h2)

/-- **A context's head moved to the frame below its head** (or cleared). -/
theorem contextStackLinksShrink_storeHeadBelow {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext} {head? : Option (SeLe4n.ReplyId × Reply)}
    (hObjInv : st.objects.invExt) (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hHead : donationHeadOf? st scId sc = .ok head?)
    (hH : sc'.scReply = head?.bind (fun p => p.2.prev))
    (h : storeObject scId.toObjId (.schedContext sc') st = .ok ((), st')) :
    contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_storeSchedContext hObjInv h fun x hx => ?_
  rw [hH] at hx
  cases head? with
  | none => cases hx
  | some p =>
    obtain ⟨rid, r⟩ := p
    have hKey := donationHeadOf?_ok_key st scId sc _ hHead
    obtain ⟨hR, -⟩ := donationHeadOf?_ok_resolves st scId sc rid r hHead
    exact .lower (r := rid)
      (.head (by rw [contextStackHead_eq_obj, hSc]; simpa [objStackHead] using hKey.symm))
      (by rw [replyStackPrev_eq_obj, hR]; exact hx)

/-- **The donation return is a links shrink.** -/
theorem returnDonatedSchedContext_linksShrink {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    contextStackLinksShrink st st' := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4, hSc, -, -, hHead, hS1, hS2, -, hS3,
      -, hS4, hEq⟩ := returnDonatedSchedContext_ok_storeChain st st' serverTid scId
    originalOwner newOwner? h
  have hI1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hI2 := storeDonationHeadPop_preserves_objects_invExt hI1 hS2
  have hI3 := storeObject_preserves_objects_invExt s2 s3 _ _ hI2 hS3
  exact ((((contextStackLinksShrink_storeHeadBelow hObjInv hSc hHead rfl hS1).trans
    (storeDonationHeadPop_linksShrink hI1 hS2)).trans
    (contextStackLinksShrink_storeObject_other hI2 hS3 (fun _ e => by cases e)
      (fun _ e => by cases e))).trans
    (contextStackLinksShrink_storeObject_other hI3 hS4 (fun _ e => by cases e)
      (fun _ e => by cases e))).trans (contextStackLinksShrink_of_objects_eq (by rw [hEq]))

theorem returnDonatedSchedContext_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (returnDonatedSchedContext_linksShrink hObjInv h)

/-! ### The push -/

/-- **The push's three writes, slot by slot**: the context's new head, the
pushed frame linked down to the old head, and the old head's upward link. -/
theorem donationHeadPush_slots {st s1 s2 : SystemState} {scId : SeLe4n.SchedContextId}
    {sc scStored : SchedContext} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    (hObjInv : st.objects.invExt) (hSc : st.getSchedContext? scId = some sc)
    (hRep : st.getReply? pushRid = some pushReply)
    (hS1 : storeObject scId.toObjId (.schedContext scStored) st = .ok ((), s1))
    (hS2 : storeDonationFramePush scId pushRid pushReply sc.scReply s1 = .ok s2) :
    ∀ k : SeLe4n.ObjId,
      (k = scId.toObjId ∧ s2.objects[k]? = some (.schedContext scStored)) ∨
      (k = pushRid.toObjId ∧ s2.objects[k]? =
        some (.reply { pushReply with prev := sc.scReply, next := some (.head scId) })) ∨
      (k ≠ scId.toObjId ∧ k ≠ pushRid.toObjId ∧
        (s2.objects[k]? = st.objects[k]? ∨ ∃ o : Reply, st.objects[k]? = some (.reply o) ∧
          s2.objects[k]? = some (.reply { o with next := some (.frame pushRid) }))) := by
  have hKey := getReply?_getSchedContext?_key_ne st pushRid scId pushReply sc hRep hSc
  have hI1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  obtain ⟨hNotSelf, s1', hSP, hRest⟩ := storeDonationFramePush_cases hS2
  have hI1' := storeObject_preserves_objects_invExt s1 s1' _ _ hI1 hSP
  have e1 : ∀ k, k ≠ scId.toObjId → s1.objects[k]? = st.objects[k]? :=
    fun k hk => storeObject_objects_ne st s1 _ k _ hk hObjInv hS1
  have e1' : ∀ k, k ≠ pushRid.toObjId → s1'.objects[k]? = s1.objects[k]? :=
    fun k hk => storeObject_objects_ne s1 s1' _ k _ hk hI1 hSP
  -- the last store, read at every key
  have hLast : ∀ k, k ≠ pushRid.toObjId →
      (s2.objects[k]? = s1'.objects[k]? ∨ ∃ o : Reply, s1'.objects[k]? = some (.reply o) ∧
        s2.objects[k]? = some (.reply { o with next := some (.frame pushRid) })) ∧
      s2.objects[pushRid.toObjId]? = s1'.objects[pushRid.toObjId]? := by
    intro k hk
    rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, hOld, hOR, hSO⟩
    · exact ⟨.inl rfl, rfl⟩
    · have hOP : old.toObjId ≠ pushRid.toObjId := fun e =>
        hNotSelf (by rw [hOld, SeLe4n.ReplyId.toObjId_injective _ _ e])
      refine ⟨?_, storeObject_objects_ne s1' s2 _ _ _ (Ne.symm hOP) hI1' hSO⟩
      by_cases hko : k = old.toObjId
      · subst hko
        exact .inr ⟨oldR, (SystemState.getReply?_eq_some_iff _ _ _).mp hOR,
          storeObject_objects_eq s1' s2 _ _ hI1' hSO⟩
      · exact .inl (storeObject_objects_ne s1' s2 _ _ _ hko hI1' hSO)
  intro k
  by_cases hk0 : k = scId.toObjId
  · subst hk0
    refine .inl ⟨rfl, ?_⟩
    rw [(hLast _ hKey.symm).1.elim id (fun ⟨o, ho, _⟩ => by
      rw [e1' _ hKey.symm, storeObject_objects_eq st s1 _ _ hObjInv hS1] at ho; cases ho),
      e1' _ hKey.symm]
    exact storeObject_objects_eq st s1 _ _ hObjInv hS1
  by_cases hkp : k = pushRid.toObjId
  · subst hkp
    refine .inr (.inl ⟨rfl, ?_⟩)
    rw [(hLast scId.toObjId hKey.symm).2]
    exact storeObject_objects_eq s1 s1' _ _ hI1 hSP
  · refine .inr (.inr ⟨hk0, hkp, ?_⟩)
    rcases (hLast k hkp).1 with h | ⟨o, ho, h⟩
    · exact .inl (by rw [h, e1' k hkp, e1 k hk0])
    · rw [e1' k hkp, e1 k hk0] at ho; exact .inr ⟨o, ho, h⟩

/-- **The push carries the lenders' flow where the donor flows to the context**:
the pushed frame is the donor's own reply object, on no stack before the push
(`donationPushFrame?`, read with the chain invariant), its caller is the donor
(`replyCallerLinkageReciprocal`), and every other head, link and caller is one
the state already had. -/
theorem donateSchedContext_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId}
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hRecip : replyCallerLinkageReciprocal st) (hInv : contextLendersFlow ctx st)
    (hFlow : securityFlowsTo (ctx.threadLabelOf clientTid)
      (ctx.objectLabelOf clientScId.toObjId) = true)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    contextLendersFlow ctx st' := by
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hSc, -, hLk, hFrame, hS1, hS2, hLC, hS3, hLS, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  obtain ⟨hRO, hRep, -, hFN, -⟩ := donationPushFrame?_ok st donorTcb pushRid pushReply hFrame
  have hRepObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hRep
  have hScObj := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  obtain ⟨r0, hr0, hc0⟩ := hRecip.1 clientTid donorTcb pushRid
    (lookupTcb_some_objects st clientTid donorTcb hLk) hRO
  rw [hRepObj] at hr0; cases hr0
  have hI1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hI2 := storeDonationFramePush_preserves_objects_invExt hI1 hS2
  have hI3 := storeObject_preserves_objects_invExt s2 s3 _ _ hI2 hS3
  have hK := donationHeadPush_slots hObjInv hSc hRep hS1 hS2
  have hFlow2 : contextLendersFlow ctx s2 := by
    refine contextLendersFlow_of_push (s0 := clientScId) (p := pushRid) hInv
      (not_onContextStack_of_next_none hChain hRep hFN) (fun r hH => ?_) (fun s r hs hH => ?_)
      (fun x hP => ?_) (fun r x hr hP => ?_) (fun r l hC => ?_) (fun l hC => ?_)
    · rw [contextStackHead_eq_obj] at hH
      rcases hK clientScId.toObjId with ⟨-, h2⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [h2] at hH; simp only [objStackHead, Option.some.injEq] at hH; exact hH.symm
      · exact absurd e.symm (getReply?_getSchedContext?_key_ne st pushRid clientScId _ sc hRep hSc)
      · exact absurd rfl e
    · rw [contextStackHead_eq_obj] at hH ⊢
      rcases hK s.toObjId with ⟨e, -⟩ | ⟨-, h2⟩ | ⟨-, -, h2 | ⟨o, -, h2⟩⟩
      · exact absurd (SeLe4n.SchedContextId.toObjId_injective _ _ e) hs
      · rw [h2] at hH; cases hH
      · rw [← h2]; exact hH
      · rw [h2] at hH; cases hH
    · rw [replyStackPrev_eq_obj] at hP
      rw [contextStackHead_eq_obj, hScObj]
      rcases hK pushRid.toObjId with ⟨e, -⟩ | ⟨-, h2⟩ | ⟨-, e, -⟩
      · exact absurd e (getReply?_getSchedContext?_key_ne st pushRid clientScId _ sc hRep hSc)
      · rw [h2] at hP; exact hP
      · exact absurd rfl e
    · rw [replyStackPrev_eq_obj] at hP ⊢
      rcases hK r.toObjId with ⟨-, h2⟩ | ⟨e, -⟩ | ⟨-, -, h2 | ⟨o, ho, h2⟩⟩
      · rw [h2] at hP; cases hP
      · exact absurd (SeLe4n.ReplyId.toObjId_injective _ _ e) hr
      · rw [← h2]; exact hP
      · rw [h2] at hP; rw [ho]; exact hP
    · rw [replyStackCaller_eq_obj] at hC ⊢
      rcases hK r.toObjId with ⟨-, h2⟩ | ⟨e, h2⟩ | ⟨-, -, h2 | ⟨o, ho, h2⟩⟩
      · rw [h2] at hC; cases hC
      · rw [h2] at hC; rw [e, hRepObj]; exact hC
      · rw [← h2]; exact hC
      · rw [h2] at hC; rw [ho]; exact hC
    · rw [replyStackCaller_eq_obj, hRepObj] at hC
      simp only [objStackCaller] at hC
      rw [hc0] at hC; cases hC; exact hFlow
  refine contextLendersFlow_of_linksShrink hFlow2 ?_
  exact ((contextStackLinksShrink_storeObject_other hI2 hS3 (fun _ e => by cases e)
      (fun _ e => by cases e)).trans
    (contextStackLinksShrink_storeObject_other hI3 hS4 (fun _ e => by cases e)
      (fun _ e => by cases e))).trans (contextStackLinksShrink_of_objects_eq (by rw [hEq]))

end SeLe4n.Kernel
