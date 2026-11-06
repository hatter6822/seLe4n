/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.UnheldContextPop
import SeLe4n.Kernel.IPC.Operations.UnheldContextPopInPlace
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.LoanCoherence

/-!
# The IPC bundle across the pop of a context no thread holds

`returnUnheldSchedContext` (seL4-MCS's `reply_pop` after the holder's
`schedContext_unbindTCB`) writes the context, the popped head and the frame
below it, and the recipient's binding.  The bundle's fifteen conjuncts that read
no binding carry across the read agreement the three stores keep
(`ipcInvariantFull_of_donationReadAgreement`); the four donation conjuncts are
proved here on the post-state, from three pre-state facts the caller supplies:
no thread holds the context as its own (the context is bound to none,
`schedContextBindingConsistent`), no loan names the recipient, and none names
the outer caller.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

section UnheldPop

variable {st st' : SystemState} {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
  {newOwner? : Option SeLe4n.ThreadId}

/-- **What the unheld pop writes, key by key**: the context's new record at its
key, the recipient's new binding at its key (on the thread it read there), and
every other thread and context as it was. -/
theorem returnUnheldSchedContext_objects (hObjInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)) (ot : TCB),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
      outerCallerAcceptable st owner owner newOwner? = true ∧
      donationRecipientAcceptable st owner = true ∧
      st.objects[owner.toObjId]? = some (.tcb ot) ∧ ¬ owner.isReserved ∧
      st'.objects[scId.toObjId]? = some (.schedContext
        (donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev)) newOwner?)) ∧
      st'.objects[owner.toObjId]? = some (.tcb { ot with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }) ∧
      (∀ k t, k ≠ owner.toObjId → st'.objects[k]? = some (.tcb t) → st.objects[k]? = some (.tcb t)) ∧
      (∀ k t, k ≠ owner.toObjId → st.objects[k]? = some (.tcb t) → st'.objects[k]? = some (.tcb t)) ∧
      (∀ k x, k ≠ scId.toObjId → st'.objects[k]? = some (.schedContext x) →
        st.objects[k]? = some (.schedContext x)) ∧
      (∀ k x, k ≠ scId.toObjId → st.objects[k]? = some (.schedContext x) →
        st'.objects[k]? = some (.schedContext x)) := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, hB, hOut, hRcp, _hHead, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hNR := lookupTcb_some_not_reserved _ _ _ hL
  have hO2 : s2.objects[owner.toObjId]? = some (.tcb ot) := lookupTcb_some_objects s2 owner ot hL
  have hO1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ hO2
  have hNe : owner.toObjId ≠ scId.toObjId := by
    intro e; rw [e, storeObject_objects_eq st s1 _ _ hObjInv hS1] at hO1; cases hO1
  have hO : st.objects[owner.toObjId]? = some (.tcb ot) := by
    rw [← storeObject_objects_ne st s1 _ _ _ hNe hObjInv hS1]; exact hO1
  have eO : st'.objects = s3.objects := by rw [hEq, markKeyChangeFrom_objects]
  have hSc2 : s2.objects[scId.toObjId]? = some (.schedContext
      (donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev)) newOwner?)) := by
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 scId
    have e1 : s1.getSchedContext? scId = some
        (donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev)) newOwner?) :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
        (storeObject_objects_eq st s1 _ _ hObjInv hS1)
    exact (SystemState.getSchedContext?_eq_some_iff _ _ _).mp (e.trans e1)
  refine ⟨sc, head?, ot, hSc, hB, hOut, hRcp, hO, hNR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eO, storeObject_objects_ne s2 s3 _ _ _ hNe.symm hInv2 hS3]; exact hSc2
  · rw [eO]; exact storeObject_objects_eq s2 s3 _ _ hInv2 hS3
  · intro k t hk ht
    rw [eO, storeObject_objects_ne s2 s3 _ _ _ hk hInv2 hS3] at ht
    have h1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ ht
    by_cases e : k = scId.toObjId
    · subst e; rw [storeObject_objects_eq st s1 _ _ hObjInv hS1] at h1; cases h1
    · rw [storeObject_objects_ne st s1 _ _ _ e hObjInv hS1] at h1; exact h1
  · intro k t hk ht
    have hkS : k ≠ scId.toObjId := by intro e; rw [e, hSc] at ht; cases ht
    rw [eO, storeObject_objects_ne s2 s3 _ _ _ hk hInv2 hS3]
    apply storeDonationHeadPop_tcb_eq hInv1 hS2
    rw [storeObject_objects_ne st s1 _ _ _ hkS hObjInv hS1]; exact ht
  · intro k x hk hx
    have hkO : k ≠ owner.toObjId := by
      intro e; rw [e, eO, storeObject_objects_eq s2 s3 _ _ hInv2 hS3] at hx; cases hx
    rw [eO, storeObject_objects_ne s2 s3 _ _ _ hkO hInv2 hS3] at hx
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 (SeLe4n.SchedContextId.ofObjId k)
    have hx' : s2.getSchedContext? (SeLe4n.SchedContextId.ofObjId k) = some x :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (by
        rw [SeLe4n.SchedContextId.toObjId_ofObjId]; exact hx)
    rw [e] at hx'
    have h1 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hx'
    rw [SeLe4n.SchedContextId.toObjId_ofObjId,
      storeObject_objects_ne st s1 _ _ _ hk hObjInv hS1] at h1; exact h1
  · intro k x hk hx
    have hkO : k ≠ owner.toObjId := by intro e; rw [e, hO] at hx; cases hx
    rw [eO, storeObject_objects_ne s2 s3 _ _ _ hkO hInv2 hS3]
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 (SeLe4n.SchedContextId.ofObjId k)
    have hx1 : s1.getSchedContext? (SeLe4n.SchedContextId.ofObjId k) = some x :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (by
        rw [SeLe4n.SchedContextId.toObjId_ofObjId,
          storeObject_objects_ne st s1 _ _ _ hk hObjInv hS1]; exact hx)
    rw [← e] at hx1
    have h2 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hx1
    rw [SeLe4n.SchedContextId.toObjId_ofObjId] at h2; exact h2

/-- The unheld pop keeps the read agreement: a context store, the head pop and a
binding store. -/
theorem returnUnheldSchedContext_donationReadAgreement (hObjInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    donationReadAgreement st st' := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, _, _, _, _, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have a1 := donationReadAgreement_of_schedContextStore st s1 scId.toObjId sc _ hSc hObjInv hS1
  have a2 := donationReadAgreement_of_headPop hInv1 hS2
  have a3 := donationReadAgreement_of_tcbBindingStore s2 s3 owner.toObjId ot
    (donationReturnBinding scId newOwner?) ot.originScCode
    (lookupTcb_some_objects s2 owner ot hL) hInv2 hS3
  exact donationReadAgreement_of_objects_eq (by rw [hEq, markKeyChangeFrom_objects])
    ((a1.trans a2).trans a3)

/-- The binding the pop gives its recipient, read back off the codes it stores. -/
theorem donationReturnBinding_stored (ot : TCB) (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) :
    ({ ot with
        scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
        scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }
      : TCB).schedContextBinding = donationReturnBinding scId newOwner? :=
  SchedContextBinding.ofCodes_codes _

/-- **The unheld pop keeps the IPC bundle**, given that no thread's binding
names the context (it is bound to none), that no loan names the recipient, and
that none names the outer caller the pop makes it owe. -/
theorem returnUnheldSchedContext_preserves_ipcInvariantFull (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hFree : ∀ (X : SeLe4n.ThreadId) (t : TCB), st.objects[X.toObjId]? = some (.tcb t) →
      t.schedContextBinding.scId? ≠ some scId)
    (hNoOwner : ∀ (X : SeLe4n.ThreadId) (t : TCB) (s' : SeLe4n.SchedContextId),
      st.objects[X.toObjId]? = some (.tcb t) → t.schedContextBinding ≠ .donated s' owner)
    (hOuterFree : ∀ outer, newOwner? = some outer → ∀ (X : SeLe4n.ThreadId) (t : TCB)
      (s' : SeLe4n.SchedContextId),
      st.objects[X.toObjId]? = some (.tcb t) → t.schedContextBinding ≠ .donated s' outer)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨sc, head?, ot, hSc, hB0, hOut, _hRcp, hO, _hNR, hSc', hO', tBwd, tFwd, cBwd, cFwd⟩ :=
    returnUnheldSchedContext_objects hObjInv h
  have hAgree := returnUnheldSchedContext_donationReadAgreement hObjInv h
  have hBd := donationReturnBinding_stored ot scId newOwner?
  -- a thread of the post-state is the recipient with the pop's binding, or a
  -- thread of the pre-state
  have split : ∀ (X : SeLe4n.ThreadId) (t : TCB), st'.objects[X.toObjId]? = some (.tcb t) →
      (X = owner ∧ t.schedContextBinding = donationReturnBinding scId newOwner?) ∨
        (X ≠ owner ∧ st.objects[X.toObjId]? = some (.tcb t)) := by
    intro X t hX
    by_cases e : X.toObjId = owner.toObjId
    · have eX := SeLe4n.ThreadId.toObjId_injective _ _ e
      subst eX
      rw [hO'] at hX
      cases hX
      exact Or.inl ⟨rfl, hBd⟩
    · exact Or.inr ⟨fun h => e (h ▸ rfl), tBwd _ _ e hX⟩
  have hUnheld : ∀ tid, sc.boundThread ≠ some tid := by
    intro tid e
    unfold SchedContext.boundThread at e
    rw [hB0] at e; cases e
  have hDOV : donationOwnerValid st' := by
    intro tid tcb s o hT hBdT
    rcases split tid tcb hT with ⟨rfl, hb⟩ | ⟨hNe, hT0⟩
    · rw [hb] at hBdT
      cases hN : newOwner? with
      | none => rw [hN] at hBdT; cases hBdT
      | some outer =>
        rw [hN] at hBdT
        simp only [donationReturnBinding_some, SchedContextBinding.donated.injEq] at hBdT
        obtain ⟨rfl, rfl⟩ := hBdT
        rw [hN] at hOut
        unfold outerCallerAcceptable at hOut
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hOut
        obtain ⟨⟨hNeO, -⟩, hM⟩ := hOut
        cases hOt : st.getTcb? outer with
        | none => rw [hOt] at hM; cases hM
        | some oT =>
          rw [hOt] at hM
          simp only [Bool.and_eq_true] at hM
          obtain ⟨hU, hR⟩ := hM
          have hU : oT.schedContextBinding = .unbound := by
            revert hU; cases oT.schedContextBinding <;> simp [BEq.beq]
          refine ⟨⟨_, hSc', ?_⟩, oT, tFwd _ _ (fun e => hNeO (SeLe4n.ThreadId.toObjId_injective _ _ e))
            ((SystemState.getTcb?_eq_some_iff _ _ _).mp hOt), hU, ?_⟩
          · unfold SchedContext.boundThread donationReturnSchedContext
            simp only [SeLe4n.ThreadId.optCode, SeLe4n.ThreadId.ofOptCode]
          · revert hR
            cases oT.ipcState with
            | blockedOnReply e r => intro _; exact ⟨e, r, rfl⟩
            | _ => intro hR; cases hR
    · obtain ⟨⟨x, hx, hxB⟩, oT, hoT, hoU, hoR⟩ :=
        hInv.donationOwnerValid tid tcb s o hT0 hBdT
      have hsNe : s.toObjId ≠ scId.toObjId := by
        intro e
        rw [e, hSc] at hx
        cases hx
        exact hUnheld tid hxB
      have hoNe : o.toObjId ≠ owner.toObjId := by
        intro e
        have eo := SeLe4n.ThreadId.toObjId_injective _ _ e
        subst eo
        exact hNoOwner tid tcb s hT0 hBdT
      exact ⟨⟨x, cFwd _ _ hsNe hx, hxB⟩, oT, tFwd _ _ hoNe hoT, hoU, hoR⟩
  have hDOU : donationOwnerUnique st' := by
    intro t1 t2 tcb1 tcb2 s1 s2 o h1 h2 hB1 hB2
    rcases split t1 tcb1 h1 with ⟨rfl, hb1⟩ | ⟨hN1, hPre1⟩ <;>
      rcases split t2 tcb2 h2 with ⟨e2, hb2⟩ | ⟨hN2, hPre2⟩
    · exact e2.symm
    · rw [hb1] at hB1
      cases hN : newOwner? with
      | none => rw [hN] at hB1; cases hB1
      | some outer =>
        rw [hN] at hB1
        simp only [donationReturnBinding_some, SchedContextBinding.donated.injEq] at hB1
        obtain ⟨-, rfl⟩ := hB1
        exact absurd hB2 (hOuterFree outer hN t2 tcb2 s2 hPre2)
    · subst e2
      rw [hb2] at hB2
      cases hN : newOwner? with
      | none => rw [hN] at hB2; cases hB2
      | some outer =>
        rw [hN] at hB2
        simp only [donationReturnBinding_some, SchedContextBinding.donated.injEq] at hB2
        obtain ⟨-, rfl⟩ := hB2
        exact absurd hB1 (hOuterFree outer hN t1 tcb1 s1 hPre1)
    · exact hInv.donationOwnerUnique t1 t2 tcb1 tcb2 s1 s2 o hPre1 hPre2 hB1 hB2
  have hDBT : donationBudgetTransfer st' := by
    intro t1 t2 tcb1 tcb2 s h1 h2 hNe hS1 hS2
    rcases split t1 tcb1 h1 with ⟨rfl, hb1⟩ | ⟨hN1, hPre1⟩ <;>
      rcases split t2 tcb2 h2 with ⟨e2, hb2⟩ | ⟨hN2, hPre2⟩
    · exact hNe e2.symm
    · rw [hb1] at hS1
      have : s = scId := by cases newOwner? <;> simpa [SchedContextBinding.scId?] using hS1.symm
      subst this
      exact hFree t2 tcb2 hPre2 hS2
    · subst e2
      rw [hb2] at hS2
      have : s = scId := by cases newOwner? <;> simpa [SchedContextBinding.scId?] using hS2.symm
      subst this
      exact hFree t1 tcb1 hPre1 hS1
    · exact hInv.donationBudgetTransfer t1 t2 tcb1 tcb2 s hPre1 hPre2 hNe hS1 hS2
  exact ipcInvariantFull_of_donationReadAgreement st st' hInv hAgree
    (donationOwnerValid_implies_donationChainAcyclic st' hDOV) hDOV hDBT hDOU

end UnheldPop

/-- **What the unheld pop leaves of the replies**: a reply it names neither as
the head nor as the frame below keeps its record, the frame below (kept apart
from the head) heads the context, as `returnDonatedSchedContext_reply_cases`
says of the donation return. -/
theorem returnUnheldSchedContext_reply_cases {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : returnUnheldSchedContext st s c n = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)),
      st.objects[s.toObjId]? = some (.schedContext sc) ∧ donationHeadOf? st s sc = .ok head? ∧
      (∀ (k : SeLe4n.ObjId) (r : Reply), st.objects[k]? = some (.reply r) →
        (∀ x rx, head? = some (x, rx) → k ≠ x.toObjId) →
        (∀ x rx y, head? = some (x, rx) → rx.prev = some y → k ≠ y.toObjId) →
        st'.objects[k]? = some (.reply r)) ∧
      (∀ x rx y b, head? = some (x, rx) → rx.prev = some y →
        st.objects[y.toObjId]? = some (.reply b) → y.toObjId ≠ x.toObjId →
        st'.objects[y.toObjId]? = some (.reply { b with next := some (.head s) })) ∧
      (∀ x rx, head? = some (x, rx) → st.objects[x.toObjId]? = some (.reply rx) →
        (∀ y, rx.prev = some y → y.toObjId ≠ x.toObjId) →
        st'.objects[x.toObjId]? = some (.reply { rx with prev := none, next := none })) := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, hHead, hS1, hClear, hL1, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ s c n hPop
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hI2 := storeDonationHeadPop_preserves_objects_invExt hI1 hClear
  have eO : st'.objects = s3.objects := by rw [hEq, markKeyChangeFrom_objects]
  have tail : ∀ (k : SeLe4n.ObjId) (r : Reply), s2.objects[k]? = some (.reply r) →
      st'.objects[k]? = some (.reply r) := by
    intro k r hk
    have hc : k ≠ c.toObjId := by
      intro e; rw [e, lookupTcb_some_objects _ _ _ hL1] at hk; cases hk
    rw [eO, storeObject_objects_ne _ _ _ k _ hc hI2 hS3]; exact hk
  have first : ∀ (k : SeLe4n.ObjId) (r : Reply), st.objects[k]? = some (.reply r) →
      s1.objects[k]? = some (.reply r) := by
    intro k r hk
    have hne : k ≠ s.toObjId := by intro e; rw [e, hSc] at hk; cases hk
    rw [storeObject_objects_ne _ _ _ k _ hne hInv hS1]; exact hk
  refine ⟨sc, head?, hSc, hHead, fun k r hk h1 h2 => tail k r ?_,
    fun x rx y b hHd hP hb hyx => tail _ _ ?_, fun x rx hHd hx hyx => tail _ _ ?_⟩
  · rw [storeDonationHeadPop_objects_ne hI1 hClear k h1 h2]; exact first k r hk
  · subst hHd
    rw [storeDonationHeadPop_some] at hClear
    revert hClear
    cases hCl : storeDonationHeadClear (some x) s1 with
    | error e => intro hc; cases hc
    | ok s1' =>
      intro hRe
      simp only at hRe
      obtain ⟨r0, -, hS0⟩ := storeDonationHeadClear_some_ok hCl
      have hI1' := storeObject_preserves_objects_invExt _ _ _ _ hI1 hS0
      have hb1 : s1'.objects[y.toObjId]? = some (.reply b) := by
        rw [storeObject_objects_ne _ _ _ _ _ hyx hI1 hS0]; exact first _ _ hb
      rw [hP] at hRe
      obtain ⟨b', hb', hS2⟩ := storeReplyReHead_some_ok hRe
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hb1] at hb'
      cases hb'
      exact storeObject_objects_eq _ _ _ _ hI1' hS2
  · subst hHd
    rw [storeDonationHeadPop_some] at hClear
    revert hClear
    cases hCl : storeDonationHeadClear (some x) s1 with
    | error e => intro hc; cases hc
    | ok s1' =>
      intro hRe
      simp only at hRe
      obtain ⟨r0, hr0, hS0⟩ := storeDonationHeadClear_some_ok hCl
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr (first _ _ hx)] at hr0
      cases hr0
      have hI1' := storeObject_preserves_objects_invExt _ _ _ _ hI1 hS0
      have hx1 : s1'.objects[x.toObjId]? = some (.reply { rx with prev := none, next := none }) :=
        storeObject_objects_eq _ _ _ _ hI1 hS0
      revert hRe
      cases hP : rx.prev with
      | none => intro hRe; cases hRe; exact hx1
      | some y =>
        intro hRe
        obtain ⟨b', -, hS2⟩ := storeReplyReHead_some_ok hRe
        rw [storeObject_objects_ne _ _ _ _ _ (fun e => hyx y hP e.symm) hI1' hS2]
        exact hx1

/-- **The unheld pop clears the reply it pops**: the head the context names,
whose frame below links up to it (the reply-stack resolver reads that link, so
the frame below is another reply), left heading nothing. -/
theorem returnUnheldSchedContext_head_unlinked {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hRes : replyStackOuterCaller? st s = .ok n)
    (hPop : returnUnheldSchedContext st s c n = .ok st') {rid : SeLe4n.ReplyId} {sc : SchedContext}
    (hSc : st.getSchedContext? s = some sc) (hHd : sc.scReply = some rid) :
    ∃ rx : Reply, st'.objects[rid.toObjId]? = some (.reply { rx with prev := none, next := none }) := by
  obtain ⟨sc0, head?, hSc0, hHead, -, -, hCleared⟩ := returnUnheldSchedContext_reply_cases hInv hPop
  rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc] at hSc0
  cases hSc0
  have hGetSc := hSc
  unfold donationHeadOf? at hHead
  rw [hHd] at hHead
  simp only [] at hHead
  cases hG : st.getReply? rid with
  | none => rw [hG] at hHead; cases hHead
  | some rx =>
    rw [hG] at hHead
    simp only [] at hHead
    split at hHead
    · cases hHead
    · rename_i hN
      cases hHead
      have hN' : rx.next = some (.head s) := by simpa using hN
      have hx := (SystemState.getReply?_eq_some_iff _ _ _).mp hG
      refine ⟨rx, hCleared rid rx rfl hx (fun y hP e => ?_)⟩
      -- The resolver read the frame below, a frame link up to `rid`; `rid` heads.
      unfold replyStackOuterCaller? at hRes
      rw [hGetSc] at hRes
      simp only at hRes
      unfold donationHeadOf? at hRes
      rw [hHd] at hRes
      simp only [] at hRes
      rw [hG] at hRes
      simp only [] at hRes
      rw [if_neg (by simpa using hN)] at hRes
      simp only [hP] at hRes
      have ey : y = rid := SeLe4n.ReplyId.toObjId_injective _ _ e
      subst ey
      rw [hG] at hRes
      simp only [] at hRes
      split at hRes
      · cases hRes
      · rename_i hNx
        exact hNx (by rw [hN']; rfl)

/-- **The unheld pop keeps every lent context headed by its lender's frame**
(seL4-MCS's `reply_pop`): the thread the context goes back to holds it on loan
only from the outer caller the reply stack names, whose frame the pop has just
made the head; every other loan's lender keeps its frame, which is neither the
popped head (its context is bound to no thread, so no thread holds it on loan,
`donationOwnerValid`) nor the frame below it (a frame link, not a head).  The
recipient's reply link is kept. -/
theorem returnUnheldSchedContext_keepsLentContextHeads {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hW : lentContextHeadsLenderFrame st)
    (hOwn : donationOwnerValid st) (hLink : replyCallerLinkageReciprocal st)
    (hRes : replyStackOuterCaller? st s = .ok n)
    (hPop : returnUnheldSchedContext st s c n = .ok st') :
    lentContextHeadsLenderFrame st' := by
  obtain ⟨sc, head?, hSc, hHead, hKeep, hBelow, -⟩ := returnUnheldSchedContext_reply_cases hInv hPop
  obtain ⟨sc0, -, ot, hSc0, hB0, -, -, hO, -, -, hO', tBwd, -, -, -⟩ :=
    returnUnheldSchedContext_objects hInv hPop
  rw [hSc] at hSc0; cases hSc0
  have hGetSc : st.getSchedContext? s = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  have hHeadAt : ∀ x rx, head? = some (x, rx) →
      st.objects[x.toObjId]? = some (.reply rx) ∧ rx.next = some (.head s) := by
    intro x rx e
    subst e
    unfold donationHeadOf? at hHead
    revert hHead
    cases sc.scReply with
    | none => intro hc; cases hc
    | some rid' =>
      simp only []
      cases hG : st.getReply? rid' with
      | none => intro hc; cases hc
      | some r' =>
        simp only []
        split
        · intro hc; cases hc
        · rename_i hN
          intro hc; cases hc
          exact ⟨(SystemState.getReply?_eq_some_iff _ _ _).mp hG, by simpa using hN⟩
  have hBelowAt : ∀ x rx y, head? = some (x, rx) → rx.prev = some y →
      ∃ b outer, st.objects[y.toObjId]? = some (.reply b) ∧ b.next = some (.frame x) ∧
        b.caller = some outer ∧ n = some outer := by
    intro x rx y e hP
    unfold replyStackOuterCaller? at hRes
    rw [hGetSc] at hRes
    simp only at hRes
    rw [hHead, e] at hRes
    simp only at hRes
    rw [hP] at hRes
    simp only at hRes
    cases hGb : st.getReply? y with
    | none => rw [hGb] at hRes; cases hRes
    | some b =>
      rw [hGb] at hRes
      simp only at hRes
      split at hRes
      · cases hRes
      · rename_i hNx
        cases hCl : b.caller with
        | none => rw [hCl] at hRes; cases hRes
        | some outer =>
          rw [hCl] at hRes
          cases hRes
          exact ⟨b, outer, (SystemState.getReply?_eq_some_iff _ _ _).mp hGb,
            by simpa using hNx, hCl, rfl⟩
  have hNoneOf : head? = none ∨ (∃ x rx, head? = some (x, rx) ∧ rx.prev = none) → n = none := by
    intro hc
    unfold replyStackOuterCaller? at hRes
    rw [hGetSc] at hRes
    simp only at hRes
    rw [hHead] at hRes
    rcases hc with e | ⟨x, rx, e, hP⟩
    · rw [e] at hRes; simp only [Except.ok.injEq] at hRes; exact hRes.symm
    · rw [e] at hRes; simp only [hP, Except.ok.injEq] at hRes; exact hRes.symm
  have keepHead : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (sc' : SeLe4n.SchedContextId),
      st.objects[rid.toObjId]? = some (.reply r) → r.next = some (.head sc') →
      (∀ x rx, head? = some (x, rx) → rid.toObjId ≠ x.toObjId) →
      st'.objects[rid.toObjId]? = some (.reply r) := by
    intro rid r sc' hR hN hNx
    refine hKeep _ r hR hNx (fun x rx y e hP hy => ?_)
    obtain ⟨b, -, hb, hbN, -⟩ := hBelowAt x rx y e hP
    rw [← hy, hR] at hb; cases hb
    rw [hN] at hbN; cases hbN
  -- A thread after the pop: the recipient with its new binding, or a thread before it.
  have hThread : ∀ (k : SeLe4n.ThreadId) (t' : TCB), st'.objects[k.toObjId]? = some (.tcb t') →
      ∃ t, st.objects[k.toObjId]? = some (.tcb t) ∧ t'.replyObject = t.replyObject ∧
        (k.toObjId = c.toObjId ∧ t'.schedContextBinding = donationReturnBinding s n ∨
          k.toObjId ≠ c.toObjId ∧ t'.schedContextBinding = t.schedContextBinding) := by
    intro k t' hk
    by_cases e : k.toObjId = c.toObjId
    · rw [e, hO'] at hk; cases hk
      exact ⟨ot, e ▸ hO, rfl, Or.inl ⟨e, donationReturnBinding_stored ot s n⟩⟩
    · exact ⟨t', tBwd _ _ e hk, rfl, Or.inr ⟨e, rfl⟩⟩
  intro holder ht' sc' o ot' hH' hB' hO''
  obtain ⟨ot0, hOpre, hRO, -⟩ := hThread o ot' hO''
  obtain ⟨ht, hHpre, -, hCase⟩ := hThread holder ht' hH'
  rcases hCase with ⟨eC, hBn⟩ | ⟨eC, hBeq⟩
  · -- The thread the context goes back to: on loan from the outer caller.
    rw [hBn] at hB'
    cases hn : n with
    | none => rw [hn] at hB'; cases hB'
    | some outer =>
      rw [hn] at hB'
      simp only [donationReturnBinding, SchedContextBinding.donated.injEq] at hB'
      obtain ⟨e1, e2⟩ := hB'
      cases hHd : head? with
      | none => rw [hNoneOf (Or.inl hHd)] at hn; cases hn
      | some p =>
        obtain ⟨x, rx⟩ := p
        cases hP : rx.prev with
        | none => rw [hNoneOf (Or.inr ⟨x, rx, hHd, hP⟩)] at hn; cases hn
        | some y =>
          obtain ⟨b, outer', hb, hbN, hbC, hn'⟩ := hBelowAt x rx y hHd hP
          have eo : outer' = o := (Option.some.inj (hn'.symm.trans hn)).trans e2
          obtain ⟨tcbO, hTO, hROy, -⟩ := hLink.2 y b o hb (by rw [hbC, eo])
          have eT : tcbO = ot0 := by
            rw [hOpre] at hTO; exact (KernelObject.tcb.inj (Option.some.inj hTO)).symm
          have hyx : y.toObjId ≠ x.toObjId := by
            intro e
            rw [e, (hHeadAt x rx hHd).1] at hb
            have eb : rx = b := KernelObject.reply.inj (Option.some.inj hb)
            rw [← eb, (hHeadAt x rx hHd).2] at hbN
            cases hbN
          refine ⟨y, { b with next := some (.head s) }, by rw [hRO, ← eT]; exact hROy,
            hBelow x rx y b hHd hP hb hyx, ?_⟩
          show some (ReplyStackLink.head s) = some (.head sc')
          rw [e1]
  · -- Any other loan: its holder and binding are the pre-state's.
    rw [hBeq] at hB'
    obtain ⟨rid, r, hROr, hR, hN⟩ := hW holder ht sc' o ot0 hHpre hB' hOpre
    refine ⟨rid, r, by rw [hRO]; exact hROr, keepHead rid r sc' hR hN (fun x rx e hx => ?_), hN⟩
    -- The popped head heads `s`, which is bound to no thread.
    obtain ⟨hxR, hxN⟩ := hHeadAt x rx e
    rw [hx, hxR] at hR
    have er : rx = r := KernelObject.reply.inj (Option.some.inj hR)
    rw [← er, hxN] at hN
    have e3 : s = sc' := ReplyStackLink.head.inj (Option.some.inj hN)
    obtain ⟨⟨sc1, hSc1, hBd⟩, -⟩ := hOwn holder ht sc' o hHpre hB'
    rw [← e3, hSc] at hSc1
    have es : sc = sc1 := KernelObject.schedContext.inj (Option.some.inj hSc1)
    rw [← es] at hBd
    unfold SchedContext.boundThread at hBd
    rw [hB0] at hBd; cases hBd

/-- **What the unheld pop does to a thread**: its binding rewritten, at most. -/
theorem returnUnheldSchedContext_tcb_rewrite {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : returnUnheldSchedContext st s c n = .ok st') :
    (∀ (k : SeLe4n.ObjId) (t0 : TCB), st.objects[k]? = some (.tcb t0) →
      ∃ t', st'.objects[k]? = some (.tcb t') ∧ tcbBindingRewrite t' t0) ∧
    (∀ (k : SeLe4n.ObjId) (t' : TCB), st'.objects[k]? = some (.tcb t') →
      ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbBindingRewrite t' t0) := by
  obtain ⟨_, _, ot, -, -, -, -, hO, -, -, hO', tBwd, tFwd, -, -⟩ :=
    returnUnheldSchedContext_objects hInv hPop
  refine ⟨fun k t0 hk => ?_, fun k t' hk => ?_⟩
  · by_cases e : k = c.toObjId
    · subst e; rw [hO] at hk; cases hk
      exact ⟨_, hO', _, _, rfl⟩
    · exact ⟨t0, tFwd _ _ e hk, .refl t0⟩
  · by_cases e : k = c.toObjId
    · subst e; rw [hO'] at hk; cases hk
      exact ⟨ot, hO, _, _, rfl⟩
    · exact ⟨t', tBwd _ _ e hk, .refl t'⟩

/-- **The unheld pop writes no notification**: a context, replies and a thread. -/
theorem returnUnheldSchedContext_notification_iff {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : returnUnheldSchedContext st s c n = .ok st')
    (k : SeLe4n.ObjId) (nt : Notification) :
    st'.objects[k]? = some (.notification nt) ↔ st.objects[k]? = some (.notification nt) := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, -, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ s c n hPop
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hO2 := lookupTcb_some_objects _ _ _ hL
  have eO : st'.objects = s3.objects := by rw [hEq, markKeyChangeFrom_objects]
  constructor
  · intro hk
    rw [eO] at hk
    have hkO : k ≠ c.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv2 hS3] at hk; cases hk
    rw [storeObject_objects_ne _ _ _ _ _ hkO hInv2 hS3] at hk
    have h1 := storeDonationHeadPop_non_reply_backward hInv1 hS2 k _ (fun _ e => by cases e) hk
    have hkS : k ≠ s.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv hS1] at h1; cases h1
    rwa [storeObject_objects_ne _ _ _ _ _ hkS hInv hS1] at h1
  · intro hk
    have hkS : k ≠ s.toObjId := by intro e; rw [e, hSc] at hk; cases hk
    have hkO : k ≠ c.toObjId := by
      intro e
      have h1 : s1.objects[k]? = some (.notification nt) := by
        rw [storeObject_objects_ne _ _ _ _ _ hkS hInv hS1]; exact hk
      rw [← e, storeDonationHeadPop_non_reply_eq hInv1 hS2 k (fun r e' => by rw [h1] at e'; cases e'),
        h1] at hO2
      cases hO2
    rw [eO, storeObject_objects_ne _ _ _ _ _ hkO hInv2 hS3,
      storeDonationHeadPop_non_reply_eq hInv1 hS2 k (fun r e' => by
        rw [storeObject_objects_ne _ _ _ _ _ hkS hInv hS1, hk] at e'; cases e'),
      storeObject_objects_ne _ _ _ _ _ hkS hInv hS1]
    exact hk

/-- **The unheld pop writes no endpoint**: every endpoint it leaves was there
before. -/
theorem returnUnheldSchedContext_endpoint_backward {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : returnUnheldSchedContext st s c n = .ok st')
    (k : SeLe4n.ObjId) (ep : Endpoint) (hk : st'.objects[k]? = some (.endpoint ep)) :
    st.objects[k]? = some (.endpoint ep) := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, -, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ s c n hPop
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have eO : st'.objects = s3.objects := by rw [hEq, markKeyChangeFrom_objects]
  rw [eO] at hk
  have hkO : k ≠ c.toObjId := by
    intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv2 hS3] at hk; cases hk
  rw [storeObject_objects_ne _ _ _ _ _ hkO hInv2 hS3] at hk
  have h1 := storeDonationHeadPop_non_reply_backward hInv1 hS2 k _ (fun _ e => by cases e) hk
  have hkS : k ≠ s.toObjId := by
    intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv hS1] at h1; cases h1
  rwa [storeObject_objects_ne _ _ _ _ _ hkS hInv hS1] at h1

/-- **The unheld pop keeps the donation chains**: the head pop's chain writes
(`donationHeadPop_preserves_donationChainWellFormed`), then a thread's binding
rewrite, which is no chain data. -/
theorem returnUnheldSchedContext_preserves_donationChainWellFormed {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hPop : returnUnheldSchedContext st s c n = .ok st') : donationChainWellFormed st' := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, hHead, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ s c n hPop
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hChain2 : donationChainWellFormed s2 :=
    donationHeadPop_preserves_donationChainWellFormed hInv hChain
      ((SystemState.getSchedContext?_eq_some_iff st s sc).mpr hSc) hHead (by simp) hS1 hS2
  exact donationChainWellFormed_of_frame
    ((donationChainFrame_of_tcb_rewrite hInv2 (lookupTcb_some_objects _ _ _ hL) hS3).trans
      (donationChainFrame.of_objects_eq (by rw [hEq, markKeyChangeFrom_objects]))) hChain2


/-- **The unheld pop closes a chain relaxed at its head**: where the chains hold
everywhere but the head the pop removes (or everywhere, when the context heads
nothing), the pop leaves them whole — `donationHeadPop_preserves_donationChainWellFormed_of_except`,
then a thread's binding rewrite. -/
theorem returnUnheldSchedContext_preserves_donationChainWellFormed_of_except
    {st st' : SystemState} {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId}
    {n : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hChainNone : ∀ sc, st.getSchedContext? s = some sc →
      donationHeadOf? st s sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ sc rid r, st.getSchedContext? s = some sc →
      donationHeadOf? st s sc = .ok (some (rid, r)) → donationChainWellFormedExcept st rid)
    (hPop : returnUnheldSchedContext st s c n = .ok st') : donationChainWellFormed st' := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, hHead, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ s c n hPop
  have hScGet : st.getSchedContext? s = some sc :=
    (SystemState.getSchedContext?_eq_some_iff st s sc).mpr hSc
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hChain2 : donationChainWellFormed s2 :=
    donationHeadPop_preserves_donationChainWellFormed_of_except hInv
      (fun hNone => hChainNone sc hScGet (hNone ▸ hHead))
      (fun rid r hSome => hChainHead sc rid r hScGet (hSome ▸ hHead))
      hScGet hHead (by simp) hS1 hS2
  exact donationChainWellFormed_of_frame
    ((donationChainFrame_of_tcb_rewrite hInv2 (lookupTcb_some_objects _ _ _ hL) hS3).trans
      (donationChainFrame.of_objects_eq (by rw [hEq, markKeyChangeFrom_objects]))) hChain2

/-- **The pop at an unheld head closes a chain relaxed at that head**, the
settle after it writing release links alone. -/
theorem popUnheldReplyHead_preserves_donationChainWellFormed_of_except {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (hInv : st.objects.invExt)
    (hChainNone : ∀ scId sc, replyFrameHeadContext? st rid = some scId →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ scId sc hid r, replyFrameHeadContext? st rid = some scId →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok (some (hid, r)) → donationChainWellFormedExcept st hid)
    (hChainNoHead : replyFrameHeadContext? st rid = none → donationChainWellFormed st)
    (h : popUnheldReplyHead st rid target home = .ok st') : donationChainWellFormed st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨hN, rfl⟩ | ⟨scId, n, st1, hH, _, hP, rfl⟩
  · exact hChainNoHead hN
  · exact donationChainWellFormed_of_frame
      (donationChainFrame.of_objectsAgreeOffSchedulerLinks
        (.of_releaseLinks (SchedContextOps.settleReturnedContext_agree _ _ _)))
      (returnUnheldSchedContext_preserves_donationChainWellFormed_of_except hInv
        (hChainNone scId · hH) (hChainHead scId · · · hH) hP)

/-- **The unheld pop in place keeps the donation chains** on every state its
gate admits: there it is the specification's pop (`unheldPopsInPlace_pop`),
which keeps them (`returnUnheldSchedContext_preserves_donationChainWellFormed`). -/
theorem returnUnheldSchedContextInPlace_preserves_donationChainWellFormed (st : SystemState)
    (scId : SeLe4n.SchedContextId) (c : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hG : unheldPopsInPlace st scId c = true) :
    donationChainWellFormed (returnUnheldSchedContextInPlace st c scId) := by
  have h := (unheldPopsInPlace_pop st scId c hG).2
  unfold returnUnheldSchedContextResolved at h
  cases hO : replyStackOuterCaller? st scId with
  | error e => rw [hO] at h; cases h
  | ok n =>
    rw [hO] at h
    simp only [] at h
    exact returnUnheldSchedContext_preserves_donationChainWellFormed hInv hChain h

/-- **What the pop at an unheld head needs of the state it runs on, beyond the
bundle** (WS-ZA ZA6.34): where the reply heads a context no thread holds, no
thread holds that context as its own (`.bound`) and no thread holds a context
on loan from the recipient.  The bundle's `donationOwnerValid` already excludes
a loan of the context itself, since a loaned context names its holder; these
two it does not decide.  Vacuous where the reply heads nothing or the context
is held. -/
def unheldReplyPopCoherent (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) : Prop :=
  ∀ scId, replyFrameHeadHolder? st rid = none → replyFrameHeadContext? st rid = some scId →
    (∀ (X : SeLe4n.ThreadId) (t : TCB), st.objects[X.toObjId]? = some (.tcb t) →
      t.schedContextBinding ≠ .bound scId) ∧
    (∀ (X : SeLe4n.ThreadId) (t : TCB) (s' : SeLe4n.SchedContextId),
      st.objects[X.toObjId]? = some (.tcb t) → t.schedContextBinding ≠ .donated s' target)

/-- A reply heading no context asks nothing of the pop. -/
theorem unheldReplyPopCoherent_of_no_head {st : SystemState} {rid : SeLe4n.ReplyId}
    (target : SeLe4n.ThreadId) (h : replyFrameHeadContext? st rid = none) :
    unheldReplyPopCoherent st rid target := by
  intro scId _ hH; rw [h] at hH; cases hH

/-- **The binding half of `unheldReplyPopCoherent`**: where the reply heads a
context no thread holds, no thread binds that context as its own.  The loan half
is the dispatch's own no-loan fact about the answered caller, which every
caller already states; this half is the one it does not. -/
def unheldReplyHeadBoundByNone (st : SystemState) (rid : SeLe4n.ReplyId) : Prop :=
  ∀ scId, replyFrameHeadHolder? st rid = none → replyFrameHeadContext? st rid = some scId →
    ∀ (X : SeLe4n.ThreadId) (t : TCB), st.objects[X.toObjId]? = some (.tcb t) →
      t.schedContextBinding ≠ .bound scId

/-- **The unheld pop's coherence, from its two halves**: the binding half, and
no loan from the recipient where the reply's head is held by no thread. -/
theorem unheldReplyPopCoherent_of_boundByNone {st : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} (hB : unheldReplyHeadBoundByNone st rid)
    (hL : replyFrameHeadHolder? st rid = none →
      ∀ (X : SeLe4n.ThreadId) (t : TCB) (s' : SeLe4n.SchedContextId),
        st.objects[X.toObjId]? = some (.tcb t) → t.schedContextBinding ≠ .donated s' target) :
    unheldReplyPopCoherent st rid target :=
  fun scId hN hC => ⟨hB scId hN hC, hL hN⟩

/-- **The pop at an unheld head keeps the IPC bundle** (WS-ZA ZA6.34): the
unheld pop (`returnUnheldSchedContext_preserves_ipcInvariantFull`), its three
facts from the coherence hypothesis, the bundle's `donationOwnerValid` and the
reply stack's outer-caller obligation; then the settle, which writes release
links only. -/
theorem popUnheldReplyHead_preserves_ipcInvariantFull {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStackValid : ∀ scId serverTid originalOwner,
      replyStackOuterCallerValid st scId serverTid originalOwner)
    (hCoh : unheldReplyPopCoherent st rid target)
    (hNoHolder : replyFrameHeadHolder? st rid = none)
    (h : popUnheldReplyHead st rid target home = .ok st') : ipcInvariantFull st' := by
  rcases popUnheldReplyHead_ok_cases h with ⟨_, rfl⟩ | ⟨scId, st1, hH, hR, rfl⟩
  · exact hInv
  · obtain ⟨n, hN, hP⟩ := returnUnheldSchedContextResolved_ok_decompose hR
    obtain ⟨hBoundFree, hNoOwner⟩ := hCoh scId hNoHolder hH
    obtain ⟨sc, -, -, hSc, hB0, -, -, -, -, -, -, -, -, -, -⟩ :=
      returnUnheldSchedContext_objects hObjInv hP
    have hUnheld : ∀ (X : SeLe4n.ThreadId) (sc1 : SchedContext),
        st.objects[scId.toObjId]? = some (.schedContext sc1) → sc1.boundThread ≠ some X := by
      intro X sc1 h1 e
      rw [hSc] at h1; cases h1
      unfold SchedContext.boundThread at e; rw [hB0] at e; cases e
    have hFree : ∀ (X : SeLe4n.ThreadId) (tX : TCB), st.objects[X.toObjId]? = some (.tcb tX) →
        tX.schedContextBinding.scId? ≠ some scId := by
      intro X tX hX' e
      cases hb : tX.schedContextBinding with
      | unbound => rw [hb] at e; cases e
      | bound s' =>
        rw [hb] at e; cases e
        exact hBoundFree X tX hX' hb
      | donated s' o =>
        rw [hb] at e; cases e
        obtain ⟨⟨sc1, h1, hbt⟩, -⟩ := hInv.donationOwnerValid X tX _ o hX' hb
        exact hUnheld X sc1 h1 hbt
    exact ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
      (.of_releaseLinks (SchedContextOps.settleReturnedContext_agree st1 home scId))
      (returnUnheldSchedContext_preserves_ipcInvariantFull hObjInv hInv hFree hNoOwner
        (hStackValid scId target target n hN).2 hP)

end SeLe4n.Kernel
