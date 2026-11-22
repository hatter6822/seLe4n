/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.UnheldContextPop

/-!
# The IPC bundle across the pop of a held context its recipient cannot take

`keepDonatedSchedContext` is seL4-MCS's `reply_pop` at a head whose context a
thread holds, where the thread the pop answers holds a context of its own: the
head is popped off the context, and the context stays with its holder as the
binding the frame below owes (`donationReturnBinding`).  It writes the context's
head and origin, the two replies, and the holder's binding, and no other thread.

The bundle's conjuncts that read no binding carry across the read agreement the
three stores keep; the four donation conjuncts are proved on the post-state.  The
pop runs where the reply leg has already woken the thread the holder's loan
names (`ipcInvariantFullExceptDonationOwner`, relaxed at that thread), and the
held pop discharges the relaxation: after it no loan names that thread.  The one
caller obligation is the donation pop's own (`donationOuterUnowned`): no loan
already names the outer caller the holder comes to owe.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

section HeldPop

variable {st st' : SystemState} {holder : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
  {newOwner? : Option SeLe4n.ThreadId}

/-- **The held pop's holder guard holds wherever a context's bound thread names
it back** (the second half of the binding pair `schedContextBindingConsistent`,
which the scheduler bundle carries).  The pop reads its holder after its two
stores, which write the context and the reply objects and no thread, so the
thread it reads is the pre-state's `sc.boundThread`, whose binding the
invariant says is `.bound scId` or `.donated scId _`.  So the guard
`ht.schedContextBinding.scId? = some scId` never refuses on a state the
invariant holds of, and the held pop is seL4's `reply_pop` there. -/
theorem keepDonatedSchedContext_holderGuard_of_schedContextBindingConsistent
    (hObjInv : st.objects.invExt) (hCons : schedContextBindingConsistent st)
    {sc X : SchedContext} {head? : Option (SeLe4n.ReplyId × Reply)} {s1 s2 : SystemState}
    {ht : TCB}
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hB : sc.boundThread = some holder)
    (hS1 : storeObject scId.toObjId (.schedContext X) st = .ok ((), s1))
    (hS2 : storeDonationHeadPop scId head? s1 = .ok s2)
    (hL : lookupTcb s2 holder = some ht) :
    ht.schedContextBinding.scId? = some scId := by
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hO2 := lookupTcb_some_objects s2 holder ht hL
  have h1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ hO2
  have hNe : holder.toObjId ≠ scId.toObjId := by
    intro e'; rw [e', storeObject_objects_eq st s1 _ _ hObjInv hS1] at h1; cases h1
  rw [storeObject_objects_ne st s1 _ _ _ hNe hObjInv hS1] at h1
  obtain ⟨t, hT, hBind⟩ := hCons.2 scId sc hSc holder hB
  rw [hT] at h1
  have e : t = ht := by injection h1 with h1; injection h1
  subst e
  rcases hBind with hb | ⟨o, hb⟩ <;> rw [hb] <;> rfl

/-- **The holder guard is redundant under the binding pair**: on a state where a
context's bound thread names it back, the held pop that passes its seL4 checks
(the context bound to `holder`, the outer caller acceptable, the head resolved)
and whose stores succeed answers `.ok` — the guard's refusal branch is never
taken.  Stated over `schedContextBindingConsistent`, the scheduler bundle's
binding pair. -/
theorem keepDonatedSchedContext_ok_of_schedContextBindingConsistent
    (hObjInv : st.objects.invExt) (hCons : schedContextBindingConsistent st)
    {sc : SchedContext} {head? : Option (SeLe4n.ReplyId × Reply)} {s1 s2 : SystemState}
    {ht : TCB}
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hB : sc.boundThread = some holder)
    (hOut : outerCallerAcceptable st holder holder newOwner? = true)
    (hHead : donationHeadOf? st scId sc = .ok head?)
    (hS1 : storeObject scId.toObjId
        (.schedContext (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev)) newOwner?))
        st = .ok ((), s1))
    (hS2 : storeDonationHeadPop scId head? s1 = .ok s2)
    (hL : lookupTcb s2 holder = some ht)
    (hS3 : storeObject holder.toObjId (.tcb { ht with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) })
        s2 = .ok ((), st')) :
    keepDonatedSchedContext st holder scId newOwner? = .ok st' := by
  have hG := keepDonatedSchedContext_holderGuard_of_schedContextBindingConsistent hObjInv
    hCons hSc hB hS1 hS2 hL
  have hSc' : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  unfold keepDonatedSchedContext
  simp only [hSc', hB, hOut, hHead, hS1, hS2, hL, hG, bne_self_eq_false, Bool.not_true,
    Bool.false_eq_true, if_false]
  rw [hS3]

/-- The held pop keeps the read agreement: a context store, the head pop and a
binding store. -/
theorem keepDonatedSchedContext_donationReadAgreement (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    donationReadAgreement st st' := by
  obtain ⟨sc, head?, ot, s1, s2, hSc, _, _, _, hS1, hS2, hL, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have a1 := donationReadAgreement_of_schedContextStore st s1 scId.toObjId sc _ hSc hObjInv hS1
  have a2 := donationReadAgreement_of_headPop hInv1 hS2
  have a3 := donationReadAgreement_of_tcbBindingStore s2 st' holder.toObjId ot
    (donationReturnBinding scId newOwner?) ot.originScCode
    (lookupTcb_some_objects s2 holder ot hL) hInv2 hS3
  exact (a1.trans a2).trans a3

/-- **The held pop discharges the reply leg's relaxation and keeps the bundle.**
The holder's loan names `bindingOwner` (the thread the reply leg woke, where
`donationOwnerValid` is relaxed); the pop rewrites the holder's binding to the
one the frame below owes, so afterwards no loan names `bindingOwner` (no second
loan named it before, `donationOwnerUnique`), and the loan it now owes names an
outer caller the pop accepted (`outerCallerAcceptable`) and no other loan
names (`donationOuterUnowned`). -/
theorem keepDonatedSchedContext_establishes_ipcInvariantFull_of_except
    (hObjInv : st.objects.invExt) {bindingOwner : SeLe4n.ThreadId}
    (hInv : ipcInvariantFullExceptDonationOwner st bindingOwner)
    (hRet : replyDonationReturn? st holder = some (scId, bindingOwner))
    (hOuterFree : donationOuterUnowned st newOwner?)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨sc, head?, ht, hSc, hB0, hOut, _, hHt, _, hSc', hHt', tBwd, tFwd, cBwd, cFwd⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  obtain ⟨pTcb, hLk, hPB⟩ := replyDonationReturn?_some_lookup st holder scId bindingOwner hRet
  have hPObj : st.objects[holder.toObjId]? = some (.tcb pTcb) := lookupTcb_some_objects st holder pTcb hLk
  have hEqT : pTcb = ht := by rw [hPObj] at hHt; cases hHt; rfl
  subst hEqT
  have hAgree := keepDonatedSchedContext_donationReadAgreement hObjInv h
  have hBd := donationReturnBinding_stored pTcb scId newOwner?
  have split : ∀ (X : SeLe4n.ThreadId) (t : TCB), st'.objects[X.toObjId]? = some (.tcb t) →
      (X = holder ∧ t.schedContextBinding = donationReturnBinding scId newOwner?) ∨
        (X ≠ holder ∧ st.objects[X.toObjId]? = some (.tcb t)) := by
    intro X t hX
    by_cases e : X.toObjId = holder.toObjId
    · have eX := SeLe4n.ThreadId.toObjId_injective _ _ e
      subst eX
      rw [hHt'] at hX
      cases hX
      exact Or.inl ⟨rfl, hBd⟩
    · exact Or.inr ⟨fun h => e (h ▸ rfl), tBwd _ _ e hX⟩
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
          · exact hB0
          · revert hR
            cases oT.ipcState with
            | blockedOnReply e r => intro _; exact ⟨e, r, rfl⟩
            | _ => intro hR; cases hR
    · obtain ⟨⟨x, hx, hxB⟩, oT, hoT, hoU, hoR⟩ :=
        hInv.donationOwnerValidExcept tid tcb s o hT0 hBdT
      have hsNe : s.toObjId ≠ scId.toObjId := by
        intro e
        rw [e, hSc] at hx
        cases hx
        rw [hB0] at hxB
        exact hNe (Option.some.inj hxB).symm
      have hoNe : o.toObjId ≠ holder.toObjId := by
        intro e
        have eo := SeLe4n.ThreadId.toObjId_injective _ _ e
        subst eo
        rw [hPObj] at hoT
        cases hoT
        rw [hPB] at hoU; cases hoU
      have hoR' : ∃ epId replyTarget, oT.ipcState = .blockedOnReply epId replyTarget := by
        rcases hoR with hEq | hR
        · subst hEq
          exact absurd (hInv.donationOwnerUnique tid holder tcb pTcb s scId o hT0 hPObj hBdT hPB) hNe
        · exact hR
      exact ⟨⟨x, cFwd _ _ hsNe hx, hxB⟩, oT, tFwd _ _ hoNe hoT, hoU, hoR'⟩
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
    have hPS : pTcb.schedContextBinding.scId? = some scId := by rw [hPB]; rfl
    rcases split t1 tcb1 h1 with ⟨rfl, hb1⟩ | ⟨hN1, hPre1⟩ <;>
      rcases split t2 tcb2 h2 with ⟨e2, hb2⟩ | ⟨hN2, hPre2⟩
    · exact hNe e2.symm
    · rw [hb1] at hS1
      have : s = scId := by cases newOwner? <;> simpa [SchedContextBinding.scId?] using hS1.symm
      subst this
      exact hInv.donationBudgetTransfer t1 t2 pTcb tcb2 s hPObj hPre2 hNe hPS hS2
    · subst e2
      rw [hb2] at hS2
      have : s = scId := by cases newOwner? <;> simpa [SchedContextBinding.scId?] using hS2.symm
      subst this
      exact hInv.donationBudgetTransfer t1 t2 tcb1 pTcb s hPre1 hPObj hNe hS1 hPS
    · exact hInv.donationBudgetTransfer t1 t2 tcb1 tcb2 s hPre1 hPre2 hNe hS1 hS2
  exact ipcInvariantFull_of_donationReadAgreement_of_except st st' bindingOwner hInv hAgree
    (donationOwnerValid_implies_donationChainAcyclic st' hDOV) hDOV hDBT hDOU

/-- **The held pop keeps the bundle** from an unrelaxed pre-state. -/
theorem keepDonatedSchedContext_preserves_ipcInvariantFull (hObjInv : st.objects.invExt)
    {owner : SeLe4n.ThreadId} (hInv : ipcInvariantFull st)
    (hRet : replyDonationReturn? st holder = some (scId, owner))
    (hOuterFree : donationOuterUnowned st newOwner?)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    ipcInvariantFull st' :=
  keepDonatedSchedContext_establishes_ipcInvariantFull_of_except hObjInv
    (ipcInvariantFullExceptDonationOwner_of_full owner hInv) hRet hOuterFree h

/-- **The held pop closes a chain relaxed at its head**, as the donation pop
does: its first two stores are the head pop's, and the holder's binding store
carries no chain data. -/
theorem keepDonatedSchedContext_preserves_donationChainWellFormed_of_except
    (hObjInv : st.objects.invExt)
    (hChainNone : ∀ sc, st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ sc rid r, st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok (some (rid, r)) → donationChainWellFormedExcept st rid)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    donationChainWellFormed st' := by
  obtain ⟨sc, head?, ht, s1, s2, hSc, -, -, hHead, hS1, hS2, hL, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hScGet : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hSc
  have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hChain2 : donationChainWellFormed s2 :=
    donationHeadPop_preserves_donationChainWellFormed_of_except hObjInv
      (fun hNone => hChainNone sc hScGet (hNone ▸ hHead))
      (fun rid r hSome => hChainHead sc rid r hScGet (hSome ▸ hHead))
      hScGet hHead rfl hS1 hS2
  exact donationChainWellFormed_of_frame
    (donationChainFrame_of_tcb_rewrite hInv2 (lookupTcb_some_objects s2 holder ht hL) hS3) hChain2

/-- **The held pop keeps the donation chain** from an unrelaxed pre-state. -/
theorem keepDonatedSchedContext_preserves_donationChainWellFormed
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    donationChainWellFormed st' :=
  keepDonatedSchedContext_preserves_donationChainWellFormed_of_except hObjInv
    (fun _ _ _ => hChain) (fun _ rid _ _ _ => donationChainWellFormedExcept_of_wellFormed hChain rid) h

end HeldPop

end SeLe4n.Kernel
