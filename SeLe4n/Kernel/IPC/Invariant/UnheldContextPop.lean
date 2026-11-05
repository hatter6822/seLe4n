/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.UnheldContextPop
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

end SeLe4n.Kernel
