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

/-- **What the held pop writes, key by key**: the context's sever record at its
key, the holder's new binding at its key (on the thread it read there), and
every other thread and context as it was. -/
theorem keepDonatedSchedContext_objects (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)) (ht : TCB),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThread = some holder ∧
      outerCallerAcceptable st holder holder newOwner? = true ∧
      donationHeadOf? st scId sc = .ok head? ∧
      st.objects[holder.toObjId]? = some (.tcb ht) ∧ ¬ holder.isReserved ∧
      st'.objects[scId.toObjId]? = some (.schedContext
        (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev)) newOwner?)) ∧
      st'.objects[holder.toObjId]? = some (.tcb { ht with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }) ∧
      (∀ k t, k ≠ holder.toObjId → st'.objects[k]? = some (.tcb t) → st.objects[k]? = some (.tcb t)) ∧
      (∀ k t, k ≠ holder.toObjId → st.objects[k]? = some (.tcb t) → st'.objects[k]? = some (.tcb t)) ∧
      (∀ k x, k ≠ scId.toObjId → st'.objects[k]? = some (.schedContext x) →
        st.objects[k]? = some (.schedContext x)) ∧
      (∀ k x, k ≠ scId.toObjId → st.objects[k]? = some (.schedContext x) →
        st'.objects[k]? = some (.schedContext x)) := by
  obtain ⟨sc, head?, ot, s1, s2, hSc, hB, hOut, hHead, hS1, hS2, hL, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hNR := lookupTcb_some_not_reserved _ _ _ hL
  have hO2 : s2.objects[holder.toObjId]? = some (.tcb ot) := lookupTcb_some_objects s2 holder ot hL
  have hO1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ hO2
  have hNe : holder.toObjId ≠ scId.toObjId := by
    intro e; rw [e, storeObject_objects_eq st s1 _ _ hObjInv hS1] at hO1; cases hO1
  have hO : st.objects[holder.toObjId]? = some (.tcb ot) := by
    rw [← storeObject_objects_ne st s1 _ _ _ hNe hObjInv hS1]; exact hO1
  have hSc2 : s2.objects[scId.toObjId]? = some (.schedContext
      (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev)) newOwner?)) := by
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 scId
    have e1 : s1.getSchedContext? scId = some
        (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev)) newOwner?) :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
        (storeObject_objects_eq st s1 _ _ hObjInv hS1)
    exact (SystemState.getSchedContext?_eq_some_iff _ _ _).mp (e.trans e1)
  refine ⟨sc, head?, ot, hSc, hB, hOut, hHead, hO, hNR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [storeObject_objects_ne s2 st' _ _ _ hNe.symm hInv2 hS3]; exact hSc2
  · exact storeObject_objects_eq s2 st' _ _ hInv2 hS3
  · intro k t hk ht
    rw [storeObject_objects_ne s2 st' _ _ _ hk hInv2 hS3] at ht
    have h1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ ht
    by_cases e : k = scId.toObjId
    · subst e; rw [storeObject_objects_eq st s1 _ _ hObjInv hS1] at h1; cases h1
    · rw [storeObject_objects_ne st s1 _ _ _ e hObjInv hS1] at h1; exact h1
  · intro k t hk ht
    have hkS : k ≠ scId.toObjId := by intro e; rw [e, hSc] at ht; cases ht
    rw [storeObject_objects_ne s2 st' _ _ _ hk hInv2 hS3]
    apply storeDonationHeadPop_tcb_eq hInv1 hS2
    rw [storeObject_objects_ne st s1 _ _ _ hkS hObjInv hS1]; exact ht
  · intro k x hk hx
    have hkO : k ≠ holder.toObjId := by
      intro e; rw [e, storeObject_objects_eq s2 st' _ _ hInv2 hS3] at hx; cases hx
    rw [storeObject_objects_ne s2 st' _ _ _ hkO hInv2 hS3] at hx
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 (SeLe4n.SchedContextId.ofObjId k)
    have hx' : s2.getSchedContext? (SeLe4n.SchedContextId.ofObjId k) = some x :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (by
        rw [SeLe4n.SchedContextId.toObjId_ofObjId]; exact hx)
    rw [e] at hx'
    have h1 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hx'
    rw [SeLe4n.SchedContextId.toObjId_ofObjId,
      storeObject_objects_ne st s1 _ _ _ hk hObjInv hS1] at h1; exact h1
  · intro k x hk hx
    have hkO : k ≠ holder.toObjId := by intro e; rw [e, hO] at hx; cases hx
    rw [storeObject_objects_ne s2 st' _ _ _ hkO hInv2 hS3]
    have e := storeDonationHeadPop_getSchedContext?_eq hInv1 hS2 (SeLe4n.SchedContextId.ofObjId k)
    have hx1 : s1.getSchedContext? (SeLe4n.SchedContextId.ofObjId k) = some x :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (by
        rw [SeLe4n.SchedContextId.toObjId_ofObjId,
          storeObject_objects_ne st s1 _ _ _ hk hObjInv hS1]; exact hx)
    rw [← e] at hx1
    have h2 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hx1
    rw [SeLe4n.SchedContextId.toObjId_ofObjId] at h2; exact h2

/-- **The held pop rewrites one thread's binding codes and no other field**:
every thread of the post-state is a thread of the pre-state with at most its two
binding codes replaced. -/
theorem keepDonatedSchedContext_tcb_rewrite (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t' : TCB) (hT : st'.objects[k]? = some (.tcb t')) :
    ∃ t, st.objects[k]? = some (.tcb t) ∧
      ∃ c o, t' = { t with scBindingScCode := c, scBindingOwnerCode := o } := by
  obtain ⟨_, _, ht, _, _, _, _, hHt, _, _, hHt', tBwd, _, _, _⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  by_cases e : k = holder.toObjId
  · subst e
    rw [hHt'] at hT; cases hT
    exact ⟨ht, hHt, _, _, rfl⟩
  · refine ⟨t', tBwd _ _ e hT, t'.scBindingScCode, t'.scBindingOwnerCode, ?_⟩
    cases t'; rfl

/-- **The held pop's thread writes, both ways, as binding rewrites**: the shape
the frames over a rewrite of binding codes consume. -/
theorem keepDonatedSchedContext_tcb_bindingRewrite (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    (∀ (k : SeLe4n.ObjId) (t0 : TCB), st.objects[k]? = some (.tcb t0) →
      ∃ t', st'.objects[k]? = some (.tcb t') ∧ tcbBindingRewrite t' t0) ∧
    (∀ (k : SeLe4n.ObjId) (t' : TCB), st'.objects[k]? = some (.tcb t') →
      ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbBindingRewrite t' t0) := by
  obtain ⟨_, _, ht, _, _, _, _, hO, _, _, hO', tBwd, tFwd, _, _⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  refine ⟨fun k t0 hk => ?_, fun k t' hk => ?_⟩
  · by_cases e : k = holder.toObjId
    · subst e; rw [hO] at hk; cases hk
      exact ⟨_, hO', _, _, rfl⟩
    · exact ⟨t0, tFwd _ _ e hk, .refl t0⟩
  · by_cases e : k = holder.toObjId
    · subst e; rw [hO'] at hk; cases hk
      exact ⟨ht, hO, _, _, rfl⟩
    · exact ⟨t', tBwd _ _ e hk, .refl t'⟩

/-- **The holder before and after the held pop**: the thread it read, whose
binding names the context (the pop's guard), and that thread with the binding
the frame below owes. -/
theorem keepDonatedSchedContext_holder (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    ∃ ht : TCB, st.objects[holder.toObjId]? = some (.tcb ht) ∧
      ht.schedContextBinding.scId? = some scId ∧
      st'.objects[holder.toObjId]? = some (.tcb { ht with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }) := by
  obtain ⟨_, _, ht1, s1, s2, hG, -, -, -, -, hS1, hS2, hL, -⟩ :=
    keepDonatedSchedContext_ok_storeChainGuarded h
  obtain ⟨_, _, ht, _, _, _, _, hO, _, _, hO', _, _, _, _⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hO2 := lookupTcb_some_objects s2 holder ht1 hL
  have h1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ hO2
  have hNe : holder.toObjId ≠ scId.toObjId := by
    intro e'; rw [e', storeObject_objects_eq st s1 _ _ hObjInv hS1] at h1; cases h1
  rw [storeObject_objects_ne st s1 _ _ _ hNe hObjInv hS1, hO] at h1
  have e2 : ht = ht1 := by injection h1 with h1; injection h1 with h1
  subst e2
  exact ⟨ht, hO, hG, hO'⟩

/-- The binding the held pop writes names the context it kept. -/
theorem tcb_donationReturnBinding_scId? (scId : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId)
    (ht : TCB) :
    ({ ht with
        scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId n),
        scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId n) } :
      TCB).schedContextBinding.scId? = some scId := by
  cases n <;> rfl

/-- **The held pop moves no thread onto a context**: a thread bound to a context
after it was bound to the same context before (the holder keeps the context its
binding named, the pop's guard). -/
theorem keepDonatedSchedContext_binding_backward (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (y : SeLe4n.ThreadId) (t' : TCB) (s : SeLe4n.SchedContextId)
    (hT : st'.objects[y.toObjId]? = some (.tcb t')) (hS : t'.schedContextBinding.scId? = some s) :
    ∃ t0, st.objects[y.toObjId]? = some (.tcb t0) ∧ t0.schedContextBinding.scId? = some s := by
  obtain ⟨_, _, ht1, s1, s2, hG, -, -, -, -, hS1, hS2, hL, -⟩ :=
    keepDonatedSchedContext_ok_storeChainGuarded h
  obtain ⟨_, _, ht, _, _, _, _, hO, _, _, hO', tBwd, _, _, _⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  by_cases e : y.toObjId = holder.toObjId
  · rw [e] at hT ⊢
    rw [hO'] at hT; cases hT
    have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hO2 := lookupTcb_some_objects s2 holder ht1 hL
    have h1 := storeDonationHeadPop_tcb_backward hInv1 hS2 _ _ hO2
    have hNe : holder.toObjId ≠ scId.toObjId := by
      intro e'; rw [e', storeObject_objects_eq st s1 _ _ hObjInv hS1] at h1; cases h1
    rw [storeObject_objects_ne st s1 _ _ _ hNe hObjInv hS1, hO] at h1
    have e2 : ht = ht1 := by injection h1 with h1; injection h1 with h1
    subst e2
    refine ⟨ht, hO, ?_⟩
    rw [hG]
    cases newOwner? <;> simp [TCB.schedContextBinding, donationReturnBinding,
      SchedContextBinding.scId?] at hS <;> exact congrArg some hS
  · exact ⟨t', tBwd _ _ e hT, hS⟩

/-- The resolved held pop moves no thread onto a context. -/
theorem keepDonatedSchedContextResolved_binding_backward (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContextResolved st holder scId = .ok st')
    (y : SeLe4n.ThreadId) (t' : TCB) (s : SeLe4n.SchedContextId)
    (hT : st'.objects[y.toObjId]? = some (.tcb t')) (hS : t'.schedContextBinding.scId? = some s) :
    ∃ t0, st.objects[y.toObjId]? = some (.tcb t0) ∧ t0.schedContextBinding.scId? = some s := by
  obtain ⟨_, -, hK⟩ := keepDonatedSchedContextResolved_ok_decompose h
  exact keepDonatedSchedContext_binding_backward hObjInv hK y t' s hT hS

/-- The held pop keeps every thread's placement: it rewrites binding codes. -/
theorem keepDonatedSchedContext_getTcb?_placement_eq (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map TCB.placement = (st.getTcb? tid).map TCB.placement := by
  obtain ⟨_, _, ot, _, _, _, _, hO, _, _, hO', tBwd, tFwd, _, _⟩ :=
    keepDonatedSchedContext_objects hObjInv h
  by_cases e : tid.toObjId = holder.toObjId
  · unfold SystemState.getTcb?; rw [e, hO, hO']; rfl
  · cases h1 : st.getTcb? tid with
    | some t =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
        (tFwd _ t e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1))]
    | none =>
      cases h2 : st'.getTcb? tid with
      | none => rfl
      | some t =>
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
          (tBwd _ t e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2))] at h1
        cases h1

/-- The held pop keeps every thread's IPC state. -/
theorem keepDonatedSchedContext_tcb_ipcState_backward (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t' : TCB) (hT : st'.objects[k]? = some (.tcb t')) :
    ∃ t, st.objects[k]? = some (.tcb t) ∧ t.ipcState = t'.ipcState := by
  obtain ⟨t, hPre, c, o, rfl⟩ := keepDonatedSchedContext_tcb_rewrite hObjInv h k t' hT
  exact ⟨t, hPre, rfl⟩

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

/-- **The held pop keeps every object that is no context, reply or thread**: it
stores a context, the replies and one thread. -/
theorem keepDonatedSchedContext_other_iff (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (k : SeLe4n.ObjId) (o : KernelObject) (hSc : ∀ x, o ≠ .schedContext x)
    (hRp : ∀ x, o ≠ .reply x) (hTc : ∀ x, o ≠ .tcb x) :
    st'.objects[k]? = some o ↔ st.objects[k]? = some o := by
  obtain ⟨sc, head?, ht, s1, s2, hSc0, -, -, -, hS1, hS2, hL, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hO2 : s2.objects[holder.toObjId]? = some (.tcb ht) := lookupTcb_some_objects s2 holder ht hL
  constructor
  · intro hk
    have hkT : k ≠ holder.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv2 hS3] at hk; cases hk; exact hTc _ rfl
    rw [storeObject_objects_ne _ _ _ _ _ hkT hInv2 hS3] at hk
    have h1 := storeDonationHeadPop_non_reply_backward hInv1 hS2 k _ hRp hk
    have hkS : k ≠ scId.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hObjInv hS1] at h1; cases h1; exact hSc _ rfl
    rwa [storeObject_objects_ne _ _ _ _ _ hkS hObjInv hS1] at h1
  · intro hk
    have hkS : k ≠ scId.toObjId := by
      intro e; rw [e, hSc0] at hk; cases hk; exact hSc _ rfl
    have h1 : s1.objects[k]? = some o := by
      rw [storeObject_objects_ne _ _ _ _ _ hkS hObjInv hS1]; exact hk
    have h2 : s2.objects[k]? = some o := by
      rw [storeDonationHeadPop_non_reply_eq hInv1 hS2 k (fun r e' => by
        rw [h1] at e'; cases e'; exact hRp _ rfl), h1]
    have hkT : k ≠ holder.toObjId := by
      intro e; rw [e, hO2] at h2; cases h2; exact hTc _ rfl
    rw [storeObject_objects_ne _ _ _ _ _ hkT hInv2 hS3]; exact h2

/-- The held pop keeps every endpoint. -/
theorem keepDonatedSchedContext_endpoint_backward (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (k : SeLe4n.ObjId) (ep : Endpoint) (hk : st'.objects[k]? = some (.endpoint ep)) :
    st.objects[k]? = some (.endpoint ep) :=
  (keepDonatedSchedContext_other_iff hObjInv h k _ (fun _ e => by cases e)
    (fun _ e => by cases e) (fun _ e => by cases e)).mp hk

/-- **The held pop keeps every notification**: it stores a context, the replies
and one thread. -/
theorem keepDonatedSchedContext_notification_iff (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st')
    (k : SeLe4n.ObjId) (nt : Notification) :
    st'.objects[k]? = some (.notification nt) ↔ st.objects[k]? = some (.notification nt) := by
  obtain ⟨sc, head?, ht, s1, s2, hSc, -, -, -, hS1, hS2, hL, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hO2 : s2.objects[holder.toObjId]? = some (.tcb ht) := lookupTcb_some_objects s2 holder ht hL
  constructor
  · intro hk
    have hkT : k ≠ holder.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hInv2 hS3] at hk; cases hk
    rw [storeObject_objects_ne _ _ _ _ _ hkT hInv2 hS3] at hk
    have h1 := storeDonationHeadPop_non_reply_backward hInv1 hS2 k _ (fun _ e => by cases e) hk
    have hkS : k ≠ scId.toObjId := by
      intro e; rw [e, storeObject_objects_eq _ _ _ _ hObjInv hS1] at h1; cases h1
    rwa [storeObject_objects_ne _ _ _ _ _ hkS hObjInv hS1] at h1
  · intro hk
    have hkS : k ≠ scId.toObjId := by intro e; rw [e, hSc] at hk; cases hk
    have h1 : s1.objects[k]? = some (.notification nt) := by
      rw [storeObject_objects_ne _ _ _ _ _ hkS hObjInv hS1]; exact hk
    have h2 : s2.objects[k]? = some (.notification nt) := by
      rw [storeDonationHeadPop_non_reply_eq hInv1 hS2 k (fun r e' => by rw [h1] at e'; cases e'), h1]
    have hkT : k ≠ holder.toObjId := by intro e; rw [e, hO2] at h2; cases h2
    rw [storeObject_objects_ne _ _ _ _ _ hkT hInv2 hS3]; exact h2

end HeldPop

end SeLe4n.Kernel
