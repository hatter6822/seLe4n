/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Capability.FrameFinalise

/-!
# The finalising delete keeps every lent context headed by its lender

WS-ZA ZA5.4 part 25.  `lentContextHeadsLenderFrame` is a stated pre-state fact
of the delete dispatch (`LoanCoherence.lean`); this module proves that every
step the finalising delete runs keeps it, so the delete and the revocation loop
carry it from that one fact: the slot delete (a CNode or a thread's space slot,
then the derivation links), the page teardown (address-space roots alone), each
kind's finalisation — every write in its slot by `FinaliseFrame`'s lent-context
frame, except two — and the retire (no reply it erases heads a stack).

The two exceptions are where the fact is read, not just carried:

* **the reply cancel** lets go of the caller's reply link
  (`consumeCallerReply`).  The caller lends to no one: under the fact a loan
  from it would make the reply it waits on a stack head, and the finalisation
  admits only a reply that heads no stack (`replyCaller_lendsNone`).  That is
  the `O(1)` reading that replaced the whole-store `loansFromNone` walk.
* **the unstack** clears the head reply's upward link.  It runs on a context
  the holder's unbind has just unbound (`finaliseSchedContextUnbind_unbound`),
  so no thread holds it on loan (`donationOwnerValid`), and no other context's
  head is touched.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A store at a key holding `o`, of an object keeping what the fact reads. -/
theorem loanWrite.of_storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {o o' : KernelObject} (hInv : st.objects.invExt) (hPre : st.objects[k]? = some o)
    (h : storeObject k o' st = .ok ((), st')) (hK : objectLoanKept o' o) : loanWrite st st' := by
  intro oid
  by_cases e : oid = k
  · subst e; exact Or.inr ⟨o, o', hPre, storeObject_objects_eq st st' oid o' hInv h, hK⟩
  · exact Or.inl (storeObject_objects_ne st st' k oid o' e hInv h)

/-- ...and the same, `c`'s reply link perhaps let go. -/
theorem loanWriteOff.of_storeObject {c : SeLe4n.ThreadId} {st st' : SystemState}
    {k : SeLe4n.ObjId} {o o' : KernelObject} (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some o) (h : storeObject k o' st = .ok ((), st'))
    (hK : objectLoanKeptOff (k = c.toObjId) o' o) : loanWriteOff c st st' := by
  intro oid
  by_cases e : oid = k
  · subst e; exact Or.inr ⟨o, o', hPre, storeObject_objects_eq st st' oid o' hInv h, hK⟩
  · exact Or.inl (storeObject_objects_ne st st' k oid o' e hInv h)

/-- **The splice keeps every stack head**: it rewrites replies alone, the frame
above the cut keeping its upward link and the frame below moving from one frame
link to another (`spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink`). -/
theorem loanWrite.of_spliceReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) : loanWrite st (spliceReplyFrameOutOrSelf st rid) := by
  intro oid
  rcases spliceReplyFrameOutOrSelf_objects_rewrite st rid hInv oid with e | ⟨r, r', hr, hr', -⟩
  · exact Or.inl e
  · refine Or.inr ⟨.reply r, .reply r', hr, hr', fun _ e => (by cases e), fun r0 s e hn => ?_⟩
    cases e
    have hq : (spliceReplyFrameOutOrSelf st rid).getReply? ⟨oid.val⟩ = some r' := by
      rw [SystemState.getReply?_eq_some_iff]; exact hr'
    obtain ⟨rp, hp, -, hN⟩ :=
      spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink st rid hInv _ r' hq
    rw [SystemState.getReply?_eq_some_iff,
      show (⟨oid.val⟩ : SeLe4n.ReplyId).toObjId = oid from rfl, hr] at hp
    cases hp
    rcases hN with e | ⟨a, b, ha, -⟩
    · exact ⟨r', rfl, e.trans hn⟩
    · rw [hn] at ha; cases ha

/-- ...and so does a thread's frame spliced off its stack. -/
theorem loanWrite.of_spliceThreadReplyFrameOut (st : SystemState) (t : TCB)
    (hInv : st.objects.invExt) : loanWrite st (spliceThreadReplyFrameOut st t) := by
  unfold spliceThreadReplyFrameOut
  cases t.replyObject with
  | none => exact .refl st
  | some rid => exact loanWrite.of_spliceReplyFrameOutOrSelf st rid hInv

/-- **The consume lets go of the caller's reply link alone**: the reply's
consumed record keeps a stack head's link (`Reply.consumed`), and the caller's
reply link is cleared. -/
theorem loanWriteOff.of_consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) : loanWriteOff c st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact (loanWrite.refl st).off c
  · rename_i rid _
    have h := SystemState.consumeCallerReply_eq_link st c rid
    generalize st.consumeCallerReplyLink c rid = st' at h ⊢
    unfold SystemState.consumeCallerReply at h
    cases hC : SystemState.consumeReply rid st with
    | error e => rw [hC] at h; cases h
    | ok p =>
      obtain ⟨⟨⟩, st1⟩ := p
      rw [hC] at h
      have f1 : loanWriteOff c st st1 ∧ st1.objects.invExt := by
        unfold SystemState.consumeReply at hC
        cases hR : st.getReply? rid with
        | none => rw [hR] at hC; cases hC; exact ⟨(loanWrite.refl st).off c, hInv⟩
        | some r =>
          rw [hR] at hC
          refine ⟨loanWriteOff.of_storeObject hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
            hC ⟨fun _ e => (by cases e), fun r0 s e hn => ?_⟩,
            storeObject_preserves_objects_invExt _ _ _ _ hInv hC⟩
          cases e
          refine ⟨r.consumed, rfl, ?_⟩
          unfold Reply.consumed; rw [hn]
      simp only at h
      cases hT : st1.getTcb? c with
      | none => rw [hT] at h; cases h; exact f1.1
      | some tcb =>
        rw [hT] at h
        exact f1.1.trans (loanWriteOff.of_storeObject f1.2
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) h
          ⟨fun tx e => by cases e; exact ⟨tcb, rfl, Or.inl rfl, fun _ _ h => h⟩,
            fun _ _ e => by cases e⟩)

/-- **A reply's caller the finalisation admits lends to no one**, on a state
where every lent context is headed by its lender's frame: a loan from it would
make the reply it waits on a stack head, and the reply heads no stack.  The
`O(1)` reading of the admission (`replyStackLinkIsHead`) that stands in for a
walk of the whole store. -/
theorem replyCaller_lendsNone {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hW : lentContextHeadsLenderFrame st)
    (hX : st.getObject? x = some (.reply r)) (hT : st.getTcb? c = some t)
    (hHd : replyStackLinkIsHead r.next = false) (hRO : t.replyObject = some ⟨x.val⟩) :
    ∀ (holder : SeLe4n.ThreadId) (ht : TCB) (s : SeLe4n.SchedContextId),
      st.objects[holder.toObjId]? = some (.tcb ht) → ht.schedContextBinding ≠ .donated s c := by
  intro holder ht s hH hB
  obtain ⟨rid, r', hRO', hR', hN⟩ :=
    hW holder ht s c t hH hB ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
  rw [hRO] at hRO'; cases hRO'
  rw [show (⟨x.val⟩ : SeLe4n.ReplyId).toObjId = x from rfl, ← SystemState.getObject?_eq_getElem,
    hX] at hR'
  cases hR'
  rw [hN] at hHd; simp [replyStackLinkIsHead] at hHd

/-- **A reply's caller cancel, with its boost reverted, keeps the fact**: the
splice, the restore, the unlink and the walk keep every thread's reply link and
loan and every stack head; the consume lets go of the caller's link, and the
caller lends to no one (`replyCaller_lendsNone`). -/
theorem finaliseReplyStep_keepsLentContextHeads {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt)
    (hW : lentContextHeadsLenderFrame s) (hX : s.getObject? x = some (.reply r))
    (hT : s.getTcb? c = some t)
    (hF : replyCallerFinalisable x r c t = true) :
    lentContextHeadsLenderFrame
      (finaliseReplyRevert (Lifecycle.Suspend.cancelIpcBlocking s c t) t.blockingServer?) := by
  obtain ⟨hHd, -, -, -, ⟨ep, rt, hB⟩, hRO, -, -, -, hD⟩ := replyCallerFinalisable_parts hX hF
  have hNo := replyCaller_lendsNone hW hX hT hHd hRO
  rw [cancelIpcBlocking_replyArm_of_noDonation s c t hB hD]
  have f1 := loanWrite.of_spliceThreadReplyFrameOut s t hInv
  have i1 := (FinaliseFrameAny.spliceThreadReplyFrameOut s t hInv).invExt
  generalize spliceThreadReplyFrameOut s t = s1 at f1 i1
  have F2 : FinaliseFrame s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact FinaliseFrame.updateTcb _ c _ i1
  generalize Lifecycle.Suspend.restoreToReadyCancelled s1 c = s2 at F2
  have f3 := loanWriteOff.of_consumeReplyLink s2 c t F2.invExt
  have i3 := (FinaliseFrameAny.consumeReplyLink s2 c t F2.invExt).invExt
  generalize Lifecycle.Suspend.consumeReplyLink s2 c t = s3 at f3 i3
  have f4 := loanWrite.of_agreeOffRunLinks
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks s3 c t.blockingServer?)
  have i4 := SystemState.unlinkReplyWaiterOpt_objects_invExt s3 c t.blockingServer? i3
  generalize s3.unlinkReplyWaiterOpt c t.blockingServer? = s4 at f4 i4
  have F5 := FinaliseFrame.finaliseReplyRevert s4 t.blockingServer? i4
  exact hW.of_loanWriteOff hNo
    ((((f1.off c).trans (F2.loan.off c)).trans f3).trans ((f4.off c).trans (F5.loan.off c)))

/-- **The unstack keeps the fact on a context no thread is bound to**: the head
reply it clears headed this context, which no thread holds on loan
(`donationOwnerValid`: a holder is the context's bound thread), and the context
write reads no thread and no reply. -/
theorem finaliseUnstack_keepsLentContextHeads {s s1 : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} {rid : SeLe4n.ReplyId} {r : Reply} (hInv : s.objects.invExt)
    (hOwn : donationOwnerValid s) (hW : lentContextHeadsLenderFrame s)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hB0 : sc.boundThreadCode = 0)
    (hR : s.getReply? rid = some r) (hN : r.next = some (.head ⟨x.val⟩))
    (hS : storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1)) :
    lentContextHeadsLenderFrame
      (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) := by
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hSco := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hX : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x := rfl
  rw [hX] at hSco
  have hRX : rid.toObjId ≠ x := by intro e; rw [e, hSco] at hRo; cases hRo
  have hI1 := storeObject_preserves_objects_invExt s s1 _ _ hInv hS
  -- The context write: its own key, or nothing.
  have hCtx : ∀ k, k ≠ x → (s1.updateSchedContext ⟨x.val⟩ fun sc =>
      { sc with scReply := none }).objects[k]? = s1.objects[k]? :=
    fun k hk => SystemState.updateSchedContext_objects_ne _ _ _ k (by rw [hX]; exact Ne.symm hk) hI1
  have hAtX : ∀ tx, (s1.updateSchedContext ⟨x.val⟩ fun sc =>
      { sc with scReply := none }).objects[x]? ≠ some (.tcb tx) := by
    intro tx e
    cases hG : s1.getSchedContext? ⟨x.val⟩ with
    | none =>
      rw [SystemState.updateSchedContext_eq_self_of_none hG,
        storeObject_objects_ne s s1 _ x _ (Ne.symm hRX) hInv hS, hSco] at e
      cases e
    | some y =>
      rw [SystemState.updateSchedContext_eq_of_some hG] at e
      dsimp only at e
      rw [hX, RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hI1] at e
      cases e
  generalize s1.updateSchedContext ⟨x.val⟩ (fun sc => { sc with scReply := none }) = s2 at hCtx hAtX
  have hOff : ∀ k, k ≠ x → k ≠ rid.toObjId → s2.objects[k]? = s.objects[k]? := fun k h1 h2 =>
    (hCtx k h1).trans (storeObject_objects_ne s s1 _ k _ h2 hInv hS)
  have back : ∀ (k : SeLe4n.ObjId) (tx : TCB), s2.objects[k]? = some (.tcb tx) →
      s.objects[k]? = some (.tcb tx) := by
    intro k tx hk
    by_cases e1 : k = x
    · subst e1; exact absurd hk (hAtX tx)
    by_cases e2 : k = rid.toObjId
    · subst e2
      rw [hCtx _ e1, storeObject_objects_eq s s1 _ _ hInv hS] at hk; cases hk
    · rw [← hOff k e1 e2]; exact hk
  intro holder ht scId owner ot hH hB hO
  have hH0 := back _ _ hH
  obtain ⟨rid', r', hRO, hR', hN'⟩ := hW holder ht scId owner ot hH0 hB (back _ _ hO)
  have hNeR : rid' ≠ rid := by
    rintro rfl
    rw [hRo] at hR'; cases hR'
    rw [hN] at hN'; cases hN'
    obtain ⟨⟨sc', hSc', hBd⟩, -⟩ := hOwn holder ht ⟨x.val⟩ owner hH0 hB
    rw [hX, hSco] at hSc'; cases hSc'
    unfold SchedContext.boundThread at hBd; rw [hB0] at hBd; cases hBd
  have hNeX : rid'.toObjId ≠ x := by intro e; rw [e, hSco] at hR'; cases hR'
  exact ⟨rid', r', hRO, by
    rw [hOff _ hNeX (fun e => hNeR (SeLe4n.ReplyId.toObjId_injective _ _ e))]; exact hR', hN'⟩

/-- **A retire keeps the fact when what it erases heads no stack**: a retire
write moves no thread and erases at most `x`, so every loan and every lender's
link stand, and every stack head stands but `x`'s. -/
theorem lentContextHeadsLenderFrame.of_finalRetireWrite {st st' : SystemState} {x : SeLe4n.ObjId}
    (hW : lentContextHeadsLenderFrame st) (F : finalRetireWrite st st' x)
    (hX : ∀ r, st.objects[x]? = some (.reply r) → r.next = none) :
    lentContextHeadsLenderFrame st' := by
  have back : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
      st.objects[k]? = some (.tcb tx) := by
    intro k tx hk
    rcases F k with e | ⟨-, -, hn⟩ | ⟨U, -, hU'⟩
    · rw [← e]; exact hk
    · rw [hn] at hk; cases hk
    · rw [hU'] at hk; cases hk
  intro holder ht scId owner ot hH hB hO
  obtain ⟨rid, r, hRO, hR, hN⟩ := hW holder ht scId owner ot (back _ _ hH) hB (back _ _ hO)
  refine ⟨rid, r, hRO, ?_, hN⟩
  rcases F rid.toObjId with e | ⟨hx, -, -⟩ | ⟨U, hU, -⟩
  · rw [e]; exact hR
  · rw [hx] at hR; rw [hX r hR] at hN; cases hN
  · rw [hR] at hU; cases hU

/-- **An admitted retire erases no reply that heads a stack**: a reply is a
passive object, retired only while quiescent (`passiveObjectQuiescent`: no
caller and no stack link). -/
theorem finalRetireAdmitted_reply_unlinked {st : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireAdmitted st x = true) {r : Reply} (hR : st.objects[x]? = some (.reply r)) :
    r.next = none := by
  have hP : passiveKernelObject st.objects[x]? := by rw [hR]; trivial
  obtain ⟨hQ, -⟩ := passiveObjectRetirable_parts (finalRetireAdmitted.retirable h hP)
  unfold passiveObjectQuiescent at hQ
  rw [SystemState.getObject?_eq_getElem, hR] at hQ
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hQ
  exact hQ.2

/-- **The retire keeps the fact.** -/
theorem retireFinalObject_keepsLentContextHeads (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (hW : lentContextHeadsLenderFrame st) :
    lentContextHeadsLenderFrame (retireFinalObject ec target recorder st) := by
  rcases retireFinalObject_admitted ec target recorder st with e | hA
  · rw [e]; exact hW
  exact hW.of_finalRetireWrite (retireFinalObject_frame ec target recorder st hInv).2.2.2.2
    (fun r hR => finalRetireAdmitted_reply_unlinked hA hR)

/-- **Writes off the derivation links keep it**: a CNode is no thread and no
reply, and a thread differs only in its space slots' links. -/
theorem loanWrite.of_agreeOffDerivationLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st) : loanWrite st st' := by
  intro oid
  rcases h oid with e | ⟨cn, cn', ha, hb, -⟩ | ⟨t, t', ha, hb, hw⟩
  · exact Or.inl e
  · exact Or.inr ⟨.cnode cn, .cnode cn', ha, hb,
      objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e)⟩
  · refine Or.inr ⟨.tcb t, .tcb t', ha, hb, objectLoanKept_tcb ⟨?_, fun s o hd => ?_⟩⟩
    · simpa [TCB.withoutLinks] using congrArg TCB.replyObjectCode hw
    · have e1 : t'.scBindingScCode = t.scBindingScCode := by
        simpa [TCB.withoutLinks] using congrArg TCB.scBindingScCode hw
      have e2 : t'.scBindingOwnerCode = t.scBindingOwnerCode := by
        simpa [TCB.withoutLinks] using congrArg TCB.scBindingOwnerCode hw
      unfold TCB.schedContextBinding at hd ⊢; rw [← e1, ← e2]; exact hd

/-- **The slot delete keeps the fact**: it empties a CNode slot or a thread's
space slot, then splices the slot out of the derivation tree. -/
theorem cspaceDeleteSlot_keepsLentContextHeads (st st' : SystemState) (addr : CSpaceAddr)
    (hInv : st.objects.invExt) (hW : lentContextHeadsLenderFrame st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) : lentContextHeadsLenderFrame st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hC : loanWrite st stC := by
    rcases cspaceDeleteSlotCore_ok_cases hCore with ⟨cn, hPre, hS⟩ | ⟨t, hPre, hS⟩
    · exact loanWrite.of_storeObject hInv hPre hS
        (objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e))
    · exact loanWrite.of_storeObject hInv hPre hS (objectLoanKept_tcb ⟨rfl, fun _ _ h => h⟩)
  exact (hW.of_loanWrite hC).of_loanWrite (loanWrite.of_agreeOffDerivationLinks
    (spliceDeletedCdtNode_agree (cspaceDeleteSlotCore_invExt _ _ _ hInv hCore) addr).1)

/-- **The page teardown keeps the fact**: it rewrites address-space roots
alone. -/
theorem finaliseDestroyedCapabilities_keepsLentContextHeads (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st st' : SystemState)
    (hInv : st.objects.invExt) (hW : lentContextHeadsLenderFrame st)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    lentContextHeadsLenderFrame st' := by
  have hR := (finaliseDestroyedCapabilities_ok_frame ec named pages st st' hInv h).2.1
  refine hW.of_loanWrite fun oid => ?_
  rcases hR oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
  · exact Or.inl e
  · exact Or.inr ⟨.vspaceRoot r, .vspaceRoot r', hr, hr',
      objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e)⟩

