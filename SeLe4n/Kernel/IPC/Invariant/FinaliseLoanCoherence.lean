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
  (`consumeCallerReply`), so the caller must lend to no one by then.  A reply
  heading no stack has a caller that lends to no one: under the fact a loan
  from it would make the reply it waits on a stack head
  (`replyCaller_lendsNone`), the `O(1)` reading that replaced the whole-store
  `loansFromNone` walk.  A head reply's cancel first hands the caller's
  reservation back (seL4 MCS's `reply_pop`): the pop keeps the fact, the
  caller now holding the context on loan from the outer caller, whose frame
  the pop makes the head (`returnDonatedSchedContext_keepsLentContextHeads`),
  and leaves no loan from the caller (`finaliseReplyReturn_keepsLentContextHeads`).
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

/-- **The caller of a reply heading no stack lends to no one**, on a state
where every lent context is headed by its lender's frame: a loan from it would
make the reply it waits on a stack head.  The `O(1)` reading of the reply's
link (`replyStackLinkIsHead`) that stands in for a walk of the whole store. -/
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

/-- **What the donation return leaves of the replies**: a reply it names neither
as the head nor as the frame below keeps its record, and the frame below (its
link to the head kept apart from the head itself) heads the context, and the
head itself (kept apart from the frame below) is unlinked from the stack. -/
theorem returnDonatedSchedContext_reply_cases {st st' : SystemState} {h : SeLe4n.ThreadId}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hPop : returnDonatedSchedContext st h s c n = .ok st') :
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
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4, hSc, -, -, hHead, hS1, hClear, hL1,
    hS3, hL2, hS4, hEq⟩ := returnDonatedSchedContext_ok_storeChain _ _ h s c n hPop
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hI2 := storeDonationHeadPop_preserves_objects_invExt hI1 hClear
  have hI3 := storeObject_preserves_objects_invExt _ _ _ _ hI2 hS3
  have eO : st'.objects = s4.objects := by rw [hEq]
  have tail : ∀ (k : SeLe4n.ObjId) (r : Reply), s2.objects[k]? = some (.reply r) →
      st'.objects[k]? = some (.reply r) := by
    intro k r hk
    have hc : k ≠ c.toObjId := by
      intro e; rw [e, lookupTcb_some_objects _ _ _ hL1] at hk; cases hk
    have h3 : s3.objects[k]? = some (.reply r) := by
      rw [storeObject_objects_ne _ _ _ k _ hc hI2 hS3]; exact hk
    have hh : k ≠ h.toObjId := by
      intro e; rw [e, lookupTcb_some_objects _ _ _ hL2] at h3; cases h3
    rw [eO, storeObject_objects_ne _ _ _ k _ hh hI3 hS4]; exact h3
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

/-- **The donation return keeps the fact** (seL4 MCS's `reply_pop`): the thread
the context is taken from holds nothing any more; the thread it goes back to
holds it on loan only from the outer caller the reply stack names, whose frame
the pop has just made the head; and every other loan's lender keeps its frame,
which is neither the popped head (its context is bound to the thread it is taken
from, `donationOwnerValid`) nor the frame below it (a frame link, not a head). -/
theorem returnDonatedSchedContext_keepsLentContextHeads {st st' : SystemState}
    {h : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId}
    {n : Option SeLe4n.ThreadId} (hInv : st.objects.invExt) (hW : lentContextHeadsLenderFrame st)
    (hOwn : donationOwnerValid st) (hLink : replyCallerLinkageReciprocal st)
    (hRes : replyStackOuterCaller? st s = .ok n)
    (hPop : returnDonatedSchedContext st h s c n = .ok st')
    (hBound : ∀ sc, st.objects[s.toObjId]? = some (.schedContext sc) → sc.boundThread = some h) :
    lentContextHeadsLenderFrame st' := by
  obtain ⟨sc, head?, hSc, hHead, hKeep, hBelow, -⟩ := returnDonatedSchedContext_reply_cases hInv hPop
  have hGetSc : st.getSchedContext? s = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  -- What the head validation and the resolver read.
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
  -- A reply off the head and the frame below keeps its record; a stack head
  -- other than the popped head is not the frame below.
  have keepHead : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (sc' : SeLe4n.SchedContextId),
      st.objects[rid.toObjId]? = some (.reply r) → r.next = some (.head sc') →
      (∀ x rx, head? = some (x, rx) → rid.toObjId ≠ x.toObjId) →
      st'.objects[rid.toObjId]? = some (.reply r) := by
    intro rid r sc' hR hN hNx
    refine hKeep _ r hR hNx (fun x rx y e hP hy => ?_)
    obtain ⟨b, -, hb, hbN, -⟩ := hBelowAt x rx y e hP
    rw [← hy, hR] at hb; cases hb
    rw [hN] at hbN; cases hbN
  intro holder ht' sc' o ot' hH' hB' hO'
  obtain ⟨hSrv, hOwnB, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
    st st' h s c hInv n hPop holder.toObjId ht' hH'
  obtain ⟨ot, hOpre, -, hRO⟩ := returnDonatedSchedContext_tcb_ipcState_replyObject_backward
    st st' h s c hInv n hPop o.toObjId ot' hO'
  by_cases eH : holder.toObjId = h.toObjId
  · rw [hSrv eH] at hB'; cases hB'
  by_cases eC : holder.toObjId = c.toObjId
  · -- The thread the context goes back to: on loan from the outer caller.
    rw [hOwnB eH eC] at hB'
    cases hn : n with
    | none => rw [hn] at hB'; cases hB'
    | some outer =>
      rw [hn] at hB'
      simp only [donationReturnBinding, SchedContextBinding.donated.injEq] at hB'
      obtain ⟨e1, e2⟩ := hB'
      -- The stack had a frame below the head, whose caller is the outer caller.
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
          have eT : tcbO = ot := by
            rw [hOpre] at hTO; exact (KernelObject.tcb.inj (Option.some.inj hTO)).symm
          have hyx : y.toObjId ≠ x.toObjId := by
            intro e
            rw [e, (hHeadAt x rx hHd).1] at hb
            have eb : rx = b := KernelObject.reply.inj (Option.some.inj hb)
            rw [← eb, (hHeadAt x rx hHd).2] at hbN
            cases hbN
          refine ⟨y, { b with next := some (.head s) }, by rw [← hRO, ← eT]; exact hROy,
            hBelow x rx y b hHd hP hb hyx, ?_⟩
          show some (ReplyStackLink.head s) = some (.head sc')
          rw [e1]
  · -- Any other loan: its holder and binding are the pre-state's.
    obtain ⟨ht, hHpre, hBeq⟩ := hOther eH eC
    rw [← hBeq] at hB'
    obtain ⟨rid, r, hROr, hR, hN⟩ := hW holder ht sc' o ot hHpre hB' hOpre
    refine ⟨rid, r, by rw [← hRO]; exact hROr, keepHead rid r sc' hR hN (fun x rx e hx => ?_), hN⟩
    -- The popped head heads `s`, which is bound to `h`, not to this holder.
    obtain ⟨hxR, hxN⟩ := hHeadAt x rx e
    rw [hx, hxR] at hR
    have er : rx = r := KernelObject.reply.inj (Option.some.inj hR)
    rw [← er, hxN] at hN
    have e3 : s = sc' := ReplyStackLink.head.inj (Option.some.inj hN)
    obtain ⟨⟨sc0, hSc0, hBd⟩, -⟩ := hOwn holder ht sc' o hHpre hB'
    rw [← e3, hSc] at hSc0
    have es : sc = sc0 := KernelObject.schedContext.inj (Option.some.inj hSc0)
    rw [← es, hBound sc hSc] at hBd
    have eh : h = holder := Option.some.inj hBd
    exact eH (by rw [eh])

/-- **A finalised reply's donation return keeps the fact, and leaves no loan
from the caller**: a reply heading no stack returns nothing, and its caller
lends to no one (`replyCaller_lendsNone`); a head reply's pop commits
(`replyHeadPop_commits`), keeps the fact
(`returnDonatedSchedContext_keepsLentContextHeads`), and leaves the caller
lending nothing: the thread it took the context from holds none, the caller
holds it from the outer caller, never from itself, and any other loan from the
caller would be a second one (`donationOwnerUnique`). -/
theorem finaliseReplyReturn_keepsLentContextHeads {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt) (hFull : ipcInvariantFull s)
    (hW : lentContextHeadsLenderFrame s) (hX : s.getObject? x = some (.reply r))
    (hT : s.getTcb? c = some t) (hF : replyCallerFinalisable s x r c t = true) :
    lentContextHeadsLenderFrame (Lifecycle.Suspend.returnDonationToCancelledCaller s c t) ∧
      ∀ (holder : SeLe4n.ThreadId) (ht : TCB) (sd : SeLe4n.SchedContextId),
        (Lifecycle.Suspend.returnDonationToCancelledCaller s c t).objects[holder.toObjId]? =
          some (.tcb ht) → ht.schedContextBinding ≠ .donated sd c := by
  obtain ⟨-, -, -, -, -, hRO, -, -, -⟩ := replyCallerFinalisable_parts hF
  rcases replyCallerFinalisable_cases hX hF with ⟨hHd, hD⟩ |
    ⟨sd, sc, hd, htd, -, hSc, -, hBt, hTd, hBd, hC, hD⟩
  · have hNone : Lifecycle.Suspend.returnDonationToCancelledCaller s c t = s := by
      unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
    rw [hNone]
    exact ⟨hW, replyCaller_lendsNone hW hX hT hHd hRO⟩
  · obtain ⟨n, st', hResN, hPop, hEq⟩ := replyHeadPop_commits hInv hT hD hC
    rw [hEq]
    have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
    refine ⟨returnDonatedSchedContext_keepsLentContextHeads hInv hW hFull.donationOwnerValid
      hFull.replyCallerLinkage.1 hResN hPop (fun sc' h' => by
        rw [hScO] at h'
        rw [← KernelObject.schedContext.inj (Option.some.inj h')]; exact hBt), ?_⟩
    intro holder ht sd' hH hBind
    obtain ⟨hSrv, hOwnB, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
      s st' hd sd c hInv n hPop holder.toObjId ht hH
    by_cases eH : holder.toObjId = hd.toObjId
    · rw [hSrv eH] at hBind; cases hBind
    by_cases eC : holder.toObjId = c.toObjId
    · rw [hOwnB eH eC] at hBind
      cases hn : n with
      | none => rw [hn] at hBind; cases hBind
      | some outer =>
        rw [hn] at hBind
        simp only [donationReturnBinding, SchedContextBinding.donated.injEq] at hBind
        have hAcc := returnDonatedSchedContext_ok_outerAcceptable s st' hd sd c n hPop
        rw [hn] at hAcc
        exact (outerCallerAcceptable_some_char _ hd c outer hAcc).1 hBind.2
    · obtain ⟨ht0, hH0, hEq0⟩ := hOther eH eC
      rw [← hEq0] at hBind
      exact eH (by
        rw [hFull.donationOwnerUnique holder hd ht0 htd sd' sd c hH0
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTd) hBind hBd])

/-- **A finalised reply heads no stack once its donation is returned**: a reply
heading no stack is left as it was, and a head reply's pop (seL4 MCS's
`reply_pop`) unlinks it from the stack — the frame below it, which the pop
makes the head, is a different reply, since it links to the head by a frame
link (`replyStackOuterCaller?`), and the head's link is a head link. -/
theorem finaliseReplyReturn_replyUnheaded {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt)
    (hX : s.getObject? x = some (.reply r)) (hT : s.getTcb? c = some t)
    (hF : replyCallerFinalisable s x r c t = true) :
    ∃ rR, (Lifecycle.Suspend.returnDonationToCancelledCaller s c t).objects[x]? =
      some (.reply rR) ∧ ∀ sc, rR.next ≠ some (.head sc) := by
  have hXo : s.objects[x]? = some (.reply r) := by rw [← SystemState.getObject?_eq_getElem]; exact hX
  rcases replyCallerFinalisable_cases hX hF with ⟨hHd, hD⟩ |
    ⟨sd, sc, hd, htd, hRN, hSc, hScR, -, -, -, hC, hD⟩
  · have hNone : Lifecycle.Suspend.returnDonationToCancelledCaller s c t = s := by
      unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
    rw [hNone]
    exact ⟨r, hXo, fun sc e => by rw [e] at hHd; simp [replyStackLinkIsHead] at hHd⟩
  · obtain ⟨n, st', hResN, hPop, hEq⟩ := replyHeadPop_commits hInv hT hD hC
    rw [hEq]
    obtain ⟨sc0, head?, hSc0, hHead, -, -, hTop⟩ := returnDonatedSchedContext_reply_cases hInv hPop
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc] at hSc0
    cases hSc0
    have hGetR : s.getReply? ⟨x.val⟩ = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hXo
    have hHd' : head? = some (⟨x.val⟩, r) := by
      unfold donationHeadOf? at hHead
      rw [hScR] at hHead
      simp only [hGetR, hRN, bne_self_eq_false, Bool.false_eq_true, if_false,
        Except.ok.injEq] at hHead
      exact hHead.symm
    refine ⟨{ r with prev := none, next := none }, hTop _ r hHd' hXo (fun y hP e => ?_),
      fun _ e => by cases e⟩
    -- The frame below links to the head by a frame link; the head's own is a head link.
    unfold replyStackOuterCaller? at hResN
    rw [hSc] at hResN
    simp only at hResN
    rw [hHead, hHd'] at hResN
    simp only [hP] at hResN
    rw [SeLe4n.ReplyId.toObjId_injective _ _ e, hGetR] at hResN
    simp only [hRN] at hResN
    cases hResN

/-- **A reply's caller cancel, with its reservation handed back and its boost
reverted, keeps the fact**: the donation return keeps it and leaves no loan
from the caller (`finaliseReplyReturn_keepsLentContextHeads`); the splice, the
restore, the unlink, the replenishment migration, the holder's deschedule and
the walk keep every thread's reply link and loan and every stack head; the
consume lets go of the caller's link. -/
theorem finaliseReplyStep_keepsLentContextHeads {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt) (hFull : ipcInvariantFull s)
    (hW : lentContextHeadsLenderFrame s) (hX : s.getObject? x = some (.reply r))
    (hT : s.getTcb? c = some t)
    (hF : replyCallerFinalisable s x r c t = true) :
    lentContextHeadsLenderFrame
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -, -, -, -⟩ := replyCallerFinalisable_parts hF
  obtain ⟨hW0, hNo⟩ := finaliseReplyReturn_keepsLentContextHeads hInv hFull hW hX hT hF
  have i0 := (FinaliseFrameAny.returnDonationToCancelledCaller s c t hInv).invExt
  have hCancel : loanWriteOff c (Lifecycle.Suspend.returnDonationToCancelledCaller s c t)
      (Lifecycle.Suspend.cancelIpcBlocking s c t) := by
    rw [cancelIpcBlocking_replyArm_unfold s c t hB]
    have f1 := loanWrite.of_spliceThreadReplyFrameOut _ t i0
    have i1 := (FinaliseFrameAny.spliceThreadReplyFrameOut _ t i0).invExt
    generalize spliceThreadReplyFrameOut (Lifecycle.Suspend.returnDonationToCancelledCaller s c t)
      t = s1 at f1 i1
    have F2 : FinaliseFrame s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 c) := by
      unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
      exact FinaliseFrame.updateTcb _ c _ i1
    generalize Lifecycle.Suspend.restoreToReadyCancelled s1 c = s2 at F2
    have f3 := loanWriteOff.of_consumeReplyLink s2 c t F2.invExt
    generalize Lifecycle.Suspend.consumeReplyLink s2 c t = s3 at f3
    have f4 := loanWrite.of_agreeOffRunLinks
      (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks s3 c t.blockingServer?)
    exact (((f1.off c).trans (F2.loan.off c)).trans f3).trans (f4.off c)
  have iC := (FinaliseFrameAny.replyCancel s c t hInv hB).invExt
  have f5 := loanWrite.of_agreeOffRunLinks (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks c t s)
  have F6 := FinaliseFrame.finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?
    (cancelIpcBlockingReclaimed_objects_invExt c t s iC)
  exact hW0.of_loanWriteOff hNo ((hCancel.trans (f5.off c)).trans (F6.loan.off c))

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

