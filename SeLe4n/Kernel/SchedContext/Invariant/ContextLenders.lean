-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.NotificationDonationContextLabel
import SeLe4n.Kernel.IPC.Invariant.Defs

/-!
# The lenders on a context's stack: the transport relations

`contextLendersFlow` reads three things of a state and nothing else: each
context's stack head (`SchedContext.scReply`), each reply object's link down the
stack (`Reply.prev`) and each reply object's caller (`Reply.caller`).  This
module states them as three views (`contextStackHead`, `replyStackPrev`,
`replyStackCaller`), restates the stack in those views
(`OnContextStack_iff_views`), and gives the two relations every kernel step's
preservation goes through (WS-SX SX8, the lender invariant of D27):

* **the frame** (`contextStackViewsAgree`): a step that writes none of the
  three views carries the predicate (`contextLendersFlow_of_viewsAgree`);
* **the shrink** (`contextStacksShrink`): a step after which every lender on a
  context's stack was already a lender on that context's stack carries it
  (`contextLendersFlow_of_shrink`).  Removing a frame, splicing a frame out and
  clearing a head are shrinks; a frame relinked onto another context's stack is
  not, which is the case the relation is there to refuse.

A push of a new frame under a context is neither: its lender is new, and the
push carries the predicate only where the lend admission passed
(`callLendAdmits`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A context's stack head. -/
def contextStackHead (st : SystemState) (s : SeLe4n.SchedContextId) : Option SeLe4n.ReplyId :=
  (st.getSchedContext? s).bind (·.scReply)

/-- A reply object's link down its stack. -/
def replyStackPrev (st : SystemState) (r : SeLe4n.ReplyId) : Option SeLe4n.ReplyId :=
  (st.getReply? r).bind (·.prev)

/-- A reply object's caller. -/
def replyStackCaller (st : SystemState) (r : SeLe4n.ReplyId) : Option SeLe4n.ThreadId :=
  (st.getReply? r).bind (·.caller)

/-- **The stack in the views**: the head, or one `prev` link below a frame on
it. -/
inductive OnContextStackView (st : SystemState) (s : SeLe4n.SchedContextId) :
    SeLe4n.ReplyId → Prop where
  | head {r : SeLe4n.ReplyId} : contextStackHead st s = some r → OnContextStackView st s r
  | lower {r r' : SeLe4n.ReplyId} :
      OnContextStackView st s r → replyStackPrev st r = some r' → OnContextStackView st s r'

theorem OnContextStack_iff_views {st : SystemState} {s : SeLe4n.SchedContextId}
    {r : SeLe4n.ReplyId} : OnContextStack st s r ↔ OnContextStackView st s r := by
  constructor
  · intro h
    induction h with
    | head hSc hR => exact .head (by simp only [contextStackHead, hSc, Option.bind_some, hR])
    | lower _ hRep hP ih =>
      exact .lower ih (by simp only [replyStackPrev, hRep, Option.bind_some, hP])
  · intro h
    induction h with
    | head hH =>
      unfold contextStackHead at hH
      cases hSc : st.getSchedContext? s with
      | none => rw [hSc] at hH; cases hH
      | some sc => rw [hSc, Option.bind_some] at hH; exact .head hSc hH
    | @lower r0 _ _ hP ih =>
      unfold replyStackPrev at hP
      cases hRep : st.getReply? r0 with
      | none => rw [hRep] at hP; cases hP
      | some rep => rw [hRep, Option.bind_some] at hP; exact .lower ih hRep hP

/-- **`contextLendersFlow` in the views.** -/
theorem contextLendersFlow_iff_views {ctx : LabelingContext} {st : SystemState} :
    contextLendersFlow ctx st ↔
      ∀ (s : SeLe4n.SchedContextId) (r : SeLe4n.ReplyId) (lender : SeLe4n.ThreadId),
        OnContextStackView st s r → replyStackCaller st r = some lender →
          securityFlowsTo (ctx.threadLabelOf lender) (ctx.objectLabelOf s.toObjId) = true := by
  constructor
  · intro h s r lender hOn hC
    unfold replyStackCaller at hC
    cases hRep : st.getReply? r with
    | none => rw [hRep] at hC; cases hC
    | some rep =>
      rw [hRep, Option.bind_some] at hC
      exact h s r rep lender (OnContextStack_iff_views.mpr hOn) hRep hC
  · intro h s r rep lender hOn hRep hC
    exact h s r lender (OnContextStack_iff_views.mp hOn)
      (by simp only [replyStackCaller, hRep, Option.bind_some, hC])

/-- **The shrink**: every lender on a context's stack after the step was a
lender on that same context's stack before it. -/
def contextStacksShrink (st st' : SystemState) : Prop :=
  ∀ (s : SeLe4n.SchedContextId) (r : SeLe4n.ReplyId) (lender : SeLe4n.ThreadId),
    OnContextStackView st' s r → replyStackCaller st' r = some lender →
      ∃ r0, OnContextStackView st s r0 ∧ replyStackCaller st r0 = some lender

theorem contextStacksShrink.refl (st : SystemState) : contextStacksShrink st st :=
  fun _ r _ hOn hC => ⟨r, hOn, hC⟩

theorem contextStacksShrink.trans {st st' st'' : SystemState}
    (h1 : contextStacksShrink st st') (h2 : contextStacksShrink st' st'') :
    contextStacksShrink st st'' := by
  intro s r lender hOn hC
  obtain ⟨r1, hOn1, hC1⟩ := h2 s r lender hOn hC
  exact h1 s r1 lender hOn1 hC1

/-- **A shrink carries the lenders' flow.** -/
theorem contextLendersFlow_of_shrink {ctx : LabelingContext} {st st' : SystemState}
    (hInv : contextLendersFlow ctx st) (h : contextStacksShrink st st') :
    contextLendersFlow ctx st' := by
  rw [contextLendersFlow_iff_views] at hInv ⊢
  intro s r lender hOn hC
  obtain ⟨r0, hOn0, hC0⟩ := h s r lender hOn hC
  exact hInv s r0 lender hOn0 hC0

/-- **The frame**: a step writing no context's stack head, no reply object's
`prev` link and no reply object's caller. -/
structure contextStackViewsAgree (st st' : SystemState) : Prop where
  head : ∀ s, contextStackHead st' s = contextStackHead st s
  prev : ∀ r, replyStackPrev st' r = replyStackPrev st r
  caller : ∀ r, replyStackCaller st' r = replyStackCaller st r

theorem contextStackViewsAgree.refl (st : SystemState) : contextStackViewsAgree st st :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem contextStackViewsAgree.trans {st st' st'' : SystemState}
    (h1 : contextStackViewsAgree st st') (h2 : contextStackViewsAgree st' st'') :
    contextStackViewsAgree st st'' :=
  ⟨fun s => (h2.head s).trans (h1.head s), fun r => (h2.prev r).trans (h1.prev r),
    fun r => (h2.caller r).trans (h1.caller r)⟩

theorem OnContextStackView.of_viewsAgree {st st' : SystemState} {s : SeLe4n.SchedContextId}
    {r : SeLe4n.ReplyId} (h : contextStackViewsAgree st st') (hOn : OnContextStackView st' s r) :
    OnContextStackView st s r := by
  induction hOn with
  | head hH => exact .head ((h.head s).symm.trans hH)
  | lower _ hP ih => exact .lower ih ((h.prev _).symm.trans hP)

/-- **The frame is a shrink.** -/
theorem contextStacksShrink_of_viewsAgree {st st' : SystemState}
    (h : contextStackViewsAgree st st') : contextStacksShrink st st' :=
  fun _ r _ hOn hC => ⟨r, hOn.of_viewsAgree h, (h.caller r).symm.trans hC⟩

theorem contextLendersFlow_of_viewsAgree {ctx : LabelingContext} {st st' : SystemState}
    (hInv : contextLendersFlow ctx st) (h : contextStackViewsAgree st st') :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_shrink hInv (contextStacksShrink_of_viewsAgree h)

/-- **The frame read on the objects**: a step after which every context and
every reply object reads as it did, as far as the three views go, is a frame;
in particular one that writes no context and no reply object. -/
theorem contextStackViewsAgree_of_objects {st st' : SystemState}
    (hSc : ∀ s, (st'.getSchedContext? s).map (·.scReply) = (st.getSchedContext? s).map (·.scReply))
    (hRp : ∀ r, (st'.getReply? r).map (fun rep => (rep.prev, rep.caller)) =
      (st.getReply? r).map (fun rep => (rep.prev, rep.caller))) :
    contextStackViewsAgree st st' := by
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_⟩
  · have := hSc s
    unfold contextStackHead
    cases h1 : st'.getSchedContext? s <;> cases h2 : st.getSchedContext? s <;>
      simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
        Option.bind_some, Option.bind_none] at this ⊢
    exact this
  · have := hRp r
    unfold replyStackPrev
    cases h1 : st'.getReply? r <;> cases h2 : st.getReply? r <;>
      simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
        Option.bind_some, Option.bind_none, Prod.mk.injEq] at this ⊢
    exact this.1
  · have := hRp r
    unfold replyStackCaller
    cases h1 : st'.getReply? r <;> cases h2 : st.getReply? r <;>
      simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
        Option.bind_some, Option.bind_none, Prod.mk.injEq] at this ⊢
    exact this.2


/-! ### The chain frame, read for the lenders -/

theorem contextStackHead_eq_stackHead (st : SystemState) (s : SeLe4n.SchedContextId) :
    contextStackHead st s = (schedContextStackHead? st.objects[s.toObjId]?).bind id := by
  unfold contextStackHead SystemState.getSchedContext? schedContextStackHead?
  split <;> simp_all

theorem replyStackPrev_eq_links (st : SystemState) (r : SeLe4n.ReplyId) :
    replyStackPrev st r = (replyStackLinks? st.objects[r.toObjId]?).bind (·.1) := by
  unfold replyStackPrev SystemState.getReply? replyStackLinks?
  split <;> simp_all

/-- **A chain frame that keeps every caller is a lenders frame.** -/
theorem contextStackViewsAgree_of_chainFrame {st st' : SystemState}
    (h : donationChainFrame st st') (hC : ∀ r, replyStackCaller st' r = replyStackCaller st r) :
    contextStackViewsAgree st st' :=
  ⟨fun s => by rw [contextStackHead_eq_stackHead, contextStackHead_eq_stackHead,
      h.stackHeads s.toObjId],
   fun r => by rw [replyStackPrev_eq_links, replyStackPrev_eq_links, h.replyLinks r.toObjId],
   hC⟩

end SeLe4n.Kernel
