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
import SeLe4n.Kernel.SchedContext.Invariant.BindingLabels

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


/-! ### The links shrink: the step every removal is

A removal writes the three views in one direction only: a context's head moves
to a frame already on its stack or is cleared, a `prev` link is cleared or kept,
and a caller is cleared or kept.  `contextStackLinksShrink` is that relation; it
composes, and it is a shrink (`contextStacksShrink_of_linksShrink`).  It is read
slot by slot off the object store (`contextStackLinksShrink_of_slot`), so a
removal composed of stores carries it store by store. -/

/-- A slot's stack head: the head of the context the slot holds. -/
def objStackHead : Option KernelObject → Option SeLe4n.ReplyId
  | some (.schedContext sc) => sc.scReply
  | _ => none

/-- A slot's link down a stack: the `prev` of the reply object the slot holds. -/
def objStackPrev : Option KernelObject → Option SeLe4n.ReplyId
  | some (.reply r) => r.prev
  | _ => none

/-- A slot's caller: the caller of the reply object the slot holds. -/
def objStackCaller : Option KernelObject → Option SeLe4n.ThreadId
  | some (.reply r) => r.caller
  | _ => none

theorem contextStackHead_eq_obj (st : SystemState) (s : SeLe4n.SchedContextId) :
    contextStackHead st s = objStackHead st.objects[s.toObjId]? := by
  unfold contextStackHead SystemState.getSchedContext?
  cases st.objects[s.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem replyStackPrev_eq_obj (st : SystemState) (r : SeLe4n.ReplyId) :
    replyStackPrev st r = objStackPrev st.objects[r.toObjId]? := by
  unfold replyStackPrev SystemState.getReply?
  cases st.objects[r.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem replyStackCaller_eq_obj (st : SystemState) (r : SeLe4n.ReplyId) :
    replyStackCaller st r = objStackCaller st.objects[r.toObjId]? := by
  unfold replyStackCaller SystemState.getReply?
  cases st.objects[r.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- **The links shrink**: every head after the step is a frame that was on the
same context's stack, and every `prev` link and every caller after it was there
before it. -/
structure contextStackLinksShrink (st st' : SystemState) : Prop where
  head : ∀ s r, contextStackHead st' s = some r → OnContextStackView st s r
  prev : ∀ r x, replyStackPrev st' r = some x → replyStackPrev st r = some x
  caller : ∀ r l, replyStackCaller st' r = some l → replyStackCaller st r = some l

theorem OnContextStackView.of_linksShrink {st st' : SystemState} {s : SeLe4n.SchedContextId}
    {r : SeLe4n.ReplyId} (h : contextStackLinksShrink st st') (hOn : OnContextStackView st' s r) :
    OnContextStackView st s r := by
  induction hOn with
  | head hH => exact h.head _ _ hH
  | lower _ hP ih => exact .lower ih (h.prev _ _ hP)

theorem contextStackLinksShrink.refl (st : SystemState) : contextStackLinksShrink st st :=
  ⟨fun _ _ hH => .head hH, fun _ _ h => h, fun _ _ h => h⟩

theorem contextStackLinksShrink.trans {st st' st'' : SystemState}
    (h1 : contextStackLinksShrink st st') (h2 : contextStackLinksShrink st' st'') :
    contextStackLinksShrink st st'' :=
  ⟨fun s r hH => (h2.head s r hH).of_linksShrink h1,
   fun r x hP => h1.prev r x (h2.prev r x hP),
   fun r l hC => h1.caller r l (h2.caller r l hC)⟩

theorem contextStackLinksShrink.of_eq {st st' : SystemState} (h : st' = st) :
    contextStackLinksShrink st st' := h ▸ refl st

/-- **The links shrink is a shrink.** -/
theorem contextStacksShrink_of_linksShrink {st st' : SystemState}
    (h : contextStackLinksShrink st st') : contextStacksShrink st st' :=
  fun _ r l hOn hC => ⟨r, hOn.of_linksShrink h, h.caller r l hC⟩

theorem contextLendersFlow_of_linksShrink {ctx : LabelingContext} {st st' : SystemState}
    (hInv : contextLendersFlow ctx st) (h : contextStackLinksShrink st st') :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_shrink hInv (contextStacksShrink_of_linksShrink h)

/-- **The frame is a links shrink.** -/
theorem contextStackLinksShrink_of_viewsAgree {st st' : SystemState}
    (h : contextStackViewsAgree st st') : contextStackLinksShrink st st' :=
  ⟨fun s _ hH => .head ((h.head s).symm.trans hH), fun r _ hP => (h.prev r).symm.trans hP,
   fun r _ hC => (h.caller r).symm.trans hC⟩

/-- The links shrink, read slot by slot. -/
theorem contextStackLinksShrink_of_objects {st st' : SystemState}
    (hHead : ∀ (s : SeLe4n.SchedContextId) r,
      objStackHead st'.objects[s.toObjId]? = some r → OnContextStackView st s r)
    (hPrev : ∀ (r : SeLe4n.ReplyId) x,
      objStackPrev st'.objects[r.toObjId]? = some x → objStackPrev st.objects[r.toObjId]? = some x)
    (hCaller : ∀ (r : SeLe4n.ReplyId) l,
      objStackCaller st'.objects[r.toObjId]? = some l →
        objStackCaller st.objects[r.toObjId]? = some l) :
    contextStackLinksShrink st st' :=
  ⟨fun s r h => hHead s r (by rw [← contextStackHead_eq_obj]; exact h),
   fun r x h => by rw [replyStackPrev_eq_obj] at h ⊢; exact hPrev r x h,
   fun r l h => by rw [replyStackCaller_eq_obj] at h ⊢; exact hCaller r l h⟩

/-- **One slot written**: the links shrink when the object written heads only a
frame already on the stack of the context at that slot, links down only where
the slot did, and names only the caller the slot did. -/
theorem contextStackLinksShrink_of_slot {st st' : SystemState} (k : SeLe4n.ObjId)
    (hNe : ∀ x, x ≠ k → st'.objects[x]? = st.objects[x]?)
    (hHead : ∀ (s : SeLe4n.SchedContextId) r, s.toObjId = k →
      objStackHead st'.objects[k]? = some r → OnContextStackView st s r)
    (hPrev : ∀ x, objStackPrev st'.objects[k]? = some x → objStackPrev st.objects[k]? = some x)
    (hCaller : ∀ l, objStackCaller st'.objects[k]? = some l →
      objStackCaller st.objects[k]? = some l) :
    contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_of_objects (fun s r h => ?_) (fun r x h => ?_) (fun r l h => ?_)
  · by_cases hk : s.toObjId = k
    · exact hHead s r hk (hk ▸ h)
    · rw [hNe _ hk] at h; exact .head (by rw [contextStackHead_eq_obj]; exact h)
  · by_cases hk : r.toObjId = k
    · subst hk; exact hPrev x h
    · rw [hNe _ hk] at h; exact h
  · by_cases hk : r.toObjId = k
    · subst hk; exact hCaller l h
    · rw [hNe _ hk] at h; exact h

/-- **One store**: `contextStackLinksShrink_of_slot` at a `storeObject`. -/
theorem contextStackLinksShrink_storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hHead : ∀ (s : SeLe4n.SchedContextId) r, s.toObjId = k →
      objStackHead (some o) = some r → OnContextStackView st s r)
    (hPrev : ∀ x, objStackPrev (some o) = some x → objStackPrev st.objects[k]? = some x)
    (hCaller : ∀ l, objStackCaller (some o) = some l → objStackCaller st.objects[k]? = some l) :
    contextStackLinksShrink st st' := by
  have hEq := storeObject_objects_eq st st' k o hInv h
  exact contextStackLinksShrink_of_slot k
    (fun x hx => storeObject_objects_ne st st' k x o hx hInv h)
    (fun s r hk hr => hHead s r hk (hEq ▸ hr)) (fun x hx => hPrev x (hEq ▸ hx))
    (fun l hl => hCaller l (hEq ▸ hl))

/-- **A store of an object that is neither a context nor a reply object** can
only take a stack view away. -/
theorem contextStackLinksShrink_storeObject_other {st st' : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hSc : ∀ sc, o ≠ .schedContext sc) (hRp : ∀ r, o ≠ .reply r) :
    contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_storeObject hInv h (fun _ _ _ hr => ?_) (fun _ hx => ?_)
    (fun _ hl => ?_) <;> cases o <;> simp_all [objStackHead, objStackPrev, objStackCaller]

/-- **A reply object rewritten with its `prev` cleared or kept and its caller
cleared or kept** — the write every removal makes of a frame. -/
theorem contextStackLinksShrink_storeReply {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {r r' : Reply} (hInv : st.objects.invExt) (hR : st.getReply? rid = some r)
    (h : storeObject rid.toObjId (.reply r') st = .ok ((), st'))
    (hP : r'.prev = none ∨ r'.prev = r.prev) (hC : r'.caller = none ∨ r'.caller = r.caller) :
    contextStackLinksShrink st st' := by
  have hO := (SystemState.getReply?_eq_some_iff st rid r).mp hR
  refine contextStackLinksShrink_storeObject hInv h (fun _ _ _ hr => ?_) (fun x hx => ?_)
    (fun l hl => ?_)
  · simp [objStackHead] at hr
  · simp only [objStackPrev, hO] at hx ⊢; rcases hP with hP | hP <;> rw [hP] at hx
    · cases hx
    · exact hx
  · simp only [objStackCaller, hO] at hl ⊢; rcases hC with hC | hC <;> rw [hC] at hl
    · cases hl
    · exact hl

/-- **A context rewritten with its head cleared, kept, or moved to a frame on
its stack.** -/
theorem contextStackLinksShrink_storeSchedContext {st st' : SystemState}
    {s : SeLe4n.SchedContextId} {sc' : SchedContext} (hInv : st.objects.invExt)
    (h : storeObject s.toObjId (.schedContext sc') st = .ok ((), st'))
    (hH : ∀ r, sc'.scReply = some r → OnContextStackView st s r) :
    contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_storeObject hInv h (fun s0 r hk hr => ?_) (fun x hx => ?_)
    (fun l hl => ?_)
  · rw [SeLe4n.SchedContextId.toObjId_injective _ _ hk]; exact hH r hr
  · simp [objStackPrev] at hx
  · simp [objStackCaller] at hl

/-! ### The push and the free reply object -/

/-- **A frame on a context's stack links up**: under the chain invariant it
resolves to a reply object whose upward link is set (a head's to the context, a
lower frame's to the frame above). -/
theorem OnContextStackView.next_ne_none {st : SystemState} {s : SeLe4n.SchedContextId}
    {r : SeLe4n.ReplyId} (hChain : donationChainWellFormed st) (hOn : OnContextStackView st s r) :
    ∃ rep, st.getReply? r = some rep ∧ rep.next ≠ none := by
  cases hOn with
  | head hH =>
    rw [contextStackHead_eq_obj] at hH
    cases hS : st.objects[s.toObjId]? with
    | none => rw [hS] at hH; cases hH
    | some o =>
      cases o <;> rw [hS] at hH <;> simp only [objStackHead, reduceCtorEq] at hH
      obtain ⟨rep, hRep, hN⟩ := hChain.headLinkReciprocal s _ hS r hH
      exact ⟨rep, (SystemState.getReply?_eq_some_iff _ _ _).mpr hRep, by rw [hN]; simp⟩
  | @lower r0 _ _ hP =>
    rw [replyStackPrev_eq_obj] at hP
    cases hS : st.objects[r0.toObjId]? with
    | none => rw [hS] at hP; cases hP
    | some o =>
      cases o <;> rw [hS] at hP <;> simp only [objStackPrev, reduceCtorEq] at hP
      obtain ⟨b, hB, hN⟩ := hChain.prevLinkReciprocal r0 _ _ hS hP
      exact ⟨b, (SystemState.getReply?_eq_some_iff _ _ _).mpr hB, by rw [hN]; simp⟩

/-- **A reply object with no upward link is on no context's stack** — in
particular a free one (`Reply.isFree`), which is the only kind a caller is
linked to (`linkReply`). -/
theorem not_onContextStack_of_next_none {st : SystemState} {r : SeLe4n.ReplyId} {rep : Reply}
    (hChain : donationChainWellFormed st) (hR : st.getReply? r = some rep) (hN : rep.next = none)
    (s : SeLe4n.SchedContextId) : ¬ OnContextStackView st s r := by
  intro hOn
  obtain ⟨rep', hR', hN'⟩ := hOn.next_ne_none hChain
  rw [hR] at hR'; cases hR'; exact hN' hN

/-- **The push**: a frame on no stack becomes a context's head above the
context's old head, every other head, link and caller kept.  The new lender is
the pushed frame's caller, and the predicate holds after the push exactly where
that caller flows to the context's label. -/
theorem contextLendersFlow_of_push {ctx : LabelingContext} {st st' : SystemState}
    {s0 : SeLe4n.SchedContextId} {p : SeLe4n.ReplyId}
    (hInv : contextLendersFlow ctx st)
    (hFresh : ∀ s, ¬ OnContextStackView st s p)
    (hHead0 : ∀ r, contextStackHead st' s0 = some r → r = p)
    (hHead : ∀ s r, s ≠ s0 → contextStackHead st' s = some r → contextStackHead st s = some r)
    (hPrevP : ∀ x, replyStackPrev st' p = some x → contextStackHead st s0 = some x)
    (hPrev : ∀ r x, r ≠ p → replyStackPrev st' r = some x → replyStackPrev st r = some x)
    (hCaller : ∀ r l, replyStackCaller st' r = some l → replyStackCaller st r = some l)
    (hFlow : ∀ l, replyStackCaller st p = some l →
      securityFlowsTo (ctx.threadLabelOf l) (ctx.objectLabelOf s0.toObjId) = true) :
    contextLendersFlow ctx st' := by
  have key : ∀ s r, OnContextStackView st' s r → (s = s0 ∧ r = p) ∨ OnContextStackView st s r := by
    intro s r hOn
    induction hOn with
    | @head r hH =>
      by_cases hs : s = s0
      · subst hs; exact .inl ⟨rfl, hHead0 r hH⟩
      · exact .inr (.head (hHead s r hs hH))
    | @lower r r' _ hP ih =>
      rcases ih with ⟨rfl, rfl⟩ | hOn
      · exact .inr (.head (hPrevP r' hP))
      · have hne : r ≠ p := fun e => hFresh s (e ▸ hOn)
        exact .inr (.lower hOn (hPrev r r' hne hP))
  rw [contextLendersFlow_iff_views] at hInv ⊢
  intro s r l hOn hC
  have hC := hCaller r l hC
  rcases key s r hOn with ⟨rfl, rfl⟩ | hOn0
  · exact hFlow l hC
  · exact hInv s r l hOn0 hC

/-! ### The one-slot grow toolkit

A store of one thread, notification or context record, read as a step that
only takes stack views away (`contextStacksShrink`) and grows the binding views
only where the new words pair equal labels (`bindingViewsGrow`); the two carry
the lenders' flow and the equal binding labels together
(`contextLendersFlow_bindingLabelsEqual_of_grow`).  The stack half is the
links-shrink store lemmas above, read through `contextStacksShrink_of_linksShrink`. -/

/-- **The one-slot step carries both invariants**: a stack shrink carries the
lenders' flow, a binding grow the equal binding labels. -/
theorem contextLendersFlow_bindingLabelsEqual_of_grow {ctx : LabelingContext}
    {st st' : SystemState} (hL : contextLendersFlow ctx st) (hB : bindingLabelsEqual ctx st)
    (hS : contextStacksShrink st st') (hG : bindingViewsGrow ctx st st') :
    contextLendersFlow ctx st' ∧ bindingLabelsEqual ctx st' :=
  ⟨contextLendersFlow_of_shrink hL hS, bindingLabelsEqual_of_grow hB hG⟩

/-- Every slot but the stored one keeps its binding words. -/
theorem objBindingWords_storeObject_ne {st st' : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st')) :
    ∀ x, x ≠ k → objBindingWords st'.objects[x]? = objBindingWords st.objects[x]? :=
  fun x hx => congrArg objBindingWords (storeObject_objects_ne st st' k x o hx hInv h)

/-- **A thread record stored**: no stack view gained, the binding views grown
where its words pair equal labels. -/
theorem contextStacksShrink_bindingViewsGrow_storeTcb {ctx : LabelingContext}
    {st st' : SystemState} {t0 : SeLe4n.ThreadId} {tcb' : TCB} (hInv : st.objects.invExt)
    (h : storeObject t0.toObjId (.tcb tcb') st = .ok ((), st'))
    (hT : ∀ s : SeLe4n.SchedContextId, tcb'.scBindingScCode = s.val + 1 →
      ctx.threadLabelOf t0 = ctx.objectLabelOf s.toObjId)
    (hO : ∀ (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId), tcb'.scBindingScCode = s.val + 1 →
      tcb'.scBindingOwnerCode = o.val + 1 → ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId) :
    contextStacksShrink st st' ∧ bindingViewsGrow ctx st st' :=
  ⟨contextStacksShrink_of_linksShrink (contextStackLinksShrink_storeObject_other hInv h
      (fun _ e => by cases e) (fun _ e => by cases e)),
   bindingViewsGrow_of_tcbSlot (objBindingWords_storeObject_ne hInv h)
      (storeObject_objects_eq st st' _ _ hInv h) hT hO⟩

/-- **A notification stored**: no stack view gained, the binding views grown
where its context word pairs equal labels. -/
theorem contextStacksShrink_bindingViewsGrow_storeNotification {ctx : LabelingContext}
    {st st' : SystemState} {n0 : SeLe4n.ObjId} {ntfn' : Notification} (hInv : st.objects.invExt)
    (h : storeObject n0 (.notification ntfn') st = .ok ((), st'))
    (hN : ∀ s : SeLe4n.SchedContextId, ntfn'.schedContextCode = s.val + 1 →
      ctx.objectLabelOf n0 = ctx.objectLabelOf s.toObjId) :
    contextStacksShrink st st' ∧ bindingViewsGrow ctx st st' :=
  ⟨contextStacksShrink_of_linksShrink (contextStackLinksShrink_storeObject_other hInv h
      (fun _ e => by cases e) (fun _ e => by cases e)),
   bindingViewsGrow_of_notificationSlot (objBindingWords_storeObject_ne hInv h)
      (storeObject_objects_eq st st' _ _ hInv h) hN⟩

/-- **A context record stored** with its head cleared, kept or moved down its
own stack: no stack view gained, the binding views grown where its thread word
pairs equal labels. -/
theorem contextStacksShrink_bindingViewsGrow_storeSchedContext {ctx : LabelingContext}
    {st st' : SystemState} {s0 : SeLe4n.SchedContextId} {sc' : SchedContext}
    (hInv : st.objects.invExt) (h : storeObject s0.toObjId (.schedContext sc') st = .ok ((), st'))
    (hH : ∀ r, sc'.scReply = some r → OnContextStackView st s0 r)
    (hC : ∀ t : SeLe4n.ThreadId, sc'.boundThreadCode = t.val + 1 →
      ctx.threadLabelOf t = ctx.objectLabelOf s0.toObjId) :
    contextStacksShrink st st' ∧ bindingViewsGrow ctx st st' :=
  ⟨contextStacksShrink_of_linksShrink (contextStackLinksShrink_storeSchedContext hInv h hH),
   bindingViewsGrow_of_schedContextSlot (objBindingWords_storeObject_ne hInv h)
      (storeObject_objects_eq st st' _ _ hInv h) hC⟩

end SeLe4n.Kernel
