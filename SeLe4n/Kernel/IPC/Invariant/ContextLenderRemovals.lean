-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Invariant.ContextLenders
import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInPlace

/-!
# The lenders across the reply-stack removals

WS-SX SX8 (D27): every reply-stack write that takes a frame off a stack, cuts a
stack or consumes a caller is a **links shrink** (`contextStackLinksShrink`): a
`prev` link is cleared or kept, a caller is cleared or kept, and no context
heads a frame it did not have on its stack.  So each carries the lenders' flow
(`contextLendersFlow_of_linksShrink`) with no hypothesis on the labels.  These
are the lender results `SeLe4n.Testing.ReplyStackWriteCensus` names for the
removal sites.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A slot that only shrinks**: unchanged, or a reply object rewritten with
its caller kept and its `prev` cleared or kept. -/
def replySlotShrinks (st st' : SystemState) (k : SeLe4n.ObjId) : Prop :=
  st'.objects[k]? = st.objects[k]? ∨
    ∃ o o' : Reply, st.objects[k]? = some (.reply o) ∧ st'.objects[k]? = some (.reply o') ∧
      o'.caller = o.caller ∧ (o'.prev = none ∨ o'.prev = o.prev)

/-- **Every slot only shrinks: the links shrink.** -/
theorem contextStackLinksShrink_of_replySlots {st st' : SystemState}
    (h : ∀ k, replySlotShrinks st st' k) : contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_of_objects (fun s r hH => ?_) (fun r x hP => ?_)
    (fun r l hC => ?_)
  · rcases h s.toObjId with hEq | ⟨o, o', _, hPost, _⟩
    · rw [hEq] at hH; exact .head (by rw [contextStackHead_eq_obj]; exact hH)
    · rw [hPost] at hH; cases hH
  · rcases h r.toObjId with hEq | ⟨o, o', hPre, hPost, _, hPr⟩
    · rw [hEq] at hP; exact hP
    · rw [hPost] at hP; rw [hPre]; simp only [objStackPrev] at hP ⊢
      rcases hPr with hPr | hPr <;> rw [hPr] at hP
      · cases hP
      · exact hP
  · rcases h r.toObjId with hEq | ⟨o, o', hPre, hPost, hCl, _⟩
    · rw [hEq] at hC; exact hC
    · rw [hPost] at hC; rw [hPre]; simp only [objStackCaller] at hC ⊢; rw [← hCl]; exact hC

theorem replySlotShrinks.of_eq {st st' : SystemState} {k : SeLe4n.ObjId}
    (h : st'.objects[k]? = st.objects[k]?) : replySlotShrinks st st' k := .inl h

theorem replySlotShrinks.of_reply {st st' : SystemState} {rid : SeLe4n.ReplyId} {o o' : Reply}
    (hPre : st.getReply? rid = some o) (hPost : st'.getReply? rid = some o')
    (hC : o'.caller = o.caller) (hP : o'.prev = none ∨ o'.prev = o.prev) :
    replySlotShrinks st st' rid.toObjId :=
  .inr ⟨o, o', (SystemState.getReply?_eq_some_iff _ _ _).mp hPre,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hPost, hC, hP⟩

/-! ### The cut -/

theorem cutReplyFrameStores_linksShrink {st st' : SystemState} {rid above : SeLe4n.ReplyId}
    {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : cutReplyFrameStores st rid above r a = .ok st') :
    contextStackLinksShrink st st' := by
  have hCut := cutReplyFrameStores_getReply?_cut hObjInv hR hN hA hP h
  refine contextStackLinksShrink_of_replySlots fun k => ?_
  by_cases hkR : k = rid.toObjId
  · subst hkR; exact .of_reply hR hCut rfl (.inl rfl)
  by_cases hkA : k = above.toObjId
  · subst hkA
    have hNe : above ≠ rid := fun e => hkR (by rw [e])
    exact .of_reply hA (cutReplyFrameStores_getReply?_above hObjInv hR hN hA hP hNe h)
      (Reply.unlinkedFrom_caller a rid) (.inl (Reply.unlinkedFrom_prev a rid))
  cases hBelow : cutFrameBelow? st rid r above with
  | none =>
    exact .of_eq ((cutReplyFrameStores_sever_values hObjInv hBelow h).2.2 k hkA hkR)
  | some pair =>
    obtain ⟨below, b⟩ := pair
    have hV := cutReplyFrameStores_break_values hObjInv hR hN hA hP hBelow h
    by_cases hkB : k = below.toObjId
    · subst hkB
      exact .of_reply (cutFrameBelow?_eq_some hBelow).2.2.1 hV.2.1 rfl (.inr rfl)
    · exact .of_eq (hV.2.2.2 k hkA hkB hkR)

theorem severReplyFrameBelowStores_linksShrink {st st' : SystemState}
    {rid below : SeLe4n.ReplyId} {r b : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = none)
    (hB : st.getReply? below = some b) (hBn : b.next = some (.frame rid))
    (h : severReplyFrameBelowStores st rid below r b = .ok st') :
    contextStackLinksShrink st st' := by
  have hV := severReplyFrameBelowStores_values hObjInv hR hN hB hBn h
  refine contextStackLinksShrink_of_replySlots fun k => ?_
  by_cases hkR : k = rid.toObjId
  · subst hkR; exact .of_reply hR hV.2.1 rfl (.inl rfl)
  by_cases hkB : k = below.toObjId
  · subst hkB; exact .of_reply hB hV.1 rfl (.inr rfl)
  · exact .of_eq (hV.2.2 k hkB hkR)

/-- **The removal is a links shrink.** -/
theorem cutReplyFrameOut_linksShrink {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt) (h : cutReplyFrameOut st rid = .ok st') :
    contextStackLinksShrink st st' := by
  rcases cutReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, hN, hA, hP, hS⟩ |
      ⟨r, below, b, hR, hN, -, hB, hBn, hS⟩
  · exact .refl _
  · exact cutReplyFrameStores_linksShrink hObjInv hR hN hA hP hS
  · exact severReplyFrameBelowStores_linksShrink hObjInv hR hN hB hBn hS

theorem cutReplyFrameOut_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (hInv : contextLendersFlow ctx st) (h : cutReplyFrameOut st rid = .ok st') :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (cutReplyFrameOut_linksShrink hObjInv h)

theorem cutReplyFrameOutOrSelf_linksShrink (st : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) : contextStackLinksShrink st (cutReplyFrameOutOrSelf st rid) := by
  rcases cutReplyFrameOutOrSelf_cases st rid with h | h
  · exact .of_eq h
  · exact cutReplyFrameOut_linksShrink hObjInv h

theorem cutReplyFrameOutOrSelf_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hInv : contextLendersFlow ctx st) : contextLendersFlow ctx (cutReplyFrameOutOrSelf st rid) :=
  contextLendersFlow_of_linksShrink hInv (cutReplyFrameOutOrSelf_linksShrink st rid hObjInv)

theorem cutThreadReplyFrameOut_linksShrink (st : SystemState) (tcb : TCB)
    (hObjInv : st.objects.invExt) : contextStackLinksShrink st (cutThreadReplyFrameOut st tcb) := by
  unfold cutThreadReplyFrameOut
  split
  · exact .refl _
  · exact cutReplyFrameOutOrSelf_linksShrink st _ hObjInv

theorem cutThreadReplyFrameOut_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (tcb : TCB) (hObjInv : st.objects.invExt)
    (hInv : contextLendersFlow ctx st) : contextLendersFlow ctx (cutThreadReplyFrameOut st tcb) :=
  contextLendersFlow_of_linksShrink hInv (cutThreadReplyFrameOut_linksShrink st tcb hObjInv)

/-! ### The consume -/

theorem Reply.consumed_prev_shrinks (r : Reply) : r.consumed.prev = none ∨ r.consumed.prev = r.prev := by
  unfold Reply.consumed; split
  · exact .inr rfl
  · exact .inl rfl

/-- **The caller clear is a links shrink**: the reply object's caller cleared,
its `prev` kept on a head and cleared otherwise, and the caller's own reply
link (a thread record, which no stack view reads). -/
theorem consumeCallerReply_linksShrink {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    contextStackLinksShrink st st' := by
  unfold SystemState.consumeCallerReply at h
  have hC : ∀ {s1 : SystemState}, SystemState.consumeReply rid st = .ok ((), s1) →
      contextStackLinksShrink st s1 := by
    intro s1 h1
    unfold SystemState.consumeReply at h1
    cases hR : st.getReply? rid with
    | none => rw [hR] at h1; cases h1; exact .refl _
    | some r =>
      rw [hR] at h1
      exact contextStackLinksShrink_storeReply hObjInv hR h1 r.consumed_prev_shrinks
        (.inl (Reply.consumed_caller r))
  cases h1 : SystemState.consumeReply rid st with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    rw [h1] at h
    have hS1 := hC h1
    have hInv1 : s1.objects.invExt := by
      unfold SystemState.consumeReply at h1
      split at h1
      · exact storeObject_preserves_objects_invExt st s1 _ _ hObjInv h1
      · cases h1; exact hObjInv
    simp only [] at h
    split at h
    · cases h; exact hS1
    · exact hS1.trans (contextStackLinksShrink_storeObject_other hInv1 h
        (fun _ e => by cases e) (fun _ e => by cases e))

theorem consumeCallerReply_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (consumeCallerReply_linksShrink hObjInv h)

theorem consumeCallerReplyLink_linksShrink (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    contextStackLinksShrink st (st.consumeCallerReplyLink caller rid) :=
  consumeCallerReply_linksShrink hObjInv (SystemState.consumeCallerReply_eq_link st caller rid)

theorem consumeCallerReplyLink_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st) :
    contextLendersFlow ctx (st.consumeCallerReplyLink caller rid) :=
  contextLendersFlow_of_linksShrink hInv (consumeCallerReplyLink_linksShrink st caller rid hObjInv)

/-- **seL4's `reply_remove` is a links shrink**: the cut, then the consume. -/
theorem removeCallerReplyFrame_linksShrink {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    contextStackLinksShrink st st' :=
  (cutReplyFrameOutOrSelf_linksShrink st rid hObjInv).trans
    (consumeCallerReply_linksShrink (cutReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) h)

theorem removeCallerReplyFrame_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (removeCallerReplyFrame_linksShrink hObjInv h)

/-! ### Writers of no stack view -/

/-- **A step after which every context and every reply object was there
before** takes no stack view anywhere it was not: a links shrink. -/
theorem contextStackLinksShrink_of_agree {st st' : SystemState}
    (hRp : ∀ (x : SeLe4n.ObjId) (r : Reply), st'.objects[x]? = some (KernelObject.reply r) →
      st.objects[x]? = some (KernelObject.reply r))
    (hSc : ∀ (x : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[x]? = some (KernelObject.schedContext sc) →
      st.objects[x]? = some (KernelObject.schedContext sc)) :
    contextStackLinksShrink st st' := by
  refine contextStackLinksShrink_of_objects (fun s r hH => ?_) (fun r x hP => ?_)
    (fun r l hC => ?_)
  · cases h : st'.objects[s.toObjId]? with
    | none => rw [h] at hH; cases hH
    | some o =>
      cases o <;> rw [h] at hH <;> simp only [objStackHead, reduceCtorEq] at hH
      exact .head (by rw [contextStackHead_eq_obj, hSc _ _ h]; exact hH)
  · cases h : st'.objects[r.toObjId]? with
    | none => rw [h] at hP; cases hP
    | some o =>
      cases o <;> rw [h] at hP <;> simp only [objStackPrev, reduceCtorEq] at hP
      rw [hRp _ _ h]; exact hP
  · cases h : st'.objects[r.toObjId]? with
    | none => rw [h] at hC; cases hC
    | some o =>
      cases o <;> rw [h] at hC <;> simp only [objStackCaller, reduceCtorEq] at hC
      rw [hRp _ _ h]; exact hC

/-- **One slot written in place**: `contextStackLinksShrink_of_slot` at a table
insert. -/
theorem contextStackLinksShrink_insert {st : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hInv : st.objects.invExt)
    (hHead : ∀ (s : SeLe4n.SchedContextId) r, s.toObjId = k →
      objStackHead (some o) = some r → OnContextStackView st s r)
    (hPrev : ∀ x, objStackPrev (some o) = some x → objStackPrev st.objects[k]? = some x)
    (hCaller : ∀ l, objStackCaller (some o) = some l → objStackCaller st.objects[k]? = some l) :
    contextStackLinksShrink st { st with objects := st.objects.insert k o } := by
  have hEq : (st.objects.insert k o)[k]? = some o := by
    simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
  refine contextStackLinksShrink_of_slot (st' := { st with objects := st.objects.insert k o }) k
    (fun x hx => ?_) (fun s r hk hr => hHead s r hk (hEq ▸ hr)) (fun x hx => hPrev x (hEq ▸ hx))
    (fun l hl => hCaller l (hEq ▸ hl))
  show (st.objects.insert k o)[x]? = _
  simp only [RHTable_getElem?_eq_get?]
  exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv

/-- An in-place write of an object that is neither a context nor a reply
object. -/
theorem contextStackLinksShrink_insert_other {st : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hInv : st.objects.invExt)
    (hSc : ∀ sc, o ≠ .schedContext sc) (hRp : ∀ r, o ≠ .reply r) :
    contextStackLinksShrink st { st with objects := st.objects.insert k o } := by
  refine contextStackLinksShrink_insert hInv (fun _ _ _ hr => ?_) (fun _ hx => ?_)
    (fun _ hl => ?_) <;> cases o <;> simp_all [objStackHead, objStackPrev, objStackCaller]

/-- **A thread record write** takes no stack view. -/
theorem contextStackLinksShrink_updateTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (f : TCB → TCB) (hInv : st.objects.invExt) :
    contextStackLinksShrink st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact .refl _
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact contextStackLinksShrink_insert_other hInv (fun _ e => by cases e) (fun _ e => by cases e)

/-- **A wake** writes thread records and the scheduler alone. -/
theorem contextStackLinksShrink_enqueueRunnableOnCore (st : SystemState)
    (c : Concurrency.CoreId) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    contextStackLinksShrink st (enqueueRunnableOnCore st c t) := by
  cases hTcb : st.getTcb? t with
  | none =>
    unfold enqueueRunnableOnCore; rw [SystemState.getTcbWitnessed?_eq_none hTcb]
    exact .refl _
  | some tcb =>
    cases hR : wakeDeclines st c t with
    | true => rw [enqueueRunnableOnCore_eq_self_of_declines st c t hR]; exact .refl _
    | false =>
      have hAg := enqueueRunnableOnCore_objectsAgree_marked st c t tcb hTcb hR
      exact (contextStackLinksShrink_insert_other (k := t.toObjId)
        (o := .tcb (tcb.setIpcState .ready)) hInv (fun _ e => by cases e)
        (fun _ e => by cases e)).trans
        (contextStackLinksShrink_of_agree (fun _ _ h => hAg.get_reply_iff.mp h)
          (fun _ _ h => hAg.get_schedContext_iff.mp h))

/-- **A reply object consumed in its slot** (the in-place reply's write). -/
theorem contextStackLinksShrink_modifyObject_consumed (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) :
    contextStackLinksShrink st (st.modifyObject rid.toObjId replyConsumedObject) := by
  unfold SystemState.modifyObject RobinHood.RHTable.modify
  cases hG : st.objects.get? rid.toObjId with
  | none => exact .refl _
  | some v =>
    have hPre : st.objects[rid.toObjId]? = some v := by rw [RHTable_getElem?_eq_get?]; exact hG
    simp only []
    cases v with
    | reply r =>
      refine contextStackLinksShrink_insert hInv (fun _ _ _ hr => ?_) (fun x hx => ?_)
        (fun l hl => ?_)
      · simp [replyConsumedObject, objStackHead] at hr
      · simp only [replyConsumedObject, objStackPrev, hPre] at hx ⊢
        rcases r.consumed_prev_shrinks with h | h <;> rw [h] at hx
        · cases hx
        · exact hx
      · simp [replyConsumedObject, objStackCaller] at hl
    | schedContext sc =>
      refine contextStackLinksShrink_insert hInv (fun s0 r hk hr => ?_) (fun _ hx => ?_)
        (fun _ hl => ?_)
      · exact .head (by rw [contextStackHead_eq_obj, hk, hPre]; exact hr)
      · simp [replyConsumedObject, objStackPrev] at hx
      · simp [replyConsumedObject, objStackCaller] at hl
    | _ =>
      exact contextStackLinksShrink_insert_other hInv (fun _ e => by cases e)
        (fun _ e => by cases e)

end SeLe4n.Kernel
