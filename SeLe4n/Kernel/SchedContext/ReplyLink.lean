-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# A scheduling context letting go of the reply stack it heads

seL4-MCS's `schedContext_unbindReply` (`schedcontext.c`): when a scheduling
context heads a reply stack (`sc->scReply`), the head reply's upward link is
cleared (`replyNext = 0`) and then the context's head (`scReply = NULL`).  The
frames below the head stay linked to it, a stack no context carries, and their
callers keep waiting on their replies; a later reply to the top frame cuts it
from the frame below (`cutReplyFrameOut`'s cut from below, seL4's
`reply_remove`).

`SchedContext_Unbind` runs it last (`invokeSchedContext_Unbind`), and so does
the finalisation of a context, before the context is retyped.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Whether a reply stack's head link names the context at `x`.** -/
@[inline] def replyStackLinkHeads (x : SeLe4n.ObjId) : Option ReplyStackLink → Bool
  | some (.head s) => s.val == x.val
  | _ => false

/-- **seL4-MCS `schedContext_unbindReply`**: the context at `x` lets go of the
reply stack it heads — the head reply's upward link is cleared, then the
context's head.  The identity on a context that heads no stack, or whose head
does not name it back. -/
def schedContextUnbindReply (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getSchedContext? ⟨x.val⟩ with
  | some sc =>
    match sc.scReply with
    | some rid =>
      match st.getReply? rid with
      | some r =>
        if replyStackLinkHeads x r.next then
          match storeObject rid.toObjId (.reply { r with next := none }) st with
          | .ok ((), st1) => st1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }
          | .error _ => st
        else st
      | none => st
    | none => st
  | none => st

/-- `schedContextUnbindReply` as it is compiled: the head reply's upward link
cleared in its slot (`SystemState.storeReplyWith`), so no reply record, no
object cell and no store result is built (`schedContextUnbindReply_eq_impl`). -/
@[inline] def schedContextUnbindReplyImpl (st : SystemState) (x : SeLe4n.ObjId) :
    SystemState :=
  match st.getSchedContext? ⟨x.val⟩ with
  | some sc =>
    match sc.scReply with
    | some rid =>
      match st.getReply? rid with
      | some r =>
        if replyStackLinkHeads x r.next then
          (st.storeReplyWith rid.toObjId fun r => { r with next := none }).updateSchedContext
            ⟨x.val⟩ fun sc => { sc with scReply := none }
        else st
      | none => st
    | none => st
  | none => st

@[csimp] theorem schedContextUnbindReply_eq_impl :
    @schedContextUnbindReply = @schedContextUnbindReplyImpl := by
  funext st x
  unfold schedContextUnbindReply schedContextUnbindReplyImpl
  cases st.getSchedContext? ⟨x.val⟩ with
  | none => rfl
  | some sc =>
    dsimp only
    cases sc.scReply with
    | none => rfl
    | some rid =>
      dsimp only
      cases hR : st.getReply? rid with
      | none => rfl
      | some r =>
        dsimp only
        split
        · rw [SystemState.storeObject_reply_eq_storeReplyWith
            ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) (fun r => { r with next := none })]
        · rfl

theorem replyStackLinkHeads_spec {x : SeLe4n.ObjId} {n : Option ReplyStackLink}
    (h : replyStackLinkHeads x n = true) : n = some (.head ⟨x.val⟩) := by
  rcases n with _ | (_ | ⟨v⟩)
  · cases h
  · cases h
  · simp only [replyStackLinkHeads, beq_iff_eq] at h
    obtain ⟨vv⟩ := v
    simp only at h
    subst h; rfl

/-- **The unbind is the identity or its two writes**: the head reply's upward
link cleared by a store, then the context's head. -/
theorem schedContextUnbindReply_cases (st : SystemState) (x : SeLe4n.ObjId) :
    schedContextUnbindReply st x = st ∨
      ∃ (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply) (st1 : SystemState),
        st.getSchedContext? ⟨x.val⟩ = some sc ∧ sc.scReply = some rid ∧
        st.getReply? rid = some r ∧ r.next = some (.head ⟨x.val⟩) ∧
        storeObject rid.toObjId (.reply { r with next := none }) st = .ok ((), st1) ∧
        schedContextUnbindReply st x =
          st1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none } := by
  unfold schedContextUnbindReply
  split
  · rename_i sc hSc
    split
    · rename_i rid hR
      split
      · rename_i r hRr
        split
        · rename_i hH
          split
          · rename_i st1 hS
            exact Or.inr ⟨sc, rid, r, st1, hSc, hR, hRr, replyStackLinkHeads_spec hH, hS, rfl⟩
          · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A property the identity and the two writes keep, the unbind keeps.** -/
theorem schedContextUnbindReply_induct (P : SystemState → SystemState → Prop)
    (st : SystemState) (x : SeLe4n.ObjId) (hId : P st st)
    (hW : ∀ (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply) (st1 : SystemState),
      st.getSchedContext? ⟨x.val⟩ = some sc → sc.scReply = some rid →
      st.getReply? rid = some r → r.next = some (.head ⟨x.val⟩) →
      storeObject rid.toObjId (.reply { r with next := none }) st = .ok ((), st1) →
      P st (st1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none })) :
    P st (schedContextUnbindReply st x) := by
  rcases schedContextUnbindReply_cases st x with h | ⟨sc, rid, r, st1, h1, h2, h3, h4, h5, h⟩
  · rw [h]; exact hId
  · rw [h]; exact hW sc rid r st1 h1 h2 h3 h4 h5

/-- **The unbind writes the object store alone**: the machine and the
scheduler are the state's. -/
theorem schedContextUnbindReply_frame (st : SystemState) (x : SeLe4n.ObjId) :
    (schedContextUnbindReply st x).machine = st.machine ∧
      (schedContextUnbindReply st x).scheduler = st.scheduler :=
  schedContextUnbindReply_induct (fun a b => b.machine = a.machine ∧ b.scheduler = a.scheduler)
    st x ⟨rfl, rfl⟩ (fun _ _ _ s1 _ _ _ _ hS =>
      ⟨(SystemState.updateSchedContext_machine s1 _ _).trans
          (storeObject_machine_eq _ _ _ _ hS),
        (SystemState.updateSchedContext_scheduler s1 _ _).trans
          (storeObject_scheduler_eq _ _ _ _ hS)⟩)

theorem schedContextUnbindReply_machine (st : SystemState) (x : SeLe4n.ObjId) :
    (schedContextUnbindReply st x).machine = st.machine := (schedContextUnbindReply_frame st x).1

theorem schedContextUnbindReply_scheduler (st : SystemState) (x : SeLe4n.ObjId) :
    (schedContextUnbindReply st x).scheduler = st.scheduler := (schedContextUnbindReply_frame st x).2

end SeLe4n.Kernel
