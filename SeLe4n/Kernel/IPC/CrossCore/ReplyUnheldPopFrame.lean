/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyUnheldInPlace

/-!
# The unheld pop's frame

seL4-MCS's `reply_pop` of a context no thread holds, handed to the caller and
settled on its home core (`returnUnheldSchedContextInPlace`), writes only the
caller's binding, the reply stack's links and the context (`popFrame`); the
caller and the reply object it consumed read as the pop leaves them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section UnheldPopWrites

/-- **The unheld pop writes only what a pop writes**, each in its slot. -/
theorem returnUnheldSchedContextInPlace_popFrame (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    popFrame (returnUnheldSchedContextInPlace st owner scId) st := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact popFrame.refl st
  · split
    · exact popFrame.refl st
    · split
      · exact popFrame.refl st
      · split
        · exact popFrame.refl st
        · dsimp only
          refine (markKeyChangeParts_popFrame _ _ _ _ _).trans
            ((markCandidacyGainFor_popFrame _ _ _).trans ?_)
          split
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo))
            all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
              apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo)))
            all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
              apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))

/-- A context's update leaves a thread's slot as it was. -/
theorem updateSchedContext_tcbAt (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hX : s.objects[x]? = some (.tcb t)) :
    (s.updateSchedContext scId f).objects[x]? = some (.tcb t) := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · by_cases e : x = scId.toObjId
    · subst e; rw [objects_modifyObject_self _ _ _ hNo, hX]; rfl
    · rw [objects_modifyObject_ne _ _ _ hNo _ e, hX]
  · exact hX

/-- A reply's update leaves a thread's slot as it was. -/
theorem modifyReply_tcbAt (s : SystemState) (k : SeLe4n.ObjId) (f : Reply → Reply)
    (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hX : s.objects[x]? = some (.tcb t)) :
    (s.modifyObject k (SystemState.mapReplyObject f)).objects[x]? = some (.tcb t) := by
  by_cases e : x = k
  · subst e; rw [objects_modifyObject_self _ _ _ hNo, hX]; rfl
  · rw [objects_modifyObject_ne _ _ _ hNo _ e, hX]

/-- **The unheld pop leaves every thread but its recipient as it was.** -/
theorem returnUnheldSchedContextInPlace_tcbAt (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB} (hx : x ≠ owner.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (returnUnheldSchedContextInPlace st owner scId).objects[x]? = some (.tcb t) := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · dsimp only
          rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
          split
          · rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo)) _ hx]
            exact modifyReply_tcbAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
              (updateSchedContext_tcbAt _ _ _ hNo hX)
          · rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo))) _ hx]
            exact modifyReply_tcbAt _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo))
              (modifyReply_tcbAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (updateSchedContext_tcbAt _ _ _ hNo hX))

/-- **The unheld pop takes its head off the stack**: the reply object the
context heads ends with no links. -/
theorem returnUnheldSchedContextInPlace_reply (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ot : TCB) (hNo : st.objects.noResizeDue)
    (hSc : st.getSchedContext? scId = some sc) (hH : sc.scReply = some hr)
    (hR : st.getReply? hr = some r) (hO : st.getTcb? owner = some ot)
    (hb : ∀ b, r.prev = some b → b ≠ hr) :
    (returnUnheldSchedContextInPlace st owner scId).objects[hr.toObjId]? =
      some (.reply { r with prev := none, next := none }) := by
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hOo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hO
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hOR : hr.toObjId ≠ owner.toObjId := fun e => by rw [e, hOo] at hRo; cases hRo
  have hSR : hr.toObjId ≠ scId.toObjId := fun e => by rw [e, hScO] at hRo; cases hRo
  have hU : ∀ f : SchedContext → SchedContext,
      (st.updateSchedContext scId f).objects[hr.toObjId]? = some (.reply r) := fun f => by
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    rw [hSc]
    rw [objects_modifyObject_ne _ _ _ hNo _ hSR, hRo]
  unfold returnUnheldSchedContextInPlace
  simp only [hSc, hH, hR, hO]
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  cases hP : r.prev with
  | none =>
    dsimp only
    rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo)) _ hOR,
      objects_modifyObject_self _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo), hU]
    rfl
  | some b =>
    dsimp only
    have hbr : b.toObjId ≠ hr.toObjId := fun e =>
      hb b hP (SeLe4n.ReplyId.toObjId_injective _ _ e)
    rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo))) _ hOR,
      objects_modifyObject_ne _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo)) _ (Ne.symm hbr),
      objects_modifyObject_self _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo), hU]
    rfl

end UnheldPopWrites

section UnheldReplyRecvGuard

/-- **The stack the unheld gate reads**: under `replyUnheldPopsInPlace` the
reply object heads the stack of a context naming it back, and the frame below
it, if any, is another reply object. -/
theorem replyUnheldPopsInPlace_stack (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hG : replyUnheldPopsInPlace st c rid = true) :
    ∃ rp scId sc, st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.next = some (.head scId) ∧
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.scReply = some rid ∧
      (∀ b, rp.prev = some b → b ≠ rid) := by
  unfold replyUnheldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨_, hM⟩ := hG
  cases hRg : st.getReply? rid with
  | none => rw [hRg] at hM; cases hM
  | some rp =>
  rw [hRg] at hM
  dsimp only at hM
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head scId =>
  rw [hN] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hSm, hU⟩ := hM
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hSm; cases hSm
  | some sc =>
  rw [hScg] at hSm
  dsimp only at hSm
  have hHead : sc.scReply = some rid := by
    revert hSm
    cases sc.scReply with
    | none => intro h; cases h
    | some h =>
      intro e
      have : h = rid := by cases h; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
      rw [this]
  refine ⟨rp, scId, sc, (SystemState.getReply?_eq_some_iff _ _ _).mp hRg, hN,
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg, hHead, ?_⟩
  intro b hb
  unfold unheldPopsInPlace at hU
  rw [hScg] at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, _, hU⟩ := hU
  rw [hHead] at hU
  dsimp only at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, hU⟩ := hU
  rw [hRg] at hU
  dsimp only at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, hP⟩ := hU
  rw [hb] at hP
  dsimp only at hP
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨⟨hbne, _⟩, _⟩, _⟩ := hP
  exact fun e => by subst e; simp at hbne

end UnheldReplyRecvGuard




end SeLe4n.Kernel
