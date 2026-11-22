-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.ContextLenderPops
import SeLe4n.Kernel.IPC.Operations.UnheldContextPopInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.SchedContext.ReplyLink

/-!
# The lenders across the remaining reply-stack write sites

WS-SX SX8 (D27): the lender result of each reply-stack write site the
`ReplyStackWriteCensus` registry names beyond the removals and the push/pop
specifications: the in-place reply legs, the compiled consume, the unheld pops,
the suspend's head cut, the context's let-go of its stack, and the compiled
push and pop.  Each is a links shrink, except the compiled push, which carries
the flow where the donor flows to the context, as the push does.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ### Slot writers -/

/-- A context rewritten in its slot with its head cleared or kept. -/
theorem contextStackLinksShrink_updateSchedContext (st : SystemState)
    (scId : SeLe4n.SchedContextId) (f : SchedContext → SchedContext)
    (hInv : st.objects.invExt) (hf : ∀ sc, (f sc).scReply = none ∨ (f sc).scReply = sc.scReply) :
    contextStackLinksShrink st (st.updateSchedContext scId f) := by
  cases hS : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]; exact .refl _
  | some sc =>
    rw [SystemState.updateSchedContext_eq_of_some hS]
    have hO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS
    refine contextStackLinksShrink_insert hInv (fun s r hk hr => ?_) (fun _ hx => ?_)
      (fun _ hl => ?_)
    · simp only [objStackHead] at hr
      rcases hf sc with h | h <;> rw [h] at hr
      · cases hr
      · exact .head (by rw [contextStackHead_eq_obj, hk, hO]; exact hr)
    · simp [objStackPrev] at hx
    · simp [objStackCaller] at hl

/-- A reply object rewritten in its slot with its `prev` and caller kept. -/
theorem contextStackLinksShrink_storeReplyWith (st : SystemState) (rid : SeLe4n.ReplyId)
    (f : Reply → Reply) (hInv : st.objects.invExt)
    (hf : ∀ r, (f r).prev = r.prev ∧ (f r).caller = r.caller) :
    contextStackLinksShrink st (st.storeReplyWith rid.toObjId f) := by
  cases hO : st.objects[rid.toObjId]? with
  | none => unfold SystemState.storeReplyWith; rw [hO]; exact .refl _
  | some o =>
    cases o with
    | reply r =>
      exact contextStackLinksShrink_storeReply hInv
        ((SystemState.getReply?_eq_some_iff _ _ _).mpr hO) (SystemState.storeObject_reply_eq_storeReplyWith hO f)
        (.inr (hf r).1) (.inr (hf r).2)
    | _ => unfold SystemState.storeReplyWith; rw [hO]; exact .refl _

/-! ### The in-place reply legs -/

/-- **The in-place reply leg's shape is a links shrink**: two thread writes, a
wake, and the reply object consumed in its slot. -/
theorem contextStackLinksShrink_replyLegShape (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (f : TCB → TCB) (hInv : st.objects.invExt) :
    contextStackLinksShrink st
      (((enqueueRunnableOnCore (st.updateTcb c f) (determineTargetCore (st.updateTcb c f) c) c
        ).modifyObject rid.toObjId replyConsumedObject).updateTcb c
          (fun t => { t with replyObjectCode := 0 })) := by
  have hI1 := SystemState.updateTcb_preserves_objects_invExt st c f hInv
  have hI2 := enqueueRunnableOnCore_preserves_objects_invExt _
    (determineTargetCore (st.updateTcb c f) c) c hI1
  have hI3 := modifyObject_preserves_objects_invExt (k := rid.toObjId) (f := replyConsumedObject) hI2
  exact (((contextStackLinksShrink_updateTcb st c f hInv).trans
    (contextStackLinksShrink_enqueueRunnableOnCore _ _ c hI1)).trans
    (contextStackLinksShrink_modifyObject_consumed _ rid hI2)).trans
    (contextStackLinksShrink_updateTcb _ c _ hI3)

theorem storeReplyLeg_preserves_contextLendersFlow {ctx : LabelingContext} (st : SystemState)
    (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (storeReplyLeg st c rid msg) :=
  contextLendersFlow_of_linksShrink hFlow (contextStackLinksShrink_replyLegShape st c rid _ hInv)

theorem storeReplyLegReady_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (storeReplyLegReady st c rid) :=
  contextLendersFlow_of_linksShrink hFlow (contextStackLinksShrink_replyLegShape st c rid _ hInv)

theorem storeFaultReplyLeg_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (storeFaultReplyLeg st c rid) :=
  contextLendersFlow_of_linksShrink hFlow (contextStackLinksShrink_replyLegShape st c rid _ hInv)

/-- The compiled consume is the consume (`consumeCallerReplyInPlace_eq`). -/
theorem consumeCallerReplyInPlace_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (consumeCallerReplyInPlace st c rid) := by
  rw [consumeCallerReplyInPlace_eq]
  exact consumeCallerReplyLink_preserves_contextLendersFlow st c rid hInv hFlow

end SeLe4n.Kernel
