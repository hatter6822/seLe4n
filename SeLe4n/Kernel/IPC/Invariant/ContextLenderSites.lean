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
import SeLe4n.Kernel.IPC.Operations.HeldContextPopInPlace
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

/-! ### The unheld pops -/

theorem severUnheldSchedContext_linksShrink {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (h : severUnheldSchedContext st scId newOwner? = .ok st') :
    contextStackLinksShrink st st' := by
  unfold severUnheldSchedContext at h
  cases hS : st.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h; simp only [] at h
    split at h
    · cases h
    cases hH : donationHeadOf? st scId sc with
    | error e => rw [hH] at h; cases h
    | ok head? =>
      rw [hH] at h; simp only [] at h
      cases hS1 : storeObject scId.toObjId (.schedContext (donationSeverSchedContext sc
          (head?.bind (fun p => p.2.prev)) newOwner?)) st with
      | error e => rw [hS1] at h; cases h
      | ok p =>
        obtain ⟨⟨⟩, s1⟩ := p
        rw [hS1] at h; simp only [] at h
        exact (contextStackLinksShrink_storeHeadBelow hObjInv
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS) hH rfl hS1).trans
          (storeDonationHeadPop_linksShrink
            (storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1) h)

theorem severUnheldSchedContext_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {scId : SeLe4n.SchedContextId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : severUnheldSchedContext st scId newOwner? = .ok st') : contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (severUnheldSchedContext_linksShrink hObjInv h)

theorem returnUnheldSchedContext_linksShrink {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    contextStackLinksShrink st st' := by
  unfold returnUnheldSchedContext at h
  cases hS : st.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h; simp only [] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    cases hH : donationHeadOf? st scId sc with
    | error e => rw [hH] at h; cases h
    | ok head? =>
      rw [hH] at h; simp only [] at h
      cases hS1 : storeObject scId.toObjId (.schedContext (donationReturnSchedContext sc owner
          (head?.bind (fun p => p.2.prev)) newOwner?)) st with
      | error e => rw [hS1] at h; cases h
      | ok p =>
        obtain ⟨⟨⟩, s1⟩ := p
        rw [hS1] at h; simp only [] at h
        have hI1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
        have hA := contextStackLinksShrink_storeHeadBelow hObjInv
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS) hH rfl hS1
        cases hS2 : storeDonationHeadPop scId head? s1 with
        | error e => rw [hS2] at h; cases h
        | ok s2 =>
          rw [hS2] at h; simp only [] at h
          have hB := storeDonationHeadPop_linksShrink hI1 hS2
          have hI2 := storeDonationHeadPop_preserves_objects_invExt hI1 hS2
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i hS3; cases h
              exact (hA.trans hB).trans ((contextStackLinksShrink_storeObject_other hI2 hS3
                (fun _ e => by cases e) (fun _ e => by cases e)).trans
                (contextStackLinksShrink_of_objects_eq (markKeyChangeFrom_objects _ _ _)))

/-- **The held pop shrinks the stack links**: the sever's head pop, then the
holder's binding store, which writes no reply and no context. -/
theorem keepDonatedSchedContext_linksShrink {st st' : SystemState}
    {holder : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    contextStackLinksShrink st st' := by
  obtain ⟨sc, head?, _, s1, s2, hSc, -, -, hH, hS1, hS2, -, hS3⟩ :=
    keepDonatedSchedContext_ok_storeChain h
  have hI1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hI2 := storeDonationHeadPop_preserves_objects_invExt hI1 hS2
  exact ((contextStackLinksShrink_storeHeadBelow hObjInv hSc hH rfl hS1).trans
    (storeDonationHeadPop_linksShrink hI1 hS2)).trans
    (contextStackLinksShrink_storeObject_other hI2 hS3 (fun _ e => by cases e) (fun _ e => by cases e))

/-- **The held pop keeps every lender flowing to its context**: it shrinks the
stack links. -/
theorem keepDonatedSchedContext_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {holder : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') : contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (keepDonatedSchedContext_linksShrink hObjInv h)

/-- The resolved held pop shrinks the stack links. -/
theorem keepDonatedSchedContextResolved_linksShrink {st st' : SystemState}
    {holder : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId} (hObjInv : st.objects.invExt)
    (h : keepDonatedSchedContextResolved st holder scId = .ok st') : contextStackLinksShrink st st' :=
  keepDonatedSchedContextResolved_lift h fun _ _ hP => keepDonatedSchedContext_linksShrink hObjInv hP

theorem returnUnheldSchedContext_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') : contextLendersFlow ctx st' :=
  contextLendersFlow_of_linksShrink hInv (returnUnheldSchedContext_linksShrink hObjInv h)

/-- The compiled unheld pop is the resolved pop on the states its gate admits
(`unheldPopsInPlace_pop`). -/
theorem returnUnheldSchedContextInPlace_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (scId : SeLe4n.SchedContextId) (c : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hFlow : contextLendersFlow ctx st)
    (hG : unheldPopsInPlace st scId c = true) :
    contextLendersFlow ctx (returnUnheldSchedContextInPlace st c scId) := by
  have h := (unheldPopsInPlace_pop st scId c hG).2
  unfold returnUnheldSchedContextResolved at h
  cases hO : replyStackOuterCaller? st scId with
  | error e => rw [hO] at h; cases h
  | ok n =>
    rw [hO] at h; simp only [] at h
    exact returnUnheldSchedContext_preserves_contextLendersFlow hInv hFlow h

/-- The compiled held pop is the resolved held pop on the states its gate
admits (`keptPopsInPlace_pop`). -/
theorem keepDonatedSchedContextInPlace_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (hFlow : contextLendersFlow ctx st)
    (hG : keptPopsInPlace st holder scId = true) :
    contextLendersFlow ctx (keepDonatedSchedContextInPlace st holder scId) :=
  keepDonatedSchedContextResolved_lift (keptPopsInPlace_pop st holder scId hG).2
    fun _ _ hP => keepDonatedSchedContext_preserves_contextLendersFlow hInv hFlow hP

/-! ### The compiled push and pop -/

/-- **The compiled push carries the lenders' flow where the donor flows to the
context**: on the states its checks pass it is the push's state
(`donateSchedContext_eq_inPlace`). -/
theorem donateSchedContextInPlace_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (donor srv : TCB)
    (rid : SeLe4n.ReplyId) (pr : Reply)
    (hSc : st.getSchedContext? scId = some sc) (hB : sc.boundThread = some client)
    (hC : lookupTcb st client = some donor) (hRO : donor.replyObject = some rid)
    (hR : st.getReply? rid = some pr) (hPrev : pr.prev = none) (hNext : pr.next = none)
    (hCaller : pr.caller ≠ none) (hNe : sc.scReply ≠ some rid)
    (hOld : ∀ old, sc.scReply = some old →
      (∃ oR, st.getReply? old = some oR) ∧
      storeLeavesIndexAndTypes st old.toObjId .reply = true ∧
      st.objects.findsInPlace old.toObjId = true)
    (hS : st.getTcb? server = some srv) (hSRes : server.isReserved = false)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFr : st.objects.findsInPlace rid.toObjId = true)
    (hLc : storeLeavesIndexAndTypes st client.toObjId .tcb = true)
    (hFc : st.objects.findsInPlace client.toObjId = true)
    (hLs : storeLeavesIndexAndTypes st server.toObjId .tcb = true)
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hRecip : replyCallerLinkageReciprocal st) (hInv : contextLendersFlow ctx st)
    (hFlow : securityFlowsTo (ctx.threadLabelOf client) (ctx.objectLabelOf scId.toObjId) = true) :
    contextLendersFlow ctx (donateSchedContextInPlace st client server scId) :=
  donateSchedContext_preserves_contextLendersFlow hObjInv hChain hRecip hInv hFlow
    (donateSchedContext_eq_inPlace st client server scId sc donor srv rid pr hSc hB hC hRO hR
      hPrev hNext hCaller hNe hOld hS hSRes hLsc hFsc hLr hFr hLc hFc hLs)

/-- **The compiled pop is a links shrink** on the states its checks pass: it is
the resolved pop's state (`returnDonatedSchedContextResolved_eq_inPlace`). -/
theorem returnDonatedSchedContextInPlace_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ot ht : TCB)
    (hSc : st.getSchedContext? scId = some sc) (hB : sc.boundThread = some holder)
    (hHead : sc.scReply = some hr) (hR : st.getReply? hr = some r)
    (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → b ≠ hr ∧ (∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
      st.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable st holder owner
      (SeLe4n.ThreadId.ofOptCode (popOuterCode st r)) = true)
    (hRecip : donationRecipientAcceptable st owner = true)
    (hORes : owner.isReserved = false) (hHRes : holder.isReserved = false)
    (hOT : st.getTcb? owner = some ot) (hHT : st.getTcb? holder = some ht)
    (hNeOH : owner ≠ holder)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st hr.toObjId .reply = true)
    (hFr : st.objects.findsInPlace hr.toObjId = true)
    (hLo : storeLeavesIndexAndTypes st owner.toObjId .tcb = true)
    (hFo : st.objects.findsInPlace owner.toObjId = true)
    (hLh : storeLeavesIndexAndTypes st holder.toObjId .tcb = true)
    (hObjInv : st.objects.invExt) (hInv : contextLendersFlow ctx st) :
    contextLendersFlow ctx (returnDonatedSchedContextInPlace st holder owner scId) := by
  obtain ⟨newOwner?, _, h⟩ := returnDonatedSchedContextResolved_ok_decompose
    (returnDonatedSchedContextResolved_eq_inPlace st holder owner scId sc hr r ot ht hSc hB hHead
      hR hNext hBelow hOuter hRecip hORes hHRes hOT hHT hNeOH hLsc hFsc hLr hFr hLo hFo hLh)
  exact returnDonatedSchedContext_preserves_contextLendersFlow hObjInv hInv h

/-! ### The suspend's cuts and the context's let-go -/

theorem consumeReplyLink_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact hFlow
  · exact consumeCallerReplyLink_preserves_contextLendersFlow st tid _ hInv hFlow

/-- **seL4-MCS's `reply_remove_tcb` on a head is a links shrink**: the head's
upward link and the context's head cleared, a holder's owner record cleared. -/
theorem cutHeadFrameKeepingContext_linksShrink (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) :
    contextStackLinksShrink st (Lifecycle.Suspend.cutHeadFrameKeepingContext st rid) := by
  unfold Lifecycle.Suspend.cutHeadFrameKeepingContext
  cases replyFrameHeadContext? st rid with
  | none => exact .refl _
  | some scId =>
    simp only []
    cases hR : st.getReply? rid with
    | none => exact .refl _
    | some r =>
      simp only []
      cases hS1 : storeObject rid.toObjId (.reply { r with next := none }) st with
      | error e => exact .refl _
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        simp only []
        have hI1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS1
        have hAB := (contextStackLinksShrink_storeReply hInv hR hS1 (.inr rfl) (.inr rfl)).trans
          (contextStackLinksShrink_updateSchedContext st1 scId
            (fun sc => { sc with scReply := none, donationOrigin := none }) hI1 (fun _ => .inl rfl))
        have hI2 := SystemState.updateSchedContext_preserves_objects_invExt st1 scId
          (fun sc => { sc with scReply := none, donationOrigin := none }) hI1
        split
        · exact hAB
        · split
          · exact hAB
          · split
            · split
              · exact hAB.trans ((contextStackLinksShrink_updateTcb _ _ _ hI2).trans
                  (contextStackLinksShrink_of_objects_eq (markKeyChangeFrom_objects _ _ _)))
              · exact hAB
            · exact hAB

theorem cutHeadFrameKeepingContext_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (Lifecycle.Suspend.cutHeadFrameKeepingContext st rid) :=
  contextLendersFlow_of_linksShrink hFlow (cutHeadFrameKeepingContext_linksShrink st rid hInv)

/-- Its compiled form is the cut (`cutHeadFrameKeepingContext_eq_impl`). -/
theorem cutHeadFrameKeepingContextImpl_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (Lifecycle.Suspend.cutHeadFrameKeepingContextImpl st rid) := by
  rw [← Lifecycle.Suspend.cutHeadFrameKeepingContext_eq_impl]
  exact cutHeadFrameKeepingContext_preserves_contextLendersFlow st rid hInv hFlow

/-- **seL4's `schedContext_unbindReply` is a links shrink**: the head's upward
link cleared, then the context's head. -/
theorem schedContextUnbindReply_linksShrink (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : contextStackLinksShrink st (schedContextUnbindReply st x) := by
  unfold schedContextUnbindReply
  split
  · split
    · split
      · rename_i r hR
        split
        · split
          · rename_i st1 hS1
            exact (contextStackLinksShrink_storeReply hInv hR hS1 (.inr rfl) (.inr rfl)).trans
              (contextStackLinksShrink_updateSchedContext st1 _ _
                (storeObject_preserves_objects_invExt st st1 _ _ hInv hS1) (fun _ => .inl rfl))
          · exact .refl _
        · exact .refl _
      · exact .refl _
    · exact .refl _
  · exact .refl _

theorem schedContextUnbindReply_preserves_contextLendersFlow {ctx : LabelingContext}
    (st : SystemState) (x : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (hFlow : contextLendersFlow ctx st) : contextLendersFlow ctx (schedContextUnbindReply st x) :=
  contextLendersFlow_of_linksShrink hFlow (schedContextUnbindReply_linksShrink st x hInv)

/-! ### The caller link -/

/-- **Linking a caller adds no lender**: `linkReply` writes a caller only on a
free reply object (`Reply.isFree`, fail-closed on one in use), and a free reply
object is on no context's stack (`not_onContextStack_of_next_none`), so every
lender after the link was one before it.  This is the "callers kept" fact for
every writer that links a caller: none can rewrite the caller of a frame on a
stack. -/
theorem linkReply_preserves_contextLendersFlow {ctx : LabelingContext} {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId} (hObjInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : contextLendersFlow ctx st)
    (h : SystemState.linkReply rid caller st = .ok ((), st')) : contextLendersFlow ctx st' := by
  unfold SystemState.linkReply at h
  cases hR : st.getReply? rid with
  | none => rw [hR] at h; cases h
  | some r =>
    rw [hR] at h; simp only [] at h
    split at h
    · rename_i hFree
      have hF := (Reply.isFree_iff r).mp hFree
      have hEq := storeObject_objects_eq st st' _ _ hObjInv h
      have hNe : ∀ x, x ≠ rid.toObjId → st'.objects[x]? = st.objects[x]? :=
        fun x hx => storeObject_objects_ne st st' _ x _ hx hObjInv h
      have hO := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      -- the stacks are the stacks they were
      have hPath : ∀ s x, OnContextStackView st' s x → OnContextStackView st s x := by
        intro s x hOn
        induction hOn with
        | head hH =>
          refine .head ?_
          rw [contextStackHead_eq_obj] at hH ⊢
          by_cases hk : s.toObjId = rid.toObjId
          · rw [hk, hEq] at hH; cases hH
          · rw [hNe _ hk] at hH; exact hH
        | @lower x x' _ hP ih =>
          refine .lower ih ?_
          rw [replyStackPrev_eq_obj] at hP ⊢
          by_cases hk : x.toObjId = rid.toObjId
          · rw [hk, hEq] at hP; rw [hk, hO]; exact hP
          · rw [hNe _ hk] at hP; exact hP
      rw [contextLendersFlow_iff_views] at hFlow ⊢
      intro s x l hOn hC
      have hOn0 := hPath s x hOn
      by_cases hk : x.toObjId = rid.toObjId
      · exact absurd (SeLe4n.ReplyId.toObjId_injective _ _ hk ▸ hOn0)
          (not_onContextStack_of_next_none hChain hR hF.2.2 s)
      · rw [replyStackCaller_eq_obj, hNe _ hk, ← replyStackCaller_eq_obj] at hC
        exact hFlow s x l hOn0 hC
    · cases h

/-- **`linkCallerReply` adds no lender**: the caller link, then the caller's
own reply link (a thread record). -/
theorem linkCallerReply_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hFlow : contextLendersFlow ctx st)
    (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) : contextLendersFlow ctx st' := by
  unfold SystemState.linkCallerReply at h
  cases h1 : SystemState.linkReply rid caller st with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    rw [h1] at h; simp only [] at h
    have hF1 := linkReply_preserves_contextLendersFlow hObjInv hChain hFlow h1
    have hI1 : s1.objects.invExt := by
      unfold SystemState.linkReply at h1
      split at h1
      · split at h1
        · exact storeObject_preserves_objects_invExt st s1 _ _ hObjInv h1
        · cases h1
      · cases h1
    split at h
    · cases h
    · split at h
      · exact contextLendersFlow_of_linksShrink hF1
          (contextStackLinksShrink_storeObject_other hI1 h (fun _ e => by cases e)
            (fun _ e => by cases e))
      · cases h

end SeLe4n.Kernel
