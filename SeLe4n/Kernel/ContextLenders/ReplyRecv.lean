-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Dispatch

/-! # The reply-receive's answering leg carries the lenders' flow

WS-SX SX8.  seL4-MCS `handleReplyRecv`: `doReplyTransfer` (the reply leg, the
pop of the answered frame's context, the reply's capability transfer), then
`receiveIPC` (the return of a notification's context, the rendezvous and the
lend of the dequeued `Call`'s context).  The lend runs at the receive's lend
admission (`receiveLendAdmits`), read on the state the arm is handed, before the
reply leg; so the bridge (`replyRecvLendAdmits_flows_dequeued`) carries it
across the reply leg and the pop.

**The pop's binding frame** (`replyRecvPopDonation_binding_cases`): a thread
bound after the pop held the same context before it, or is the thread the pop
gave its context to — the answered caller, or the context's recorded origin
(`replyDonationRecipient`).  The answered caller is `.ready` after the reply leg,
so it is not the send queue's head the receive dequeues.  The recorded origin
may be: it is an unbound thread named by the context's origin record, free to
have called again since its frame was cut out.  It receives back a context it
lent itself, so the flow its label has to the context is the flow its own lend
was admitted at; the dispatch takes that fact at the pop's state as a premise
(`ReplyRecvLendersPremises.originFlows`), beside the chain facts
(`docs/REGISTERED_DEBT.md` table C, "`ipcReachable` is not carried across a trace
of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **What the pop does to the threads' bindings**: a thread bound after it held
the same context before it, or is the thread the pop handed its context to. -/
theorem replyRecvPopDonation_binding_cases {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (h : replyRecvPopDonation rid target st = .ok (r, st'))
    (y : SeLe4n.ThreadId) (t' : TCB) (s : SeLe4n.SchedContextId)
    (hT : st'.objects[y.toObjId]? = some (.tcb t')) (hS : t'.schedContextBinding.scId? = some s) :
    (∃ t0, st.objects[y.toObjId]? = some (.tcb t0) ∧ t0.schedContextBinding.scId? = some s) ∨
    (∃ sc holder, r = some (sc, holder) ∧ y = replyDonationRecipient st sc target ∧ s = sc) ∨
    (r = none ∧ y = target) := by
  unfold replyRecvPopDonation at h
  split at h
  case h_2 =>
    split at h
    · cases h
    rename_i hPop
    cases h
    rcases popUnheldReplyHead_objects_frame hPop with ⟨-, rfl⟩ |
        ⟨scId, _, st1, -, -, hP, rfl⟩ | ⟨_, _, -, -, hSv⟩
    · exact .inl ⟨t', hT, hS⟩
    · replace hT := (SchedContextOps.settleReturnedContext_agree _ _ _).symm.get_of_not_sc
        (fun _ e => KernelObject.noConfusion e) hT
      by_cases hy : y = target
      · exact .inr (.inr ⟨rfl, hy⟩)
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, tBwd, -, -, -⟩ :=
        returnUnheldSchedContext_objects hInv hP
      exact .inl ⟨t', tBwd _ _ (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e)) hT, hS⟩
    · obtain ⟨-, -, -, -, -, -, tBwd, -, -, -⟩ := severUnheldSchedContext_objects hInv hSv
      exact .inl ⟨t', tBwd _ _ hT, hS⟩
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; exact .inl ⟨t', hT, hS⟩)
    | (cases h; done)
    | skip
  rename_i oldScId holder _ _ _ _ _ _ _ _ st1 hRet
  cases h
  replace hT := (SchedContextOps.settleReturnedContext_agree _ _ _).symm.get_of_not_sc
    (fun _ e => KernelObject.noConfusion e) hT
  by_cases hy : y = replyDonationRecipient st oldScId target
  · refine .inr (.inl ⟨oldScId, holder, rfl, hy, ?_⟩)
    refine returnDonatedSchedContextResolved_lift (P := fun s1 =>
      s1.objects[y.toObjId]? = some (.tcb t') → s = oldScId) hRet (fun n s1 hS1 hT1 => ?_) hT
    have hC := returnDonatedSchedContext_tcb_binding_cases st s1 holder oldScId _ n hInv hS1
      y.toObjId t' hT1
    by_cases hH : y.toObjId = holder.toObjId
    · rw [hC.1 hH] at hS; cases hS
    · rw [hC.2.1 hH (by rw [hy]), donationReturnBinding_scId?] at hS
      exact (Option.some.inj hS).symm
  refine .inl (returnDonatedSchedContextResolved_lift (P := fun s1 =>
      s1.objects[y.toObjId]? = some (.tcb t') →
        ∃ t0, st.objects[y.toObjId]? = some (.tcb t0) ∧ t0.schedContextBinding.scId? = some s)
    hRet (fun n s1 hS1 hT1 => ?_) hT)
  have hC := returnDonatedSchedContext_tcb_binding_cases st s1 holder oldScId _ n hInv hS1
    y.toObjId t' hT1
  by_cases hH : y.toObjId = holder.toObjId
  · rw [hC.1 hH] at hS; cases hS
  · obtain ⟨t0, h0, hb⟩ := hC.2.2 hH (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e))
    exact ⟨t0, h0, by rw [hb]; exact hS⟩

/-- **The reply-receive's lend admission covers the lend it gates**: where the
admission, read on the state the arm is handed (before the reply leg), passes,
the context a dequeued `Call` lends at the receive leg is one its caller's label
flows to.  The dequeued call is the send queue's head the admission read, and it
holds there the context it lends, unless the pop handed it that context: then it
is the context's recorded origin, whose flow `hOrigin` gives (the answered
caller the pop may also hand it to is `.ready`, so it is dequeued by no
receive). -/
theorem replyRecvLendAdmits_flows_dequeued {ctx : LabelingContext}
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId}
    {tid prevCaller nextThread : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {msg : IpcMessage}
    {grant : Bool} {c : CoreId} {st st1 st1q st1p st2 : SystemState}
    {sgi sgi' : Option (CoreId × Concurrency.SgiKind)}
    {ret : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {xs summ : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hR : endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation rid prevCaller st1 = .ok (ret, st1q))
    (hX : replyRecvReplyTransfer answer st tid prevCaller grant st1q = .ok (xs, st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) c
      (receiveReturnSchedContext true st1p tid) = (st2, .ok (nextThread, summ, sgi')))
    (hOrigin : ∀ sc o, donationOriginRecipient? st1 sc = some o →
      securityFlowsTo (ctx.threadLabelOf o) (ctx.objectLabelOf sc.toObjId) = true)
    (hAdm : receiveLendAdmits ctx st epId = true) :
    rendezvousDequeuedCall st2 nextThread = true →
      ∀ s, callDonationSchedContext? st2 nextThread tid = some s →
      securityFlowsTo (ctx.threadLabelOf nextThread) (ctx.objectLabelOf s.toObjId) = true := by
  intro _ s hS
  have hInv1 : st1.objects.invExt := by
    have := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg c st hInv
    rw [hR] at this; exact this
  have hInvQ := replyRecvPopDonation_preserves_objects_invExt rid prevCaller st1 st1q ret hInv1 hPop
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have hInvP := receiveTransferCaps_objects_invExt hInvQ hX
  have hIR := receiveReturnSchedContext_objects_invExt true st1p tid hInvP
  rw [← replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  obtain ⟨hQp, hRp, hEp⟩ := replyRecvReceiveLegFacts hInv hQ hR hPop hX hReady
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  obtain ⟨hQR, -, hEB⟩ := receiveReturnSchedContext_receiveLegFacts true st1p tid hInvP hQp hRp
  cases hSender : receiveRendezvousSender? (receiveReturnSchedContext true st1p tid) epId with
  | none =>
    have hDq := endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked epId tid
      (some rid) c _ st2 nextThread summ sgi' hSender hRecv
    subst hDq
    rw [callDonationSchedContext?_self] at hS
    cases hS
  | some sender =>
    obtain ⟨ep, hEpR, hHead⟩ : ∃ ep, (receiveReturnSchedContext true st1p tid).getEndpoint? epId
        = some ep ∧ ep.sendQ.head = some sender := by
      unfold receiveRendezvousSender? at hSender
      cases hE : (receiveReturnSchedContext true st1p tid).getEndpoint? epId with
      | none => rw [hE] at hSender; simp at hSender
      | some ep => rw [hE] at hSender; exact ⟨ep, rfl, hSender⟩
    have hDq := endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head epId tid (some rid) c _ st2
      nextThread summ sgi' ep sender hEpR hHead hRecv
    subst hDq
    have hBind := endpointReceiveDualWithCapsOnCore_sameSchedContextBindings_of_rendezvous epId tid
      (some rid) c _ ep nextThread hIR hEpR hHead
    rw [hRecv] at hBind
    have hPre := callDonationSchedContext?_some_of_sameSchedContextBindings hBind nextThread tid s hS
    obtain ⟨-, ⟨cT, hCT, hCB⟩⟩ := callDonationSchedContext?_some_char _ _ _ _ hPre
    have hEpObj := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEpR
    have hCTo := lookupTcb_some_objects _ _ _ hCT
    have hNR := lookupTcb_some_not_reserved _ _ _ hCT
    rcases (hQR epId ep nextThread cT hEpObj hCTo).2 hHead with hSend | hCall
    · have hNo := endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend epId tid
        (some rid) c _ ep nextThread cT epId hIR hEpR hHead hCT hSend
      rw [hRecv] at hNo
      rename_i hCallPost
      simp only [hCallPost] at hNo
      cases hNo
    -- back across the return before the receive leg
    obtain ⟨yP, hyP, hxy⟩ := receiveReturnSchedContext_tcb true st1p tid hInvP _ cT hCTo
    have hYPCall : yP.ipcState = .blockedOnCall epId := by
      rcases hxy with rfl | rfl <;> exact hCall
    have hYPB : yP.schedContextBinding.scId? = some s := by
      rcases hxy with rfl | rfl
      · exact hCB
      · simp [TCB.schedContextBinding, SchedContextBinding.scId?] at hCB
    -- back across the reply's capability transfer
    obtain ⟨yQ, hyQ, hYQB⟩ := receiveTransferCaps_sameSchedContextBindings hInvQ hX nextThread yP hyP
    obtain ⟨yQ', hyQ', hYQI⟩ := (receiveTransferCaps_ipcFrame hInvQ hX).2.2 nextThread yP hyP
    rw [hyQ] at hyQ'
    cases hyQ'
    -- back across the pop
    obtain ⟨y1, hy1, hY1I⟩ := (replyRecvPopDonation_frame hInv1 hPop).2.2 nextThread yQ hyQ
    have hY1Call : y1.ipcState = .blockedOnCall epId := by rw [hY1I, hYQI, hYPCall]
    -- the answered caller is `.ready` after the reply leg
    have hPrevReady : ∀ x, st1.objects[prevCaller.toObjId]? = some (.tcb x) → x.ipcState = .ready :=
      fun x hx => endpointReplyOnCore_ok_target_ready tid prevCaller msg c st hInv (by rw [hR])
        (by rw [hR]; exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hx)
    have hNotPrev : nextThread ≠ prevCaller := by
      intro e; subst e
      rw [hPrevReady y1 hy1] at hY1Call; cases hY1Call
    rcases replyRecvPopDonation_binding_cases hInv1 hPop nextThread yQ s hyQ
        (by rw [hYQB]; exact hYPB) with ⟨y0, hy0, hY0B⟩ | ⟨sc, _, -, hRec, rfl⟩ | ⟨-, hRec⟩
    · rw [hy1] at hy0
      cases hy0
      -- back across the reply leg
      obtain ⟨z, hz, hZB⟩ := endpointReplyOnCore_sameSchedContextBindings tid prevCaller msg c st
        hInv nextThread y1 (by rw [hR]; exact hy1)
      obtain ⟨z', hz', -, -, hZI⟩ := endpointReplyOnCore_tcb_backward tid prevCaller msg c st hInv
        nextThread y1 (by rw [hR]; exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hy1)
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hz'] at hz
      cases hz
      have hZCall : z.ipcState = .blockedOnCall epId := by
        rcases hZI with hZI | ⟨hZI, -⟩
        · rw [hZI] at hY1Call; cases hY1Call
        · rw [← hZI]; exact hY1Call
      have hZL := lookupTcb_of_objects_of_not_reserved _ _ _
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hz') hNR
      have hEpSt := hEp epId ep (hEB epId ep hEpObj)
      rw [receiveLendAdmits_of_head ((SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hEpSt) hHead
        hZL hZCall] at hAdm
      exact callLendAdmits_flows_of_binding hAdm hZL (by rw [hZB]; exact hY0B)
    · cases hO : donationOriginRecipient? st1 s with
      | none =>
        rw [replyDonationRecipient_eq_of_no_origin _ _ _ hO] at hRec
        exact absurd hRec hNotPrev
      | some o =>
        rw [replyDonationRecipient_eq_origin _ hO] at hRec
        subst hRec
        exact hOrigin s _ hO
    · exact absurd hRec hNotPrev

namespace LendersFrame

/-- The donation pop between the legs: the return of the head frame's context,
or the unheld head's pop. -/
theorem replyRecvPopDonation {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyRecvPopDonation rid target st = .ok (r, st')) :
    LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvPopDonation at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        exact (returnDonatedSchedContextResolved hInv hRet).andThen fun hI =>
          settleReturnedContext _ _ _ hI
    · cases h
  · split at h
    · cases h
    · rename_i st1 hPop
      cases h
      exact popUnheldReplyHead hInv hPop

/-- The deschedule of the thread the pop unbound. -/
theorem replyRecvHolderDeschedule (tid holder : SeLe4n.ThreadId) (st : SystemState)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.replyRecvHolderDeschedule tid holder st) := by
  unfold _root_.SeLe4n.Kernel.replyRecvHolderDeschedule
  split
  · exact refl hInv
  · exact descheduleAtPlacement st holder hInv

/-- The receive leg's priority hand-off. -/
theorem applyReceiveLegPipHandoff (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.applyReceiveLegPipHandoff st receiver dequeued
      alreadyWalked executingCore) := by
  unfold _root_.SeLe4n.Kernel.applyReceiveLegPipHandoff
  split
  · exact refl hInv
  split
  · exact propagatePipChainCrossCore st receiver executingCore _ hInv
  · exact refl hInv

/-- The answer to the replied-to caller: its delivered message staged, or its
fault answered. -/
theorem replyRecvAnswerCaller (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none =>
    exact of_kept (chainObjectsKept.stageDeliveredMessage _ _ _ hInv)
      (RecordsFrame.stageDeliveredMessage _ _ _ hInv)
  | some o => exact faultReplyApplyOnCore st prevCaller o hInv

end LendersFrame

/-- The holder's deschedule writes run-queue links alone. -/
theorem replyRecvHolderDeschedule_objectsAgreeOffRunLinks (tid holder : SeLe4n.ThreadId)
    (st : SystemState) :
    (replyRecvHolderDeschedule tid holder st).objectsAgreeOffRunLinks st := by
  unfold replyRecvHolderDeschedule
  split
  · exact .refl _
  · exact descheduleAtPlacement_objectsAgreeOffRunLinks st holder

/-- **The post-receive half carries the lenders' flow**: the lend of the dequeued
`Call`'s context to the receiver (after the holder's deschedule, which writes
run-queue links alone, so the lend and its admission read the same thread
records), or the deschedule, then the priority walk. -/
theorem replyRecvPostReceiveDonation_preserves_contextLendersFlow {ctx : LabelingContext}
    {lend : Bool} {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (hP : LendersPremises st)
    (hPH : ∀ sc holder, returned? = some (sc, holder) →
      LendersPremises (replyRecvHolderDeschedule tid holder st))
    (hIn : contextLendersFlow ctx st)
    (hFlow : lend = true → rendezvousDequeuedCall st nextThread = true →
      ∀ s, callDonationSchedContext? st nextThread tid = some s →
      securityFlowsTo (ctx.threadLabelOf nextThread) (ctx.objectLabelOf s.toObjId) = true)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st lend
      = .ok ((), st')) :
    contextLendersFlow ctx st' := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · split at h
    · rename_i hCall
      split at h
      · cases h
      rename_i st2 hD
      cases h
      have hD' : applyReceiveRendezvousDonation st tid nextThread lend = .ok st2 := by
        unfold applyReceiveRendezvousDonation; rw [hCall]; exact hD
      have h1 := applyReceiveRendezvousDonation_preserves_contextLendersFlow hP hIn hFlow hD'
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _
        (applyReceiveRendezvousDonation_preserves_objects_invExt _ _ _ _ hP.invExt hD')) h1
    · cases h
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hP.invExt)
        hIn
  · rename_i sc holder
    have hRL := replyRecvHolderDeschedule_objectsAgreeOffRunLinks tid holder st
    have hPX := hPH sc holder rfl
    have hInX : contextLendersFlow ctx (replyRecvHolderDeschedule tid holder st) :=
      (LendersFrame.replyRecvHolderDeschedule tid holder st hP.invExt).stage hIn
    split at h
    · rename_i hCall
      split at h
      · cases h
      rename_i st2 hD
      cases h
      have hCallX : rendezvousDequeuedCall (replyRecvHolderDeschedule tid holder st) nextThread
          = true := by rw [rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hRL]; exact hCall
      have hD' : applyReceiveRendezvousDonation (replyRecvHolderDeschedule tid holder st) tid
          nextThread lend = .ok st2 := by
        unfold applyReceiveRendezvousDonation; rw [hCallX]; exact hD
      have h1 := applyReceiveRendezvousDonation_preserves_contextLendersFlow hPX hInX
        (fun hL _ s hS => hFlow hL hCall s
          (callDonationSchedContext?_some_of_sameSchedContextBindings
            (sameSchedContextBindings.of_objectsAgreeOffRunLinks hRL) nextThread tid s hS)) hD'
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _
        (applyReceiveRendezvousDonation_preserves_objects_invExt _ _ _ _ hPX.invExt hD')) h1
    · cases h
      have F := LendersFrame.descheduleAtPlacement st holder hP.invExt
      exact (F.andThen fun hI => LendersFrame.propagatePipChainCrossCore _ recordedServer
        serverCore _ hI).stage hIn

/-- **What the reply-receive's answering leg reads at the states it runs
from**: the recorded origin's flow to its context where the pop runs, the
donation chain's shape where the receive leg runs (after seL4-MCS's return), and
the chain facts where the lend runs (after the receive leg, and after the
holder's deschedule where the pop unbound one).  Premises read off those
states (`docs/REGISTERED_DEBT.md` table C, owner WS-PK). -/
def ReplyRecvLendersPremises (ctx : LabelingContext) (st : SystemState)
    (answer : Option Architecture.FaultReplyOutcome) (epId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool) (c : CoreId) : Prop :=
  ∀ st1 sgi, endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi) →
    (∀ sc o, donationOriginRecipient? st1 sc = some o →
      securityFlowsTo (ctx.threadLabelOf o) (ctx.objectLabelOf sc.toObjId) = true) ∧
    ∀ ret st1q, replyRecvPopDonation rid prevCaller st1 = .ok (ret, st1q) →
    ∀ xs st1p, replyRecvReplyTransfer answer st tid prevCaller grant st1q = .ok (xs, st1p) →
      donationChainWellFormed (receiveReturnSchedContext true st1p tid) ∧
      ∀ st2 res, endpointReceiveDualWithCapsOnCore epId tid (some rid) c
          (receiveReturnSchedContext true st1p tid) = (st2, res) →
        LendersPremises st2 ∧
        ∀ sc holder, ret = some (sc, holder) →
          LendersPremises (replyRecvHolderDeschedule tid holder st2)

/-- **The reply-receive's answering leg carries the lenders' flow** (seL4-MCS
`handleReplyRecv`): the reply leg, the pop, the reply's capability transfer, the
return, the receive leg, the lend at the receive's admission read before the
reply leg, the priority hand-off and the answer to the replied-to caller. -/
theorem endpointReplyRecvAnsweringOnCore_lendersStage {ctx : LabelingContext} {lend : Bool}
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hP : ReplyRecvLendersPremises ctx st answer epId tid rid prevCaller msg grant c)
    (hLend : lend = true → receiveLendAdmits ctx st epId = true)
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant c st lend
      = .ok (summary, st')) :
    LendersStage ctx st st' := by
  unfold endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have A := LendersFrame.endpointReplyOnCore (replier := tid) (target := prevCaller) (msg := msg)
    (c := c) hInv
  revert h A
  cases hR : endpointReplyOnCore tid prevCaller msg c st with
  | mk st1 res1 =>
  cases res1 with
  | error _ => intro h; cases h
  | ok sgi =>
  intro h A
  dsimp only at h A
  obtain ⟨hOrig, hP1⟩ := hP st1 sgi hR
  split at h
  · cases h
  rename_i ret st1q hPop
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  dsimp only at h
  obtain ⟨hChainR, hP2⟩ := hP1 ret st1q hPop xs st1p hX
  have F0 := LendersFrame.replyRecvPopDonation A.invExt hPop
  have hX' := hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX'
  have F1 : LendersFrame st1q st1p :=
    LendersFrame.of_kept (chainObjectsKept.receiveTransferCaps F0.invExt hX')
      (RecordsFrame.receiveTransferCaps F0.invExt hX')
  have FR := LendersFrame.receiveReturnSchedContext true st1p tid F1.invExt
  have S1 : LendersStage ctx st (receiveReturnSchedContext true st1p tid) :=
    ((A.stage.trans F0.stage).trans F1.stage).trans FR.stage
  revert h
  cases hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) c
      (receiveReturnSchedContext true st1p tid) with
  | mk st2 res2 =>
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, sgi'⟩ := q
  intro h
  dsimp only at h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  obtain ⟨hP3, hPH⟩ := hP2 st2 _ hRecv
  intro hF
  have h1 := endpointReceiveDualWithCapsOnCore_preserves_contextLendersFlow epId tid (some rid) c
    _ FR.invExt hChainR (S1 hF)
  rw [hRecv] at h1
  have h2 := replyRecvPostReceiveDonation_preserves_contextLendersFlow hP3 hPH h1
    (fun hL => replyRecvLendAdmits_flows_dequeued hInv hQ hReady hR hPop hX hRecv hOrig
      (hLend hL)) hPost
  have hI3 := (RecordsFrame.replyRecvPostReceiveDonation hP3.invExt hPost).invExt
  have F4 := LendersFrame.applyReceiveLegPipHandoff st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) c hI3
  exact (F4.andThen fun hI => LendersFrame.replyRecvAnswerCaller answer _ prevCaller _ hI).stage h2

/-- **The `.replyRecv` arm's transition carries the lenders' flow**: the
answering leg at the answer the replied-to caller's fault record selects. -/
theorem replyRecvTransferOnCore_lendersStage {ctx : LabelingContext} {lend : Bool}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hP : ReplyRecvLendersPremises ctx st (replyRecvCallerFaultAnswer? st prevCaller label msg)
      epId tid rid prevCaller
      (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg) grant c)
    (hLend : lend = true → receiveLendAdmits ctx st epId = true)
    (h : replyRecvTransferOnCore epId tid rid prevCaller label msg grant c st lend
      = .ok (summary, st')) :
    LendersStage ctx st st' := by
  unfold replyRecvTransferOnCore at h
  exact endpointReplyRecvAnsweringOnCore_lendersStage hInv hQ hReady hP hLend h

end SeLe4n.Kernel
