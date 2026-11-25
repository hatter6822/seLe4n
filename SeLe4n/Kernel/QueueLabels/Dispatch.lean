-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Capability

/-! # The checked dispatch keeps the endpoint waiters

WS-SX SX11.2 (D38).  The twin of `KernelRecords/Dispatch.lean` for
`endpointWaitersLabelsEqual`.  The capability table's arms are frames
(`dispatchCapabilityOnly_queueLabelsFrame`); of the IPC arms, the send and
the call block their caller only past their own two-way gate, and the receive
and the reply-receive past the gate the dispatch checks before either runs, so
each new waiter has its endpoint's label (`endpointFlowGate_implies_eq`).  The
store's invariant at each intermediate state is the frames' own.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The checked send keeps the store's invariant: a gated growth or nothing. -/
theorem endpointSendCrossCoreDispatchChecked_waitersInvExt {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload c st).1.objects.invExt := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact (QueueLabelsGrowFrame.endpointSendDualWithCapsOnCore hInv).invExt
  · exact hInv

/-- The checked call keeps the store's invariant: a gated growth or nothing. -/
theorem endpointCallCrossCoreDispatchChecked_waitersInvExt {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload c st).1.objects.invExt := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact (QueueLabelsGrowFrame.endpointCallCrossCoreDispatch hInv).invExt
  · exact hInv

/-- **A step that keeps every record view keeps every endpoint waiter.** -/
theorem EndpointWaitersShrink.of_views {st st' : SystemState}
    (hv : ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]?) :
    EndpointWaitersShrink st st' := fun x t' _ hT hW => by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have h1 := hv x.toObjId
  rw [hO, recordViewOf_tcb] at h1
  obtain ⟨tcb, hT0, hEq⟩ := KernelRecords.tcb_of_view h1.symm
  have hi : tcb.ipcState = _ := congrArg TcbRecordView.ipc hEq
  exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT0, hi ▸ hW⟩

namespace QueueLabelsFrame

/-- **A busy reply's holder cancelled** (seL4-MCS `receiveIPC`'s
`cancelIPC(replyTCB)`): its IPC cancelled, its server's boost reverted, the
holder made inactive. -/
theorem cancelReplyHolder (st : SystemState) (holder : SeLe4n.ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, -, -, e⟩
  · rw [e]; exact refl hInv
  rw [e]
  have S1 := cancelIpcKeepingContexts st holder tcb hInv
  have S2 : QueueLabelsFrame st (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) := by
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact S1.trans (of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ S1.invExt))
    · exact S1
  exact S2.trans (updateTcb _ holder S2.invExt (f := fun t => { t with threadState := .Inactive })
    fun _ => TcbWaitsKept.of_ipc rfl)

theorem cancelRecvBusyReply (ctx : LabelingContext) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (ec : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.cancelRecvBusyReply ctx tid gate decoded ec st) := by
  rcases cancelRecvBusyReply_cases ctx tid gate decoded ec st with e | ⟨hd, -, e⟩ <;> rw [e]
  · exact refl hInv
  · exact cancelReplyHolder st hd ec hInv

theorem maybeDonateSchedContext (x : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hI : x.objects.invExt) : QueueLabelsFrame x (SeLe4n.Kernel.maybeDonateSchedContext x n t) :=
  of_frame (maybeDonateSchedContext_induct (fun a b => RecordsFrame a b) x n t
    (RecordsFrame.refl hI) (fun vS vT _ _ => RecordsFrame.schedContextBindPerform x vS vT hI))

theorem maybeReturnSchedContext (x : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hI : x.objects.invExt) : QueueLabelsFrame x (SeLe4n.Kernel.maybeReturnSchedContext x n t) :=
  of_frame (maybeReturnSchedContext_induct (fun a b => RecordsFrame a b) x n t
    (RecordsFrame.refl hI) (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS t hI))

theorem receiveReturnSchedContext (blocks : Bool) (x : SystemState) (t : SeLe4n.ThreadId)
    (hI : x.objects.invExt) :
    QueueLabelsFrame x (SeLe4n.Kernel.receiveReturnSchedContext blocks x t) :=
  of_frame (receiveReturnSchedContext_induct (fun a b => RecordsFrame a b) blocks x t
    (RecordsFrame.refl hI) (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS t hI))

/-- **A receive that completes its bound notification**: the checked wait's
consumption, the badge register, then the donation or the return. -/
theorem _root_.SeLe4n.Kernel.QueueLabelsGatedFrame.completeSignalArm {ctx : LabelingContext}
    {tid : SeLe4n.ThreadId} {nid : SeLe4n.ObjId} {c : CoreId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.completeSignalArm ctx tid nid c st = .ok ((), st')) :
    QueueLabelsGatedFrame ctx st st' := by
  have hW := QueueLabelsGatedFrame.notificationWaitCrossCoreDispatchChecked (ctx := ctx)
    (nid := nid) (waiter := tid) (c := c) hInv
  unfold SeLe4n.Kernel.completeSignalArm at h
  split at h
  · rename_i hR
    cases h
    rw [hR] at hW
    exact (hW.andThen fun hI => QueueLabelsFrame.of_frame
      (RecordsFrame.writeReturnFrameToTcb _ _ _ hI)).andThen
      fun hI => QueueLabelsFrame.maybeDonateSchedContext _ _ _ hI
  · rename_i hR
    cases h
    rw [hR] at hW
    exact hW.andThen fun hI => QueueLabelsFrame.maybeReturnSchedContext _ _ _ hI
  · cases h

/-- **seL4's `sendSignal`**: the wake's step, then the donation's. -/
theorem sendSignalOnCore {n : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.sendSignalOnCore n badge c st).1 :=
  sendSignalOnCore_induct (QueueLabelsFrame st) n badge c st
    (notificationSignalBoundOnCore hInv)
    (fun t _ _ _ => (notificationSignalBoundOnCore hInv).andThen fun hI =>
      maybeDonateSchedContext _ n t hI)

theorem notificationSignalDeclassifiedCrossCoreDispatch {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st
      (SeLe4n.Kernel.notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy nid badge c st).1 :=
  have hS := notificationSignalDeclassifiedOnCore (ctx := ctx) (declPolicy := declPolicy)
    (nid := nid) (badge := badge) (c := c) hInv
  notificationSignalDeclassifiedCrossCoreDispatch_induct (QueueLabelsFrame st) ctx declPolicy nid
    badge c st hS (fun t _ _ _ => hS.andThen fun hI => maybeDonateSchedContext _ nid t hI)

theorem notificationSignalBoundCrossCoreDispatchChecked {ctx : LabelingContext}
    {nid : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st
      (SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked ctx nid signaler badge c st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (QueueLabelsFrame st) ctx nid signaler
    badge c st (refl hInv) (sendSignalOnCore hInv)

/-- **A reply-receive whose receive completes its bound notification**: the
reply leg, then the completion. -/
theorem _root_.SeLe4n.Kernel.QueueLabelsGatedFrame.replyRecvCompletesSignalArm {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st
      = .ok ((), st')) : QueueLabelsGatedFrame ctx st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  have F := replyTransferOnCoreChecked hInv hR
  rcases hOr with rfl | ⟨_, -, hC⟩
  · exact .of_frame F
  · exact (QueueLabelsGatedFrame.of_frame F).trans (QueueLabelsGatedFrame.completeSignalArm F.invExt hC)

end QueueLabelsFrame

namespace QueueLabelsStage

variable {ctx : LabelingContext}

/-- **A receive run on its busy-reply-cancelled state**, admitted by the gate
the dispatch checked: the holder's cancel, then the notification's completion,
the non-blocking miss, or the return, the rendezvous (the gate gives the
receiver the endpoint's label) and the handoff. -/
theorem receiveResolvedArm (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (gate : SyscallGate) (epId : SeLe4n.ObjId) (st st' : SystemState)
    (hInv : st.objects.invExt)
    (hGate : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (h : SeLe4n.Kernel.receiveResolvedArm ctx decoded gate tid epId ec
      (cancelRecvBusyReply ctx tid gate decoded ec st) = .ok ((), st')) :
    QueueLabelsStage ctx st st' := by
  unfold SeLe4n.Kernel.receiveResolvedArm at h
  have hS := QueueLabelsFrame.cancelRecvBusyReply ctx tid gate decoded ec st hInv
  have hIC := hS.invExt
  generalize cancelRecvBusyReply ctx tid gate decoded ec st = stC at h hS hIC
  by_cases hSig : receiveCompletesSignal ctx stC tid = true
  · cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, ↓reduceIte] at h
    exact ((QueueLabelsGatedFrame.of_frame hS).trans (QueueLabelsGatedFrame.completeSignalArm hIC h)).stage
  simp only [Bool.not_eq_true] at hSig
  by_cases hNb : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC
      epId = true
  · cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, Bool.false_eq_true, hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq,
      true_and] at h
    subst h
    exact (hS.trans (.of_frame (RecordsFrame.writeReturnFrameToTcb _ _ _ hIC))).stage
  simp only [Bool.not_eq_true] at hNb
  simp only [hSig, hNb, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  rename_i r hRes
  split at h
  · rename_i st1 dequeued summ sgi hRecv
    split at h
    · cases h
    rename_i stDon hHand
    cases h
    have F1 := hS.trans (QueueLabelsFrame.receiveReturnSchedContext
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC)
    have G := QueueLabelsGrowFrame.endpointReceiveDualWithCapsOnCore (endpointId := epId)
      (receiver := tid) (replyId := r) (c := ec) F1.invExt
    rw [hRecv] at G
    refine QueueLabelsGrowFrame.stage (F1.thenGrow (G.thenFrame ?_))
      (endpointFlowGate_implies_eq ctx epId _ _ hGate).symm
    exact (QueueLabelsFrame.of_frame (RecordsFrame.applyReceiveRendezvousHandoff G.invExt
      hHand)).andThen fun hI => .of_frame (RecordsFrame.stageDeliveredMessage _ _ _ hI)
  · cases h

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage {st s st' : SystemState} {woken? : Option SeLe4n.ThreadId}
    {stage : SystemState → SystemState} (hS : QueueLabelsStage ctx st s) (hIs : s.objects.invExt)
    (hStage : ∀ x, x.objects.invExt → QueueLabelsFrame x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    QueueLabelsStage ctx st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans (((QueueLabelsFrame.of_frame
      (RecordsFrame.clearWokenReceiverStash woken? hIs hClr)).andThen fun hI => hStage _ hI).stage)

end QueueLabelsStage

open Architecture.RegisterDecode in
/-- **Every arm `dispatchWithCapChecked` routes keeps the endpoint waiters'
labels**: the capability table's frames, and the IPC arms, each new waiter
admitted by a two-way gate. -/
theorem dispatchWithCapChecked_queueLabelsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (gate : SyscallGate) (cap : Capability) (st st' : SystemState) (hInv : st.objects.invExt)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    QueueLabelsStage ctx st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    by_cases hB : decoded.syscallId = .tcbBindNotification ∧ ∃ o, cap.target = .object o
    · obtain ⟨hSy, o, hT⟩ := hB
      unfold dispatchCapabilityOnlyChecked at h
      simp only [hSy, hT] at h
      exact (QueueLabelsGatedFrame.tcbBindNotificationArmChecked hInv h).stage
    · exact (dispatchCapabilityOnly_queueLabelsFrame decoded cap tid executingCore k st st' hC
        (fun o hSy hT => hB ⟨hSy, o, hT⟩) hInv (dispatchCapabilityOnlyChecked_ok hC h)).stage
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact ((QueueLabelsFrame.of_frame (RecordsFrame.auditReadFromCore hInv hA)).andThen
      fun hI => .of_frame (RecordsFrame.writeCallReturnWord _ _ _ hI)).stage
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact ((QueueLabelsFrame.of_frame (RecordsFrame.auditDrainVisiblePrefix hInv hA)).andThen
      fun hI => .of_frame (RecordsFrame.writeCallReturnWord _ _ _ hI)).stage
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h; exact QueueLabelsStage.refl _
    split at h
    · cases h
    rename_i hSend
    have hS := QueueLabelsStage.endpointSendCrossCoreDispatchChecked (ctx := ctx)
      (endpointId := epId) (sender := tid)
      (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
      (c := executingCore) hInv
    have hI := endpointSendCrossCoreDispatchChecked_waitersInvExt (ctx := ctx) (endpointId := epId)
      (sender := tid) (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
      (c := executingCore) hInv
    rw [hSend] at hS hI
    exact QueueLabelsStage.clearStashStage hS hI
      (fun x hx => .of_frame (RecordsFrame.stageWokenDelivery x _ _ hx)) h
  case none.receive.object epId =>
    split at h
    · cases h
    rename_i hG
    exact QueueLabelsStage.receiveResolvedArm decoded tid executingCore gate epId st st' hInv
      (by simpa using hG) h
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      have hS := QueueLabelsStage.endpointCallCrossCoreDispatchChecked (ctx := ctx)
        (endpointId := epId) (caller := tid)
        (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
        (c := executingCore) hInv
      have hI := endpointCallCrossCoreDispatchChecked_waitersInvExt (ctx := ctx) (endpointId := epId)
        (caller := tid) (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
        (c := executingCore) hInv
      rw [hCall] at hS hI
      exact hS.trans (QueueLabelsFrame.of_frame (RecordsFrame.stageWokenDelivery _ _ _ hI)).stage
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact (QueueLabelsFrame.replyTransferOnCoreChecked hInv h).stage
  case none.replyRecv.object epId =>
    split at h
    · cases h
    rename_i hG
    have hGate : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) =
        true := by simpa using hG
    split at h
    · exact QueueLabelsStage.receiveResolvedArm decoded tid executingCore gate epId st st' hInv
        hGate h
    split at h
    · cases h
    · exact QueueLabelsStage.receiveResolvedArm decoded tid executingCore gate epId st st' hInv
        hGate h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    · exact (QueueLabelsGatedFrame.replyRecvCompletesSignalArm hInv h).stage
    rename_i hX
    cases h
    unfold replyRecvTransferOnCore at hX
    exact (QueueLabelsGrowFrame.stage ((QueueLabelsGrowFrame.endpointReplyRecvAnsweringOnCore
      hInv hX).andThen fun hI => .of_frame (RecordsFrame.stageDeliveredMessage _ _ _ hI))
      (endpointFlowGate_implies_eq ctx epId _ _ hGate).symm)
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact (QueueLabelsFrame.of_frame (RecordsFrame.cspaceMintWithCdt hInv h)).stage
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact (QueueLabelsFrame.of_frame (RecordsFrame.cspaceCopy hInv h)).stage
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact (QueueLabelsFrame.of_frame (RecordsFrame.cspaceMove hInv h)).stage
    · cases h
  case none.serviceRegister.serviceRegistry _ =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    replace h := serviceEndpointArm_ok h
    obtain ⟨_, epId, -, h⟩ := h
    try dsimp only at h
    unfold registerServiceChecked at h
    split at h
    · exact (QueueLabelsFrame.of_frame (RecordsFrame.registerService hInv h)).stage
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (QueueLabelsFrame.of_fst_eq
        (QueueLabelsFrame.notificationSignalBoundCrossCoreDispatchChecked hInv) hSig).stage
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · cases h; exact (QueueLabelsFrame.of_frame (RecordsFrame.writeReturnFrameToTcb _ _ _ hInv)).stage
    exact (QueueLabelsGatedFrame.completeSignalArm hInv h).stage
  case none.declassify.auditTrail code =>
    split at h
    · cases h
    exact (QueueLabelsFrame.of_frame (RecordsFrame.declassifyObjectFromCore hInv h)).stage
  case none.declassifySignal.auditTrail code =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (QueueLabelsFrame.of_fst_eq
        (QueueLabelsFrame.notificationSignalDeclassifiedCrossCoreDispatch hInv) hSig).stage
    · cases h

/-- **The checked syscall dispatch keeps the endpoint waiters' labels**: the
yield, the capability resolution (a read), the routed arm, and the taint pass,
which writes the taint words alone. -/
theorem dispatchSyscallChecked_queueLabelsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    QueueLabelsStage ctx st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact (QueueLabelsFrame.of_frame (RecordsFrame.yieldOnCore hInv hYieldOk)).stage
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  refine (dispatchWithCapChecked_queueLabelsStage ctx decoded tid executingCore _ cap _ stPost
    hInv hD).trans (QueueLabelsStage.of_parts (EndpointWaitersShrink.of_views ?_).waiters
      (NtfnLabelsKept.of_views ?_ ctx) (EndpointQueueLabelsKept.of_views ?_ ctx)) <;>
    exact RecordsFrame.views_of_erasure RecordsFrame.erasure_taint
      (applySyscallTaint_objectsAgreeOffTaint _ _ _)

end SeLe4n.Kernel
