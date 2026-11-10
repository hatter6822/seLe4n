-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyUnheldInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.LongReplyInPlace

/-!
# A reply that transfers capabilities, delivered in place, whatever it returns

seL4-MCS's `doReplyTransfer` hands a loaned scheduling context back down its
stack (`reply_pop`) when the reply object heads it, then runs `doIPCTransfer`:
`transferCaps`, then the message.  The in-place reply on a donated reply object
(`performReplyDonatedDelivered`) and on a caller recording no server
(`performReplyUnheldDelivered`) write the return in place; here the transfer
runs in place after them (`capTransferK`) and the frame, or the long frame with
its overflow words, is written last with the transfer's report.

The return writes a scheduling context, reply links, thread bindings, release
links and scheduler flags, never a thread's buffer address, a VSpace root, a
CNode or the machine (`ipcBufferReadsAgree_replyDonationPopInPlace`,
`ipcBufferReadsAgree_returnUnheldSchedContextInPlace`), so the transfer reads
every slot and every word where the reply found it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood
open Architecture.RegisterDecode

/-! ## The return keeps every read -/

theorem ipcBufferReadsAgree_updateSchedContext (X : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : X.objects.noResizeDue) :
    ipcBufferReadsAgree (X.updateSchedContext scId f) X := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · exact ipcBufferReadsAgree_modifyObject X _ _ (fun o => by cases o <;> rfl) hNo
  · exact .refl X

theorem ipcBufferReadsAgree_markCandidacyGainFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) : ipcBufferReadsAgree (markCandidacyGainFor st tid e) st :=
  .of_eq (markCandidacyGainFor_objects st tid e) (markCandidacyGainFor_machine st tid e)

/-- Objects that agree off their release links agree on every view. -/
theorem ipcBufferReadsAgree_of_offReleaseLinks {X X' : SystemState}
    (h : X'.objectsAgreeOffReleaseLinks X) (hM : X'.machine = X.machine) :
    ipcBufferReadsAgree X' X := by
  refine ⟨fun x => ?_, hM⟩
  have hx := congrArg (fun o => o.bind ipcBufferViewOf) (h x)
  have hv : ∀ o : KernelObject, ipcBufferViewOf o.withoutRelease = ipcBufferViewOf o := by
    intro o; cases o <;> rfl
  simp only [Option.bind_map, Function.comp_def, hv] at hx
  exact hx

theorem ipcBufferReadsAgree_settleReturnedContext (st : SystemState) (c : Concurrency.CoreId)
    (s : SeLe4n.SchedContextId) :
    ipcBufferReadsAgree (SchedContextOps.settleReturnedContext st c s) st :=
  ipcBufferReadsAgree_of_offReleaseLinks (SchedContextOps.settleReturnedContext_agree st c s)
    (SchedContextOps.settleReturnedContext_machine st c s)

/-- The writes below a pop's first link: the context, then the reply links. -/
theorem ipcBufferReadsAgree_popLinks (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hr : SeLe4n.ReplyId) (prev : Option SeLe4n.ReplyId)
    (g h : Reply → Reply) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree
      (match prev with
        | none => (st.updateSchedContext scId f).modifyObject hr.toObjId (SystemState.mapReplyObject g)
        | some b => ((st.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject g)).modifyObject b.toObjId (SystemState.mapReplyObject h)) st ∧
    (match prev with
        | none => (st.updateSchedContext scId f).modifyObject hr.toObjId (SystemState.mapReplyObject g)
        | some b => ((st.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject g)).modifyObject b.toObjId
              (SystemState.mapReplyObject h)).objects.noResizeDue := by
  have h1 := updateSchedContext_noResizeDue st scId f hNo
  have h2 := modifyObject_noResizeDue _ hr.toObjId (SystemState.mapReplyObject g) h1
  have a1 := ipcBufferReadsAgree_updateSchedContext st scId f hNo
  have a2 := (ipcBufferReadsAgree_modifyObject _ hr.toObjId (SystemState.mapReplyObject g)
    (fun o => by cases o <;> rfl) h1).trans a1
  cases prev with
  | none => exact ⟨a2, h2⟩
  | some b =>
    exact ⟨(ipcBufferReadsAgree_modifyObject _ b.toObjId (SystemState.mapReplyObject h)
      (fun o => by cases o <;> rfl) h2).trans a2, modifyObject_noResizeDue _ _ _ h2⟩

/-- **The donation pop keeps every read**: it writes the context, the reply
links, the owner's and the holder's bindings and scheduler flags. -/
theorem ipcBufferReadsAgree_returnDonatedSchedContextInPlace (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (returnDonatedSchedContextInPlace st holder owner scId) st := by
  unfold returnDonatedSchedContextInPlace
  split
  · exact .refl st
  split
  · exact .refl st
  rename_i hr _
  split
  · exact .refl st
  rename_i r _
  split
  · exact .refl st
  split
  · exact .refl st
  dsimp only
  refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markCandidacyGainFor _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markCandidacyGainFor _ _ _).trans ?_
  refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans
    ((ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans ?_)
  · exact fun _ => ⟨rfl, rfl⟩
  · exact updateTcb_noResizeDue _ _ _ (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).2
  · exact fun _ => ⟨rfl, rfl⟩
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).2
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).1

/-- **The unheld pop keeps every read**, as the donation pop does. -/
theorem ipcBufferReadsAgree_returnUnheldSchedContextInPlace (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (returnUnheldSchedContextInPlace st owner scId) st := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact .refl st
  split
  · exact .refl st
  rename_i hr _
  split
  · exact .refl st
  rename_i r _
  split
  · exact .refl st
  dsimp only
  refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markCandidacyGainFor _ _ _).trans ?_
  refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans ?_
  · exact fun _ => ⟨rfl, rfl⟩
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).2
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).1

theorem ipcBufferReadsAgree_replyDonationPopInPlace (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (replyDonationPopInPlace st c holder scId home) st := by
  have hP : ipcBufferReadsAgree (popDonationSettledInPlace st c holder scId home) st :=
    (ipcBufferReadsAgree_settleReturnedContext _ home scId).trans
      (ipcBufferReadsAgree_returnDonatedSchedContextInPlace st holder c scId hNo)
  unfold replyDonationPopInPlace descheduleAtPlacement descheduleAt
  split
  · exact (ipcBufferReadsAgree_removeRunnableOnCore _ _ _).trans hP
  · exact hP

theorem ipcBufferReadsAgree_storeReplyLegReady (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReplyLegReady st c rid) st := by
  unfold storeReplyLegReady
  dsimp only
  generalize hS1 : st.updateTcb c receiverReady = S1
  have a1 : ipcBufferReadsAgree S1 st :=
    hS1 ▸ ipcBufferReadsAgree_updateTcb st c receiverReady (fun _ => ⟨rfl, rfl⟩) hNo
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ updateTcb_noResizeDue _ _ _ hNo
  generalize hS2 : enqueueRunnableOnCore S1 (determineTargetCore S1 c) c = S2
  have a2 : ipcBufferReadsAgree S2 S1 :=
    hS2 ▸ ipcBufferReadsAgree_enqueueRunnableOnCore S1 _ c hNo1
  have hNo2 : S2.objects.noResizeDue := hS2 ▸ enqueueRunnableOnCore_noResizeDue _ _ _ hNo1
  generalize hS3 : S2.modifyObject rid.toObjId replyConsumedObject = S3
  have a3 : ipcBufferReadsAgree S3 S2 :=
    hS3 ▸ ipcBufferReadsAgree_modifyObject S2 rid.toObjId replyConsumedObject
      (fun o => by cases o <;> rfl) hNo2
  have hNo3 : S3.objects.noResizeDue := hS3 ▸ modifyObject_noResizeDue _ _ _ hNo2
  exact (ipcBufferReadsAgree_updateTcb S3 c (fun t => { t with replyObjectCode := 0 })
    (fun _ => ⟨rfl, rfl⟩) hNo3).trans (a3.trans (a2.trans a1))

/-! ## The transfer and the frame after a reply's writes -/

/-- **The specification's reply transfer on a state holding the message is the
in-place one**: on the reply's writes `X`, made in place and reading every slot
and word where the reply found them, the caller holding a message of at most
four words, the transfer on no endpoint then the caller's stage with its report
is the in-place transfer then the frame with the report. -/
theorem replyHeldCaps_eq_delivered (st X : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (stcb ct : TCB) (count : Nat)
    (hNoX : X.objects.noResizeDue) (hA : ipcBufferReadsAgree X st)
    (hSz : Architecture.regMessageLength layout len ≤ 4) :
    (match receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
        (X.mapTcbInPlace c (holdMessage
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged })) with
      | .ok (s, st'') =>
        (.ok ((), Architecture.stageDeliveredMessage st'' c s.capInfo) :
          Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), capTransferK X c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count
        ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
        deliverCapsFrame
          (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
          (capStepsApply c.toObjId false ct.vspaceRoot ct.ipcBuffer x0 x1 x2 a0 b0 a1 b1 a2 b2
            dcn dsl 0 n free X)
          c layout rf len badgeWord badged) := by
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverCapsFrame i Y c layout rf len badgeWord badged)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf]
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoX]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoX hT
  rw [hT]
  simp only [mapStepState]
  rw [stageDeliveredMessage_holdMessage_caps _ _ _ _ hNo1
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    returnFrameOfMessage_regMessageBody_caps]
  rfl

/-- **As `replyHeldCaps_eq_delivered`, for a message of more than four words**:
the inline words, then the words the replier's buffer holds, which the transfer
leaves where they were (`ipcWordReadsAgree_receiveTransferCaps`). -/
theorem replyHeldCapsLong_eq_delivered (st X : SystemState) (c replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (stcb ct : TCB) (count : Nat)
    (hNoX : X.objects.noResizeDue) (hA : ipcBufferReadsAgree X st) (hLen : 4 ≤ len) :
    (match receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
        (X.mapTcbInPlace c (holdMessage (longSendMessage SeLe4n.arm64DefaultLayout rf st replier
          len (SeLe4n.Badge.opt badgeWord badged)))) with
      | .ok (s, st'') =>
        (.ok ((), Architecture.stageDeliveredMessage st'' c s.capInfo) :
          Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), capTransferK X c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count
        ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
        deliverLongCapsFrame
          (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
          (capStepsApply c.toObjId false ct.vspaceRoot ct.ipcBuffer x0 x1 x2 a0 b0 a1 b1 a2 b2
            dcn dsl 0 n free X)
          c SeLe4n.arm64DefaultLayout rf len replier badgeWord badged) := by
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverLongCapsFrame i Y c SeLe4n.arm64DefaultLayout rf len replier badgeWord
      badged)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf]
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoX]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoX hT
  rw [hT]
  simp only [mapStepState]
  rw [deliverLongCapsFrame_eq Y1 st c replier SeLe4n.arm64DefaultLayout rf len badgeWord badged
    s.capInfo hNo1 ((ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoX hT).trans hA.words) rfl hLen]

/-! ## The donated reply that transfers capabilities -/

/-- **The donated reply that transfers capabilities, delivered**: the caller
woken without the message, the loaned context handed back down the stack in
place (`replyDonationPopInPlace`), the server's priority walk, the transfer in
place on no endpoint, then the caller's frame with the transfer's report.  The
replier and the caller enter as the words the transfer reads of them, read
before the reply's writes. -/
@[noinline] def performReplyDonatedCapsDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (replyDonationPopInPlace (storeReplyRendezvousReady st c server rid) c server scId home)
    server core).1
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      c layout rf len badgeWord badged

/-- **The checked donated reply that transfers capabilities, in place**: under
the flow gate and `replyPopsInPlace`, a granting reply of at most four words to
an unfaulted caller blocked on it, whose reply object heads the stack of the
context the server holds on loan, from a replier whose frame routes as a reply,
commits `performReplyDonatedCapsDelivered`'s state. -/
theorem replyTransferChecked_donatedCaps_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (msg : IpcMessage)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hMsg : msg =
      { registers := Architecture.regMessageBody layout rf len,
        badge := SeLe4n.Badge.opt badgeWord badged })
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .reply capAddr mi) :
    replyTransferOnCoreChecked ctx replier c mi' regs msg true core st =
      .ok ((), performReplyDonatedCapsDelivered st c server rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) layout rf len badgeWord
        badged core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  obtain ⟨rp, scId, _, hRp, hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR, hDon, _⟩ :=
    replyPopsInPlace_donation st c server rid msg ct hT hSRes hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  have hSz' : ¬ msg.registers.size > maxMessageRegisters := by
    rw [hMsg, Architecture.regMessageBody_size]
    have : (4 : Nat) ≤ maxMessageRegisters := by decide
    omega
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st replier c server ct ep rid rp msg core hSz' hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  have hNoP := replyDonationPopInPlace_noResizeDue _ c server scId (determineTargetCore st c) hNoS
  have hAX := (ipcBufferReadsAgree_propagatePipChainCrossCore _ server core hNoP).trans
    ((ipcBufferReadsAgree_replyDonationPopInPlace _ c server scId (determineTargetCore st c)
      hNoS).trans (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo))
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  rw [replyDonationPopInPlace_msg c id _ id _ c server scId _ hNoS hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoP]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReply st replier stcb capAddr mi hS hR, hTgt]
  subst hMsg
  unfold performReplyDonatedCapsDelivered
  exact replyHeldCaps_eq_delivered st _ c layout rf len badgeWord badged stcb ct _
    (propagatePipChainCrossCore_noResizeDue _ _ _ hNoP) hAX hSz4

/-! ## The reply to a caller recording no server that transfers capabilities -/

/-- **The reply to a caller recording no server that transfers capabilities,
delivered**: the caller woken without the message, the context no thread holds
handed back to it in place and settled on its home, the transfer in place on
no endpoint, then the caller's frame with the transfer's report. -/
@[noinline] def performReplyUnheldCapsDelivered (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := SchedContextOps.settleReturnedContext
    (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      c layout rf len badgeWord badged

/-- **The checked reply to a caller recording no server that transfers
capabilities, in place**: under the flow gate and `replyUnheldPopsInPlace`, a
granting reply of at most four words to an unfaulted caller blocked on it with
no server recorded, from a replier whose frame routes as a reply, commits
`performReplyUnheldCapsDelivered`'s state. -/
theorem replyTransferChecked_unheldCaps_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (msg : IpcMessage)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hMsg : msg =
      { registers := Architecture.regMessageBody layout rf len,
        badge := SeLe4n.Badge.opt badgeWord badged })
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .reply capAddr mi) :
    replyTransferOnCoreChecked ctx replier c mi' regs msg true core st =
      .ok ((), performReplyUnheldCapsDelivered st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) layout rf len badgeWord badged stcb.vspaceRoot stcb.ipcBuffer
        stcb.cspaceRoot (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer
        ct.cspaceRoot) := by
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, -, hPop⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  have hSz' : ¬ msg.registers.size > maxMessageRegisters := by
    rw [hMsg, Architecture.regMessageBody_size]
    have : (4 : Nat) ≤ maxMessageRegisters := by decide
    omega
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st replier c none ct ep rid rp msg core hSz' hT hIpc
    hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  have hRec : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyLegReady_noResizeDue st c rid hNo
  have hNoP := returnUnheldSchedContextInPlace_noResizeDue _ c scId hNoS
  have hNoQ := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId hNoP
  have hAX := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId hNoS).trans
      (ipcBufferReadsAgree_storeReplyLegReady st c rid hNo))
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hAns, hcv, SystemState.unlinkReplyWaiterOpt]
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  rw [returnUnheldSchedContextInPlace_msg c id _ id _ c scId hNoS, settleReturnedContext_msg]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReply st replier stcb capAddr mi hS hR, hTgt]
  subst hMsg
  unfold performReplyUnheldCapsDelivered
  exact replyHeldCaps_eq_delivered st _ c layout rf len badgeWord badged stcb ct _ hNoQ hAX hSz4

/-! ## The request a routed long reply makes -/

/-- The extra-capability count a routed long reply frame names is the count its
message-info word holds (`routedExtraCaps`). -/
theorem routedExtraCaps_eq_of_routedReplyLong {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi) :
    routedExtraCaps rf = mi.extraCaps := by
  unfold registerRoutedSyscall at hR
  split at hR
  · unfold registerRoutedSyscallOf at hR
    dsimp only at hR
    cases hD : decodeMsgInfoWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
    | error e => rw [hD] at hR; cases hR
    | ok m =>
      rw [hD] at hR
      have hm : m = mi := by
        simp only [routedShortTail_eq, routedLongTail_eq] at hR
        by_cases hLen : m.length ≤ SeLe4n.arm64DefaultLayout.msgRegs.size <;>
          first | rw [if_pos hLen] at hR | rw [if_neg hLen] at hR
        repeat' split at hR
        all_goals first
          | (cases hR; rfl)
          | (cases hR; done)
          | (rcases unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
          | skip
        all_goals done
      subst hm
      unfold decodeMsgInfoWord at hD
      split at hD
      · cases hD; rfl
      · cases hD
  · cases hR

/-- The extra-capability count a routed long reply-receive frame names is the count its
message-info word holds (`routedExtraCaps`). -/
theorem routedExtraCaps_eq_of_routedReplyRecvLong {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi) :
    routedExtraCaps rf = mi.extraCaps := by
  unfold registerRoutedSyscall at hR
  split at hR
  · unfold registerRoutedSyscallOf at hR
    dsimp only at hR
    cases hD : decodeMsgInfoWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
    | error e => rw [hD] at hR; cases hR
    | ok m =>
      rw [hD] at hR
      have hm : m = mi := by
        simp only [routedShortTail_eq, routedLongTail_eq] at hR
        by_cases hLen : m.length ≤ SeLe4n.arm64DefaultLayout.msgRegs.size <;>
          first | rw [if_pos hLen] at hR | rw [if_neg hLen] at hR
        repeat' split at hR
        all_goals first
          | (cases hR; rfl)
          | (cases hR; done)
          | (rcases unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
          | skip
        all_goals done
      subst hm
      unfold decodeMsgInfoWord at hD
      split at hD
      · cases hD; rfl
      · cases hD
  · cases hR

/-- **The request a routed long reply makes**: under the grant right, the
replier's frame asks for the count its message-info word names, its overflow
slots all reading; without it, none. -/
theorem replyCapRequest_of_routedReplyLong (st : SystemState) (replier : SeLe4n.ThreadId)
    (stcb : TCB) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (sid : SyscallId) (g : Bool)
    (hS : st.getTcb? replier = some stcb) (hRf : stcb.registerContext = rf)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv))
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st replier j = .ok w) :
    replyCapRequest st replier g =
      frameCapRequestOf st stcb (if g then routedExtraCaps rf else 0) := by
  have hX : routedExtraCaps rf = mi.extraCaps := by
    rcases hR with ⟨h, -⟩ | ⟨h, -⟩
    · exact routedExtraCaps_eq_of_routedReplyLong h
    · exact routedExtraCaps_eq_of_routedReplyRecvLong h
  have hD : blockedSenderDecode st replier stcb = .ok (longMessageDecode sid st replier rf capAddr mi) := by
    unfold blockedSenderDecode
    rw [hRf]
    rcases hR with h | h
    · exact decodeSyscallArgsFromState_of_routedReplyLong_ok st replier rf capAddr mi sid (.inl h)
        hRead
    · exact decodeSyscallArgsFromState_of_routedReplyLong_ok st replier rf capAddr mi sid
        (.inr (.inl h)) hRead
  unfold replyCapRequest
  rw [hS]
  unfold senderFrameCapRequest
  cases g
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, frameCapRequestOf_zero]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hD, hX]
    rfl

end SeLe4n.Kernel
