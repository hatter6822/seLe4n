-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Dispatch
import SeLe4n.Kernel.KernelRecords.SyscallEntry
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry
import SeLe4n.Kernel.IPC.Invariant.FaultPreservation

/-! # Every committing entry keeps the endpoint waiters

WS-SX SX11.2 (D38).  The seven committed entry states carry
`endpointWaitersLabelsEqual`: every thread blocked sending, calling or receiving
on an endpoint has that endpoint's label after the entry if it did before.  The
timer, reschedule, FP/SIMD and interrupt entries block no thread on an endpoint;
the syscall and the two fault entries block one only past the two-way gate the
entry checks on it (the send, the call, the receive, the reply-receive and the
fault delivery).  Each entry reads the store's invariant at the state it runs
from; the syscall entry reads it after the dispatch off the records' own stage
(`syscallDispatchFromAbi_recordsStage`), as the lenders' entry does.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The settlement, the activation and the ledger drains every committing entry
ends with. -/
theorem QueueLabelsFrame.entryTail (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadAt (PriorityInheritance.settleResidencyAt st coreId) coreId))) :=
  .of_frame (RecordsFrame.chain (fun h => RecordsFrame.settleResidencyAt st coreId h)
    (fun h => (RecordsFrame.activateThreadAt _ coreId h).trans
      (RecordsFrame.clearLedgers _ (RecordsFrame.activateThreadAt _ coreId h).invExt)) hInv)

/-! ### The timer, reschedule, FP/SIMD and interrupt entries -/

/-- The per-core timer step: the clock, the tick, the domain accounting. -/
theorem QueueLabelsFrame.perCoreTimerTickStep (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : QueueLabelsFrame st (tickClockedState st ⟨coreId.toNat, hc⟩) :=
      .of_objects_eq hInv (tickClockedState_objects _ _)
    exact (hClk.andThen fun h => QueueLabelsFrame.timerTickOnCore _ _ h).andThen fun h =>
      .of_frame (RecordsFrame.scheduleDomainOnCore h (scheduleDomainOnCore_eq_state _ _))
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact .refl hInv

/-- **The timer entry's committed state keeps the endpoint waiters' labels.** -/
theorem perCoreTimerTickEntryState_queueLabelsStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((QueueLabelsFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (QueueLabelsFrame.perCoreTimerTickStep _ coreId h).andThen fun h' =>
      QueueLabelsFrame.entryTail _ coreId h').stage

/-- **The reschedule entry's committed state keeps the endpoint waiters'
labels**: every step is a records' frame. -/
theorem perCoreRescheduleEntryState_queueLabelsStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((QueueLabelsFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (QueueLabelsFrame.of_frame (RecordsFrame.perCoreRescheduleStep _ coreId h)).andThen
      fun h' => QueueLabelsFrame.entryTail _ coreId h').stage

/-- **The FP/SIMD entry's committed state keeps the endpoint waiters' labels.** -/
theorem fpAccessEntryState_queueLabelsStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv
  have hStep : RecordsFrame (Concurrency.saveCapturedTrapFrameAt st coreId frame)
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 := by
    unfold fpAccessEntryStep
    split
    · exact RecordsFrame.refl F1.invExt
    · exact (RecordsFrame.fpAccessOnCore _ _ live F1.invExt).trans
        (RecordsFrame.dispatchVacatedCore _ _ (RecordsFrame.fpAccessOnCore _ _ live F1.invExt).invExt)
  have F3 := (F1.trans hStep).trans (RecordsFrame.settleResidencyAt _ coreId hStep.invExt)
  exact (QueueLabelsFrame.of_frame (F3.trans (RecordsFrame.activateThreadAt _ coreId F3.invExt))).stage

/-- The interrupt step: seL4's `sendSignal`, which blocks no thread on an
endpoint, then the mask. -/
theorem QueueLabelsFrame.interruptEntryStep (st : SystemState)
    (coreId intId : UInt64) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.interruptEntryStep st coreId intId) :=
  interruptEntryStep_of (P := QueueLabelsFrame st) st coreId intId (.refl hInv) fun c _ _ =>
    handleInterruptOnCore_of (P := QueueLabelsFrame st) st c _
      (fun _ h => h.andThen fun hI => .of_objects_eq hI rfl) (.refl hInv)
      (fun _ _ _ => QueueLabelsFrame.sendSignalOnCore hInv)

/-- **The interrupt entry's committed state keeps the endpoint waiters'
labels.** -/
theorem interruptEntryState_queueLabelsStage (lctx : LabelingContext) (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage lctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) :=
  ((QueueLabelsFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (QueueLabelsFrame.interruptEntryStep _ coreId intId h).andThen fun h' =>
      QueueLabelsFrame.entryTail _ coreId h').stage

/-! ### The fault entries

Each step is read as its stage with the store's invariant at the state it
reaches, which the next step's frame reads. -/

/-- **The register spill, then the flow-checked delivery**: the delivery's gate,
two-way, gives the faulting thread its handler endpoint's label before the call
can block it. -/
theorem faultDeliveredState_queueLabelsStage (ctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (faultDeliveredState ctx st f ectx w c tid) ∧
      (faultDeliveredState ctx st f ectx w c tid).objects.invExt := by
  have F := QueueLabelsFrame.writeFaultRegistersToTcb st tid w hInv
  exact ⟨F.stage.trans (QueueLabelsStage.faultDeliverOnCoreChecked F.invExt),
    faultDeliverOnCoreChecked_preserves_objects_invExt ctx _ tid f _ c F.invExt⟩

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem faultEntryDeliver_queueLabelsStage (ctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (faultEntryDeliver ctx st f ectx w c).2 ∧
      (faultEntryDeliver ctx st f ectx w c).2.objects.invExt := by
  unfold faultEntryDeliver
  split
  · have F := RecordsFrame.dispatchVacatedCore st c hInv
    exact ⟨(QueueLabelsFrame.of_frame F).stage, F.invExt⟩
  · rename_i tid _
    dsimp only
    split
    · exact ⟨.refl _, hInv⟩
    · obtain ⟨S, hI⟩ := faultDeliveredState_queueLabelsStage ctx st f ectx w c tid hInv
      have F := RecordsFrame.scheduleLocalSuccessorFrom (some tid) _ c hI
      exact ⟨S.trans (QueueLabelsFrame.of_frame F).stage, F.invExt⟩

theorem faultEntryStep_queueLabelsStage (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (faultEntryStep ctx st ectx w coreId).2 ∧
      (faultEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold faultEntryStep
  split
  · split
    · split
      · exact ⟨.refl _, hInv⟩
      · exact faultEntryDeliver_queueLabelsStage ctx st _ ectx w _ hInv
    · exact ⟨.refl _, hInv⟩
  · exact ⟨.refl _, hInv⟩

theorem unknownSyscallEntryStep_queueLabelsStage (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (unknownSyscallEntryStep ctx st ectx w coreId).2 ∧
      (unknownSyscallEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_queueLabelsStage ctx st _ _ w _ hInv
    · exact ⟨.refl _, hInv⟩
  · exact ⟨.refl _, hInv⟩

/-- **The fault entry's committed state keeps the endpoint waiters' labels.** -/
theorem faultEntryState_queueLabelsStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep ctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId (some frame) hInv
  obtain ⟨S, hI⟩ := faultEntryStep_queueLabelsStage ctx _ ectx w coreId F1.invExt
  exact ((QueueLabelsFrame.of_frame F1).stage.trans S).trans
    (QueueLabelsFrame.entryTail _ coreId hI).stage

/-- **The unknown-syscall entry's committed state keeps the endpoint waiters'
labels.** -/
theorem unknownSyscallEntryState_queueLabelsStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep ctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedSyscallFrameAt st coreId (some frame) hInv
  obtain ⟨S, hI⟩ := unknownSyscallEntryStep_queueLabelsStage ctx _ ectx w coreId F1.invExt
  exact ((QueueLabelsFrame.of_frame F1).stage.trans S).trans
    (QueueLabelsFrame.entryTail _ coreId hI).stage

/-! ### The syscall entry -/

/-- **A refused receive's busy-reply cancel whose refusal raises a capability
fault** (`cancelReceiveBusyReply_cases_of_fault`): nothing, a reply holder's
cancel, or a reply-receive's after-reply stop where the fault fires
(`ReplyRecvAfterReplyEntry.fault_stop`): the state handed in, the state the
signal arm's reply left, or the nothing-received state after the reply step,
each a chain of frames (WS-SX SX36.1). -/
theorem QueueLabelsFrame.cancelReceiveBusyReply (ctx : LabelingContext) (e : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) {ke : KernelError} {t : SeLe4n.ThreadId}
    {f : Fault} (hCur : st.scheduler.currentOnCore e = some t)
    (hE : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke)
    (hF : Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st
      (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) t ke = some f) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) := by
  rcases cancelReceiveBusyReply_cases_of_fault hInv hCur hE hF with hE' | ⟨_, holder, -, -, hE'⟩ | hB
  · rw [hE']; exact QueueLabelsFrame.refl hInv
  · rw [hE']; exact QueueLabelsFrame.cancelReplyHolder st holder e hInv
  rcases hB.fault_stop hInv hCur hE hF with ⟨s0, hTS, hS | ⟨prev, mi, regs, msg, grant, st1, hR,
      hS⟩ | ⟨rid, prev, label, msg, grant, st1, popped, st1p, sgi, ret?, xs, hR, hPop, hX, hS⟩⟩ <;>
    refine hTS (QueueLabelsFrame st) (fun _ _ x hx => hx.trans (.of_frame
      (RecordsFrame.of_agreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _)
        (by rw [applySyscallTaint_frame]) (applySyscallTaint_invExt hx.invExt)
        (by rw [applySyscallTaint_machine])))) ?_ <;> rw [hS]
  · exact QueueLabelsFrame.refl hInv
  · exact QueueLabelsFrame.replyTransferOnCoreChecked hInv hR
  have F1 : QueueLabelsFrame st st1 := (QueueLabelsFrame.endpointReplyOnCore (replier := t)
    (target := prev) (msg := replyRecvLegMessage (replyRecvCallerFaultAnswer? st prev label msg) msg)
    (c := e) hInv).of_fst_eq hR
  have F2 := F1.trans (QueueLabelsFrame.of_frame (RecordsFrame.replyRecvPopDonation F1.invExt hPop))
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have F3 := F2.trans (QueueLabelsFrame.of_frame (RecordsFrame.receiveTransferCaps F2.invExt hX))
  have F4 : QueueLabelsFrame st (replyRecvAnswerCaller (replyRecvCallerFaultAnswer? st prev label msg)
      st1p prev xs.capInfo) := by
    refine F3.trans ?_
    cases replyRecvCallerFaultAnswer? st prev label msg with
    | none => exact .of_frame (RecordsFrame.stageDeliveredMessage st1p prev xs.capInfo F3.invExt)
    | some o => exact QueueLabelsFrame.faultReplyApplyOnCore st1p prev o F3.invExt
  exact F4.trans (.of_frame (RecordsFrame.replyRecvNothingReceived _ e ret? _ F4.invExt))

/-- **A refused reply-receive blocks at most its server, on its endpoint**
(WS-SX SX34): every leg it ran before it stopped is a frame but the receive,
which blocks at most the server on the endpoint, whether it returned or
refused (`QueueLabelsGrowFrame.endpointReceiveDualWithCapsOnCore`). -/
theorem QueueLabelsGrowFrame.replyRecvTransferStoppedState {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat}
    {msg : IpcMessage} {grant : Bool} {core : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    QueueLabelsGrowFrame tid epId st
      (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st) :=
  replyRecvTransferStoppedState_induct (QueueLabelsGrowFrame tid epId)
    (fun _ h => .refl h)
    (fun _ _ _ _ G G' => G.trans G')
    (fun r t m c _ h => (QueueLabelsFrame.endpointReplyOnCore (replier := r) (target := t)
      (msg := m) (c := c) h).growAt tid epId)
    (fun _ _ _ _ _ h hP => (QueueLabelsFrame.of_frame (RecordsFrame.replyRecvPopDonation h hP)).growAt
      tid epId)
    (fun _ _ _ _ _ h hX => (QueueLabelsFrame.of_frame (RecordsFrame.receiveTransferCaps h hX)).growAt
      tid epId)
    (fun a s t n h => by
      refine QueueLabelsFrame.growAt ?_ tid epId
      cases a with
      | none => exact .of_frame (RecordsFrame.stageDeliveredMessage s t n h)
      | some o => exact QueueLabelsFrame.faultReplyApplyOnCore s t o h)
    (fun s t h => (QueueLabelsFrame.of_frame (receiveReturnSchedContext_induct
      (fun a b => RecordsFrame a b) true s t (RecordsFrame.refl h)
      (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS t h))).growAt tid epId)
    (fun _ h => QueueLabelsGrowFrame.endpointReceiveDualWithCapsOnCore h)
    (fun s t h => (QueueLabelsFrame.of_frame (RecordsFrame.descheduleAtPlacement s t h)).growAt
      tid epId)
    (fun s t c h => (QueueLabelsFrame.of_frame
      (RecordsFrame.propagatePipChainCrossCore s t c _ h)).growAt tid epId) hInv

/-- **A refused reply-receive admitted by its gate carries the waiters' labels**:
the receive leg's gate, two-way, gives the server the endpoint's label. -/
theorem QueueLabelsStage.replyRecvTransferStoppedState {ctx : LabelingContext}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool} {core : CoreId}
    {st : SystemState} (hInv : st.objects.invExt)
    (hGate : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    QueueLabelsStage ctx st
      (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st) :=
  (QueueLabelsGrowFrame.replyRecvTransferStoppedState hInv).stage
    (endpointFlowGate_implies_eq ctx epId _ _ hGate).symm

/-- **A reply-receive whose receive is read after its reply carries the
waiters' labels where it stops** (WS-SX SX36.1): every leg before the receive
is a frame, and the receive, where it ran, ran on the endpoint the read on the
answered state admitted through its gate, so it blocks at most the server there,
whose label is the endpoint's. -/
theorem QueueLabelsStage.replyRecvTransferThenStoppedState {ctx : LabelingContext}
    {gate : SyscallGate} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (_root_.SeLe4n.Kernel.RefusalCarrying.stoppedState
      (replyRecvTransferThenR (replyRecvReceiveEndpoint ctx gate tid) tid rid prevCaller label msg
        grant c) st) ∧
      (_root_.SeLe4n.Kernel.RefusalCarrying.stoppedState
        (replyRecvTransferThenR (replyRecvReceiveEndpoint ctx gate tid) tid rid prevCaller label msg
          grant c) st).objects.invExt := by
  rcases replyRecvTransferThenR_stoppedState_cases (replyRecvReceiveEndpoint ctx gate tid) tid rid
      prevCaller label msg grant c st with hE | ⟨hA, e, hB⟩
  · rw [hE]; exact ⟨QueueLabelsStage.refl _, hInv⟩
  generalize _root_.SeLe4n.Kernel.RefusalCarrying.stoppedState
    (replyRecvTransferThenR (replyRecvReceiveEndpoint ctx gate tid) tid rid prevCaller label msg
      grant c) st = s at hB ⊢
  revert hB
  generalize replyRecvCallerFaultAnswer? st prevCaller label msg = answer
  generalize replyRecvLegMessage answer msg = m
  generalize (if answer.isSome = true then none else replyCapRequest st tid grant) = req
  generalize receiverCapTarget? st prevCaller = target
  generalize (recordedReplyServer? st prevCaller).getD tid = rs
  intro hB
  rcases endpointReplyRecvAnsweringBodyThenR_stopped hInv hA hB with
    ⟨-, hS⟩ | ⟨sgi, ret?, popped, -, hPop1, -, hTail⟩
  · rw [hS]; exact ⟨QueueLabelsStage.refl _, hInv⟩
  have F1 := QueueLabelsFrame.endpointReplyOnCore (replier := tid) (target := prevCaller)
    (msg := m) (c := c) hInv
  have F2 := F1.trans (QueueLabelsFrame.of_frame (RecordsFrame.replyRecvPopDonation F1.invExt hPop1))
  have hX := receiveTransferCaps_eq_done req none target popped
  generalize receiveTransferCapsDone req none target popped = Dn at hX hTail
  obtain ⟨xs, st1p⟩ := Dn
  dsimp only at hTail
  have F3 := F2.trans (QueueLabelsFrame.of_frame (RecordsFrame.receiveTransferCaps F2.invExt hX))
  have F4 : QueueLabelsFrame st (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) := by
    refine F3.trans ?_
    cases answer with
    | none => exact .of_frame (RecordsFrame.stageDeliveredMessage st1p prevCaller xs.capInfo F3.invExt)
    | some o => exact QueueLabelsFrame.faultReplyApplyOnCore st1p prevCaller o F3.invExt
  generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a at F4 hTail
  rcases hTail with ⟨-, -, hS⟩ | ⟨epId, hEok, hTail⟩
  · rw [hS]
    have F := F4.trans (.of_frame (RecordsFrame.replyRecvNothingReceived rs c ret? _ F4.invExt))
    exact ⟨F.stage, F.invExt⟩
  have F5 := F4.trans (QueueLabelsFrame.of_frame (receiveReturnSchedContext_induct
    (fun a b => RecordsFrame a b) true st1a tid (RecordsFrame.refl F4.invExt)
    (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS tid F4.invExt)))
  have G := (F5.growAt tid epId).trans
    (QueueLabelsGrowFrame.endpointReceiveDualWithCapsOnCore (replyId := some rid) (c := c) F5.invExt)
  have hL := (endpointFlowGate_implies_eq ctx epId _ _ (replyRecvReceiveEndpoint_flow hEok)).symm
  suffices hG : QueueLabelsGrowFrame tid epId st s from ⟨hG.stage hL, hG.invExt⟩
  rcases hTail with hS | ⟨st2, next, summary, sgi', hRv, hS | ⟨sc, holder, -, hS⟩⟩
  · rw [hS]
    exact G.thenFrame (.of_frame (RecordsFrame.replyRecvNothingReceived rs c ret? _ G.invExt))
  · rw [hRv] at G; rw [hS]
    exact G.thenFrame (.of_frame (RecordsFrame.replyRecvNothingReceived rs c ret? _ G.invExt))
  · rw [hRv] at G; rw [hS]
    have H := RecordsFrame.replyRecvHolderDeschedule tid holder st2 G.invExt
    exact G.thenFrame (.of_frame (H.trans (RecordsFrame.replyRecvNothingReceived rs c ret? _ H.invExt)))

/-- **The state a refusal of the checked entry reports carries the waiters'
labels** (WS-SX SX34): the state itself, its busy reply's holder cancelled, or
a reply-receive's stopped state, admitted by its receive gate. -/
theorem QueueLabelsStage.cancelReceiveBusyReply (ctx : LabelingContext) (e : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsStage ctx st (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) ∧
      (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st).objects.invExt := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with hE | ⟨_, holder, -, -, hE⟩ | hA | hB
  · rw [hE]; exact ⟨QueueLabelsStage.refl _, hInv⟩
  · rw [hE]
    have F := QueueLabelsFrame.cancelReplyHolder st holder e hInv
    exact ⟨F.stage, F.invExt⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, hFlow, hS⟩ := hA.stopped
    rw [hS]
    refine replyRecvEntryRefusalTaint_induct
      (fun x => QueueLabelsStage ctx st x ∧ x.objects.invExt)
      (fun _ _ x hx =>
        have F := RecordsFrame.of_agreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _)
          (by rw [applySyscallTaint_frame]) (applySyscallTaint_invExt hx.2)
          (by rw [applySyscallTaint_machine])
        ⟨hx.1.trans (QueueLabelsStage.of_frame F), F.invExt⟩) ?_
    exact ⟨QueueLabelsStage.replyRecvTransferStoppedState hInv hFlow,
      replyRecvTransferStoppedState_objects_invExt hInv⟩
  · obtain ⟨tid, -, decoded, gate, rid, prevCaller, replyBadge, replyGrant, -, -, -, -, -, -, hS⟩ := hB
    rw [hS]
    refine replyRecvAfterReplyRefusalTaint_induct
      (fun x => QueueLabelsStage ctx st x ∧ x.objects.invExt)
      (fun _ _ x hx =>
        have F := RecordsFrame.of_agreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _)
          (by rw [applySyscallTaint_frame]) (applySyscallTaint_invExt hx.2)
          (by rw [applySyscallTaint_machine])
        ⟨hx.1.trans (QueueLabelsStage.of_frame F), F.invExt⟩) ?_
    rcases replyRecvAnsweringThenR_stoppedState_cases ctx (replyRecvReceiveEndpoint ctx gate tid)
        decoded tid e rid prevCaller replyBadge replyGrant st with hE | ⟨st1, hR, hE⟩ | hE
    · rw [hE]; exact ⟨QueueLabelsStage.refl _, hInv⟩
    · rw [hE]
      have F := QueueLabelsFrame.replyTransferOnCoreChecked hInv hR
      exact ⟨F.stage, F.invExt⟩
    · rw [hE]; exact QueueLabelsStage.replyRecvTransferThenStoppedState hInv

/-- **The checked syscall entry keeps the endpoint waiters' labels**: the
dispatch of the request the running caller's registers decode to. -/
theorem syscallEntryChecked_queueLabelsStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    QueueLabelsStage ctx st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  split at h
  · cases h
  rename_i decoded hDec
  exact dispatchSyscallChecked_queueLabelsStage ctx decoded tid e st st' hInv h

/-- **The ABI dispatch keeps the endpoint waiters' labels**: the argument spill,
then the checked entry, or the busy-reply cancel and a dropped fault's record, a
capability fault's delivery (past its own gate) or the refusal's record. -/
theorem syscallDispatchFromAbi_queueLabelsStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome} (hInv : st.objects.invExt)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    QueueLabelsStage ctx st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact QueueLabelsStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact QueueLabelsStage.refl _
  have F1 : QueueLabelsFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact QueueLabelsFrame.updateTcb st tid hInv fun _ => TcbWaitsKept.of_ipc rfl
  dsimp only at h
  split at h
  · obtain ⟨FS, FI⟩ := QueueLabelsStage.cancelReceiveBusyReply ctx e _ F1.invExt
    have FSt := F1.stage.trans FS
    split at h
    · split at h
      · cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _
          (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6))
        rw [hL]
        exact FSt.trans (QueueLabelsStage.of_objects_eq rfl)
      · cases h
        unfold Platform.FFI.deliverSyscallCapFault
        have W := QueueLabelsFrame.writeFaultRegistersToTcb _ tid
          (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30) FI
        exact (FSt.trans W.stage).trans (QueueLabelsStage.faultDeliverOnCoreChecked W.invExt)
    · split at h
      · cases h
        exact FSt.trans (QueueLabelsStage.of_objects_eq
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _)))
      · cases h
        exact FSt.trans (QueueLabelsStage.of_objects_eq
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _))
  · rename_i hE
    cases h
    exact F1.stage.trans (syscallEntryChecked_queueLabelsStage F1.invExt hE)

/-- **The syscall step keeps the endpoint waiters' labels**: the ABI dispatch,
then the caller's return staging, the local scheduling point, the residency
settlement, the activation and the ledger drains, each a records' frame.  The
store's invariant after the dispatch is the records' own
(`syscallDispatchFromAbi_recordsStage`). -/
theorem syscallDispatchCrossCoreStep_queueLabelsStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (hK : st.kernelRecordsSound) (PR : RecordsArmPremises st)
    (hR : CurrentReady st) :
    QueueLabelsStage ctx st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have hI := KernelRecords.objects_invExt (syscallDispatchFromAbi_recordsStage PR hR hD hK)
  have F0 := RecordsFrame.stageCallerReturnFor (st.scheduler.currentOnCore e) _ e outcome hI
  have F1 := F0.trans (RecordsFrame.dropReturnedContextCaller
    (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st (st.scheduler.currentOnCore e))
    (st.scheduler.currentOnCore e) _ e F0.invExt)
  have F2 := F1.trans (RecordsFrame.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e) _ e F1.invExt)
  have F3 := F2.trans (RecordsFrame.settleResidencyOnCore _ e F2.invExt)
  have F4 := F3.trans (RecordsFrame.activateThreadOnCore _ e F3.invExt)
  exact (syscallDispatchFromAbi_queueLabelsStage (KernelRecords.objects_invExt hK) hD).trans
    (QueueLabelsFrame.of_frame (F4.trans (RecordsFrame.clearLedgers _ F4.invExt))).stage

/-- **The syscall entry's committed state keeps the endpoint waiters' labels**:
the trap-frame save, the entry's IPC-buffer words handed to the state, the
step, and the committed state dropping the words.  The records' premises and
the running callers are read off the state the step runs from. -/
theorem syscallDispatchEntryState_queueLabelsStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hK : st.kernelRecordsSound)
    (PR : RecordsArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hR : CurrentReady (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n)) :
    QueueLabelsStage ctx st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) := by
  have hI := KernelRecords.objects_invExt hK
  have F := RecordsFrame.saveCapturedSyscallFrame st e frame hI
  have F2 := F.trans (RecordsFrame.syncUserWords _ bytes n F.invExt)
  have hK1 := F2.preserves hK
  exact ((QueueLabelsFrame.of_frame F2).stage.trans
    (syscallDispatchCrossCoreStep_queueLabelsStage hK1 PR hR)).trans
    (QueueLabelsStage.of_objects_eq rfl)

end SeLe4n.Kernel
