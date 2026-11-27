-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.CapabilityDispatch
import SeLe4n.Kernel.ContextLenders.Fault
import SeLe4n.Kernel.KernelRecords.SyscallEntry
import SeLe4n.Kernel.QueueLabels.Entry

/-! # The syscall entry keeps the lenders' flow

WS-SX SX8.  The syscall entry's committed state is a lenders' stage: the
trap-frame save and the IPC-buffer words write no reply object and no context;
the argument spill writes one thread's registers; then the checked entry, or,
on a refusal, the busy reply's cancel and a dropped fault's record, a
capability fault's delivery or the refusal's record; then the caller's return
staging, the local scheduling point, the residency settlement, the activation
and the ledger drains.

The checked dispatch's premises (`LendersDispatchPremises`) and the capability
fault's delivery premises (`FaultLendPremises`) are read off the states those
steps run from, as the other entries read theirs (`docs/REGISTERED_DEBT.md`
table C, "`ipcReachable` is not carried across a trace of kernel entries",
owner WS-PK).  The creating sites' label equations read the endpoint waiters'
labels (`endpointWaitersLabelsEqual`, WS-SX SX11), taken at the entry's own
state beside the records and carried to the dispatch's and the delivery's
states by SX11's frames (WS-SX SX17).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **What the checked entry's dispatch reads**: for the caller the core runs
and the request its registers decode to, the dispatch premises at the state
the entry runs from. -/
def SyscallEntryLendPremises (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (e : CoreId) (regCount : Nat) (st : SystemState) : Prop :=
  ∀ tid p decoded, st.scheduler.currentOnCore e = some tid →
    lookupThreadRegisterContext tid st = .ok p →
    Architecture.RegisterDecode.decodeSyscallArgsFromState
      (threadOperationCode st tid layout p.1) st tid layout p.1 regCount = .ok decoded →
    ∀ tcb, st.getObject? tid.toObjId = some (.tcb tcb) → ∀ cap,
      LendersDispatchPremises ctx decoded tid e
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId } cap st

/-- **The checked syscall entry keeps the lenders' flow.** -/
theorem syscallEntryChecked_lendersStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (P : SyscallEntryLendPremises ctx layout e regCount st) (hR : CurrentReady st)
    (hW : endpointWaitersLabelsEqual ctx st)
    (hA : notificationLabelsAgree ctx st)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    LendersStage ctx st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  rename_i regs s0 hP
  split at h
  · cases h
  rename_i decoded hDec
  exact dispatchSyscallChecked_lendersStage ctx decoded tid e st st' hInv
    (P tid (regs, s0) decoded hCur hP hDec) (hR e tid hCur) hW hA h



/-- **A refused reply-receive carries equal lending labels** (WS-SX SX34): the
legs it ran before it stopped -- the reply leg, the pop (its owner the reply's
recorded caller, `calledFrame_labelEq`), the reply's capability transfer, the
caller's answer, the receiver's context return and the receive leg, whose
returned or refused state keeps the labels on a well-formed donation chain --
then the nothing-received outcome, which deschedules and walks the
priority-inheritance chain only.  No lend runs: a post-receive donation refuses
on the state it was handed (`applyRendezvousCallDonationR_stops_at_entry`). -/
theorem LendersStep.replyRecvTransferStoppedState {ctx : LabelingContext}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool} {core : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hC : replyAnsweredCaller? st rid = some prevCaller)
    (hP : ReplyRecvLendersPremises st (replyRecvCallerFaultAnswer? st prevCaller label msg)
      epId tid rid prevCaller
      (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg) grant core) :
    LendersStep ctx st
      (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st) := by
  refine ⟨fun hF => ?_, replyRecvTransferStoppedState_objects_invExt hInv⟩
  have hNR : ∀ (rs : SeLe4n.ThreadId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
      (s : SystemState), s.objects.invExt →
      LendersFrame s (replyRecvNothingReceived rs core ret? s) := by
    intro rs ret? s hS
    unfold replyRecvNothingReceived
    cases ret? with
    | none => exact LendersFrame.propagatePipChainCrossCore s rs core _ hS
    | some p =>
      obtain ⟨_, holder⟩ := p
      exact (LendersFrame.descheduleAtPlacement s holder hS).andThen fun h =>
        LendersFrame.propagatePipChainCrossCore _ rs core _ h
  rcases replyRecvTransferStoppedState_cases epId tid rid prevCaller label msg grant core st with
    hE | ⟨hA, e, hB⟩
  · rw [hE]; exact hF
  generalize _root_.SeLe4n.Kernel.replyRecvTransferStoppedState epId tid rid prevCaller label msg
    grant core st = s at hB ⊢
  rcases endpointReplyRecvAnsweringBodyR_stopped hInv hA hB with
    ⟨-, hS⟩ | ⟨sgi, ret?, popped, hR1, hPop1, hInvP, hTail⟩
  · rw [hS]; exact hF
  have A := LendersFrame.endpointReplyOnCore (replier := tid) (target := prevCaller)
    (msg := replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg)
    (c := core) hInv
  have F0 := LendersStep.replyRecvPopDonation (ctx := ctx) A.invExt hPop1
    (calledFrame_labelEq hF.1 hC A.links)
  have hXo := receiveTransferCaps_eq_done
    (if (replyRecvCallerFaultAnswer? st prevCaller label msg).isSome then none
      else replyCapRequest st tid grant) none (receiverCapTarget? st prevCaller) popped
  generalize receiveTransferCapsDone
    (if (replyRecvCallerFaultAnswer? st prevCaller label msg).isSome then none
      else replyCapRequest st tid grant) none (receiverCapTarget? st prevCaller) popped = D
    at hTail hXo
  have hX : replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st prevCaller label msg) st tid
      prevCaller grant popped = .ok (D.1, D.2) := by
    rw [replyRecvReplyTransfer_eq_receiveTransferCaps]; exact hXo
  obtain ⟨hChain, -⟩ := hP _ sgi (Prod.ext rfl hR1) ret? popped hPop1 D.1 D.2 hX
  have F1 : LendersFrame popped D.2 :=
    LendersFrame.of_kept (chainObjectsKept.receiveTransferCaps hInvP hXo)
      (RecordsFrame.receiveTransferCaps hInvP hXo)
  have FA := LendersFrame.replyRecvAnswerCaller (replyRecvCallerFaultAnswer? st prevCaller label msg)
    D.2 prevCaller D.1.capInfo F1.invExt
  have FR := LendersStep.receiveReturnSchedContext (ctx := ctx) true _ tid FA.invExt
  have S1 := FR.stage (FA.stage (F1.stage (F0.stage (A.stage hF))))
  have h1 := endpointReceiveDualWithCapsOnCore_preserves_lendingLabelsEqual epId tid (some rid)
    core _ FR.invExt hChain S1
  have hInvV := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt epId tid (some rid)
    core _ FR.invExt
  rcases hTail with hS | ⟨st2, next, summary, sgi', hV, hS⟩
  · rw [hS]; exact (hNR _ _ _ hInvV).stage h1
  rw [hV] at h1 hInvV
  rcases hS with hS | ⟨sc, holder, -, hS⟩
  · rw [hS]; exact (hNR _ _ _ hInvV).stage h1
  rw [hS]
  have HD := LendersFrame.replyRecvHolderDeschedule tid holder st2 hInvV
  exact (hNR _ _ _ HD.invExt).stage (HD.stage h1)

/-- **The state a refusal of the checked entry reports**, a labelled step:
nothing, a reply holder's cancel (its reply arm's pop to the frame's recorded
caller), or a reply-receive's stopped state, whose legs the entry's lending
premises cover (`LendersDispatchPremises.replyRecv`). -/
theorem LendersStep.cancelReceiveBusyReply (ctx : LabelingContext) (e : CoreId)
    (st : SystemState) (hInv : st.objects.invExt)
    (P : SyscallEntryLendPremises ctx SeLe4n.arm64DefaultLayout e 32 st) :
    LendersStep ctx st (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with hE | ⟨_, holder, -, -, hE⟩ | hA
  · rw [hE]; exact LendersStep.refl hInv
  · rw [hE]; exact LendersStep.cancelReplyHolder st holder e hInv
  · obtain ⟨tid, tcb, decoded, ref, -, hCur, hObj, hDec, -, -, cap, epId, rid, c, badge, grant, -,
      -, -, -, hTgt, -, -, hR, -, -, hS⟩ := hA
    have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
      simp only [lookupThreadRegisterContext, hObj]
    have hD := (P tid _ decoded hCur hRegs hDec tcb hObj cap).replyRecv epId rid c badge grant hTgt
      (by rw [← resolveReplyRecvReplyR_eq st tid _ decoded rfl
        (by simp only [callerCspaceRoot, hObj]), hR])
    rw [hS]
    exact LendersStep.replyRecvTransferStoppedState hInv (resolveReplyRecvReplyR_some_caller hR) hD

/-- **What the ABI dispatch reads**: for the caller the core runs, the checked
entry's premises at the state the arguments are spilled to, and a capability
fault's delivery premises at the state its registers are spilled to after a
refused receive's busy-reply cancel, with the context read off the spilled
registers (`Platform.FFI.deliverSyscallCapFault`). -/
structure SyscallAbiLendPremises (ctx : LabelingContext) (e : CoreId) (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64) (st : SystemState) : Prop where
  entry : ∀ tid, st.scheduler.currentOnCore e = some tid →
    SyscallEntryLendPremises ctx SeLe4n.arm64DefaultLayout e 32
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
  capFault : ∀ tid (f : Fault), st.scheduler.currentOnCore e = some tid →
    let stW := writeFaultRegistersToTcb (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid
      (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30)
    FaultLendPremises stW tid f
      (Architecture.faultContextOfThread stW tid (Platform.FFI.svcFaultIP elr) spsr) e

/-- **The ABI dispatch keeps the lenders' flow**: the argument spill, then the
checked entry, or the busy-reply cancel and a dropped fault's record, a
capability fault's delivery or the refusal's record.  The waiters (`hW`) are
carried across the spill, and across the cancel and the fault-register spill to
the delivery. -/
theorem syscallDispatchFromAbi_lendersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome} (hInv : st.objects.invExt)
    (P : SyscallAbiLendPremises ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st)
    (hR : CurrentReady st) (hW : endpointWaitersLabelsEqual ctx st)
    (hA : notificationLabelsAgree ctx st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    LendersStage ctx st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact LendersStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact LendersStage.refl _
  have F1 : LendersFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact LendersFrame.updateTcb st tid _ hInv
  have hR1 := hR.writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 x6 hInv
  have W1 : QueueLabelsFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact QueueLabelsFrame.updateTcb st tid hInv fun _ => TcbWaitsKept.of_ipc rfl
  dsimp only at h
  split at h
  · rename_i ke hE
    have F := (LendersStep.of_frame (ctx := ctx) F1).andThen fun hI =>
      LendersStep.cancelReceiveBusyReply ctx e _ hI (P.entry tid hCur)
    split at h
    · rename_i fault hF
      split at h
      · cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _
          (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6))
        rw [hL]
        exact F.stage.trans (LendersStage.of_kept (chainObjectsKept.of_objects_eq rfl))
      · cases h
        unfold Platform.FFI.deliverSyscallCapFault
        have W := (W1.andThen fun hI => QueueLabelsFrame.cancelReceiveBusyReply ctx e _ hI
            (cancelReceiveBusyReply_cases_of_fault hI
              (by rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur) hE hF)).andThen
          fun hI => QueueLabelsFrame.writeFaultRegistersToTcb _ tid
            (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30) hI
        exact F.stage.trans fun hFl => faultDeliverOnCoreChecked_preserves_lendingLabelsEqual _ tid _ _
          e (P.capFault tid _ hCur) (W.waiters hW).2
          (LendersStage.of_kept (chainObjectsKept.writeFaultRegistersToTcb _ tid _ F.invExt) hFl)
    · split at h
      · cases h
        exact F.stage.trans (LendersStage.of_kept (chainObjectsKept.of_objects_eq
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _))))
      · cases h
        exact F.stage.trans (LendersStage.of_kept (chainObjectsKept.of_objects_eq
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)))
  · rename_i hE
    cases h
    exact F1.stage.trans (syscallEntryChecked_lendersStage F1.invExt (P.entry tid hCur) hR1
      (W1.waiters hW) (W1.ntfn ctx hA) hE)


/-- **The syscall step keeps the lenders' flow**: the ABI dispatch, the
caller's return staging, the local scheduling point, the residency settlement,
the activation and the ledger drains.  The store's invariant after the dispatch
is the records' own (`syscallDispatchFromAbi_recordsStage`); the waiters are the
step's own state's. -/
theorem syscallDispatchCrossCoreStep_lendersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (hK : st.kernelRecordsSound) (PR : RecordsArmPremises st)
    (P : SyscallAbiLendPremises ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st)
    (hR : CurrentReady st) (hW : endpointWaitersLabelsEqual ctx st)
    (hA : notificationLabelsAgree ctx st) :
    LendersStage ctx st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have hI := KernelRecords.objects_invExt (syscallDispatchFromAbi_recordsStage PR hR hD hK)
  have F1 := RecordsFrame.stageCallerReturnFor (st.scheduler.currentOnCore e) _ e outcome hI
  have F2 := F1.trans (RecordsFrame.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e) _ e F1.invExt)
  have F3 := F2.trans (RecordsFrame.settleResidencyOnCore _ e F2.invExt)
  exact (syscallDispatchFromAbi_lendersStage (KernelRecords.objects_invExt hK) P hR hW hA hD).trans
    ((((LendersStage.of_kept (chainObjectsKept.stageCallerReturnFor _ _ e outcome hI)).trans
      (LendersStage.of_kept (chainObjectsKept.scheduleLocalSuccessorFrom _ _ e F1.invExt))).trans
      (LendersStage.of_kept (chainObjectsKept.settleResidencyOnCore _ e F2.invExt))).trans
      ((LendersStage.activateThreadOnCore _ e F3.invExt).trans
        (LendersStage.of_kept (chainObjectsKept.clearLedgers _))))

/-- **The syscall entry's committed state keeps the lenders' flow**: the
trap-frame save, the entry's IPC-buffer words handed to the state, the step,
and the committed state dropping the words.  The premises are read off the
state the step runs from; the waiters are the entry's own state's (`hW`), beside
the records, and the save and the words keep them. -/
theorem syscallDispatchEntryState_lendersStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hK : st.kernelRecordsSound) (hW : endpointWaitersLabelsEqual ctx st)
    (hA : notificationLabelsAgree ctx st)
    (PR : RecordsArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (P : ∀ syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30,
      SyscallAbiLendPremises ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hR : CurrentReady (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n)) :
    LendersStage ctx st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) := by
  have hI := KernelRecords.objects_invExt hK
  have hK1 := (RecordsStage.of_frameK fun hI =>
    let F := RecordsFrame.saveCapturedSyscallFrame st e frame hI
    F.trans (RecordsFrame.syncUserWords _ bytes n F.invExt)) hK
  have hS := (LendersStage.of_kept (ctx := ctx)
    ((chainObjectsKept.saveCapturedSyscallFrame st e frame hI).trans
      (chainObjectsKept.syncUserWords _ bytes n)))
  have W := (RecordsFrame.saveCapturedSyscallFrame st e frame hI).trans
    (RecordsFrame.syncUserWords _ bytes n (RecordsFrame.saveCapturedSyscallFrame st e frame hI).invExt)
  exact (hS.trans (syscallDispatchCrossCoreStep_lendersStage hK1 PR (P _ _ _ _ _ _ _ _ _ _ _ _) hR
    ((QueueLabelsFrame.of_frame W).waiters hW) ((QueueLabelsFrame.of_frame W).ntfn ctx hA))).trans
    (LendersStage.of_kept (chainObjectsKept.clearUserWords _))

end SeLe4n.Kernel
