-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.Dispatch
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
theorem EndpointWaitersFrame.entryTail (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadAt (PriorityInheritance.settleResidencyAt st coreId) coreId))) :=
  .of_frame (RecordsFrame.chain (fun h => RecordsFrame.settleResidencyAt st coreId h)
    (fun h => (RecordsFrame.activateThreadAt _ coreId h).trans
      (RecordsFrame.clearLedgers _ (RecordsFrame.activateThreadAt _ coreId h).invExt)) hInv)

/-! ### The timer, reschedule, FP/SIMD and interrupt entries -/

/-- The per-core timer step: the clock, the tick, the domain accounting. -/
theorem EndpointWaitersFrame.perCoreTimerTickStep (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : EndpointWaitersFrame st (tickClockedState st ⟨coreId.toNat, hc⟩) :=
      .of_objects_eq hInv (tickClockedState_objects _ _)
    exact (hClk.andThen fun h => EndpointWaitersFrame.timerTickOnCore _ _ h).andThen fun h =>
      .of_frame (RecordsFrame.scheduleDomainOnCore h (scheduleDomainOnCore_eq_state _ _))
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact .refl hInv

/-- **The timer entry's committed state keeps the endpoint waiters' labels.** -/
theorem perCoreTimerTickEntryState_endpointWaitersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((EndpointWaitersFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (EndpointWaitersFrame.perCoreTimerTickStep _ coreId h).andThen fun h' =>
      EndpointWaitersFrame.entryTail _ coreId h').stage

/-- **The reschedule entry's committed state keeps the endpoint waiters'
labels**: every step is a records' frame. -/
theorem perCoreRescheduleEntryState_endpointWaitersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((EndpointWaitersFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (EndpointWaitersFrame.of_frame (RecordsFrame.perCoreRescheduleStep _ coreId h)).andThen
      fun h' => EndpointWaitersFrame.entryTail _ coreId h').stage

/-- **The FP/SIMD entry's committed state keeps the endpoint waiters' labels.** -/
theorem fpAccessEntryState_endpointWaitersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
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
  exact (EndpointWaitersFrame.of_frame (F3.trans (RecordsFrame.activateThreadAt _ coreId F3.invExt))).stage

/-- The interrupt step: seL4's `sendSignal`, which blocks no thread on an
endpoint, then the mask. -/
theorem EndpointWaitersFrame.interruptEntryStep (ctx : LabelingContext) (st : SystemState)
    (coreId intId : UInt64) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.interruptEntryStep ctx st coreId intId) :=
  interruptEntryStep_of (P := EndpointWaitersFrame st) ctx st coreId intId (.refl hInv) fun c _ _ =>
    handleInterruptOnCore_of (P := EndpointWaitersFrame st) ctx st c _
      (fun _ h => h.andThen fun hI => .of_objects_eq hI rfl) (.refl hInv)
      (fun _ _ _ => EndpointWaitersFrame.sendSignalOnCoreFlowing hInv)

/-- **The interrupt entry's committed state keeps the endpoint waiters'
labels.** -/
theorem interruptEntryState_endpointWaitersStage (ctx lctx : LabelingContext) (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage lctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep ctx (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) :=
  ((EndpointWaitersFrame.of_frame (RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv)).andThen
    fun h => (EndpointWaitersFrame.interruptEntryStep ctx _ coreId intId h).andThen fun h' =>
      EndpointWaitersFrame.entryTail _ coreId h').stage

/-! ### The fault entries

Each step is read as its stage with the store's invariant at the state it
reaches, which the next step's frame reads. -/

/-- **The register spill, then the flow-checked delivery**: the delivery's gate,
two-way, gives the faulting thread its handler endpoint's label before the call
can block it. -/
theorem faultDeliveredState_endpointWaitersStage (ctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (faultDeliveredState ctx st f ectx w c tid) ∧
      (faultDeliveredState ctx st f ectx w c tid).objects.invExt := by
  have F := EndpointWaitersFrame.writeFaultRegistersToTcb st tid w hInv
  exact ⟨F.stage.trans (EndpointWaitersStage.faultDeliverOnCoreChecked F.invExt),
    faultDeliverOnCoreChecked_preserves_objects_invExt ctx _ tid f _ c F.invExt⟩

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem faultEntryDeliver_endpointWaitersStage (ctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (faultEntryDeliver ctx st f ectx w c).2 ∧
      (faultEntryDeliver ctx st f ectx w c).2.objects.invExt := by
  unfold faultEntryDeliver
  split
  · have F := RecordsFrame.dispatchVacatedCore st c hInv
    exact ⟨(EndpointWaitersFrame.of_frame F).stage, F.invExt⟩
  · rename_i tid _
    dsimp only
    split
    · exact ⟨.refl _, hInv⟩
    · obtain ⟨S, hI⟩ := faultDeliveredState_endpointWaitersStage ctx st f ectx w c tid hInv
      have F := RecordsFrame.scheduleLocalSuccessorFrom (some tid) _ c hI
      exact ⟨S.trans (EndpointWaitersFrame.of_frame F).stage, F.invExt⟩

theorem faultEntryStep_endpointWaitersStage (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (faultEntryStep ctx st ectx w coreId).2 ∧
      (faultEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold faultEntryStep
  split
  · split
    · split
      · exact ⟨.refl _, hInv⟩
      · exact faultEntryDeliver_endpointWaitersStage ctx st _ ectx w _ hInv
    · exact ⟨.refl _, hInv⟩
  · exact ⟨.refl _, hInv⟩

theorem unknownSyscallEntryStep_endpointWaitersStage (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (unknownSyscallEntryStep ctx st ectx w coreId).2 ∧
      (unknownSyscallEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_endpointWaitersStage ctx st _ _ w _ hInv
    · exact ⟨.refl _, hInv⟩
  · exact ⟨.refl _, hInv⟩

/-- **The fault entry's committed state keeps the endpoint waiters' labels.** -/
theorem faultEntryState_endpointWaitersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep ctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId (some frame) hInv
  obtain ⟨S, hI⟩ := faultEntryStep_endpointWaitersStage ctx _ ectx w coreId F1.invExt
  exact ((EndpointWaitersFrame.of_frame F1).stage.trans S).trans
    (EndpointWaitersFrame.entryTail _ coreId hI).stage

/-- **The unknown-syscall entry's committed state keeps the endpoint waiters'
labels.** -/
theorem unknownSyscallEntryState_endpointWaitersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep ctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedSyscallFrameAt st coreId (some frame) hInv
  obtain ⟨S, hI⟩ := unknownSyscallEntryStep_endpointWaitersStage ctx _ ectx w coreId F1.invExt
  exact ((EndpointWaitersFrame.of_frame F1).stage.trans S).trans
    (EndpointWaitersFrame.entryTail _ coreId hI).stage

/-! ### The syscall entry -/

/-- **A refused receive's busy-reply cancel**: nothing, or a reply holder's
cancel. -/
theorem EndpointWaitersFrame.cancelReceiveBusyReply (ctx : LabelingContext) (e : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with hE | ⟨_, holder, -, -, hE⟩ <;> rw [hE]
  · exact EndpointWaitersFrame.refl hInv
  · exact EndpointWaitersFrame.cancelReplyHolder st holder e hInv

/-- **The checked syscall entry keeps the endpoint waiters' labels**: the
dispatch of the request the running caller's registers decode to. -/
theorem syscallEntryChecked_endpointWaitersStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    EndpointWaitersStage ctx st st' := by
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
  exact dispatchSyscallChecked_endpointWaitersStage ctx decoded tid e st st' hInv h

/-- **The ABI dispatch keeps the endpoint waiters' labels**: the argument spill,
then the checked entry, or the busy-reply cancel and a dropped fault's record, a
capability fault's delivery (past its own gate) or the refusal's record. -/
theorem syscallDispatchFromAbi_endpointWaitersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome} (hInv : st.objects.invExt)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    EndpointWaitersStage ctx st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact EndpointWaitersStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact EndpointWaitersStage.refl _
  have F1 : EndpointWaitersFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact EndpointWaitersFrame.updateTcb st tid hInv fun _ => TcbWaitsKept.of_ipc rfl
  dsimp only at h
  split at h
  · have F := F1.andThen fun hI => EndpointWaitersFrame.cancelReceiveBusyReply ctx e _ hI
    split at h
    · split at h
      · cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _
          (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6))
        rw [hL]
        exact F.stage.trans (EndpointWaitersShrink.of_objects_eq rfl).stage
      · cases h
        unfold Platform.FFI.deliverSyscallCapFault
        have W := EndpointWaitersFrame.writeFaultRegistersToTcb _ tid
          (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30) F.invExt
        exact (F.stage.trans W.stage).trans (EndpointWaitersStage.faultDeliverOnCoreChecked W.invExt)
    · split at h
      · cases h
        exact F.stage.trans (EndpointWaitersShrink.of_objects_eq
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _))).stage
      · cases h
        exact F.stage.trans (EndpointWaitersShrink.of_objects_eq
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)).stage
  · rename_i hE
    cases h
    exact F1.stage.trans (syscallEntryChecked_endpointWaitersStage F1.invExt hE)

/-- **The syscall step keeps the endpoint waiters' labels**: the ABI dispatch,
then the caller's return staging, the local scheduling point, the residency
settlement, the activation and the ledger drains, each a records' frame.  The
store's invariant after the dispatch is the records' own
(`syscallDispatchFromAbi_recordsStage`). -/
theorem syscallDispatchCrossCoreStep_endpointWaitersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (hK : st.kernelRecordsSound) (PR : RecordsArmPremises st)
    (hR : CurrentReady st) :
    EndpointWaitersStage ctx st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have hI := KernelRecords.objects_invExt (syscallDispatchFromAbi_recordsStage PR hR hD hK)
  have F1 := RecordsFrame.stageCallerReturnFor (st.scheduler.currentOnCore e) _ e outcome hI
  have F2 := F1.trans (RecordsFrame.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e) _ e F1.invExt)
  have F3 := F2.trans (RecordsFrame.settleResidencyOnCore _ e F2.invExt)
  have F4 := F3.trans (RecordsFrame.activateThreadOnCore _ e F3.invExt)
  exact (syscallDispatchFromAbi_endpointWaitersStage (KernelRecords.objects_invExt hK) hD).trans
    (EndpointWaitersFrame.of_frame (F4.trans (RecordsFrame.clearLedgers _ F4.invExt))).stage

/-- **The syscall entry's committed state keeps the endpoint waiters' labels**:
the trap-frame save, the entry's IPC-buffer words handed to the state, the
step, and the committed state dropping the words.  The records' premises and
the running callers are read off the state the step runs from. -/
theorem syscallDispatchEntryState_endpointWaitersStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hK : st.kernelRecordsSound)
    (PR : RecordsArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hR : CurrentReady (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n)) :
    EndpointWaitersStage ctx st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) := by
  have hI := KernelRecords.objects_invExt hK
  have F := RecordsFrame.saveCapturedSyscallFrame st e frame hI
  have F2 := F.trans (RecordsFrame.syncUserWords _ bytes n F.invExt)
  have hK1 := F2.preserves hK
  exact ((EndpointWaitersFrame.of_frame F2).stage.trans
    (syscallDispatchCrossCoreStep_endpointWaitersStage hK1 PR hR)).trans
    (EndpointWaitersShrink.of_objects_eq rfl).stage

end SeLe4n.Kernel
