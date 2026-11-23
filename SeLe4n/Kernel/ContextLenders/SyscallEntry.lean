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
owner WS-PK).
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
    (P tid (regs, s0) decoded hCur hP hDec) (hR e tid hCur) h


/-- **A refused receive's busy-reply cancel**: nothing, or a reply holder's
cancel. -/
theorem LendersFrame.cancelReceiveBusyReply (ctx : LabelingContext) (e : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e st) := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with hE | ⟨_, holder, -, -, hE⟩ <;> rw [hE]
  · exact LendersFrame.refl hInv
  · exact LendersFrame.cancelReplyHolder st holder e hInv

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
capability fault's delivery or the refusal's record. -/
theorem syscallDispatchFromAbi_lendersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome} (hInv : st.objects.invExt)
    (P : SyscallAbiLendPremises ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st)
    (hR : CurrentReady st)
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
  dsimp only at h
  split at h
  · have F := F1.andThen fun hI => LendersFrame.cancelReceiveBusyReply ctx e _ hI
    split at h
    · split at h
      · cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _
          (_root_.SeLe4n.Kernel.cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6))
        rw [hL]
        exact F.stage.trans (LendersStage.of_kept (chainObjectsKept.of_objects_eq rfl))
      · cases h
        unfold Platform.FFI.deliverSyscallCapFault
        exact F.stage.trans fun hFl => faultDeliverOnCoreChecked_preserves_contextLendersFlow _ tid _ _
          e (P.capFault tid _ hCur)
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
    exact F1.stage.trans (syscallEntryChecked_lendersStage F1.invExt (P.entry tid hCur) hR1 hE)


/-- **The syscall step keeps the lenders' flow**: the ABI dispatch, the
caller's return staging, the local scheduling point, the residency settlement,
the activation and the ledger drains.  The store's invariant after the dispatch
is the records' own (`syscallDispatchFromAbi_recordsStage`). -/
theorem syscallDispatchCrossCoreStep_lendersStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (hK : st.kernelRecordsSound) (PR : RecordsArmPremises st)
    (P : SyscallAbiLendPremises ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st)
    (hR : CurrentReady st) :
    LendersStage ctx st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have hI := KernelRecords.objects_invExt (syscallDispatchFromAbi_recordsStage PR hR hD hK)
  have F1 := RecordsFrame.stageCallerReturnFor (st.scheduler.currentOnCore e) _ e outcome hI
  have F2 := F1.trans (RecordsFrame.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e) _ e F1.invExt)
  have F3 := F2.trans (RecordsFrame.settleResidencyOnCore _ e F2.invExt)
  exact (syscallDispatchFromAbi_lendersStage (KernelRecords.objects_invExt hK) P hR hD).trans
    ((((LendersStage.of_kept (chainObjectsKept.stageCallerReturnFor _ _ e outcome hI)).trans
      (LendersStage.of_kept (chainObjectsKept.scheduleLocalSuccessorFrom _ _ e F1.invExt))).trans
      (LendersStage.of_kept (chainObjectsKept.settleResidencyOnCore _ e F2.invExt))).trans
      ((LendersStage.activateThreadOnCore _ e F3.invExt).trans
        (LendersStage.of_kept (chainObjectsKept.clearLedgers _))))

/-- **The syscall entry's committed state keeps the lenders' flow**: the
trap-frame save, the entry's IPC-buffer words handed to the state, the step,
and the committed state dropping the words.  The premises are read off the
state the step runs from. -/
theorem syscallDispatchEntryState_lendersStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hK : st.kernelRecordsSound)
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
  exact (hS.trans (syscallDispatchCrossCoreStep_lendersStage hK1 PR (P _ _ _ _ _ _ _ _ _ _ _ _) hR)).trans
    (LendersStage.of_kept (chainObjectsKept.clearUserWords _))

end SeLe4n.Kernel
