/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Dispatch
import SeLe4n.Kernel.ReschedulePendingArms.Entry
import SeLe4n.Kernel.PerCoreTimerEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry

/-!
# Every committing entry keeps the run-queue link agreement

WS-ZA ZA4.5 part 2.  The pure step each state-committing entry runs — the
syscall, the suspend, the timer tick, the reschedule interrupt, the two fault
entries and the FP/SIMD access — is a `RunQueueStage`: the trap-frame save, the
step itself, the local scheduling point, the residency settlement and the
ledger drains, each a stage.  So a state the boot left in agreement stays in
agreement across every entry the kernel commits.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### The scheduler's own steps -/

/-- The outgoing thread's re-enqueue at a domain boundary: the context save,
then the guarded enqueue on its own core. -/
theorem requeueOutgoingOnCore_runQueueStage (st : SystemState) (c : CoreId) :
    RunQueueStage st (requeueOutgoingOnCore st c) := by
  intro hInv hR
  have hS := saveOutgoingContextOnCore_runQueueStage st c
  have hCode : ∀ y, ((saveOutgoingContextOnCore st c).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
    intro y; unfold saveOutgoingContextOnCore; split
    · rfl
    · exact SystemState.updateTcb_runCoreCode _ _
        (fun outTcb => { outTcb with registerContext := st.machine.regsOnCore c })
        (fun _ => rfl) hInv y
  revert hInv hR
  unfold requeueOutgoingOnCore; dsimp only
  split
  · exact hS
  next tid _ =>
    split
    next tcb _ =>
      split
      next hA =>
        have hA' : (saveOutgoingContextOnCore st c).runEnqueueAdmits c tid = true := by
          rw [SystemState.runEnqueueAdmits_congr (hCode tid) c]; exact hA
        have h2 := RunQueueStage.runEnqueueOnCore (saveOutgoingContextOnCore st c) c tid
          tcb.boostedPriority
        rw [SystemState.runEnqueueOnCore_of_admits _ hA'] at h2
        exact hS.trans h2
      · exact hS
    · exact hS

theorem switchDomainOnCore_runQueueStage {st st' : SystemState} {c : CoreId}
    (h : switchDomainOnCore st c = .ok st') : RunQueueStage st st' := by
  unfold switchDomainOnCore at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact (requeueOutgoingOnCore_runQueueStage st c).trans (RunQueueStage.of_frame rfl rfl rfl)

theorem scheduleDomainOnCore_runQueueStage {st st' : SystemState} {c : CoreId}
    (h : scheduleDomainOnCore st c = .ok st') : RunQueueStage st st' := by
  unfold scheduleDomainOnCore at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        exact (switchDomainOnCore_runQueueStage hD).trans (scheduleEffectiveOnCore_runQueueStage h)
    · cases h
      exact RunQueueStage.of_frame rfl rfl rfl

/-- The per-core timer step: the boot core's clock, the tick, the domain
accounting. -/
theorem perCoreTimerTickStep_runQueueStage (st : SystemState) (coreId : UInt64) :
    RunQueueStage st (perCoreTimerTickStep st coreId).1 := by
  unfold perCoreTimerTickStep
  split
  · rename_i hc
    have hClk : RunQueueStage st (tickClockedState st ⟨coreId.toNat, hc⟩) := by
      unfold tickClockedState; split
      · exact RunQueueStage.of_frame rfl rfl rfl
      · exact RunQueueStage.refl _
    split
    · exact RunQueueStage.refl _
    · rename_i r hT
      split
      · exact RunQueueStage.refl _
      · rename_i st2 hD
        exact (hClk.trans (timerTickOnCore_runQueueStage hT)).trans
          (scheduleDomainOnCore_runQueueStage hD)
  · exact RunQueueStage.refl _

/-- The reschedule interrupt's step. -/
theorem perCoreRescheduleStep_runQueueStage (st : SystemState) (coreId : UInt64) :
    RunQueueStage st (perCoreRescheduleStep st coreId) := by
  unfold perCoreRescheduleStep
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueStage hR
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

theorem dispatchVacatedCore_runQueueStage (st : SystemState) (c : CoreId) :
    RunQueueStage st (PriorityInheritance.dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact RunQueueStage.refl _
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueStage hR
    · exact RunQueueStage.refl _

/-- The executing core's scheduling point after a committed step. -/
theorem scheduleLocalSuccessorFrom_runQueueStage (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) :
    RunQueueStage post (PriorityInheritance.scheduleLocalSuccessorFrom caller? post c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueStage hR
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

theorem deferResidentElsewhere_runQueueStage (st : SystemState) (c : CoreId) :
    RunQueueStage st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · split
    · split
      · rename_i hS; exact switchToThreadOnCore_runQueueStage hS
      · exact (preemptCurrentOnCore_runQueueStage st c _).trans
          (RunQueueStage.of_frame rfl rfl rfl)
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

/-- Residency settlement: the vacated core's dispatch, the deferral of a thread
resident elsewhere, and the machine's residency record. -/
theorem settleResidencyOnCore_runQueueStage (st : SystemState) (c : CoreId) :
    RunQueueStage st (PriorityInheritance.settleResidencyOnCore st c) := by
  unfold PriorityInheritance.settleResidencyOnCore
  exact ((dispatchVacatedCore_runQueueStage st c).trans
    (deferResidentElsewhere_runQueueStage _ c)).trans (RunQueueStage.of_frame rfl rfl rfl)

theorem settleResidencyAt_runQueueStage (st : SystemState) (coreId : UInt64) :
    RunQueueStage st (PriorityInheritance.settleResidencyAt st coreId) := by
  unfold PriorityInheritance.settleResidencyAt
  split
  · exact settleResidencyOnCore_runQueueStage st _
  · exact RunQueueStage.refl _

/-! ### The trap-frame saves and the ledger drains -/

theorem saveTrapFrameOnCore_runQueueStage (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) :
    RunQueueStage st (Architecture.saveTrapFrameOnCore st c rf) := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    next tid _ =>
      split
      · dsimp only
        refine RunQueueStage.trans
          (RunQueueStage.updateTcb st tid (f := fun t => { t with registerContext := rf })
            (fun _ _ => rfl)) ?_
        exact RunQueueStage.of_frame rfl rfl rfl
      · exact RunQueueStage.refl _
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

theorem saveVacatedFrameOnCore_runQueueStage (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) :
    RunQueueStage st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
      · exact RunQueueStage.refl _
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

theorem saveCapturedTrapFrame_runQueueStage (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    RunQueueStage st (Architecture.saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact RunQueueStage.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_runQueueStage st c _).trans
      (saveVacatedFrameOnCore_runQueueStage _ c _ _)

theorem saveCapturedSyscallFrame_runQueueStage (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    RunQueueStage st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact RunQueueStage.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_runQueueStage st c _).trans
      (saveVacatedFrameOnCore_runQueueStage _ c _ _)

theorem saveCapturedTrapFrameAt_runQueueStage (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    RunQueueStage st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_runQueueStage st _ frame
  · exact RunQueueStage.refl _

/-- The two ledger drains every committing entry ends with. -/
theorem clearLedgers_runQueueStage (st : SystemState) :
    RunQueueStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st)) :=
  RunQueueStage.of_frame rfl rfl rfl

theorem clearLedgers_runQueueStage' (st : SystemState) :
    RunQueueStage st (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance st)) :=
  RunQueueStage.of_frame rfl rfl rfl

/-! ### The syscall entry -/

/-- **The checked syscall entry keeps the agreement**: the register read and the
decode read, the IPC-buffer fill writes one core's TLB, and the dispatch is a
stage. -/
theorem syscallEntryChecked_runQueueStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (hDet : entryRetypeDetached e layout regCount st)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  rename_i regs s hLk
  split at h
  · cases h
  rename_i decoded hDec
  dsimp only at h
  obtain ⟨t, ht⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st e tid
    decoded.overflowCount
  rw [ht] at h
  exact (RunQueueStage.of_frame (st' := { st with perCoreTlb := t }) rfl rfl rfl).trans
    (dispatchSyscallChecked_runQueueStage ctx decoded tid e _ st'
      (retypeDetachedFor_perCoreTlb (hDet tid regs s decoded hCur hLk hDec)) h)

/-- **The ABI dispatch keeps the agreement**: the argument spill, then the
checked entry, a capability-fault delivery, or a refusal record. -/
theorem syscallDispatchFromAbi_runQueueStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hDet : ∀ tid, st.scheduler.currentOnCore e = some tid →
      entryRetypeDetached e SeLe4n.arm64DefaultLayout 32
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5))
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    RunQueueStage st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact RunQueueStage.refl _
  rename_i tid hCur
  have hW : RunQueueStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  dsimp only at h
  split at h
  · split at h
    · cases h
      unfold Platform.FFI.deliverSyscallCapFault
      exact (hW.trans (writeFaultRegistersToTcb_runQueueStage _ tid _)).trans
        (faultDeliverOnCoreChecked_runQueueStage _ _ tid _ _ e)
    · cases h
      exact hW.trans (RunQueueStage.of_frame
        (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq]))
  · rename_i hE
    cases h
    exact hW.trans (syscallEntryChecked_runQueueStage (hDet tid hCur) hE)

/-- The caller's return staging writes its TCB's return frame and, when it is
still current, the core's registers. -/
theorem stageCallerReturnFor_runQueueStage (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) (o : Architecture.SyscallOutcome) :
    RunQueueStage post (Architecture.stageCallerReturnFor caller? post c o) := by
  cases o with
  | returns f =>
    cases caller? with
    | none => exact RunQueueStage.refl _
    | some tid =>
      unfold Architecture.stageCallerReturnFor
      dsimp only
      split
      · refine RunQueueStage.trans (writeReturnFrameToTcb_runQueueStage post tid f) ?_
        exact RunQueueStage.of_frame rfl rfl rfl
      · exact writeReturnFrameToTcb_runQueueStage post tid f
  | blocks => exact RunQueueStage.refl _
  | faulted => exact RunQueueStage.refl _

/-- **The syscall step keeps the agreement**: the ABI dispatch, the caller's
return staging, the local scheduling point, the residency settlement and the
ledger drains. -/
theorem syscallDispatchCrossCoreStep_runQueueStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st : SystemState}
    (hDet : ∀ tid, st.scheduler.currentOnCore e = some tid →
      entryRetypeDetached e SeLe4n.arm64DefaultLayout 32
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)) :
    RunQueueStage st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact ((((syscallDispatchFromAbi_runQueueStage hDet hD).trans
    (stageCallerReturnFor_runQueueStage _ _ e outcome)).trans
    (scheduleLocalSuccessorFrom_runQueueStage _ _ e)).trans
    (settleResidencyOnCore_runQueueStage _ e)).trans (clearLedgers_runQueueStage' _)

/-- **The syscall entry's committed state keeps the agreement**: the trap-frame
save, the IPC-buffer words synced into memory, and the step. -/
theorem syscallDispatchEntryState_runQueueStage (ctx : LabelingContext) (e : CoreId)
    (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (words : List (SeLe4n.PAddr × UInt64))
    (st : SystemState)
    (hDet : ∀ tid, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) words).scheduler.currentOnCore e
          = some tid →
      entryRetypeDetached e SeLe4n.arm64DefaultLayout 32
        (Platform.FFI.writeFfiRegistersToTcb (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) words) tid syscallId
          trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5)) :
    RunQueueStage st (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
      (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) words)).2 :=
  ((saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler]))).trans
    (syscallDispatchCrossCoreStep_runQueueStage hDet)

/-! ### The suspend, timer, reschedule, fault and FP/SIMD entries -/

theorem suspendThreadCrossCoreDrainedStep_runQueueStage (tid : UInt64) (e : CoreId)
    (st : SystemState) :
    RunQueueStage st (suspendThreadCrossCoreDrainedStep tid e st).2 := by
  unfold suspendThreadCrossCoreDrainedStep suspendThreadCrossCoreStep
  dsimp only
  refine RunQueueStage.trans ?_ (clearLedgers_runQueueStage _)
  split
  · exact RunQueueStage.refl _
  · split
    · exact RunQueueStage.refl _
    · unfold Concurrency.BracketSpec.run suspendThreadBracket
      dsimp only
      split
      · rename_i s' sgi hS
        exact (suspendThreadOnCore_runQueueStage hS).trans
          (scheduleLocalSuccessorFrom_runQueueStage _ _ e)
      · exact RunQueueStage.refl _

/-- **The timer entry's committed state keeps the agreement**: the trap-frame
save, the tick, the residency settlement and the ledger drains. -/
theorem perCoreTimerTickEntryState_runQueueStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    RunQueueStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (PriorityInheritance.settleResidencyAt ((timerTickBracket coreId).run
        (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId))) :=
  (((saveCapturedTrapFrameAt_runQueueStage st coreId frame).trans
    (perCoreTimerTickStep_runQueueStage _ coreId)).trans
    (settleResidencyAt_runQueueStage _ coreId)).trans (clearLedgers_runQueueStage _)

/-- **The reschedule entry's committed state keeps the agreement** (the
secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_runQueueStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    RunQueueStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (PriorityInheritance.settleResidencyAt ((rescheduleBracket coreId).run
        (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId))) :=
  (((saveCapturedTrapFrameAt_runQueueStage st coreId frame).trans
    (perCoreRescheduleStep_runQueueStage _ coreId)).trans
    (settleResidencyAt_runQueueStage _ coreId)).trans (clearLedgers_runQueueStage _)

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem faultEntryDeliver_runQueueStage (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId) :
    RunQueueStage st (faultEntryDeliver lctx st f ectx w c).2 := by
  unfold faultEntryDeliver
  split
  · exact dispatchVacatedCore_runQueueStage st c
  · exact (faultDeliveredState_runQueueStage lctx st f ectx w c _).trans
      (scheduleLocalSuccessorFrom_runQueueStage _ _ c)

theorem faultEntryStep_runQueueStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    RunQueueStage st (faultEntryStep lctx st ectx w coreId).2 := by
  unfold faultEntryStep
  split
  · split
    · split
      · exact RunQueueStage.refl _
      · exact faultEntryDeliver_runQueueStage lctx st _ ectx w _
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

theorem unknownSyscallEntryStep_runQueueStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    RunQueueStage st (unknownSyscallEntryStep lctx st ectx w coreId).2 := by
  unfold unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_runQueueStage lctx st _ ectx w _
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

/-- **The fault entry's committed state keeps the agreement.** -/
theorem faultEntryState_runQueueStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    RunQueueStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (PriorityInheritance.settleResidencyAt (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId))) :=
  (((saveCapturedTrapFrameAt_runQueueStage st coreId _).trans
    (faultEntryStep_runQueueStage lctx _ ectx w coreId)).trans
    (settleResidencyAt_runQueueStage _ coreId)).trans (clearLedgers_runQueueStage _)

theorem saveCapturedSyscallFrameAt_runQueueStage (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    RunQueueStage st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_runQueueStage st _ frame
  · exact RunQueueStage.refl _

/-- **The unknown-syscall entry's committed state keeps the agreement.** -/
theorem unknownSyscallEntryState_runQueueStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    RunQueueStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (PriorityInheritance.settleResidencyAt (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId))) :=
  (((saveCapturedSyscallFrameAt_runQueueStage st coreId _).trans
    (unknownSyscallEntryStep_runQueueStage lctx _ ectx w coreId)).trans
    (settleResidencyAt_runQueueStage _ coreId)).trans (clearLedgers_runQueueStage _)

/-- The lazy FP/SIMD switch writes the previous owner's saved FP context and the
core's owner slot. -/
theorem fpAccessOnCore_runQueueStage (st : SystemState) (c : CoreId)
    (live : Option FpContext) :
    RunQueueStage st (Architecture.fpAccessOnCore st c live).2 := by
  have hW : ∀ (s : SystemState) (o : SeLe4n.ThreadId) (ctx : FpContext),
      RunQueueStage s (Architecture.writeFpContextToTcb s o ctx) := fun s o _ => by
    unfold Architecture.writeFpContextToTcb
    exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  have hSet : ∀ (s : SystemState) (t? : Option SeLe4n.ThreadId), RunQueueStage st s →
      RunQueueStage st (Architecture.setFpOwner s c t?) := fun s _ h =>
    h.trans (RunQueueStage.of_frame (st := s) rfl rfl rfl)
  unfold Architecture.fpAccessOnCore
  split
  · exact RunQueueStage.refl _
  · split
    · exact RunQueueStage.refl _
    · split
      · exact RunQueueStage.refl _
      · split
        · exact RunQueueStage.refl _
        · dsimp only
          apply hSet
          split
          · exact hW _ _ _
          · exact RunQueueStage.refl _

/-- **The FP/SIMD entry's committed state keeps the agreement.** -/
theorem fpAccessEntryState_runQueueStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) :
    RunQueueStage st (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) := by
  refine RunQueueStage.trans (saveCapturedTrapFrameAt_runQueueStage st coreId frame) ?_
  refine RunQueueStage.trans ?_ (settleResidencyAt_runQueueStage _ coreId)
  unfold fpAccessEntryStep
  split
  · exact RunQueueStage.refl _
  · exact (fpAccessOnCore_runQueueStage _ _ live).trans (dispatchVacatedCore_runQueueStage _ _)

end SeLe4n.Kernel
