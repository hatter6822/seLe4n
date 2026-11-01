-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Dispatch
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.PerCoreTimerEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry

/-! # Every committing entry keeps the mappings recorded

The pure step each state-committing entry runs (the syscall, the
timer tick, the reschedule interrupt, the two fault entries and the FP/SIMD
access) is a `MappingStage`: the trap-frame save, the step itself, the local
scheduling point, the residency settlement and the ledger drains, each a stage.
So a state the boot left with every live mapping recorded keeps them recorded
across every entry the kernel commits.

The syscall entries dispatch to the map, the unmap, the deletes and the space
set, which read the capability invariants and the teardown's well-formedness
(`MappingArmPremises`).  Each syscall entry reads them off the state it starts
from and carries them across the writes it makes before the dispatch: the
register spill, the trap-frame save, the IPC-buffer words and the TLB fill
write thread registers or no object, derivation tree or ASID table.  No other
entry reaches those arms, so the others read no premise.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### The scheduler's own steps -/

/-- The outgoing thread's re-enqueue at a domain boundary: the context save,
then the admitted enqueue of core `c`'s current thread. -/
theorem requeueOutgoingOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (requeueOutgoingOnCore st c) := by
  have hS := saveOutgoingContextOnCore_mappingStage st c
  unfold requeueOutgoingOnCore; dsimp only
  split
  · exact hS
  · split
    · split
      · exact hS.trans (runEnqueueAdmitted_mappingStage _ _ _ _)
      · exact hS
    · exact hS

/-- The domain switch: the re-enqueue, then scheduler writes alone. -/
theorem switchDomainOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    (h : switchDomainOnCore st c = .ok st') : MappingStage st st' := by
  unfold switchDomainOnCore at h
  split at h
  · cases h; exact MappingStage.refl _
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact (requeueOutgoingOnCore_mappingStage st c).trans (MappingStage.of_objects_eq rfl)

theorem scheduleDomainOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    (h : scheduleDomainOnCore st c = .ok st') : MappingStage st st' := by
  unfold scheduleDomainOnCore at h
  split at h
  · cases h; exact MappingStage.refl _
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        exact (switchDomainOnCore_mappingStage hD).trans (scheduleEffectiveOnCore_mappingStage h)
    · cases h
      exact MappingStage.of_objects_eq rfl

/-- The per-core timer step: the boot core's clock, the tick, the domain
accounting. -/
theorem perCoreTimerTickStep_mappingStage (st : SystemState) (coreId : UInt64) :
    MappingStage st (perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : MappingStage st (tickClockedState st ⟨coreId.toNat, hc⟩) :=
      MappingStage.of_objects_eq (tickClockedState_objects _ _)
    exact (hClk.trans (timerTickOnCore_mappingStage _ _)).trans
      (scheduleDomainOnCore_mappingStage (scheduleDomainOnCore_eq_state _ _))
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact MappingStage.refl _

/-- The reschedule interrupt's step. -/
theorem perCoreRescheduleStep_mappingStage (st : SystemState) (coreId : UInt64) :
    MappingStage st (perCoreRescheduleStep st coreId) := by
  unfold perCoreRescheduleStep
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_mappingStage hR
    · exact MappingStage.refl _
  · exact MappingStage.refl _

theorem dispatchVacatedCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (PriorityInheritance.dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact MappingStage.refl _
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_mappingStage hR
    · exact MappingStage.refl _

/-- The executing core's scheduling point after a committed step. -/
theorem scheduleLocalSuccessorFrom_mappingStage (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) :
    MappingStage post (PriorityInheritance.scheduleLocalSuccessorFrom caller? post c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_mappingStage hR
    · exact MappingStage.refl _
  · exact MappingStage.refl _

/-- A thread resident on another core is not resumed here: core `c` switches
to its idle thread, or drops its current slot. -/
theorem deferResidentElsewhere_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · split
    · split
      · rename_i hS
        exact switchToThreadOnCore_mappingStage hS
      · exact (preemptCurrentOnCore_mappingStage st c _).trans (MappingStage.of_objects_eq rfl)
    · exact MappingStage.refl _
  · exact MappingStage.refl _

/-- Residency settlement: the vacated core's dispatch, the deferral of a thread
resident elsewhere, and the machine's residency record. -/
theorem settleResidencyOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (PriorityInheritance.settleResidencyOnCore st c) := by
  unfold PriorityInheritance.settleResidencyOnCore
  exact ((dispatchVacatedCore_mappingStage st c).trans
    (deferResidentElsewhere_mappingStage _ c)).trans (MappingStage.of_objects_eq rfl)

theorem settleResidencyAt_mappingStage (st : SystemState) (coreId : UInt64) :
    MappingStage st (PriorityInheritance.settleResidencyAt st coreId) := by
  unfold PriorityInheritance.settleResidencyAt
  split
  · exact settleResidencyOnCore_mappingStage st _
  · exact MappingStage.refl _

/-- WS-ZA ZA6.7: the yield completion rewrites a context and a thread in place. -/
theorem completeYieldTo_mappingStage (st : SystemState) (y : SeLe4n.ThreadId) :
    MappingStage st (completeYieldTo st y) := by
  unfold completeYieldTo
  split
  · split
    · exact MappingStage.refl _
    · exact (setConsumed_mappingStage _ _ _).trans (cancelYieldTo_mappingStage _ _)
  · exact MappingStage.refl _

/-- WS-ZA ZA6.7: **the activation keeps the mappings recorded**: the yield
completion, and the core's bank, which holds no mapping. -/
theorem activateThreadOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (activateThreadOnCore st c) := by
  rcases activateThreadOnCore_objects st c with h | ⟨tid, _, h⟩
  · exact MappingStage.of_objects_eq h
  · exact (completeYieldTo_mappingStage st tid).trans (MappingStage.of_objects_eq h)

theorem activateThreadAt_mappingStage (st : SystemState) (coreId : UInt64) :
    MappingStage st (activateThreadAt st coreId) := by
  unfold activateThreadAt
  split
  · exact activateThreadOnCore_mappingStage st _
  · exact MappingStage.refl _

/-! ### The trap-frame saves and the ledger drains -/

theorem saveTrapFrameOnCore_mappingStage (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) : MappingStage st (Architecture.saveTrapFrameOnCore st c rf) := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    next tid _ =>
      split
      · exact (updateTcb_mappingStage st tid _).trans (MappingStage.of_objects_eq rfl)
      · exact MappingStage.refl _
    · exact MappingStage.refl _
  · exact MappingStage.refl _

theorem saveVacatedFrameOnCore_mappingStage (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) :
    MappingStage st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact updateTcb_mappingStage _ _ _
      · exact MappingStage.refl _
    · exact MappingStage.refl _
  · exact MappingStage.refl _

theorem saveCapturedTrapFrame_mappingStage (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    MappingStage st (Architecture.saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact MappingStage.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_mappingStage st c _).trans
      (saveVacatedFrameOnCore_mappingStage _ c _ _)

theorem saveCapturedSyscallFrame_mappingStage (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    MappingStage st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact MappingStage.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_mappingStage st c _).trans
      (saveVacatedFrameOnCore_mappingStage _ c _ _)

theorem saveCapturedTrapFrameAt_mappingStage (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    MappingStage st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_mappingStage st _ frame
  · exact MappingStage.refl _

theorem saveCapturedSyscallFrameAt_mappingStage (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    MappingStage st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_mappingStage st _ frame
  · exact MappingStage.refl _

/-- The syscall trap-frame save writes thread registers and the core's
registers alone: the arms' premises hold after it. -/
theorem saveCapturedSyscallFrame_mappingArmPremises {st : SystemState} (c : CoreId)
    (frame : Option Architecture.InFlightContext) (P : MappingArmPremises st) :
    MappingArmPremises (Architecture.saveCapturedSyscallFrame st c frame) := by
  have hT : ∀ (s : SystemState) (rf : SeLe4n.RegisterFile), MappingArmPremises s →
      MappingArmPremises (Architecture.saveTrapFrameOnCore s c rf) := fun s rf Q => by
    unfold Architecture.saveTrapFrameOnCore
    split
    · split
      next tid _ =>
        split
        · exact (Q.updateTcb tid _).of_tables_eq rfl rfl rfl
        · exact Q
      · exact Q
    · exact Q
  have hV : ∀ (s : SystemState) (rf saved : SeLe4n.RegisterFile), MappingArmPremises s →
      MappingArmPremises (Architecture.saveVacatedFrameOnCore s c rf saved) := fun s rf saved Q => by
    unfold Architecture.saveVacatedFrameOnCore
    split
    · split
      · split
        · exact Q.updateTcb _ _
        · exact Q
      · exact Q
    · exact Q
  cases frame with
  | none => exact P
  | some ic => exact hV _ _ _ (hT _ _ P)

/-- The two ledger drains every committing entry ends with. -/
theorem clearLedgers_mappingStage (st : SystemState) :
    MappingStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st)) :=
  MappingStage.of_objects_eq rfl

theorem clearLedgers_mappingStage' (st : SystemState) :
    MappingStage st (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance st)) :=
  MappingStage.of_objects_eq rfl

/-! ### The syscall entry -/

/-- **The checked syscall entry keeps the mappings recorded**: the register read
and the decode read, the IPC-buffer fill writes one core's TLB, and the
dispatch is a stage from the premises the fill keeps. -/
theorem syscallEntryChecked_mappingStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (P : MappingArmPremises st)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    MappingStage st st' := by
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
  exact (MappingStage.of_objects_eq (st' := { st with perCoreTlb := t }) rfl).trans
    (dispatchSyscallChecked_mappingStage ctx decoded tid e _ st' (P.of_tables_eq rfl rfl rfl) h)

/-- **The ABI dispatch keeps the mappings recorded**: the argument spill (a
register write, which keeps the premises), then the checked entry, a
capability-fault delivery, or a refusal record. -/
theorem syscallDispatchFromAbi_mappingStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome} (P : MappingArmPremises st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    MappingStage st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact MappingStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact MappingStage.refl _
  have hW : MappingStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact updateTcb_mappingStage _ _ _
  have P1 : MappingArmPremises
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact P.updateTcb _ _
  dsimp only at h
  split at h
  · split at h
    · cases h
      unfold Platform.FFI.deliverSyscallCapFault
      exact (hW.trans (writeFaultRegistersToTcb_mappingStage _ tid _)).trans
        (faultDeliverOnCoreChecked_mappingStage _ _ tid _ _ e)
    · cases h
      exact hW.trans (MappingStage.of_objects_eq
        (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _))
  · rename_i hE
    cases h
    exact hW.trans (syscallEntryChecked_mappingStage P1 hE)

/-- The caller's return staging writes its TCB's return frame and, when it is
still current, the core's registers. -/
theorem stageCallerReturnFor_mappingStage (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) (o : Architecture.SyscallOutcome) :
    MappingStage post (Architecture.stageCallerReturnFor caller? post c o) := by
  cases o with
  | returns f =>
    cases caller? with
    | none => exact MappingStage.refl _
    | some tid =>
      unfold Architecture.stageCallerReturnFor
      dsimp only
      split
      · exact (writeReturnFrameToTcb_mappingStage post tid f).trans (MappingStage.of_objects_eq rfl)
      · exact writeReturnFrameToTcb_mappingStage post tid f
  | blocks => exact MappingStage.refl _
  | faulted => exact MappingStage.refl _

/-- **The syscall step keeps the mappings recorded**: the ABI dispatch, the
caller's return staging, the local scheduling point, the residency settlement
and the ledger drains. -/
theorem syscallDispatchCrossCoreStep_mappingStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (P : MappingArmPremises st) :
    MappingStage st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact (syscallDispatchFromAbi_mappingStage P hD).trans
    ((((stageCallerReturnFor_mappingStage _ _ e outcome).trans
    (scheduleLocalSuccessorFrom_mappingStage _ _ e)).trans
    (settleResidencyOnCore_mappingStage _ e)).trans
    ((activateThreadOnCore_mappingStage _ e).trans (clearLedgers_mappingStage' _)))

/-- **The syscall entry's committed state keeps the mappings recorded**: the
trap-frame save, the entry's IPC-buffer words handed to the state, the step,
and the committed state dropping the words.  The premises are read off the
state the entry starts from. -/
theorem syscallDispatchEntryState_mappingStage (ctx : LabelingContext) (e : CoreId)
    (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (P : MappingArmPremises st) :
    MappingStage st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) := by
  have hS := (saveCapturedSyscallFrame_mappingStage st e frame).trans
    (MappingStage.of_objects_eq (Architecture.IpcBufferRead.syncUserWords_objects _ bytes n))
  have P1 : MappingArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n) :=
    (saveCapturedSyscallFrame_mappingArmPremises e frame P).of_tables_eq
      (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
      (by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
  exact (hS.trans (syscallDispatchCrossCoreStep_mappingStage P1)).trans
    (MappingStage.of_objects_eq (Architecture.IpcBufferRead.syncUserWords_objects _ _ _))

/-- **The syscall entry keeps every live mapping recorded**, from the kernel's
invariant bundle and the ASID table's table invariant on the state it starts
from (`MappingArmPremises.of_proofLayerInvariantBundle`). -/
theorem syscallDispatchEntryState_preserves_liveMappingsRecorded (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hB : Architecture.proofLayerInvariantBundle st)
    (hA : st.asidTable.invExtK) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).liveMappingsRecorded :=
  (syscallDispatchEntryState_mappingStage ctx e syscallId trapped frame bytes n st
    (MappingArmPremises.of_proofLayerInvariantBundle hB hA)).preserves
    (objects_invExt_of_capabilityInvariantBundle _ hB.2.1)
    hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### The timer, reschedule, fault and FP/SIMD entries -/

/-- **The timer entry's committed state keeps the mappings recorded**: the
trap-frame save, the tick, the residency settlement, the activation and the
ledger drains. -/
theorem perCoreTimerTickEntryState_mappingStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    MappingStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((saveCapturedTrapFrameAt_mappingStage st coreId frame).trans
    (perCoreTimerTickStep_mappingStage _ coreId)).trans
    (((settleResidencyAt_mappingStage _ coreId).trans (activateThreadAt_mappingStage _ coreId)).trans
      (clearLedgers_mappingStage _))

/-- **The reschedule entry's committed state keeps the mappings recorded** (the
secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_mappingStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    MappingStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((((saveCapturedTrapFrameAt_mappingStage st coreId frame).trans
    (perCoreRescheduleStep_mappingStage _ coreId)).trans
    (settleResidencyAt_mappingStage _ coreId)).trans (activateThreadAt_mappingStage _ coreId)).trans
    (clearLedgers_mappingStage _)

/-- The register spill, then the flow-checked delivery. -/
theorem faultDeliveredState_mappingStage (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    MappingStage st (faultDeliveredState lctx st f ectx w c tid) :=
  (writeFaultRegistersToTcb_mappingStage st tid w).trans
    (faultDeliverOnCoreChecked_mappingStage lctx _ tid f _ c)

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem faultEntryDeliver_mappingStage (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId) :
    MappingStage st (faultEntryDeliver lctx st f ectx w c).2 := by
  unfold faultEntryDeliver
  split
  · exact dispatchVacatedCore_mappingStage st c
  · dsimp only
    split
    · exact MappingStage.refl _
    · exact (faultDeliveredState_mappingStage lctx st f ectx w c _).trans
        (scheduleLocalSuccessorFrom_mappingStage _ _ c)

theorem faultEntryStep_mappingStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    MappingStage st (faultEntryStep lctx st ectx w coreId).2 := by
  unfold faultEntryStep
  split
  · split
    · split
      · exact MappingStage.refl _
      · exact faultEntryDeliver_mappingStage lctx st _ ectx w _
    · exact MappingStage.refl _
  · exact MappingStage.refl _

theorem unknownSyscallEntryStep_mappingStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    MappingStage st (unknownSyscallEntryStep lctx st ectx w coreId).2 := by
  unfold unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_mappingStage lctx st _ ectx w _
    · exact MappingStage.refl _
  · exact MappingStage.refl _

/-- **The fault entry's committed state keeps the mappings recorded.** -/
theorem faultEntryState_mappingStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    MappingStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))) :=
  ((saveCapturedTrapFrameAt_mappingStage st coreId (some frame)).trans
    (faultEntryStep_mappingStage lctx _ ectx w coreId)).trans
    (((settleResidencyAt_mappingStage _ coreId).trans (activateThreadAt_mappingStage _ coreId)).trans
      (clearLedgers_mappingStage _))

/-- **The unknown-syscall entry's committed state keeps the mappings recorded.** -/
theorem unknownSyscallEntryState_mappingStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    MappingStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  ((saveCapturedSyscallFrameAt_mappingStage st coreId (some frame)).trans
    (unknownSyscallEntryStep_mappingStage lctx _ ectx w coreId)).trans
    (((settleResidencyAt_mappingStage _ coreId).trans (activateThreadAt_mappingStage _ coreId)).trans
      (clearLedgers_mappingStage _))

/-- The lazy FP/SIMD switch writes the previous owner's saved FP context and the
core's owner slot. -/
theorem fpAccessOnCore_mappingStage (st : SystemState) (c : CoreId)
    (live : Option FpContext) :
    MappingStage st (Architecture.fpAccessOnCore st c live).2 := by
  have hW : ∀ (s : SystemState) (o : SeLe4n.ThreadId) (ctx : FpContext),
      MappingStage s (Architecture.writeFpContextToTcb s o ctx) := fun s o _ => by
    unfold Architecture.writeFpContextToTcb
    exact updateTcb_mappingStage _ _ _
  have hSet : ∀ (s : SystemState) (t? : Option SeLe4n.ThreadId), MappingStage st s →
      MappingStage st (Architecture.setFpOwner s c t?) := fun s _ h =>
    h.trans (MappingStage.of_objects_eq (st := s) rfl)
  unfold Architecture.fpAccessOnCore
  split
  · exact MappingStage.refl _
  · split
    · exact MappingStage.refl _
    · split
      · exact MappingStage.refl _
      · split
        · exact MappingStage.refl _
        · dsimp only
          apply hSet
          split
          · exact hW _ _ _
          · exact MappingStage.refl _

/-- **The FP/SIMD entry's committed state keeps the mappings recorded.** -/
theorem fpAccessEntryState_mappingStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) :
    MappingStage st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) := by
  refine (saveCapturedTrapFrameAt_mappingStage st coreId frame).trans ?_
  refine MappingStage.trans ?_ (activateThreadAt_mappingStage _ coreId)
  refine MappingStage.trans ?_ (settleResidencyAt_mappingStage _ coreId)
  unfold fpAccessEntryStep
  split
  · exact MappingStage.refl _
  · exact (fpAccessOnCore_mappingStage _ _ live).trans (dispatchVacatedCore_mappingStage _ _)

end SeLe4n.Kernel
