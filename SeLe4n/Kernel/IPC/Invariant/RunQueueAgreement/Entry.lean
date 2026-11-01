/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Dispatch
import SeLe4n.Kernel.ReschedulePendingArms.Entry
import SeLe4n.Kernel.PerCoreTimerEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry
import SeLe4n.Kernel.ReschedulePendingArms.Tick

/-!
# Every committing entry keeps the run-queue link agreement

WS-ZA ZA4.5 part 2.  The pure step each state-committing entry runs — the
syscall, the timer tick, the reschedule interrupt, the two fault
entries and the FP/SIMD access — is a `RunQueueStage`: the trap-frame save, the
step itself, the local scheduling point, the residency settlement and the
ledger drains, each a stage.  So a state the boot left in agreement stays in
agreement across every entry the kernel commits.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### The current contexts' placement -/

/-- WS-ZA ZA6.4: **every core's current context is placeable on its core** in a
state whose current threads are homed on their cores (`currentDequeuedUnique`),
whose bindings are paired, and whose release queues are affinity-consistent: the
context a current thread's binding names names it back, so it is bound, and it
is linked on its thread's home core or on none — the precondition of the
charge's postpone (`SystemState.currentContextPlaceableOnCore`), discharged by
the kernel's invariants. -/
theorem currentContextPlaceableOnCore_of_invariants {st : SystemState} (c : CoreId)
    (hRef : st.releaseQueueRefined) (hD : st.currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional st)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d) :
    st.currentContextPlaceableOnCore c := by
  intro tid tcb scId sc hCur hT hb hS
  have hH := currentBoundHomedOnCore_of_placement st c hD hBi tid tcb hCur hT
  have hB := hH.2 scId sc hb hS
  exact ⟨by rw [hB]; rfl, releaseFreeFor_of_boundHome hRef hAff hS hB hH.1⟩

/-- ...and on the tick's prepared state, after the drain: the drain moves no
thread, no binding and no current slot, and keeps the release queues refined
and affinity-consistent. -/
theorem timerTickOnCorePrepared_currentContextPlaceableOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined) (hD : st.currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional st)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d) :
    (timerTickOnCorePrepared st c).currentContextPlaceableOnCore c := by
  intro tid tcb scId sc hCur hT hb hS
  have hH := timerTickOnCorePrepared_currentBoundHomedOnCore st c hInv hD hBi tid tcb hCur hT
  have hB := hH.2 scId sc hb hS
  have hRef' : (timerTickOnCorePrepared st c).releaseQueueRefined := by
    simp only [timerTickOnCorePrepared]
    exact processReplenishmentsDueOnCore_preserves_releaseQueueRefined _ c _ hInv
      (SystemState.releaseStateAgree.refined
        (SystemState.releaseStateAgree.of_objects_eq (st := st) (by rfl) (by rfl)) hRef)
  exact ⟨by rw [hB]; rfl, releaseFreeFor_of_boundHome hRef'
    (timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore st c hInv hRef hAff)
    hS hB hH.1⟩

/-! ### The scheduler's own steps -/

/-- The outgoing thread's re-enqueue at a domain boundary: the context save,
then the guarded enqueue of core `c`'s current thread on `c` — it opens `c`'s
scheduling point. -/
theorem requeueOutgoingOnCore_runQueueWindowStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueWindowStage (.preempt c) st (requeueOutgoingOnCore st c) := by
  have hS := (saveOutgoingContextOnCore_runQueueStage st c).window (.preempt c)
  unfold requeueOutgoingOnCore; dsimp only
  split
  · exact hS
  next tid hCur =>
    split
    next tcb _ =>
      split
      next hA =>
        refine SystemState.RunQueueWindowStage.of_invExt fun hInv => ?_
        have hCode : ∀ y, ((saveOutgoingContextOnCore st c).getTcb? y).map TCB.runCoreCode =
            (st.getTcb? y).map TCB.runCoreCode := by
          intro y; unfold saveOutgoingContextOnCore; split
          · rfl
          · exact SystemState.updateTcb_runCoreCode _ _
              (fun outTcb => { outTcb with registerContext := st.machine.regsOnCore c })
              (fun _ => rfl) hInv y
        have hA' : (saveOutgoingContextOnCore st c).runEnqueueAdmits c tid = true := by
          rw [SystemState.runEnqueueAdmits_congr (hCode tid) c]; exact hA
        have h2 := SystemState.RunQueueWindowStage.requeueCurrent
          (saveOutgoingContextOnCore st c) c tid tcb.boostedPriority
          (by rw [saveOutgoingContextOnCore_scheduler]; exact hCur)
        rw [SystemState.runEnqueueOnCore_of_admits _ hA'] at h2
        exact hS.trans h2
      · exact hS
    · exact hS

/-- The domain switch: the outgoing thread's re-enqueue opens core `c`'s
scheduling point, and emptying `c`'s current slot closes it. -/
theorem switchDomainOnCore_runQueueEntryStage {st st' : SystemState} {c : CoreId}
    (h : switchDomainOnCore st c = .ok st') : SystemState.RunQueueEntryStage st st' := by
  unfold switchDomainOnCore at h
  split at h
  · cases h; exact (RunQueueStage.refl _).entry
  · dsimp only at h
    split at h
    · cases h
    · cases h
      refine (requeueOutgoingOnCore_runQueueWindowStage st c).dispatch
        (vacateCurrent_runQueueDispatchStage rfl rfl rfl fun c' => ?_)
      show _ = if c' = c then _ else _
      by_cases hc : c' = c
      · subst hc; simp
      · rw [if_neg hc]
        simp only [SchedulerState.setDomainScheduleIndexOnCore_currentOnCore,
          SchedulerState.setDomainTimeRemainingOnCore_currentOnCore,
          SchedulerState.setActiveDomainOnCore_currentOnCore]
        exact SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)

theorem scheduleDomainOnCore_runQueueEntryStage {st st' : SystemState} {c : CoreId}
    (h : scheduleDomainOnCore st c = .ok st') : SystemState.RunQueueEntryStage st st' := by
  unfold scheduleDomainOnCore at h
  split at h
  · cases h; exact (RunQueueStage.refl _).entry
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        exact (switchDomainOnCore_runQueueEntryStage hD).trans
          (scheduleEffectiveOnCore_runQueueDispatchStage h).stage.entry
    · cases h
      exact RunQueueStage.entry (RunQueueStage.of_frame rfl rfl rfl)

/-- The per-core timer step: the boot core's clock, the tick, the domain
accounting.  The tick's postpone reads the kernel's placement invariants at the
step's state (`timerTickOnCorePrepared_currentContextPlaceableOnCore`), as the
step's reschedule coverage does (`perCoreTimerTickStep_stepCovers`). -/
theorem perCoreTimerTickStep_runQueueEntryStage (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined) (hD : st.currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional st)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d) :
    SystemState.RunQueueEntryStage st (perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : RunQueueStage st (tickClockedState st ⟨coreId.toNat, hc⟩) := by
      unfold tickClockedState; split
      · exact RunQueueStage.of_frame rfl rfl rfl
      · exact RunQueueStage.refl _
    have hCInv : (tickClockedState st ⟨coreId.toNat, hc⟩).objects.invExt := by
      rw [tickClockedState_objects]; exact hInv
    have hCRef : (tickClockedState st ⟨coreId.toNat, hc⟩).releaseQueueRefined := by
      unfold tickClockedState; split <;> exact hRef
    have hCBi : schedContextBindingBidirectional (tickClockedState st ⟨coreId.toNat, hc⟩) := by
      unfold tickClockedState; split <;> exact hBi
    have hCAff : ∀ d, replenishQueueAffinityConsistentOnCore
        (tickClockedState st ⟨coreId.toNat, hc⟩) d := by
      unfold tickClockedState; split <;> exact hAff
    have hCD : (tickClockedState st ⟨coreId.toNat, hc⟩).currentDequeuedUnique :=
      SystemState.currentDequeuedUniqueExcept_of_eq (st := st)
        (by rw [tickClockedState_scheduler])
        (fun c t => by unfold SystemState.runLinkOn SystemState.getTcb?; rw [tickClockedState_objects])
        (SystemState.StateMono.of_objects (tickClockedState_objects _ _)) hD
    exact (hClk.entry.trans (timerTickOnCore_runQueueEntryStage _ _
      (timerTickOnCorePrepared_currentContextPlaceableOnCore _ _ hCInv hCRef hCD hCBi hCAff))).trans
      (scheduleDomainOnCore_runQueueEntryStage (scheduleDomainOnCore_eq_state _ _))
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact (RunQueueStage.refl _).entry

/-- The reschedule interrupt's step. -/
theorem perCoreRescheduleStep_runQueueEntryStage (st : SystemState) (coreId : UInt64) :
    SystemState.RunQueueEntryStage st (perCoreRescheduleStep st coreId) := by
  unfold perCoreRescheduleStep
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueEntryStage hR
    · exact (RunQueueStage.refl _).entry
  · exact (RunQueueStage.refl _).entry

theorem dispatchVacatedCore_runQueueEntryStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage st (PriorityInheritance.dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact (RunQueueStage.refl _).entry
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueEntryStage hR
    · exact (RunQueueStage.refl _).entry

/-- The executing core's scheduling point after a committed step. -/
theorem scheduleLocalSuccessorFrom_runQueueEntryStage (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage post
      (PriorityInheritance.scheduleLocalSuccessorFrom caller? post c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore_runQueueEntryStage hR
    · exact (RunQueueStage.refl _).entry
  · exact (RunQueueStage.refl _).entry

/-- A thread resident on another core is not resumed here: core `c` switches
to its idle thread, or drops its current slot. -/
theorem deferResidentElsewhere_runQueueEntryStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · split
    · split
      · rename_i hS
        exact (switchToThreadOnCore_runQueueSwitchStage hS fun _ => .inr (.inr rfl)).entry
      · exact (dropCurrentOnCore_runQueueSwitchStage st c).entry
    · exact (RunQueueStage.refl _).entry
  · exact (RunQueueStage.refl _).entry

/-- A slot named by a thread whose TCB, if any, holds no yield link holds yield-to
code `0`. -/
theorem objYieldCodes_fst_zero_of_getTcb? {st : SystemState} {tid : SeLe4n.ThreadId}
    (h : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) :
    (objYieldCodes st.objects[tid.toObjId]?).1 = 0 := by
  cases hT : st.getTcb? tid with
  | some t => rw [objYieldCodes_of_getTcb? hT]; exact h t hT
  | none =>
    cases hF : (objYieldCodes st.objects[tid.toObjId]?).1 with
    | zero => rfl
    | succ n =>
      obtain ⟨t, hT', -⟩ := getTcb?_of_objYieldCodes_fst hF
      rw [SeLe4n.ThreadId.toObjId_injective _ _ (SeLe4n.ThreadId.toObjId_ofObjId _), hT] at hT'
      cases hT'

/-- WS-ZA ZA6.8: **the residency record and the activation after it are one
stage**.  The record makes core `c`'s current thread (or none) its resident,
and that thread may hold a yield link until the activation completes it; the
activation writes no residency record (`activateThreadOnCore_residentOnCore`)
and leaves the core's current thread unlinked
(`activateThreadOnCore_settle_unlinkedOnCore`), so together they make no
linked thread resident.  The record alone is no stage: it is the one write
that sets a resident thread. -/
theorem recordResidentThenActivate_runQueueEntryStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage
      (PriorityInheritance.deferResidentElsewhere (PriorityInheritance.dispatchVacatedCore st c) c)
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c) := by
  have A := (activateThreadOnCore_runQueueStage (PriorityInheritance.settleResidencyOnCore st c) c).entry
  refine SystemState.RunQueueEntryStage.of_frameThen
    (m := PriorityInheritance.settleResidencyOnCore st c) rfl rfl rfl rfl rfl rfl A fun h r =>
    ⟨(A.1.live h (SystemState.runQueueRefined_of_frame
      (fun c t => SystemState.runLinkOn_of_objects rfl c t) rfl rfl r)).unset, fun d tid hR => ?_⟩
  rw [activateThreadOnCore_residentOnCore] at hR
  by_cases hd : d = c
  · rw [hd] at hR
    exact Or.inr (objYieldCodes_fst_zero_of_getTcb? fun t hT =>
      activateThreadOnCore_settle_unlinkedOnCore st c h tid t
        (Or.inr (by rw [activateThreadOnCore_residentOnCore]; exact hR)) hT)
  · refine Or.inl ?_
    have e : (PriorityInheritance.settleResidencyOnCore st c).machine.residentOnCore d =
        (PriorityInheritance.deferResidentElsewhere
          (PriorityInheritance.dispatchVacatedCore st c) c).machine.residentOnCore d := by
      simp only [PriorityInheritance.settleResidencyOnCore]
      exact MachineState.residentOnCore_setResidentOnCore_ne _ _ _ _ (Ne.symm hd)
    rw [← e]; exact hR

/-- **Residency settlement and the activation**: the vacated core's dispatch,
the deferral of a thread resident elsewhere, then the residency record with the
activation after it. -/
theorem settleThenActivateOnCore_runQueueEntryStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage st
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c) :=
  ((dispatchVacatedCore_runQueueEntryStage st c).trans
    (deferResidentElsewhere_runQueueEntryStage _ c)).trans
      (recordResidentThenActivate_runQueueEntryStage st c)

theorem settleThenActivateAt_runQueueEntryStage (st : SystemState) (coreId : UInt64) :
    SystemState.RunQueueEntryStage st
      (activateThreadAt (PriorityInheritance.settleResidencyAt st coreId) coreId) := by
  unfold PriorityInheritance.settleResidencyAt activateThreadAt
  cases Concurrency.coreIdOfUInt64? coreId with
  | some c => exact settleThenActivateOnCore_runQueueEntryStage st c
  | none => exact (RunQueueStage.refl _).entry

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

/-- The trap-frame saves write registers alone: they change no thread's IPC
blocking. -/
theorem saveTrapFrameOnCore_ipcFrame (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile) :
    IpcFrame st (Architecture.saveTrapFrameOnCore st c rf) := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    next tid _ =>
      split
      · dsimp only
        exact (IpcFrame.updateTcb st tid (f := fun t => { t with registerContext := rf })
          fun _ => rfl).trans (IpcFrame.of_frame rfl fun _ => rfl)
      · exact IpcFrame.refl _
    · exact IpcFrame.refl _
  · exact IpcFrame.refl _

theorem saveVacatedFrameOnCore_ipcFrame (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) :
    IpcFrame st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact IpcFrame.updateTcb _ _ fun _ => rfl
      · exact IpcFrame.refl _
    · exact IpcFrame.refl _
  · exact IpcFrame.refl _

theorem saveCapturedTrapFrame_ipcFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    IpcFrame st (Architecture.saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact IpcFrame.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_ipcFrame st c _).trans (saveVacatedFrameOnCore_ipcFrame _ c _ _)

theorem saveCapturedSyscallFrame_ipcFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    IpcFrame st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact IpcFrame.refl _
  | some ic =>
    exact (saveTrapFrameOnCore_ipcFrame st c _).trans (saveVacatedFrameOnCore_ipcFrame _ c _ _)

theorem saveCapturedTrapFrameAt_ipcFrame (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    IpcFrame st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_ipcFrame st _ frame
  · exact IpcFrame.refl _

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
theorem syscallEntryChecked_runQueueEntryStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState}
    (E : EntryPremises st)
    (hNI : ∀ tid, st.scheduler.currentOnCore e = some tid → isIdleThreadId tid = false)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
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
  have hF := RunQueueStage.of_frame (st := st) (st' := { st with perCoreTlb := t }) rfl rfl rfl
  exact hF.entry.trans
    (dispatchSyscallChecked_runQueueEntryStage ctx decoded tid e _ st'
      ((E.of_ipcFrame hF (IpcFrame.of_frame rfl fun _ => rfl)).arm hCur (hNI tid hCur)) h)

/-- **The ABI dispatch keeps the agreement**: the argument spill, then the
checked entry, a capability-fault delivery, or a refusal record. -/
theorem syscallDispatchFromAbi_runQueueEntryStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (E : EntryPremises st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact (RunQueueStage.refl _).entry
  rename_i tid hCur
  split at h
  · cases h; exact (RunQueueStage.refl _).entry
  rename_i hIdle
  have hNI : isIdleThreadId tid = false := by simpa using hIdle
  have hW : RunQueueStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  have E1 : EntryPremises (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) :=
    E.of_ipcFrame hW (by
      unfold Platform.FFI.writeFfiRegistersToTcb
      exact IpcFrame.updateTcb _ _ fun _ => rfl)
  have hCur1 : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).scheduler.currentOnCore e
      = some tid := by rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur
  dsimp only at h
  split at h
  · split at h
    · cases h
      unfold Platform.FFI.deliverSyscallCapFault
      have hW2 := writeFaultRegistersToTcb_runQueueStage
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid
        (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
      have E2 := E1.of_ipcFrame hW2 (by
        unfold writeFaultRegistersToTcb
        exact IpcFrame.updateTcb _ _ fun _ => rfl)
      exact (hW.trans hW2).entry.trans
        (faultDeliverOnCoreChecked_runQueueEntryStage _ _ tid _ _ e E2.endpointHeads
          (by rw [writeFaultRegistersToTcb_scheduler]; exact hCur1) hNI)
    · cases h
      exact (hW.trans (RunQueueStage.of_frame
        (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
        (hT := by unfold Platform.FFI.recordSyscallRefusal; split <;> (try split) <;> rfl)
        (hS := by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
        (hRes := by unfold Platform.FFI.recordSyscallRefusal; split <;> (try split) <;> rfl))).entry
  · rename_i hE
    cases h
    exact hW.entry.trans (syscallEntryChecked_runQueueEntryStage E1
      (fun t ht => by rw [hCur1] at ht; cases ht; exact hNI) hE)

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
theorem syscallDispatchCrossCoreStep_runQueueEntryStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st : SystemState}
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact (syscallDispatchFromAbi_runQueueEntryStage E hD).trans
    ((((stageCallerReturnFor_runQueueStage _ _ e outcome).entry.trans
    (scheduleLocalSuccessorFrom_runQueueEntryStage _ _ e)).trans
    (settleThenActivateOnCore_runQueueEntryStage _ e)).trans
    (clearLedgers_runQueueStage' _).entry)

/-- **The syscall entry's committed state keeps the agreement**: the trap-frame
save, the entry's IPC-buffer words handed to the state, the step, and the
committed state dropping the words. -/
theorem syscallDispatchEntryState_runQueueEntryStage (ctx : LabelingContext) (e : CoreId)
    (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState)
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) :=
  have hS := (saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hT := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
      (hS := by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hRes := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl))
  have hF := (saveCapturedSyscallFrame_ipcFrame st e frame).trans
    (IpcFrame.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      fun _ => by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  have hC := RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 ByteArray.empty 0)
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  (hS.entry.trans (syscallDispatchCrossCoreStep_runQueueEntryStage (E.of_ipcFrame hS hF))).trans
    hC.entry

/-- **The syscall entry keeps the table references recorded**, so the retire's
read of an object's own back-links (`SystemState.tableBackLinksClear`) answers
what a walk of the registry and the interrupt table would. -/
theorem syscallDispatchEntryState_preserves_tableReferencesRecorded (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hT : st.tableReferencesRecorded) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).tableReferencesRecorded :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e syscallId trapped frame bytes n st E).tableReferencesRecorded
    hInv hR hT

/-! ### The timer, reschedule, fault and FP/SIMD entries -/

/-- **The timer entry's committed state keeps the agreement**: the trap-frame
save, the tick, the residency settlement and the ledger drains.  The tick reads
the placement invariants at the state it runs from, the saved one. -/
theorem perCoreTimerTickEntryState_runQueueEntryStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d) :
    SystemState.RunQueueEntryStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((saveCapturedTrapFrameAt_runQueueStage st coreId frame).entry.trans
    (perCoreTimerTickStep_runQueueEntryStage _ coreId hInv hRef hD hBi hAff)).trans
    ((settleThenActivateAt_runQueueEntryStage _ coreId).trans (clearLedgers_runQueueStage _).entry)

/-- **The reschedule entry's committed state keeps the agreement** (the
secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_runQueueEntryStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    SystemState.RunQueueEntryStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  (((saveCapturedTrapFrameAt_runQueueStage st coreId frame).entry.trans
    (perCoreRescheduleStep_runQueueEntryStage _ coreId)).trans
    (settleThenActivateAt_runQueueEntryStage _ coreId)).trans
    (clearLedgers_runQueueStage _).entry

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem faultEntryDeliver_runQueueEntryStage (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (faultEntryDeliver lctx st f ectx w c).2 := by
  unfold faultEntryDeliver
  split
  · exact dispatchVacatedCore_runQueueEntryStage st c
  · rename_i tid hCur
    dsimp only
    split
    · exact (RunQueueStage.refl _).entry
    · rename_i hIdle
      exact (faultDeliveredState_runQueueEntryStage lctx st f ectx w c _ E.objInv
        E.endpointHeads hCur (by simpa using hIdle)).trans
        (scheduleLocalSuccessorFrom_runQueueEntryStage _ _ c)

theorem faultEntryStep_runQueueEntryStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (faultEntryStep lctx st ectx w coreId).2 := by
  unfold faultEntryStep
  split
  · split
    · split
      · exact (RunQueueStage.refl _).entry
      · exact faultEntryDeliver_runQueueEntryStage lctx st _ ectx w _ E
    · exact (RunQueueStage.refl _).entry
  · exact (RunQueueStage.refl _).entry

theorem unknownSyscallEntryStep_runQueueEntryStage (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (unknownSyscallEntryStep lctx st ectx w coreId).2 := by
  unfold unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_runQueueEntryStage lctx st _ ectx w _ E
    · exact (RunQueueStage.refl _).entry
  · exact (RunQueueStage.refl _).entry

/-- **The fault entry's committed state keeps the agreement.** -/
theorem faultEntryState_runQueueEntryStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId (some frame)
  ((hS.entry.trans (faultEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _)))).trans
    ((settleThenActivateAt_runQueueEntryStage _ coreId).trans (clearLedgers_runQueueStage _).entry))

theorem saveCapturedSyscallFrameAt_runQueueStage (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    RunQueueStage st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_runQueueStage st _ frame
  · exact RunQueueStage.refl _

/-- **The unknown-syscall entry's committed state keeps the agreement.** -/
theorem unknownSyscallEntryState_runQueueEntryStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  have hS := saveCapturedSyscallFrameAt_runQueueStage st coreId (some frame)
  have hF : IpcFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) := by
    unfold Concurrency.saveCapturedSyscallFrameAt
    split
    · exact saveCapturedSyscallFrame_ipcFrame st _ _
    · exact IpcFrame.refl _
  ((hS.entry.trans (unknownSyscallEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS hF))).trans
    ((settleThenActivateAt_runQueueEntryStage _ coreId).trans (clearLedgers_runQueueStage _).entry))

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
theorem fpAccessEntryState_runQueueEntryStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) :
    SystemState.RunQueueEntryStage st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) := by
  refine (saveCapturedTrapFrameAt_runQueueStage st coreId frame).entry.trans ?_
  refine SystemState.RunQueueEntryStage.trans ?_ (settleThenActivateAt_runQueueEntryStage _ coreId)
  unfold fpAccessEntryStep
  split
  · exact (RunQueueStage.refl _).entry
  · exact (fpAccessOnCore_runQueueStage _ _ live).entry.trans
      (dispatchVacatedCore_runQueueEntryStage _ _)

/-! ### The refill state across every entry -/

/-- WS-ZA ZA6.4: **a kernel entry keeps the refill state sound**: its link half
carries it (`RunQueueLinkStage.refills`) off no context. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStage.refillsSound {st st' : SystemState}
    (h : SystemState.RunQueueEntryStage st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    st'.refillsSound :=
  (SystemState.refillsSound_iff_except _).mpr
    (h.1.refills _ hInv hR hRel ((SystemState.refillsSound_iff_except _).mp hS))

/-- **The syscall entry keeps the refill state sound** — the bind, the configure
and the bound yield among its arms. -/
theorem syscallDispatchEntryState_preserves_refillsSound (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hRel : st.releaseQueueRefined)
    (hS : st.refillsSound) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).refillsSound :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e syscallId trapped frame bytes n st E).refillsSound
    E.objInv E.refined hRel hS

/-- **The timer entry keeps the refill state sound** — the drain's refills and
re-placements, and the charge with its postpone. -/
theorem perCoreTimerTickEntryState_preserves_refillsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hRel : st.releaseQueueRefined)
    (hS : st.refillsSound)
    (hInv' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi' : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff' : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).refillsSound :=
  (perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv' hRef' hD' hBi' hAff').refillsSound
    hInv hR hRel hS

/-- **The reschedule entry keeps the refill state sound.** -/
theorem perCoreRescheduleEntryState_preserves_refillsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hRel : st.releaseQueueRefined)
    (hS : st.refillsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).refillsSound :=
  (perCoreRescheduleEntryState_runQueueEntryStage coreId frame st).refillsSound hInv hR hRel hS

/-- **The fault entry keeps the refill state sound.** -/
theorem faultEntryState_preserves_refillsSound (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).refillsSound :=
  (faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E).refillsSound
    E.objInv E.refined hRel hS

/-- **The unknown-syscall entry keeps the refill state sound.** -/
theorem unknownSyscallEntryState_preserves_refillsSound (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (st : SystemState)
    (E : EntryPremises st) (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).refillsSound :=
  (unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E).refillsSound
    E.objInv E.refined hRel hS

/-- **The FP/SIMD entry keeps the refill state sound.** -/
theorem fpAccessEntryState_preserves_refillsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId).refillsSound :=
  (fpAccessEntryState_runQueueEntryStage coreId frame live st).refillsSound hInv hR hRel hS

/-! ### The yield link across every entry -/

/-- WS-ZA ZA6.6: **a kernel entry keeps the yield link in agreement**: its link
half carries it (`RunQueueLinkStage.yield`) — the yield, the suspend and the
finalise steps among its arms. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStage.yieldLinksAgree {st st' : SystemState}
    (h : SystemState.RunQueueEntryStage st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hY : st.yieldLinksAgree) : st'.yieldLinksAgree :=
  h.1.yield hInv hR hY

/-- **The syscall entry keeps the yield link in agreement.** -/
theorem syscallDispatchEntryState_preserves_yieldLinksAgree (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hY : st.yieldLinksAgree) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).yieldLinksAgree :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e syscallId trapped frame bytes n st E
    ).yieldLinksAgree E.objInv E.refined hY

/-- **The timer entry keeps the yield link in agreement.** -/
theorem perCoreTimerTickEntryState_preserves_yieldLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hY : st.yieldLinksAgree)
    (hInv' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi' : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff' : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).yieldLinksAgree :=
  (perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv' hRef' hD' hBi' hAff'
    ).yieldLinksAgree hInv hR hY

/-- **The reschedule entry keeps the yield link in agreement.** -/
theorem perCoreRescheduleEntryState_preserves_yieldLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hY : st.yieldLinksAgree) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).yieldLinksAgree :=
  (perCoreRescheduleEntryState_runQueueEntryStage coreId frame st).yieldLinksAgree hInv hR hY

/-- **The fault entry keeps the yield link in agreement.** -/
theorem faultEntryState_preserves_yieldLinksAgree (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hY : st.yieldLinksAgree) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).yieldLinksAgree :=
  (faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E).yieldLinksAgree
    E.objInv E.refined hY

/-- **The unknown-syscall entry keeps the yield link in agreement.** -/
theorem unknownSyscallEntryState_preserves_yieldLinksAgree (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (st : SystemState)
    (E : EntryPremises st) (hY : st.yieldLinksAgree) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).yieldLinksAgree :=
  (unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E).yieldLinksAgree
    E.objInv E.refined hY

/-- **The FP/SIMD entry keeps the yield link in agreement.** -/
theorem fpAccessEntryState_preserves_yieldLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hY : st.yieldLinksAgree) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId).yieldLinksAgree :=
  (fpAccessEntryState_runQueueEntryStage coreId frame live st).yieldLinksAgree hInv hR hY

end SeLe4n.Kernel
