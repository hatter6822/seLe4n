/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Dispatch
import SeLe4n.Kernel.ReschedulePendingArms.Entry
import SeLe4n.Kernel.PerCoreTimerEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry
import SeLe4n.Kernel.ReschedulePendingArms.Tick
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery
import SeLe4n.Kernel.ReplyRecvRefusalErrors
import SeLe4n.Kernel.IPC.Invariant.EndpointsAndIpcStatesBack

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

/-- A thread resident on another core is not resumed here: core `c` reloads
its saved context into the bank, then switches to its idle thread, or drops its
current slot. -/
theorem deferResidentElsewhere_runQueueEntryStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueEntryStage st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · rename_i tid _
    have hR := (restoreIncomingContextOnCore_runQueueStage st c tid).entry
    split
    · dsimp only
      split
      · rename_i hS
        exact hR.trans (switchToThreadOnCore_runQueueSwitchStage hS fun _ => .inr (.inr rfl)).entry
      · exact hR.trans (dropCurrentOnCore_runQueueSwitchStage _ c).entry
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
  obtain ⟨hO, hQ, hE, hC, hS⟩ := PriorityInheritance.settleResidencyOnCore_frame st c
  refine SystemState.RunQueueEntryStage.of_frameThen
    (m := PriorityInheritance.settleResidencyOnCore st c) hO hQ hE hC hS A fun h r =>
    ⟨fun k hk => by
      rw [← hO]
      exact (A.1.live (hO ▸ h) (SystemState.runQueueRefined_of_frame
        (fun c t => SystemState.runLinkOn_of_objects hO c t) hQ hE r)).unset k hk,
      fun d tid hR => ?_⟩
  rw [activateThreadOnCore_residentOnCore] at hR
  by_cases hd : d = c
  · rw [hd] at hR
    exact Or.inr (objYieldCodes_fst_zero_of_getTcb? fun t hT =>
      activateThreadOnCore_settle_unlinkedOnCore st c (hO ▸ h) tid t
        (Or.inr (by rw [activateThreadOnCore_residentOnCore]; exact hR)) hT)
  · refine Or.inl ?_
    have e : (PriorityInheritance.settleResidencyOnCore st c).machine.residentOnCore d =
        (PriorityInheritance.deferResidentElsewhere
          (PriorityInheritance.dispatchVacatedCore st c) c).machine.residentOnCore d :=
      PriorityInheritance.settleResidencyOnCore_residentOnCore_ne st c d (Ne.symm hd)
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

/-! ### The trap-frame saves write no scheduler state -/

theorem saveCapturedTrapFrame_scheduler (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedTrapFrame st c frame).scheduler = st.scheduler := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedTrapFrame, Architecture.saveVacatedFrameOnCore_scheduler,
      Architecture.saveTrapFrameOnCore_scheduler]

theorem saveCapturedSyscallFrame_scheduler (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedSyscallFrame st c frame).scheduler = st.scheduler := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedSyscallFrame, Architecture.saveVacatedFrameOnCore_scheduler,
      Architecture.saveTrapFrameOnCore_scheduler]

theorem saveCapturedTrapFrameAt_scheduler (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedTrapFrameAt st coreId frame).scheduler = st.scheduler := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_scheduler st _ frame
  · rfl

theorem saveCapturedSyscallFrameAt_scheduler (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedSyscallFrameAt st coreId frame).scheduler = st.scheduler := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_scheduler st _ frame
  · rfl
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
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st e) st st' := by
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
  have hF := RunQueueStage.of_frame (st := st) (st' := st) rfl rfl rfl
  exact (hF.entry.toOn (SystemState.currentObjOn st e)).trans
    (dispatchSyscallChecked_runQueueEntryStage ctx decoded tid e _ st'
      ((E.of_ipcFrame hF (IpcFrame.of_frame rfl fun _ => rfl)).arm hCur (hNI tid hCur)) h)

/-- **The run queues agree across a refused reply-receive** (WS-SX SX34): the
legs the transition ran before it stopped are the success path's prefix -- the
reply leg, the pop, the transfer, the caller's answer, the context return and
the receive leg, which is an entry stage on either outcome -- and the
nothing-received outcome is a stage. -/
theorem replyRecvTransferStoppedState_runQueueEntryStage {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hRf : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hQ : queueHeadBlockedConsistent st)
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueEntryStage st
      (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant c st) := by
  rcases replyRecvTransferStoppedState_cases epId tid rid prevCaller label msg grant c st with
    hE | ⟨hA, e, hB⟩
  · rw [hE]; exact (RunQueueStage.refl _).entry
  generalize replyRecvTransferStoppedState epId tid rid prevCaller label msg grant c st = s at hB ⊢
  revert hB
  generalize replyRecvCallerFaultAnswer? st prevCaller label msg = answer
  generalize replyRecvLegMessage answer msg = m
  generalize (if answer.isSome = true then none else replyCapRequest st tid grant) = req
  generalize receiverCapTarget? st prevCaller = target
  generalize (recordedReplyServer? st prevCaller).getD tid = rs
  intro hB
  rcases endpointReplyRecvAnsweringBodyR_stopped hInv hA hB with
    ⟨-, hS⟩ | ⟨sgi, ret?, popped, hR1, hPop1, hInvP, hTail⟩
  · rw [hS]; exact (RunQueueStage.refl _).entry
  have hPrev : ∀ sgi?, (endpointReplyOnCore tid prevCaller m c st).2 = .ok sgi? →
      (endpointReplyOnCore tid prevCaller m c st).1.readyOrAbsent prevCaller ∧
      prevCaller ≠ tid ∧ isIdleThreadId prevCaller = false := by
    intro sgi hOk
    obtain ⟨-, tcb', ep, ex, -, hL, hS, -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _ hOk
    have hT := getTcb?_of_lookupTcb _ _ _ hL
    refine ⟨fun x hx => endpointReplyOnCore_ok_target_ready _ _ _ _ _ hInv hOk hx, ?_,
      notIdle_of_blocked hD hT (by rw [hS]; exact fun h => by cases h)⟩
    rintro rfl
    obtain ⟨tcb, hT0, hRun, -⟩ := hD.runnable hCur
    rw [hT] at hT0
    cases hT0
    rw [hS] at hRun
    cases hRun
  have hE := endpointReplyOnCore_runQueueStage tid prevCaller m c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  have hC1 : (endpointReplyOnCore tid prevCaller m c st).1.scheduler.currentOnCore c = some tid :=
    (endpointReplyOnCore_currentOnCore tid prevCaller m c st c).trans hCur
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller m c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward tid prevCaller m c st hInv
  have hCB := endpointReplyOnCore_currentOnCore tid prevCaller m c st
  have hQ1 : ∀ sgi?, (endpointReplyOnCore tid prevCaller m c st).2 = .ok sgi? →
      queueHeadBlockedConsistent (endpointReplyOnCore tid prevCaller m c st).1 := fun _ hOk =>
    endpointReplyOnCore_preserves_queueHeadBlockedConsistent tid prevCaller m c st hInv hQ hOk
  generalize endpointReplyOnCore tid prevCaller m c st = p
    at hE hC1 hInv1 hEB hCB hQ1 hPrev hR1 hPop1 hTail
  obtain ⟨st1, r⟩ := p
  dsimp only at hE hC1 hInv1 hEB hCB hQ1 hPrev hR1 hPop1 hTail
  subst hR1
  obtain ⟨hRdy1, hNe, hNIp⟩ := hPrev _ rfl
  have hH1 := (endpointHeadsWakeable_of hD hQ).of_frame hEB hCB (hQ1 _ rfl)
  have hPop := hPop1
  have hX := receiveTransferCaps_eq_done req none target popped
  generalize receiveTransferCapsDone req none target popped = Dn at hX hTail
  obtain ⟨xs, st1p⟩ := Dn
  dsimp only at hTail
  have hPopS := (replyRecvPopDonation_runQueueStage hPop).trans (receiveTransferCaps_runQueueStage hX)
  have hIq : popped.objects.invExt :=
    let ⟨hI1, hR1⟩ := hE.1.links hInv hRf
    ((replyRecvPopDonation_runQueueStage hPop).1.links hI1 hR1).1
  have hPE : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[oid]? = some (.endpoint ep) →
      st1.objects[oid]? = some (.endpoint ep) := by
    obtain ⟨hQE, -, -⟩ := replyRecvPopDonation_frame hInv1 hPop
    obtain ⟨hXE, -, -⟩ := receiveTransferCaps_ipcFrame hIq hX
    exact fun oid ep hE => hQE oid ep (hXE oid ep hE)
  have hPC : ∀ c, st1p.scheduler.currentOnCore c = st1.scheduler.currentOnCore c := by
    obtain ⟨-, hQC, -⟩ := replyRecvPopDonation_frame hInv1 hPop
    intro c
    rw [← hQC c, receiveTransferCaps_scheduler_eq hX]
  have hPT : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st1p.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st1.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
    obtain ⟨-, -, hQT⟩ := replyRecvPopDonation_frame hInv1 hPop
    obtain ⟨-, -, hXT⟩ := receiveTransferCaps_ipcFrame hIq hX
    intro y tcb' hT
    obtain ⟨t1, h1, e1⟩ := hXT y tcb' hT
    obtain ⟨t0, h0, e0⟩ := hQT y t1 h1
    exact ⟨t0, h0, e0.trans e1⟩
  have hA1 : st1.activeAt tid :=
    activeKeptStage.of_stage hE hInv hRf tid (hD.runnable hCur).activeAt
  have hAp : st1p.activeAt tid :=
    let ⟨hI1, hR1⟩ := hE.1.links hInv hRf
    activeKeptStage.of_stage hPopS hI1 hR1 tid hA1
  have hHp := hH1.of_frame hPE hPC (queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT
      (hQ1 _ rfl))
  obtain ⟨hI1, hR1⟩ := hE.1.links hInv hRf
  obtain ⟨hIp, hRp⟩ := hPopS.1.links hI1 hR1
  have AS := replyRecvAnswerCaller_runQueueEntryStage answer st1p prevCaller xs.capInfo
    ((hPopS.2.2 hI1 hR1).readyOrAbsent hRdy1) hNIp
  obtain ⟨hHa, hCura, hActa⟩ := replyRecvAnswerCaller_receiveEntryFacts answer xs.capInfo hIp hHp
    ((hPC c).trans hC1) hAp hNe
  obtain ⟨hIa, hRa⟩ := AS.1.links hIp hRp
  generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a
    at AS hHa hCura hActa hIa hRa hTail
  have RR := receiveReturnSchedContext_runQueueStage true st1a tid
  obtain ⟨hHR, hCurR, hActR⟩ := receiveReturnSchedContext_receiveEntryFacts true hIa hHa hCura hActa
  have hR := endpointReceiveDualWithCapsOnCore_runQueueEntryStage epId tid (some rid) c
    (receiveReturnSchedContext true st1a tid) hHR hCurR hNI hActR
  have hAll := (((hE.trans hPopS).entry.trans AS).trans RR.entry).trans hR
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) c
    (receiveReturnSchedContext true st1a tid) = q at hAll hTail
  rcases hTail with hS | ⟨st2, next, summary, sgi', hV, hS⟩
  · rw [hS]; exact hAll.trans (replyRecvNothingReceived_runQueueStage _ _ _ _).entry
  subst hV
  rcases hS with hS | ⟨sc, holder, -, hS⟩
  · rw [hS]; exact hAll.trans (replyRecvNothingReceived_runQueueStage _ _ _ _).entry
  rw [hS]
  exact hAll.trans ((replyRecvHolderDeschedule_runQueueStage tid holder st2).trans
    (replyRecvNothingReceived_runQueueStage _ _ _ _)).entry

open SeLe4n.Model.SystemState in
/-- **The run queues agree across a reply-receive whose receive is read after
its reply** (WS-SX SX36.1): `replyRecvTransferStoppedState_runQueueEntryStage`
for the after-reply composite, whose one further stop -- the receive's endpoint
refused on the answered state -- is the nothing-received outcome there, a
stage. -/
theorem replyRecvTransferThenStoppedState_runQueueEntryStage
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hRf : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hQ : queueHeadBlockedConsistent st)
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueEntryStage st (_root_.SeLe4n.Kernel.RefusalCarrying.stoppedState
      (replyRecvTransferThenR recvEp tid rid prevCaller label msg grant c) st) := by
  rcases replyRecvTransferThenR_stoppedState_cases recvEp tid rid prevCaller label msg grant c st
    with hE | ⟨hA, e, hB⟩
  · rw [hE]; exact (RunQueueStage.refl _).entry
  generalize _root_.SeLe4n.Kernel.RefusalCarrying.stoppedState
    (replyRecvTransferThenR recvEp tid rid prevCaller label msg grant c) st = s at hB ⊢
  revert hB
  generalize replyRecvCallerFaultAnswer? st prevCaller label msg = answer
  generalize replyRecvLegMessage answer msg = m
  generalize (if answer.isSome = true then none else replyCapRequest st tid grant) = req
  generalize receiverCapTarget? st prevCaller = target
  generalize (recordedReplyServer? st prevCaller).getD tid = rs
  intro hB
  rcases endpointReplyRecvAnsweringBodyThenR_stopped hInv hA hB with
    ⟨-, hS⟩ | ⟨sgi, ret?, popped, hR1, hPop1, hInvP, hTail⟩
  · rw [hS]; exact (RunQueueStage.refl _).entry
  have hPrev : ∀ sgi?, (endpointReplyOnCore tid prevCaller m c st).2 = .ok sgi? →
      (endpointReplyOnCore tid prevCaller m c st).1.readyOrAbsent prevCaller ∧
      prevCaller ≠ tid ∧ isIdleThreadId prevCaller = false := by
    intro sgi hOk
    obtain ⟨-, tcb', ep, ex, -, hL, hS, -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _ hOk
    have hT := getTcb?_of_lookupTcb _ _ _ hL
    refine ⟨fun x hx => endpointReplyOnCore_ok_target_ready _ _ _ _ _ hInv hOk hx, ?_,
      notIdle_of_blocked hD hT (by rw [hS]; exact fun h => by cases h)⟩
    rintro rfl
    obtain ⟨tcb, hT0, hRun, -⟩ := hD.runnable hCur
    rw [hT] at hT0
    cases hT0
    rw [hS] at hRun
    cases hRun
  have hE := endpointReplyOnCore_runQueueStage tid prevCaller m c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  have hC1 : (endpointReplyOnCore tid prevCaller m c st).1.scheduler.currentOnCore c = some tid :=
    (endpointReplyOnCore_currentOnCore tid prevCaller m c st c).trans hCur
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller m c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward tid prevCaller m c st hInv
  have hCB := endpointReplyOnCore_currentOnCore tid prevCaller m c st
  have hQ1 : ∀ sgi?, (endpointReplyOnCore tid prevCaller m c st).2 = .ok sgi? →
      queueHeadBlockedConsistent (endpointReplyOnCore tid prevCaller m c st).1 := fun _ hOk =>
    endpointReplyOnCore_preserves_queueHeadBlockedConsistent tid prevCaller m c st hInv hQ hOk
  generalize endpointReplyOnCore tid prevCaller m c st = p
    at hE hC1 hInv1 hEB hCB hQ1 hPrev hR1 hPop1 hTail
  obtain ⟨st1, r⟩ := p
  dsimp only at hE hC1 hInv1 hEB hCB hQ1 hPrev hR1 hPop1 hTail
  subst hR1
  obtain ⟨hRdy1, hNe, hNIp⟩ := hPrev _ rfl
  have hH1 := (endpointHeadsWakeable_of hD hQ).of_frame hEB hCB (hQ1 _ rfl)
  have hPop := hPop1
  have hX := receiveTransferCaps_eq_done req none target popped
  generalize receiveTransferCapsDone req none target popped = Dn at hX hTail
  obtain ⟨xs, st1p⟩ := Dn
  dsimp only at hTail
  have hPopS := (replyRecvPopDonation_runQueueStage hPop).trans (receiveTransferCaps_runQueueStage hX)
  have hIq : popped.objects.invExt :=
    let ⟨hI1, hR1⟩ := hE.1.links hInv hRf
    ((replyRecvPopDonation_runQueueStage hPop).1.links hI1 hR1).1
  have hPE : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[oid]? = some (.endpoint ep) →
      st1.objects[oid]? = some (.endpoint ep) := by
    obtain ⟨hQE, -, -⟩ := replyRecvPopDonation_frame hInv1 hPop
    obtain ⟨hXE, -, -⟩ := receiveTransferCaps_ipcFrame hIq hX
    exact fun oid ep hE => hQE oid ep (hXE oid ep hE)
  have hPC : ∀ c, st1p.scheduler.currentOnCore c = st1.scheduler.currentOnCore c := by
    obtain ⟨-, hQC, -⟩ := replyRecvPopDonation_frame hInv1 hPop
    intro c
    rw [← hQC c, receiveTransferCaps_scheduler_eq hX]
  have hPT : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st1p.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st1.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
    obtain ⟨-, -, hQT⟩ := replyRecvPopDonation_frame hInv1 hPop
    obtain ⟨-, -, hXT⟩ := receiveTransferCaps_ipcFrame hIq hX
    intro y tcb' hT
    obtain ⟨t1, h1, e1⟩ := hXT y tcb' hT
    obtain ⟨t0, h0, e0⟩ := hQT y t1 h1
    exact ⟨t0, h0, e0.trans e1⟩
  have hA1 : st1.activeAt tid :=
    activeKeptStage.of_stage hE hInv hRf tid (hD.runnable hCur).activeAt
  have hAp : st1p.activeAt tid :=
    let ⟨hI1, hR1⟩ := hE.1.links hInv hRf
    activeKeptStage.of_stage hPopS hI1 hR1 tid hA1
  have hHp := hH1.of_frame hPE hPC (queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT
      (hQ1 _ rfl))
  obtain ⟨hI1, hR1⟩ := hE.1.links hInv hRf
  obtain ⟨hIp, hRp⟩ := hPopS.1.links hI1 hR1
  have AS := replyRecvAnswerCaller_runQueueEntryStage answer st1p prevCaller xs.capInfo
    ((hPopS.2.2 hI1 hR1).readyOrAbsent hRdy1) hNIp
  obtain ⟨hHa, hCura, hActa⟩ := replyRecvAnswerCaller_receiveEntryFacts answer xs.capInfo hIp hHp
    ((hPC c).trans hC1) hAp hNe
  obtain ⟨hIa, hRa⟩ := AS.1.links hIp hRp
  generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a
    at AS hHa hCura hActa hIa hRa hTail
  rcases hTail with ⟨-, -, hS⟩ | ⟨epId, -, hTail⟩
  · -- the receive's endpoint, read on the answered state, refused
    rw [hS]
    exact ((hE.trans hPopS).entry.trans AS).trans (replyRecvNothingReceived_runQueueStage _ _ _ _).entry
  have RR := receiveReturnSchedContext_runQueueStage true st1a tid
  obtain ⟨hHR, hCurR, hActR⟩ := receiveReturnSchedContext_receiveEntryFacts true hIa hHa hCura hActa
  have hR := endpointReceiveDualWithCapsOnCore_runQueueEntryStage epId tid (some rid) c
    (receiveReturnSchedContext true st1a tid) hHR hCurR hNI hActR
  have hAll := (((hE.trans hPopS).entry.trans AS).trans RR.entry).trans hR
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) c
    (receiveReturnSchedContext true st1a tid) = q at hAll hTail
  rcases hTail with hS | ⟨st2, next, summary, sgi', hV, hS⟩
  · rw [hS]; exact hAll.trans (replyRecvNothingReceived_runQueueStage _ _ _ _).entry
  subst hV
  rcases hS with hS | ⟨sc, holder, -, hS⟩
  · rw [hS]; exact hAll.trans (replyRecvNothingReceived_runQueueStage _ _ _ _).entry
  rw [hS]
  exact hAll.trans ((replyRecvHolderDeschedule_runQueueStage tid holder st2).trans
    (replyRecvNothingReceived_runQueueStage _ _ _ _)).entry

/-- **The caller's answer keeps the executing core's current thread** where the
answered caller is another thread: the staged frame and the restart write a TCB
only, and the abandon deschedules the caller alone. -/
theorem replyRecvAnswerCaller_currentOnCore (answer : Option Architecture.FaultReplyOutcome)
    {S : SystemState} {p tid : SeLe4n.ThreadId} (capInfo : Nat) {c : CoreId}
    (hCur : S.scheduler.currentOnCore c = some tid) (hNe : p ≠ tid) :
    (replyRecvAnswerCaller answer S p capInfo).scheduler.currentOnCore c = some tid := by
  cases answer with
  | none =>
    show (Architecture.stageDeliveredMessage S p capInfo).scheduler.currentOnCore c = some tid
    rw [Architecture.stageDeliveredMessage_scheduler_eq]; exact hCur
  | some o =>
    cases o with
    | restart frame =>
      show (S.updateTcb p _).scheduler.currentOnCore c = some tid
      rw [SystemState.updateTcb_scheduler]; exact hCur
    | abandon =>
      show (faultAbandonOnCore S p (faultAbandonCore S p)).scheduler.currentOnCore c = some tid
      unfold faultAbandonOnCore
      rw [SystemState.updateTcb_scheduler]
      exact removeRunnableOnCore_currentOnCore_fwd S p _ c (Ne.symm hNe) hCur

/-- **The nothing-received outcome keeps the executing core's current thread**,
whatever holder it deschedules: a holder current there keeps the slot
(`descheduleKeepingCurrentOnCore`), any other is removed where it is placed,
and the priority-inheritance walk moves no current slot. -/
theorem replyRecvNothingReceived_currentOnCore (rs : SeLe4n.ThreadId) (c : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) {S : SystemState}
    {tid : SeLe4n.ThreadId} (h : S.scheduler.currentOnCore c = some tid) :
    (replyRecvNothingReceived rs c ret? S).scheduler.currentOnCore c = some tid := by
  unfold replyRecvNothingReceived
  cases ret? with
  | none => rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]; exact h
  | some p =>
    obtain ⟨_, holder⟩ := p
    dsimp only
    rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]
    by_cases hH : S.scheduler.currentOnCore c = some holder
    · rw [descheduleKeepingCurrentOnCore_of_current S holder c hH]; exact h
    · rw [descheduleKeepingCurrentOnCore_of_not_current S holder c hH]
      unfold descheduleAtPlacement descheduleAt
      split
      · exact removeRunnableOnCore_currentOnCore_fwd S holder _ c (fun he => hH (he ▸ h)) h
      · exact h

/-- **The nothing-received state after a reply keeps the endpoint heads blocked
and the executing core's current thread** (WS-SX SX36.1): the run-queue reading
of `replyRecvNothingReceivedAfterReply_facts`. -/
theorem replyRecvNothingReceivedAfterReply_entryFacts
    {answer : Option Architecture.FaultReplyOutcome} {t prev rs : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {rid : SeLe4n.ReplyId}
    {st st1 popped st1p : SystemState} {sgi : Option (CoreId × Concurrency.SgiKind)}
    {ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {xs : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) (hD : st.currentDequeuedUnique)
    (hCur : st.scheduler.currentOnCore c = some t)
    (hR : endpointReplyOnCore t prev msg c st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation rid prev st1 = .ok (ret?, popped))
    (hX : replyRecvReplyTransfer answer st t prev grant popped = .ok (xs, st1p)) :
    queueHeadBlockedConsistent
        (replyRecvNothingReceived rs c ret? (replyRecvAnswerCaller answer st1p prev xs.capInfo)) ∧
      (replyRecvNothingReceived rs c ret?
        (replyRecvAnswerCaller answer st1p prev xs.capInfo)).scheduler.currentOnCore c = some t := by
  obtain ⟨tcb0, hT0, hRun, -⟩ := hD.runnable hCur
  have hNe : prev ≠ t := by
    obtain ⟨-, tcb', ep, ex, -, hL, hS', -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _
      (show (endpointReplyOnCore t prev msg c st).2 = .ok sgi by rw [hR])
    have hT := getTcb?_of_lookupTcb _ _ _ hL
    rintro rfl
    rw [hT] at hT0
    cases hT0
    rw [hS'] at hRun
    cases hRun
  have hQ1 := endpointReplyOnCore_preserves_queueHeadBlockedConsistent t prev msg c st hInv hQ
    (sgi? := sgi) (by rw [hR])
  have hI1 := endpointReplyOnCore_preserves_objects_invExt t prev msg c st hInv
  have hC1 := (endpointReplyOnCore_currentOnCore t prev msg c st c).trans hCur
  rw [hR] at hI1 hC1 hQ1
  have hI2 := replyRecvPopDonation_preserves_objects_invExt rid prev st1 popped ret? hI1 hPop
  have hC2 := ((replyRecvPopDonation_frame hI1 hPop).2.1 c).trans hC1
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have hIp := receiveTransferCaps_objects_invExt hI2 hX
  have hCp : st1p.scheduler.currentOnCore c = some t := by
    rw [receiveTransferCaps_scheduler_eq hX]; exact hC2
  have hIa := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prev xs.capInfo hIp
  obtain ⟨hPE, -, hPT⟩ := replyRecvPopDonation_frame hI1 hPop
  obtain ⟨hXE, -, hXT⟩ := receiveTransferCaps_ipcFrame hI2 hX
  obtain ⟨hE, hT⟩ := replyRecvAnswerCaller_ipcBackward answer st1p prev xs.capInfo hIp
  have B := ((show EndpointsAndIpcStatesBack st1 popped from ⟨hPE, hPT⟩).trans
    (show EndpointsAndIpcStatesBack popped st1p from ⟨hXE, hXT⟩)).trans
    ((show EndpointsAndIpcStatesBack st1p _ from ⟨hE, hT⟩).trans
      (replyRecvNothingReceived_endpointsAndIpcStatesBack rs c ret? _ hIa))
  exact ⟨B.queueHeadBlocked hQ1, replyRecvNothingReceived_currentOnCore rs c ret?
    (replyRecvAnswerCaller_currentOnCore answer xs.capInfo hCp hNe)⟩

/-- **The holder-only deschedule keeps core `c`'s current thread** (WS-SX
SX36.2): the holder current there stays, and another holder's deschedule does
not touch the slot. -/
theorem descheduleKeepingCurrentOnCore_currentOnCore_kept {S : SystemState}
    {holder t : SeLe4n.ThreadId} {c : CoreId} (h : S.scheduler.currentOnCore c = some t) :
    (descheduleKeepingCurrentOnCore S holder c).scheduler.currentOnCore c = some t := by
  by_cases hH : S.scheduler.currentOnCore c = some holder
  · rw [descheduleKeepingCurrentOnCore_of_current S holder c hH]; exact h
  · rw [descheduleKeepingCurrentOnCore_of_not_current S holder c hH]
    unfold descheduleAtPlacement descheduleAt
    split
    · exact removeRunnableOnCore_currentOnCore_fwd S holder _ c (fun he => hH (he ▸ h)) h
    · exact h

/-- **The reply's return, keeping the current slot, keeps core `c`'s current
thread** (WS-SX SX36.2): the pop, the return and the settle write no current
slot, and the holder's deschedule is the holder-only one at `c`. -/
theorem applyReplyDonationOnCore_keep_currentOnCore {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {targetV : SeLe4n.ValidThreadId} {ownerHome c : CoreId}
    {t : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetV ownerHome true c = .ok st')
    (hCur : st.scheduler.currentOnCore c = some t) :
    st'.scheduler.currentOnCore c = some t := by
  unfold applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · exact ((popUnheldReplyHead_frame hInv h).2.1 c).trans hCur
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | exact ((keepDonatedSchedContextResolved_frame hInv h).2.1 c).trans hCur
    | skip
  all_goals
    rename_i st1 hRet
    cases h
    rw [descheduleReturnedHolder_true]
    refine descheduleKeepingCurrentOnCore_currentOnCore_kept ?_
    rw [SchedContextOps.settleReturnedContext_currentOnCore]
    refine Eq.trans ?_ hCur
    exact returnDonatedSchedContextResolved_lift (P := fun s =>
      s.scheduler.currentOnCore c = st.scheduler.currentOnCore c) hRet
      (fun n s hS => by
        show s.scheduler.currentOnCore c = _
        rw [returnDonatedSchedContext_scheduler_eq st s _ _ _ n hS]; rfl)

/-- **The cross-core reply, keeping the current slot, keeps core `c`'s current
thread** (WS-SX SX36.2): the reply leg and the chain walk write no current slot,
and the return keeps it. -/
theorem endpointReplyCrossCoreDispatch_keep_currentOnCore {replier target t : SeLe4n.ThreadId}
    {msg : IpcMessage} {c : CoreId} {st st' : SystemState} {x : Option (CoreId × SgiKind)}
    (hInv : st.objects.invExt)
    (h : endpointReplyCrossCoreDispatch replier target msg c st true = (st', .ok x))
    (hCur : st.scheduler.currentOnCore c = some t) :
    st'.scheduler.currentOnCore c = some t := by
  have hC1 := endpointReplyOnCore_currentOnCore replier target msg c st c
  have hI1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hInv
  unfold endpointReplyCrossCoreDispatch at h
  generalize endpointReplyOnCore replier target msg c st = p at h hC1 hI1
  obtain ⟨st1, r⟩ := p
  dsimp only at h hC1 hI1
  have hC := hC1.trans hCur
  cases r with
  | error e => cases h
  | ok sgi =>
    dsimp only at h
    repeat' (first | split at h | dsimp only at h)
    all_goals first
      | (cases h; done)
      | (cases h; exact hC)
      | (cases h; rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]; exact hC)
      | (rename_i hRet; cases h; rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]
         exact applyReplyDonationOnCore_keep_currentOnCore hI1 hRet hC)
      | (rename_i hRet; cases h; exact applyReplyDonationOnCore_keep_currentOnCore hI1 hRet hC)

/-- **The `.reply` arm's transition, keeping the current slot, keeps core `c`'s
current thread** (WS-SX SX36.2), where the answered caller is not that thread:
the reply, its capability transfer and the caller's answer write no other
current slot. -/
theorem replyTransferOnCoreChecked_keep_currentOnCore {ctx : LabelingContext}
    {replier callerTid t : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st true = .ok ((), st'))
    (hCur : st.scheduler.currentOnCore c = some t) (hNe : callerTid ≠ t) :
    st'.scheduler.currentOnCore c = some t := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · split at h
    · rename_i st1 x hF
      cases h
      unfold faultReplyOnCore at hF
      split at hF
      · cases hF
      split at hF
      · cases hF
      dsimp only at hF
      split at hF
      · cases hF
      rename_i st2 sgi hD
      cases hF
      exact replyRecvAnswerCaller_currentOnCore (some _) 0
        (endpointReplyCrossCoreDispatch_keep_currentOnCore hInv hD hCur) hNe
    · cases h
  · split at h
    · rename_i st1 x hD
      split at h
      · rename_i summary st2 hX
        cases h
        unfold endpointReplyCrossCoreDispatchChecked at hD
        split at hD
        · have hC := endpointReplyCrossCoreDispatch_keep_currentOnCore hInv hD hCur
          unfold replyTransferCaps at hX
          exact replyRecvAnswerCaller_currentOnCore none _
            (by rw [receiveTransferCaps_scheduler_eq hX]; exact hC) hNe
        · cases hD
      · cases h
    · cases h

/-- **The ABI dispatch keeps the agreement**: the argument spill, then the
checked entry, a capability-fault delivery, or a refusal record. -/
theorem syscallDispatchFromAbi_runQueueEntryStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (E : EntryPremises st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st e) st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact (RunQueueStage.refl _).entry.toOn _
  rename_i tid hCur
  split at h
  · cases h; exact (RunQueueStage.refl _).entry.toOn _
  rename_i hIdle
  have hNI : isIdleThreadId tid = false := by simpa using hIdle
  have hW : RunQueueStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  have E1 : EntryPremises (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) :=
    E.of_ipcFrame hW (by
      unfold Platform.FFI.writeFfiRegistersToTcb
      exact IpcFrame.updateTcb _ _ fun _ => rfl)
  have hCur1 : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).scheduler.currentOnCore e
      = some tid := by rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur
  dsimp only at h
  split at h
  · -- WS-SX SX4: a refused receive hands back its busy reply's cancel, a
    -- kernel-entry stage that keeps the endpoint heads blocked.  WS-SX SX34: a
    -- reply-receive's stopped state is a kernel-entry stage too, and raises a
    -- capability fault only where it stopped where it started
    -- (`cancelReceiveBusyReply_cases_of_fault`), so the fault's delivery reads
    -- the heads and the current thread on the two cases it always took.
    rename_i ke hE
    have hS : SystemState.RunQueueEntryStage
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
          (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) := by
      rcases cancelReceiveBusyReply_cases_holder ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) with
        hEq | ⟨_, hd, -, -, hEq⟩ | hA | hB
      · rw [hEq]; exact (RunQueueStage.refl _).entry
      · rw [hEq]; exact cancelReplyHolder_runQueueEntryStage _ hd e
      · obtain ⟨t, _, _, _, _, _, _, _, _, _, hCt, -, -, hEq⟩ := hA.stopped
        rw [hCur1] at hCt
        cases hCt
        rw [hEq]
        refine replyRecvEntryRefusalTaint_induct (fun x => SystemState.RunQueueEntryStage _ x)
          (fun _ _ x hx => SystemState.RunQueueEntryStage.trans hx
            (RunQueueStage.of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _)
              applySyscallTaint_invExt (by rw [applySyscallTaint_scheduler])
              (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
              (by rw [applySyscallTaint_scheduler])).entry) ?_
        exact replyRecvTransferStoppedState_runQueueEntryStage E1.objInv E1.refined E1.dequeued
          E1.queueHeads hCur1 hNI
      · -- WS-SX SX36.1: the after-reply stop is a stage
        obtain ⟨t, -, decoded', gate, rid, prev, badge, grant, -, hCt, -, -, -, -, hEq⟩ := hB
        rw [hCur1] at hCt
        cases hCt
        rw [hEq]
        refine replyRecvAfterReplyRefusalTaint_induct (fun x => SystemState.RunQueueEntryStage _ x)
          (fun _ _ x hx => SystemState.RunQueueEntryStage.trans hx
            (RunQueueStage.of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _)
              applySyscallTaint_invExt (by rw [applySyscallTaint_scheduler])
              (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
              (by rw [applySyscallTaint_scheduler])).entry) ?_
        rcases replyRecvAnsweringThenR_stoppedState_cases ctx (replyRecvReceiveEndpoint ctx gate tid)
            decoded' tid e rid prev badge grant _ with h0 | ⟨st1, hR, h1⟩ | h2
        · rw [h0]; exact (RunQueueStage.refl _).entry
        · rw [h1]; exact replyTransferOnCoreChecked_runQueueEntryStage E1.objInv E1.dequeued hR
        · rw [h2]
          exact replyRecvTransferThenStoppedState_runQueueEntryStage E1.objInv E1.refined
            E1.dequeued E1.queueHeads hCur1 hNI
    have hFF : ∀ f, Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
          (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid ke =
          some f →
        queueHeadBlockedConsistent (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) ∧
        (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)).scheduler.currentOnCore e
          = some tid := by
      intro f hF
      rcases cancelReceiveBusyReply_cases_of_fault E1.objInv hCur1 hE hF with
        hEq | ⟨_, hd, -, -, hEq⟩ | hB
      · rw [hEq]; exact ⟨E1.queueHeads, hCur1⟩
      · rw [hEq]
        exact ⟨cancelReplyHolder_queueHeadBlockedConsistent _ hd e E1.objInv E1.queueHeadCancelFacts,
          by rw [cancelReplyHolder_currentOnCore]; exact hCur1⟩
      · -- WS-SX SX36.1: the after-reply fault fires on the entry state, on the
        -- state the signal arm's reply left, or on the nothing-received state
        rcases hB.fault_stop E1.objInv hCur1 hE hF with ⟨s0, hTS, hS | ⟨prev, mi, regs, msg, grant,
            st1, hR, hS⟩ | ⟨rid, prev, label, msg, grant, st1, popped, st1p, sgi, ret?, xs, hR, hPop,
            hX, hS⟩⟩ <;>
          refine hTS (fun x => queueHeadBlockedConsistent x ∧ x.scheduler.currentOnCore e = some tid)
            (fun _ _ x hx => ⟨queueHeadBlockedConsistent_of_readViewAgreement
              (ipcReadViewAgreement.of_objectsAgreeOffTaint
                (applySyscallTaint_objectsAgreeOffTaint _ _ _)) hx.1,
              by rw [applySyscallTaint_scheduler]; exact hx.2⟩) ?_ <;>
          rw [hS]
        · exact ⟨E1.queueHeads, hCur1⟩
        · obtain ⟨tcb0, hT0, hRun, -⟩ := E1.dequeued.runnable hCur1
          refine ⟨(replyTransferOnCoreChecked_receiveLegFacts E1.objInv E1.queueHeads
            (fun x hx => by rw [hT0] at hx; cases hx; exact hRun) hR).1, ?_⟩
          -- The signal arm's reply keeps the executing core's current thread: the
          -- answered caller waits for its reply, so it is not that ready thread.
          have hNe : prev ≠ tid := by
            rintro rfl
            have hA := replyRecvCallerAwaitsReply_of_replyTransferOnCoreChecked_ok hR
            unfold replyRecvCallerAwaitsReply lookupTcb at hA
            cases hRes : prev.isReserved <;> simp [hRes, hT0, hRun] at hA
          exact replyTransferOnCoreChecked_keep_currentOnCore E1.objInv hR hCur1 hNe
        · exact replyRecvNothingReceivedAfterReply_entryFacts E1.objInv E1.queueHeads E1.dequeued
            hCur1 hR hPop hX
    obtain ⟨hIR, hRR⟩ := hS.1.links E1.objInv E1.refined
    have hDR := hS.2 E1.objInv E1.refined hRR E1.dequeued
    generalize cancelReceiveBusyReply ctx e
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) = stR
      at h hS hFF hIR hRR hDR
    split at h
    · split at h
      · -- a dropped fault: the refusal's state and its ledger record
        cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _ stR
        rw [hL]
        exact ((hW.entry.trans hS).trans ((RunQueueStage.of_frame rfl rfl rfl rfl
          (hS := rfl) (hRes := rfl) :
            RunQueueStage stR { stR with declassificationRefusals := L })).entry).toOn _
      · rename_i fault hF _
        obtain ⟨hQR, hCurR⟩ := hFF fault hF
        cases h
        unfold Platform.FFI.deliverSyscallCapFault
        have hW2 := writeFaultRegistersToTcb_runQueueStage stR tid
          (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30)
        obtain ⟨hI2, hR2⟩ := hW2.1.links hIR hRR
        have hD2 : SystemState.currentDequeuedUnique _ := hW2.2.1 none hIR hRR hR2 hDR
        have hQ2 : queueHeadBlockedConsistent (writeFaultRegistersToTcb stR tid
            (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30)) := by
          unfold writeFaultRegistersToTcb
          exact queueHeadBlockedConsistent_updateTcb_of_ipcState_eq _ _ _ hIR (fun _ => rfl) hQR
        have hCur2 : (writeFaultRegistersToTcb stR tid
            (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30)).scheduler.currentOnCore e
            = some tid := by rw [writeFaultRegistersToTcb_scheduler]; exact hCurR
        exact ((hW.entry.trans hS).trans (hW2.entry.trans
          (faultDeliverOnCoreChecked_runQueueEntryStage _ _ tid _ _ e
            (endpointHeadsWakeable_of hD2 hQ2) hCur2 hNI hI2 hR2
            (hD2.runnable hCur2).activeAt))).toOn _
    · split at h
      · cases h
        exact ((hW.entry.trans hS).trans (RunQueueStage.of_frame
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _))
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
          (hS := by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
          (hRes := by
            unfold Platform.FFI.recordSyscallRefusal Architecture.recordErrorOverflow
            split <;> (try split) <;> (try split) <;> rfl)).entry).toOn _
      · cases h
        exact ((hW.entry.trans hS).trans (RunQueueStage.of_frame
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
          (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
          (hS := by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq])
          (hRes := by
            unfold Platform.FFI.recordSyscallRefusal
            split <;> (try split) <;> rfl)).entry).toOn _
  · rename_i hE
    cases h
    rw [← SystemState.currentObjOn_congr (st' := Platform.FFI.writeFfiRegistersToTcb st tid syscallId
      x0 x1 x2 x3 x4 x5 x6) (by rw [Platform.FFI.writeFfiRegistersToTcb_scheduler])]
    exact (hW.entry.toOn _).trans (syscallEntryChecked_runQueueEntryStage E1
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
  | resumes => exact RunQueueStage.refl _

/-- **The syscall step keeps the agreement**: the ABI dispatch, the caller's
return staging, the drop of a caller whose lent context went back, the local
scheduling point, the residency settlement and the
ledger drains. -/
theorem syscallDispatchCrossCoreStep_runQueueEntryStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState}
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st e) st
      (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
        x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact (syscallDispatchFromAbi_runQueueEntryStage E hD).trans
    ((((((stageCallerReturnFor_runQueueStage _ _ e outcome).entry.trans
    (dropReturnedContextCaller_runQueueStage
      (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st (st.scheduler.currentOnCore e))
      (st.scheduler.currentOnCore e) _ e).entry).trans
    (scheduleLocalSuccessorFrom_runQueueEntryStage _ _ e)).trans
    (settleThenActivateOnCore_runQueueEntryStage _ e)).trans
    (clearLedgers_runQueueStage' _).entry).toOn _)

/-- **The syscall entry's committed state keeps the agreement**: the trap-frame
save, the entry's IPC-buffer words handed to the state, the step, and the
committed state dropping the words. -/
theorem syscallDispatchEntryState_runQueueEntryStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState)
    (E : EntryPremises st) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st e) st
      (Architecture.IpcBufferRead.clearUserWords
        (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
          (Architecture.IpcBufferRead.syncUserWords
            (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) :=
  have hS := (saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hS := by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hRes := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl))
  have hF := (saveCapturedSyscallFrame_ipcFrame st e frame).trans
    (IpcFrame.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      fun _ => by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  have hC := RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 ByteArray.empty 0)
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
    (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  have hL : SystemState.currentObjOn (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n) e = SystemState.currentObjOn st e :=
    SystemState.currentObjOn_congr (by
      rw [Architecture.IpcBufferRead.syncUserWords_scheduler, saveCapturedSyscallFrame_scheduler])
  ((hS.entry.toOn _).trans (hL ▸ syscallDispatchCrossCoreStep_runQueueEntryStage
    (E.of_ipcFrame hS hF))).trans (hC.entry.toOn _)

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
      exact (faultDeliveredState_runQueueEntryStage lctx st f ectx w c _ E.objInv E.refined
        (E.dequeued.runnable hCur).activeAt E.endpointHeads hCur (by simpa using hIdle)).trans
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
    · exact faultEntryDeliver_runQueueEntryStage lctx st _ (unknownSyscallContext ectx) w _ E
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

/-- WS-ZA ZA6.29: and so does an entry that links only threads of `L`. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStageOn.refillsSound
    {L : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (h : SystemState.RunQueueEntryStageOn L st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    st'.refillsSound :=
  (SystemState.refillsSound_iff_except _).mpr
    (h.1.refills _ hInv hR hRel ((SystemState.refillsSound_iff_except _).mp hS))

/-- **The syscall entry keeps the refill state sound** — the bind, the configure
and the bound yield among its arms. -/
theorem syscallDispatchEntryState_preserves_refillsSound (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hRel : st.releaseQueueRefined)
    (hS : st.refillsSound) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).refillsSound :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e trapped frame bytes n st E).refillsSound
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

/-- WS-ZA ZA6.29: and so does an entry that links only threads of `L` — the
yieldTo's link is set at both ends. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStageOn.yieldLinksAgree
    {L : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (h : SystemState.RunQueueEntryStageOn L st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hY : st.yieldLinksAgree) : st'.yieldLinksAgree :=
  h.1.yield hInv hR hY

/-- **The syscall entry keeps the yield link in agreement.** -/
theorem syscallDispatchEntryState_preserves_yieldLinksAgree (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hY : st.yieldLinksAgree) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).yieldLinksAgree :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e trapped frame bytes n st E
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

/-! ### The notification link across every entry -/

/-- WS-SX SX8.3: **a kernel entry keeps the notification link in agreement**: its
link half carries it (`RunQueueLinkStage.notificationLinks`) — the bind, the
unbinds, the retype, the retire and the finalise steps among its arms. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStage.notificationLinksAgree {st st' : SystemState}
    (h : SystemState.RunQueueEntryStage st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hY : notificationLinksAgree st) : notificationLinksAgree st' :=
  h.1.notificationLinks hInv hR hY

/-- WS-SX SX8.3: and so does an entry that links only threads of `L`. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueEntryStageOn.notificationLinksAgree
    {L : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (h : SystemState.RunQueueEntryStageOn L st st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) (hY : notificationLinksAgree st) : notificationLinksAgree st' :=
  h.1.notificationLinks hInv hR hY

/-- **The syscall entry keeps the notification link in agreement.** -/
theorem syscallDispatchEntryState_preserves_notificationLinksAgree (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st) (hY : notificationLinksAgree st) :
    notificationLinksAgree (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) :=
  (syscallDispatchEntryState_runQueueEntryStage ctx e trapped frame bytes n st E
    ).notificationLinksAgree E.objInv E.refined hY

/-- **The timer entry keeps the notification link in agreement.** -/
theorem perCoreTimerTickEntryState_preserves_notificationLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hY : notificationLinksAgree st)
    (hInv' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD' : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi' : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff' : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d) :
    notificationLinksAgree (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  (perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv' hRef' hD' hBi' hAff'
    ).notificationLinksAgree hInv hR hY

/-- **The reschedule entry keeps the notification link in agreement.** -/
theorem perCoreRescheduleEntryState_preserves_notificationLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hY : notificationLinksAgree st) :
    notificationLinksAgree (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  (perCoreRescheduleEntryState_runQueueEntryStage coreId frame st).notificationLinksAgree hInv hR hY

/-- **The fault entry keeps the notification link in agreement.** -/
theorem faultEntryState_preserves_notificationLinksAgree (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hY : notificationLinksAgree st) :
    notificationLinksAgree (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  (faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E).notificationLinksAgree
    E.objInv E.refined hY

/-- **The unknown-syscall entry keeps the notification link in agreement.** -/
theorem unknownSyscallEntryState_preserves_notificationLinksAgree (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (st : SystemState)
    (E : EntryPremises st) (hY : notificationLinksAgree st) :
    notificationLinksAgree (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  (unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E).notificationLinksAgree
    E.objInv E.refined hY

/-- **The FP/SIMD entry keeps the notification link in agreement.** -/
theorem fpAccessEntryState_preserves_notificationLinksAgree (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hY : notificationLinksAgree st) :
    notificationLinksAgree (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) :=
  (fpAccessEntryState_runQueueEntryStage coreId frame live st).notificationLinksAgree hInv hR hY

/-! ### The interrupt entry (WS-ZA ZA6.32) -/

/-- The mask writes the machine's mask and the physical-write ledger alone. -/
theorem setInterruptLineMask_runQueueStage (st : SystemState) (line : Nat) (masked : Bool) :
    RunQueueStage st (Architecture.setInterruptLineMask st line masked) :=
  RunQueueStage.of_frame rfl rfl rfl

/-- **seL4's `handleInterrupt` on a core keeps the run queues in agreement**:
seL4's `sendSignal` (the bound-aware signal's stage and the stash clear, then
the donation to the thread it woke), then the mask. -/
theorem handleInterruptOnCore_runQueueStage (st : SystemState) (c : CoreId) (line : Nat)
    (hHeads : notificationHeadsWakeable st) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (handleInterruptOnCore st c line) := by
  unfold handleInterruptOnCore
  split
  · rename_i ntfn badge _
    have hB := sendSignalOnCore_runQueueStage ntfn badge c st hHeads hBlk
    exact (hB).trans
      (setInterruptLineMask_runQueueStage _ _ _)
  · exact setInterruptLineMask_runQueueStage _ _ _

theorem interruptEntryStep_runQueueStage (st : SystemState) (coreId intId : UInt64)
    (E : EntryPremises st) : RunQueueStage st (interruptEntryStep st coreId intId) :=
  interruptEntryStep_of (P := RunQueueStage st) st coreId intId (RunQueueStage.refl _)
    (fun c _ _ => handleInterruptOnCore_runQueueStage st c _ E.ntfnHeads E.blocked)

/-- **The interrupt entry's committed state keeps the agreement**: the save,
the step, the settle and activation, and the ledger drains. -/
theorem interruptEntryState_runQueueEntryStage (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (E : EntryPremises st) :
    SystemState.RunQueueEntryStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) :=
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId frame
  ((hS.entry.trans (interruptEntryStep_runQueueStage _ coreId intId
    (E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _))).entry).trans
    ((settleThenActivateAt_runQueueEntryStage _ coreId).trans (clearLedgers_runQueueStage _).entry))

/-- **The interrupt entry keeps the refill state sound.** -/
theorem interruptEntryState_preserves_refillsSound (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (E : EntryPremises st)
    (hRel : st.releaseQueueRefined) (hS : st.refillsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))).refillsSound :=
  (interruptEntryState_runQueueEntryStage coreId intId frame st E).refillsSound
    E.objInv E.refined hRel hS

/-- **The interrupt entry keeps the yield link in agreement.** -/
theorem interruptEntryState_preserves_yieldLinksAgree (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (E : EntryPremises st)
    (hY : st.yieldLinksAgree) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))).yieldLinksAgree :=
  (interruptEntryState_runQueueEntryStage coreId intId frame st E).yieldLinksAgree
    E.objInv E.refined hY

/-- **The interrupt entry keeps the notification link in agreement.** -/
theorem interruptEntryState_preserves_notificationLinksAgree (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (E : EntryPremises st)
    (hY : notificationLinksAgree st) :
    notificationLinksAgree (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) :=
  (interruptEntryState_runQueueEntryStage coreId intId frame st E).notificationLinksAgree
    E.objInv E.refined hY

end SeLe4n.Kernel
