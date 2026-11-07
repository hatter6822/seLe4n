-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Dispatch
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.PerCoreTimerEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery

/-! # Every committing entry keeps the records

WS-ZA ZA6.37.  The pure step each state-committing entry runs (the timer tick,
the reschedule interrupt, the device interrupt, the two fault entries, the
FP/SIMD access and the syscall) is a records stage: the trap-frame save, the step
itself, the local scheduling point, the residency settlement and the ledger
drains, each a stage.  The timer, reschedule and FP/SIMD entries read no
premise.  The interrupt's bound signal and the fault deliveries read the
reply-waiter queues' own premises, the reachable state and the running thread,
off the state the step runs from, as the delete's coverage reads its bundle
there (`syscallDispatchEntryState_preserves_residentsHaveTcbs`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### The scheduler's own steps -/

namespace RecordsFrame

/-- The outgoing thread's re-enqueue at a domain boundary: the context save,
then the admitted enqueue of core `c`'s current thread. -/
theorem requeueOutgoingOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.requeueOutgoingOnCore st c) := by
  have F := saveOutgoingContextOnCore st c hInv
  unfold _root_.SeLe4n.Kernel.requeueOutgoingOnCore; dsimp only
  split
  · exact F
  · split
    · split
      · exact F.trans (runEnqueueAdmitted _ _ _ _ F.invExt)
      · exact F
    · exact F

/-- The domain switch: the re-enqueue, then scheduler writes alone. -/
theorem switchDomainOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.switchDomainOnCore st c = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.switchDomainOnCore at h
  split at h
  · cases h; exact refl hInv
  · dsimp only at h
    split at h
    · cases h
    · cases h
      have F := requeueOutgoingOnCore st c hInv
      exact F.trans (of_objects_eq F.invExt rfl rfl)

theorem scheduleDomainOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.scheduleDomainOnCore st c = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.scheduleDomainOnCore at h
  split at h
  · cases h; exact refl hInv
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        have F := switchDomainOnCore hInv hD
        exact F.trans (scheduleEffectiveOnCore F.invExt h)
    · cases h
      exact of_objects_eq hInv rfl rfl

/-- The reschedule interrupt's step. -/
theorem perCoreRescheduleStep (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.perCoreRescheduleStep st coreId) := by
  unfold _root_.SeLe4n.Kernel.perCoreRescheduleStep
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore hInv hR
    · exact refl hInv
  · exact refl hInv

/-- The lazy FP/SIMD switch writes the previous owner's saved FP context and the
core's owner slot. -/
theorem fpAccessOnCore (st : SystemState) (c : CoreId) (live : Option FpContext)
    (hInv : st.objects.invExt) : RecordsFrame st (Architecture.fpAccessOnCore st c live).2 := by
  have hSet : ∀ (s : SystemState) (t? : Option SeLe4n.ThreadId), RecordsFrame st s →
      RecordsFrame st (Architecture.setFpOwner s c t?) := fun s _ F =>
    F.trans (of_objects_eq F.invExt rfl rfl)
  unfold Architecture.fpAccessOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · split
      · exact refl hInv
      · split
        · exact refl hInv
        · dsimp only
          apply hSet
          split
          · unfold Architecture.writeFpContextToTcb
            exact updateTcb _ _ hInv fun _ => rfl
          · exact refl hInv

end RecordsFrame

namespace RecordsStage

/-- The per-core timer step: the boot core's clock, the tick, the domain
accounting. -/
theorem perCoreTimerTickStep (st : SystemState) (coreId : UInt64) :
    RecordsStage st (_root_.SeLe4n.Kernel.perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : RecordsStage st (tickClockedState st ⟨coreId.toNat, hc⟩) :=
      of_frameK fun h => RecordsFrame.of_objects_eq h (tickClockedState_objects _ _)
        (by unfold tickClockedState; split <;> rfl) (by unfold tickClockedState; split <;> rfl)
    exact (hClk.trans (timerTickOnCore _ _)).trans
      (of_frameK fun h => RecordsFrame.scheduleDomainOnCore h (scheduleDomainOnCore_eq_state _ _))
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact refl _

end RecordsStage

/-- The settlement, the activation and the ledger drains every committing entry
ends with. -/
theorem RecordsStage.entryTail (st : SystemState) (coreId : UInt64) :
    RecordsStage st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadAt (PriorityInheritance.settleResidencyAt st coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h => RecordsFrame.settleResidencyAt st coreId h).trans
    (RecordsStage.of_frameK fun h => RecordsFrame.activateThreadAt _ coreId h)).trans
    (RecordsStage.of_frameK fun h => RecordsFrame.clearLedgers _ h)

/-! ### The timer, reschedule and FP/SIMD entries -/

/-- **The timer entry's committed state keeps the records**: the trap-frame
save, the tick, the residency settlement, the activation and the ledger drains. -/
theorem perCoreTimerTickEntryState_recordsStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    RecordsStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h => RecordsFrame.saveCapturedTrapFrameAt st coreId frame h).trans
    (RecordsStage.perCoreTimerTickStep _ coreId)).trans (RecordsStage.entryTail _ coreId)

/-- **The reschedule entry's committed state keeps the records** (the secondary
core's first entry is this one). -/
theorem perCoreRescheduleEntryState_recordsStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    RecordsStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h => RecordsFrame.saveCapturedTrapFrameAt st coreId frame h).trans
    (RecordsStage.of_frameK fun h => RecordsFrame.perCoreRescheduleStep _ coreId h)).trans
    (RecordsStage.entryTail _ coreId)

/-- **The FP/SIMD entry's committed state keeps the records.** -/
theorem fpAccessEntryState_recordsStage (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) :
    RecordsStage st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) := by
  refine (RecordsStage.of_frameK fun h =>
    RecordsFrame.saveCapturedTrapFrameAt st coreId frame h).trans ?_
  refine RecordsStage.trans ?_ (RecordsStage.of_frameK fun h => RecordsFrame.activateThreadAt _ coreId h)
  refine RecordsStage.trans ?_
    (RecordsStage.of_frameK fun h => RecordsFrame.settleResidencyAt _ coreId h)
  unfold fpAccessEntryStep
  split
  · exact RecordsStage.refl _
  · exact RecordsStage.of_frameK fun h =>
      (RecordsFrame.fpAccessOnCore _ _ live h).trans
        (RecordsFrame.dispatchVacatedCore _ _ (RecordsFrame.fpAccessOnCore _ _ live h).invExt)

/-! ### The interrupt entry -/

/-- WS-ZA ZA6.32: the interrupt step: the bound signal, the stash clear and the
woken thread's staging, then the mask, which writes no object.  The signal reads
the reachable state the step runs from. -/
theorem RecordsStage.interruptEntryStep (st : SystemState) (coreId intId : UInt64)
    (hR : ipcReachable st) : RecordsStage st (_root_.SeLe4n.Kernel.interruptEntryStep st coreId intId) :=
  interruptEntryStep_of (P := RecordsStage st) st coreId intId (.refl st) fun c _ _ =>
    handleInterruptOnCore_of (P := RecordsStage st) st c _
      (fun _ h => h.trans (.of_frameK fun hI => RecordsFrame.of_objects_eq hI rfl rfl)) (.refl st)
      (fun ntfn _ _ => interruptSignal_of (P := RecordsStage st) ntfn _ c st
        (RecordsStage.notificationSignalBoundOnCore hR)
        (fun _ _ _ hC => ((((RecordsStage.notificationSignalBoundOnCore hR).trans
          (.of_frameK fun hI => RecordsFrame.clearWokenReceiverStash _ hI hC)).trans
          (stageWokenDelivery_recordsStage _ _ 0)).trans (stageWokenDelivery_recordsStage _ _ 0))))

/-- WS-ZA ZA6.32: **the interrupt entry's committed state keeps the records**,
from the reachable state the step runs from: the trap-frame save writes one
thread's registers and the core's, which the reachable state does not read. -/
theorem interruptEntryState_recordsStage (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hR : ipcReachable (Concurrency.saveCapturedTrapFrameAt st coreId frame)) :
    RecordsStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h => RecordsFrame.saveCapturedTrapFrameAt st coreId frame h).trans
    (RecordsStage.interruptEntryStep _ coreId intId hR)).trans (RecordsStage.entryTail _ coreId)

/-! ### The fault entries -/

/-- Every core's current thread is `.ready` in IPC. -/
def CurrentReady (st : SystemState) : Prop :=
  ∀ c t, st.scheduler.currentOnCore c = some t → CallerReady st t

/-- Between scheduling points every current thread is runnable, so `.ready`. -/
theorem currentReady_of_currentDequeuedUnique {st : SystemState} (h : st.currentDequeuedUnique) :
    CurrentReady st := fun c t hc => by
  rcases (h.current c t hc).2.2 with h' | ⟨tcb, hT, hR⟩
  · cases h'
  · exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, hR.1⟩

/-- A TCB write that keeps the IPC state keeps a thread `.ready`. -/
theorem CallerReady.updateTcb {st : SystemState} {t u : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).ipcState = x.ipcState) (h : CallerReady st t) :
    CallerReady (st.updateTcb u f) t := by
  obtain ⟨tcb, hT, hR⟩ := h
  by_cases hEq : u.toObjId = t.toObjId
  · have hId := SeLe4n.ThreadId.toObjId_injective _ _ hEq
    subst hId
    have := SystemState.updateTcb_getTcb?_self st u f hInv
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT, Option.map_some] at this
    exact ⟨f tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp this, by rw [hf]; exact hR⟩
  · exact ⟨tcb, by rw [SystemState.updateTcb_objects_ne st u f t.toObjId hEq hInv]; exact hT, hR⟩

/-- **The fault delivery keeps the reply-waiter queues**, for a faulting thread
`.ready` in IPC: it waits on no server, and no receive queue it meets has it at
the head. -/
theorem faultDeliverOnCore_preserves_replyWaitersConsistent_of_ready {st : SystemState}
    {tid : SeLe4n.ThreadId} {f : Fault} {fctx : FaultContext} {c : CoreId}
    (hI : st.objects.invExt) (hC : st.replyWaitersConsistent) (hQ : queueHeadBlockedConsistent st)
    (hRd : CallerReady st tid) : (faultDeliverOnCore st tid f fctx c).1.replyWaitersConsistent :=
  faultDeliverOnCore_preserves_replyWaitersConsistent st tid f fctx c hI hC hRd.serverFree
    (fun eid ep r hE hH => ⟨(fun hEq => by
        subst hEq
        obtain ⟨tcb, hT, hR⟩ := hRd
        have := (hQ eid ep r tcb hE hT).1 hH
        rw [hR] at this; cases this),
      receiveHead_serverFree hQ hE hH⟩)

/-- **The register spill, then the flow-checked delivery, keep the records**, for
a faulting thread `.ready` in IPC: the spill writes its registers alone. -/
theorem RecordsStage.faultDeliveredState (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hQ : queueHeadBlockedConsistent st) (hRd : CallerReady st tid) :
    RecordsStage st (_root_.SeLe4n.Kernel.faultDeliveredState lctx st f ectx w c tid) := fun hK => by
  have hI := KernelRecords.objects_invExt hK
  have S1 := RecordsStep.writeFaultRegistersToTcb st tid w hI
  have hQ1 : queueHeadBlockedConsistent (writeFaultRegistersToTcb st tid w) :=
    queueHeadBlockedConsistent_updateTcb_of_ipcState_eq _ _ _ hI (fun _ => rfl) hQ
  have hRd1 : CallerReady (writeFaultRegistersToTcb st tid w) tid :=
    hRd.updateTcb hI (fun _ => rfl)
  have hC1 : (writeFaultRegistersToTcb st tid w).replyWaitersConsistent :=
    hK.2.1.of_views (replyViews_updateTcb_eq _ _ hI fun _ => rfl)
  unfold _root_.SeLe4n.Kernel.faultDeliveredState
  dsimp only
  refine RecordsStage.of_step (S1.trans (RecordsStep.faultDeliverOnCoreChecked (ctx := lctx)
    (t := tid) (f := f) (c := c) S1.invExt hQ1)) (fun _ => ?_) hK
  have hSus : ∀ tf, (recordPendingFault (faultSuspendOnCore (writeFaultRegistersToTcb st tid w)
      tid c) tid tf).replyWaitersConsistent := fun tf =>
    hC1.of_views ((recordPendingFault_replyViews_eq _ _ _
      (faultSuspendOnCore_preserves_objects_invExt _ _ _ S1.invExt)).trans
      (faultSuspendOnCore_replyViews_eq _ _ _ S1.invExt))
  unfold faultDeliverOnCoreChecked
  split
  · exact hSus _
  · split
    · exact faultDeliverOnCore_preserves_replyWaitersConsistent_of_ready S1.invExt hC1 hQ1 hRd1
    · exact hSus _

/-- The fault delivery both fault entries share: a vacated core's dispatch, or
the delivery and the core's own scheduling point. -/
theorem RecordsStage.faultEntryDeliver (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hQ : queueHeadBlockedConsistent st) (hCR : CurrentReady st) :
    RecordsStage st (_root_.SeLe4n.Kernel.faultEntryDeliver lctx st f ectx w c).2 := by
  unfold _root_.SeLe4n.Kernel.faultEntryDeliver
  split
  · exact of_frameK fun h => RecordsFrame.dispatchVacatedCore st c h
  · rename_i tid hTid
    dsimp only
    split
    · exact refl _
    · exact (faultDeliveredState lctx st f ectx w c tid hQ (hCR c tid hTid)).trans
        (of_frameK fun h => RecordsFrame.scheduleLocalSuccessorFrom _ _ c h)

theorem RecordsStage.faultEntryStep (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hQ : queueHeadBlockedConsistent st) (hCR : CurrentReady st) :
    RecordsStage st (_root_.SeLe4n.Kernel.faultEntryStep lctx st ectx w coreId).2 := by
  unfold _root_.SeLe4n.Kernel.faultEntryStep
  split
  · split
    · split
      · exact refl _
      · exact faultEntryDeliver lctx st _ ectx w _ hQ hCR
    · exact refl _
  · exact refl _

theorem RecordsStage.unknownSyscallEntryStep (lctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hQ : queueHeadBlockedConsistent st) (hCR : CurrentReady st) :
    RecordsStage st (_root_.SeLe4n.Kernel.unknownSyscallEntryStep lctx st ectx w coreId).2 := by
  unfold _root_.SeLe4n.Kernel.unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver lctx st _ (unknownSyscallContext ectx) w _ hQ hCR
    · exact refl _
  · exact refl _

/-- **The fault entry's committed state keeps the records**, from the queue
heads and the running threads of the state the step runs from. -/
theorem faultEntryState_recordsStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState)
    (hQ : queueHeadBlockedConsistent (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)))
    (hCR : CurrentReady (Concurrency.saveCapturedTrapFrameAt st coreId (some frame))) :
    RecordsStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h =>
    RecordsFrame.saveCapturedTrapFrameAt st coreId (some frame) h).trans
    (RecordsStage.faultEntryStep lctx _ ectx w coreId hQ hCR)).trans (RecordsStage.entryTail _ coreId)

/-- **The unknown-syscall entry's committed state keeps the records.** -/
theorem unknownSyscallEntryState_recordsStage (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState)
    (hQ : queueHeadBlockedConsistent (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)))
    (hCR : CurrentReady (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame))) :
    RecordsStage st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) :=
  ((RecordsStage.of_frameK fun h =>
    RecordsFrame.saveCapturedSyscallFrameAt st coreId (some frame) h).trans
    (RecordsStage.unknownSyscallEntryStep lctx _ ectx w coreId hQ hCR)).trans
    (RecordsStage.entryTail _ coreId)

end SeLe4n.Kernel
