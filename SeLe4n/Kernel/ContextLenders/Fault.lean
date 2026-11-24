-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Call
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.IPC.Invariant.FaultPreservation
import SeLe4n.Kernel.EndpointWaiters.ThreadLifecycle

/-! # The fault and unknown-syscall entries keep the lenders' flow

WS-SX SX8.  seL4's `handleFault`: the faulting thread's registers are spilled,
then the fault is sent to its handler as a Call (`faultDeliverOnCore`), which
lends the faulting thread's context — or, with no handler or a
refused flow, the thread is suspended.  The lend reads the chain facts at the
state the delivery runs from and at the state its rendezvous leaves
(`FaultLendPremises`), as `Stage.lean` describes.  The handler Call's lend is a
creating site (WS-SX SX17): its label equation is the checked branch's gate
with the waiters (`endpointWaitersLabelsEqual`, SX11) the entry carries from
its own state to the delivery's. -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.Architecture (faultContextOfThread faultOfExceptionContext)

namespace chainObjectsKept

theorem writeFaultRegistersToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st tid w) :=
  updateTcb st tid _ hInv

theorem recordPendingFault (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.recordPendingFault st tid tf) :=
  updateTcb st tid _ hInv

theorem faultSuspendOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.faultSuspendOnCore st tid c) :=
  (removeRunnableOnCore st tid c).trans
    (updateTcb _ tid _ (removeRunnableOnCore_objects_invExt st tid c hInv))

theorem stageDeliveredMessage (st : SystemState) (t : SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.stageDeliveredMessage st t n) := by
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · exact (updateTcb st t _ hInv).trans (of_objects_eq rfl)
      · exact refl _
    · exact refl _
  · exact refl _

theorem stageWokenDelivery (st : SystemState) (w? : Option SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.stageWokenDelivery st w? n) := by
  unfold Architecture.stageWokenDelivery
  split
  · exact stageDeliveredMessage st _ n hInv
  · exact refl _

/-- The suspension a fault falls back to: the thread descheduled, its fault
recorded. -/
theorem faultSuspended (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) (tf : ThreadFault)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.recordPendingFault
      (_root_.SeLe4n.Kernel.faultSuspendOnCore st tid c) tid tf) :=
  (faultSuspendOnCore st tid c hInv).trans
    (recordPendingFault _ tid tf (faultSuspendOnCore_preserves_objects_invExt st tid c hInv))

theorem saveCapturedSyscallFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    chainObjectsKept st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame st _ frame hInv
  · exact refl _

end chainObjectsKept

/-- **What a fault's delivery lends from**, at the state it runs from: the
store's invariant and the donation chain there, and the lenders' premises at
the state the handler rendezvous leaves, for the handler the thread resolves. -/
structure FaultLendPremises (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (c : CoreId) : Prop where
  invExt : st.objects.invExt
  chain : donationChainWellFormed st
  queueHeads : queueHeadBlockedConsistent st
  mid : ∀ tgt : FaultHandlerTarget, resolveFaultHandler st tid = .ok tgt →
    LendersPremises (endpointCallWithCapsOnCore tgt.endpoint tid
      (.fault f fctx tgt.cap.badge tgt.cap.canLinkReply) c st).1

/-- **The fault delivery carries the lenders' flow**: a suspension writes the
faulting thread's record, and a delivery is the handler Call, then the woken
handler's frame and the recorded fault.  The Call's lend reads the blocked
receivers' labels (`hW`). -/
theorem faultDeliverOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : CoreId)
    (hP : FaultLendPremises st tid f fctx c) (hW : blockedReceiverLabelsEqual ctx st)
    (hGate : ∀ tgt, resolveFaultHandler st tid = .ok tgt →
      ctx.threadLabelOf tid = ctx.endpointLabelOf tgt.endpoint)
    (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (faultDeliverOnCore st tid f fctx c).1 := by
  unfold faultDeliverOnCore
  split
  · exact LendersStage.of_kept (chainObjectsKept.faultSuspended st tid c _ hP.invExt) hFlow
  · rename_i tgt hRes
    dsimp only
    have hD := endpointCallCrossCoreDispatch_preserves_lendingLabelsEqual tgt.endpoint tid
      (.fault f fctx tgt.cap.badge tgt.cap.canLinkReply) c st hP.invExt hP.chain
      (hP.mid tgt hRes) hW hP.queueHeads (hGate tgt hRes) hFlow
    have hI := endpointCallCrossCoreDispatch_preserves_objects_invExt tgt.endpoint tid
      (.fault f fctx tgt.cap.badge tgt.cap.canLinkReply) c st hP.invExt
    split
    · exact LendersStage.of_kept (chainObjectsKept.faultSuspended st tid c _ hP.invExt) hFlow
    · rename_i st' summary sgi? hEq
      rw [hEq] at hD hI
      simp only at hD hI
      exact LendersStage.of_kept ((chainObjectsKept.stageWokenDelivery st' _ _ hI).trans
        (chainObjectsKept.recordPendingFault _ tid _
          (RecordsFrame.stageWokenDelivery st' _ _ hI).invExt)) hD

/-- **The flow-checked delivery** the fault entries run: the admission is read
on the state the delivery starts from. -/
theorem faultDeliverOnCoreChecked_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : CoreId)
    (hP : FaultLendPremises st tid f fctx c) (hW : blockedReceiverLabelsEqual ctx st)
    (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (faultDeliverOnCoreChecked ctx st tid f fctx c).1 := by
  unfold faultDeliverOnCoreChecked
  split
  · exact LendersStage.of_kept (chainObjectsKept.faultSuspended st tid c _ hP.invExt) hFlow
  · rename_i tgt hRes
    split
    · rename_i hG
      refine faultDeliverOnCore_preserves_lendingLabelsEqual st tid f fctx c hP hW
        (fun tgt' hR' => ?_) hFlow
      rw [hRes] at hR'; cases hR'
      exact endpointFlowGate_implies_eq ctx _ _ _ hG
    · exact LendersStage.of_kept (chainObjectsKept.faultSuspended st tid c _ hP.invExt) hFlow

/-- **What a fault entry's delivery lends from**: for the thread current on the
core, the delivery's premises at the state its registers are spilled to, with
the context read off the spilled registers (`faultDeliveredState`). -/
def FaultEntryLendPremises (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (c : CoreId) : Prop :=
  ∀ tid, st.scheduler.currentOnCore c = some tid →
    FaultLendPremises (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st tid w) tid f
      (faultContextOfThread (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st tid w) tid
        ectx.elr ectx.spsr) c

/-- The fault entries' delivery: the spill, then the checked delivery, the
waiters carried across the spill. -/
theorem LendersStage.faultDeliveredState {ctx : LabelingContext} (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hW : endpointWaitersLabelsEqual ctx st)
    (hP : FaultLendPremises (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st tid w) tid f
      (faultContextOfThread (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st tid w) tid
        ectx.elr ectx.spsr) c) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.faultDeliveredState ctx st f ectx w c tid) :=
  fun hF => faultDeliverOnCoreChecked_preserves_lendingLabelsEqual _ tid f _ c hP
    ((EndpointWaitersFrame.writeFaultRegistersToTcb st tid w hInv).stage hW).2
    (LendersStage.of_kept (chainObjectsKept.writeFaultRegistersToTcb st tid w hInv) hF)

/-- The delivery both fault entries share: a vacated core's dispatch, or the
delivery and the core's own scheduling point. -/
theorem LendersStage.faultEntryDeliver {ctx : LabelingContext} (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt) (hW : endpointWaitersLabelsEqual ctx st)
    (hP : FaultEntryLendPremises st f ectx w c) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.faultEntryDeliver ctx st f ectx w c).2 := by
  unfold _root_.SeLe4n.Kernel.faultEntryDeliver
  split
  · exact of_kept (chainObjectsKept.dispatchVacatedCore st c hInv)
  · rename_i tid hTid
    dsimp only
    split
    · exact refl _
    · have hI : (_root_.SeLe4n.Kernel.faultDeliveredState ctx st f ectx w c tid).objects.invExt :=
        faultDeliverOnCoreChecked_preserves_objects_invExt ctx _ tid f _ c (hP tid hTid).invExt
      exact (faultDeliveredState st f ectx w c tid hInv hW (hP tid hTid)).trans
        (of_kept (chainObjectsKept.scheduleLocalSuccessorFrom _ _ c hI))

/-- The shared delivery keeps the store's invariant. -/
theorem faultEntryDeliver_invExt (ctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt) :
    (_root_.SeLe4n.Kernel.faultEntryDeliver ctx st f ectx w c).2.objects.invExt := by
  unfold _root_.SeLe4n.Kernel.faultEntryDeliver
  split
  · exact (RecordsFrame.dispatchVacatedCore st c hInv).invExt
  · rename_i tid _
    dsimp only
    split
    · exact hInv
    · have hI : (_root_.SeLe4n.Kernel.faultDeliveredState ctx st f ectx w c tid).objects.invExt :=
        faultDeliverOnCoreChecked_preserves_objects_invExt ctx _ tid f _ c
          (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv)
      exact (RecordsFrame.scheduleLocalSuccessorFrom _ _ c hI).invExt

theorem faultEntryStep_invExt (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    (_root_.SeLe4n.Kernel.faultEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold _root_.SeLe4n.Kernel.faultEntryStep
  split
  · split
    · split
      · exact hInv
      · exact faultEntryDeliver_invExt ctx st _ ectx w _ hInv
    · exact hInv
  · exact hInv

theorem unknownSyscallEntryStep_invExt (ctx : LabelingContext) (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    (_root_.SeLe4n.Kernel.unknownSyscallEntryStep ctx st ectx w coreId).2.objects.invExt := by
  unfold _root_.SeLe4n.Kernel.unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver_invExt ctx st _ _ w _ hInv
    · exact hInv
  · exact hInv

theorem LendersStage.faultEntryStep {ctx : LabelingContext} (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) (hW : endpointWaitersLabelsEqual ctx st)
    (hP : ∀ (f : Fault) (c : CoreId), faultOfExceptionContext ectx = some f →
      c.val = coreId.toNat → FaultEntryLendPremises st f ectx w c) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.faultEntryStep ctx st ectx w coreId).2 := by
  unfold _root_.SeLe4n.Kernel.faultEntryStep
  split
  · split
    · split
      · exact refl _
      · rename_i f hF
        exact faultEntryDeliver st _ ectx w _ hInv hW (hP f _ hF rfl)
    · exact refl _
  · exact refl _

theorem LendersStage.unknownSyscallEntryStep {ctx : LabelingContext} (st : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hInv : st.objects.invExt) (hW : endpointWaitersLabelsEqual ctx st)
    (hP : ∀ c : CoreId, c.val = coreId.toNat →
      FaultEntryLendPremises st (.unknownSyscall (w.gprAt 7)) (unknownSyscallContext ectx) w c) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.unknownSyscallEntryStep ctx st ectx w coreId).2 := by
  unfold _root_.SeLe4n.Kernel.unknownSyscallEntryStep
  split
  · split
    · exact faultEntryDeliver st _ _ w _ hInv hW (hP _ rfl)
    · exact refl _
  · exact refl _

/-- **The fault entry's committed state keeps the lenders' flow**, from the
delivery's premises at the state the trap frame is saved to, and the waiters at
the entry's own state (`hW`), which the save keeps. -/
theorem faultEntryState_lendersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt)
    (hW : endpointWaitersLabelsEqual ctx st)
    (hP : ∀ (f : Fault) (c : CoreId), faultOfExceptionContext ectx = some f →
      c.val = coreId.toNat →
      FaultEntryLendPremises (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) f ectx w c) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep ctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId (some frame) hInv
  refine ((LendersStage.of_kept (chainObjectsKept.saveCapturedTrapFrameAt st coreId _ hInv)).trans
    (LendersStage.faultEntryStep _ ectx w coreId F1.invExt
      ((EndpointWaitersFrame.of_frame F1).stage hW) hP)).trans
    (LendersStage.entryTail _ coreId ?_)
  exact faultEntryStep_invExt ctx _ ectx w coreId F1.invExt

/-- **The unknown-syscall entry's committed state keeps the lenders' flow.** -/
theorem unknownSyscallEntryState_lendersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hInv : st.objects.invExt)
    (hW : endpointWaitersLabelsEqual ctx st)
    (hP : ∀ c : CoreId, c.val = coreId.toNat →
      FaultEntryLendPremises (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame))
        (.unknownSyscall (w.gprAt 7)) (unknownSyscallContext ectx) w c) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep ctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedSyscallFrameAt st coreId (some frame) hInv
  refine ((LendersStage.of_kept (chainObjectsKept.saveCapturedSyscallFrameAt st coreId _ hInv)).trans
    (LendersStage.unknownSyscallEntryStep _ ectx w coreId F1.invExt
      ((EndpointWaitersFrame.of_frame F1).stage hW) hP)).trans
    (LendersStage.entryTail _ coreId ?_)
  exact unknownSyscallEntryStep_invExt ctx _ ectx w coreId F1.invExt

end SeLe4n.Kernel
