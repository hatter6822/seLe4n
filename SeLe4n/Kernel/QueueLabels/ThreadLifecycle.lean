-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Cancellation
import SeLe4n.Kernel.KernelRecords.Thread

/-! # The suspend and the resume: frames

WS-SX SX11.2.  The suspend cancels the thread's IPC (a frame,
`QueueLabelsFrame.cancelIpcBlocking`) and marks it `.Inactive`; the resume
restores it `.ready`.  Every other write they make keeps every thread's IPC
state.  The proofs follow the records' own (`KernelRecords/ThreadLifecycle.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace QueueLabelsFrame

/-- seL4-MCS's `cancelIPC` as the suspend runs it: the head cut, then the
teardown. -/
theorem cancelIpcKeepingContexts (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.cancelIpcKeepingContexts st t tcb) :=
  have F := RecordsFrame.cutCancelledCallerHead st tcb hInv
  (of_frame F).trans (cancelIpcBlocking _ t tcb F.invExt)

/-- **The thread suspend** moves no thread onto an endpoint. -/
theorem suspendThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    QueueLabelsFrame st st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue => cases hStep; exact refl hInv
    case isFalse hA =>
      have S1 := cancelIpcKeepingContexts st vtid.val tcb hInv
      have S2 : QueueLabelsFrame st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact S1
        | some serverId =>
          exact S1.trans (of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ S1.invExt))
      have S3 := S2.trans (of_frame (RecordsFrame.descheduleAt _ vtid.val
        (placedCoreOf? st vtid.val) S2.invExt))
      have S4 := S3.trans (show QueueLabelsFrame _
          (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        exact updateTcb _ _ S3.invExt fun _ => TcbWaitsKept.of_ipc rfl)
      have S5 := S4.trans (updateTcb _ vtid.val S4.invExt
        (f := fun t => { t with threadState := .Inactive }) fun _ => TcbWaitsKept.of_ipc rfl)
      have S6 := S5.trans (of_frame (RecordsFrame.releaseRemoveThread _ vtid.val S5.invExt))
      have S7 := S6.trans (of_frame (RecordsFrame.cancelYieldTo _ vtid.val S6.invExt))
      exact S7.trans (of_frame (RecordsStep.suspendRescheduleOnCore S7.invExt hStep))

/-- The resume's ready mark: the restore, then the thread state and boost. -/
theorem resumeReadyMidState (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.resumeReadyMidState st t) := by
  have S := restoreToReadyStaging st t false hInv
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only
  exact S.trans (updateTcb _ t S.invExt fun _ => TcbWaitsKept.of_ipc rfl)

/-- **The thread resume** moves no thread onto an endpoint. -/
theorem resumeThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    QueueLabelsFrame st st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have S1 := resumeReadyMidState st vtid.val hInv
      have R1 := resumeReadyMidState_readyNoFault st vtid.val hInv
      have F2 := RecordsFrame.markKeyChangeFrom st _ vtid.val S1.invExt
      have F3 := RecordsFrame.resumeContext _ vtid.val (determineTargetCore st vtid.val) F2.invExt
      have S0 := (S1.trans (of_frame F2)).trans (of_frame F3)
      have hR : ∀ x, (Lifecycle.Suspend.resumeContext
          (_root_.SeLe4n.Kernel.markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
            vtid.val) vtid.val (determineTargetCore st vtid.val)).getTcb? vtid.val = some x →
          x.ipcState = .ready := fun x hx => by
        rw [Lifecycle.Suspend.resumeContext_getTcb? _ _ _ F2.invExt, markKeyChangeFrom_getTcb?] at hx
        exact (R1 x hx).1
      have S := S0.trans (of_frame (RecordsFrame.enqueueRunnableOnCore _
        (determineTargetCore st vtid.val) vtid.val S0.invExt hR))
      split at h
      · split at h
        · split at h
          · rename_i hH
            rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
            exact S.trans (of_frame (RecordsFrame.handleRescheduleSgiOnCore S.invExt hH))
          · cases h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact S
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact S0
  · cases h

/-- The resume's fault retire writes the thread's fault record and registers. -/
theorem retirePendingFaultForResume (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.retirePendingFaultForResume st t) := by
  unfold _root_.SeLe4n.Kernel.retirePendingFaultForResume
  split
  · split
    · split
      · unfold discardPendingFault
        exact updateTcb st t (f := fun tcb => tcb.setPendingFault none) hInv
          fun _ => TcbWaitsKept.of_ipc rfl
      · unfold applyFaultRestart
        exact updateTcb st t hInv fun _ => TcbWaitsKept.of_ipc rfl
    · exact refl hInv
  · exact refl hInv

/-- The fault-register spill writes the thread's registers. -/
theorem writeFaultRegistersToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st t w) :=
  updateTcb st t (f := fun tcb => { tcb with registerContext := w.spill tcb.registerContext }) hInv
    fun _ => TcbWaitsKept.of_ipc rfl

end QueueLabelsFrame

end SeLe4n.Kernel
