-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.ThreadLifecycle
import SeLe4n.Kernel.KernelRecords.Thread
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersDispatch
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# The suspend and the resume keep the reply-waiter queues

WS-ZA ZA6.37.  The records the suspend and the resume keep (`RecordsStep`) leave
the reply-waiter queues to a theorem of their own, and this is it.  The suspend's
IPC cancel is the one step that edits a queue: it is `cancelIpcBlocking` handed
the thread's TCB as the suspend read it, after a head cut that keeps every reply
view, so that TCB's view is still the thread's
(`cancelIpcBlocking_preserves_replyWaitersConsistent_of_view`).  Every other
step keeps every view.  The resume's restore clears the thread's server, which
keeps the queues when the thread waits on none: a resumed thread is `.ready` in
IPC (the dispatch's `threadIpcFieldsQuiescent`), so it does.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A step after which the store keeps its invariant and the reply-waiter queues
stay consistent. -/
def WaitersStage (st st' : SystemState) : Prop :=
  st.objects.invExt → st.replyWaitersConsistent →
    st'.objects.invExt ∧ st'.replyWaitersConsistent

namespace WaitersStage

theorem trans {a b c : SystemState} (h₁ : WaitersStage a b) (h₂ : WaitersStage b c) :
    WaitersStage a c := fun hI hC =>
  have h := h₁ hI hC
  h₂ h.1 h.2

theorem of_frame {st st' : SystemState} (F : st.objects.invExt → RecordsFrame st st') :
    WaitersStage st st' := fun hI hC =>
  ⟨(F hI).invExt, hC.of_views (F hI).replyViews⟩

theorem of_eq {st st' : SystemState} (h : st' = st) : WaitersStage st st' :=
  fun hI hC => h ▸ ⟨hI, hC⟩

/-- A TCB write that keeps every reply view. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x, (f x).replyView = x.replyView) : WaitersStage st (st.updateTcb t f) :=
  fun hI hC => ⟨SystemState.updateTcb_preserves_objects_invExt st t f hI,
    hC.of_views (replyViews_updateTcb_eq st t hI hf)⟩

end WaitersStage

/-- **The suspend's IPC cancel keeps the reply-waiter queues**: the head cut
keeps every reply view, so the TCB the suspend read still carries the thread's
view, and the teardown keeps the queues for it. -/
theorem cancelIpcKeepingContexts_waitersStage (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? t = some tcb) :
    WaitersStage st (Lifecycle.Suspend.cancelIpcKeepingContexts st t tcb) := fun hI hC =>
  have F := RecordsFrame.cutCancelledCallerHead st tcb hI
  ⟨(RecordsStep.cancelIpcKeepingContexts st t tcb hI).invExt,
    cancelIpcBlocking_preserves_replyWaitersConsistent_of_view _ t tcb
      (by rw [F.replyViews]
          exact SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT))
      F.invExt (hC.of_views F.replyViews)⟩

/-- **The thread suspend keeps the reply-waiter queues.** -/
theorem suspendThreadOnCore_waitersStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    WaitersStage st st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have S1 := cancelIpcKeepingContexts_waitersStage st vtid.val tcb hT
      have S2 : WaitersStage st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact S1
        | some serverId =>
          exact S1.trans (.of_frame fun h => RecordsFrame.propagatePipChainCrossCore _ _ _ _ h)
      have S3 := S2.trans (.of_frame fun h => RecordsFrame.descheduleAt _ vtid.val
        (placedCoreOf? st vtid.val) h)
      have S4 := S3.trans (show WaitersStage _ (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        exact WaitersStage.updateTcb _ _ fun _ => rfl)
      have S5 := S4.trans (WaitersStage.updateTcb _ vtid.val
        (f := fun t => { t with threadState := .Inactive }) fun _ => rfl)
      have S6 := S5.trans (.of_frame fun h => RecordsFrame.releaseRemoveThread _ vtid.val h)
      have S7 := S6.trans (.of_frame fun h => RecordsFrame.cancelYieldTo _ vtid.val h)
      exact S7.trans (.of_frame fun h => RecordsStep.suspendRescheduleOnCore h hStep)

/-- **The restore of a thread `.ready` in IPC keeps the reply-waiter queues**: it
clears the thread's server, which names none. -/
theorem restoreToReady_waitersStage (st : SystemState) (t : SeLe4n.ThreadId)
    (hR : ∀ x, st.getTcb? t = some x → x.ipcState = .ready) :
    WaitersStage st (Lifecycle.Suspend.restoreToReady st t) := fun hI hC =>
  ⟨(RecordsStep.restoreToReadyStaging st t false hI).invExt,
    hC.of_views (by
      rw [restoreToReady_replyViews st t hI]
      exact ReplyViews.setServer_of_server fun v hv => by
        obtain ⟨x, hO, rfl⟩ := SystemState.tcb_of_replyViews hv
        have hx := hR x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO)
        show x.blockingServer? = none
        unfold TCB.blockingServer?; rw [hx])⟩

/-- The resume's ready mark: the restore, then the thread state and boost. -/
theorem resumeReadyMidState_waitersStage (st : SystemState) (t : SeLe4n.ThreadId)
    (hR : ∀ x, st.getTcb? t = some x → x.ipcState = .ready) :
    WaitersStage st (Lifecycle.Suspend.resumeReadyMidState st t) := by
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only
  exact (restoreToReady_waitersStage st t hR).trans (WaitersStage.updateTcb _ t fun _ => rfl)

/-- **The thread resume keeps the reply-waiter queues**, for a thread `.ready` in
IPC: the ready mark clears a server it does not name, and the key hook, the
context, the wake and the scheduling point keep every reply view. -/
theorem resumeThreadOnCore_waitersStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hReady : ∀ x, st.getTcb? vtid.val = some x → x.ipcState = .ready)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    WaitersStage st st' := by
  intro hInv hC
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have S1 := RecordsStep.resumeReadyMidState st vtid.val hInv
      have R1 := resumeReadyMidState_readyNoFault st vtid.val hInv
      have F2 := RecordsFrame.markKeyChangeFrom st _ vtid.val S1.invExt
      have F3 := RecordsFrame.resumeContext _ vtid.val (determineTargetCore st vtid.val) F2.invExt
      have W0 := ((resumeReadyMidState_waitersStage st vtid.val hReady).trans
        (.of_frame fun _ => F2)).trans (.of_frame fun _ => F3)
      have hR : ∀ x, (Lifecycle.Suspend.resumeContext
          (_root_.SeLe4n.Kernel.markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
            vtid.val) vtid.val (determineTargetCore st vtid.val)).getTcb? vtid.val = some x →
          x.ipcState = .ready := fun x hx => by
        rw [Lifecycle.Suspend.resumeContext_getTcb? _ _ _ F2.invExt, markKeyChangeFrom_getTcb?] at hx
        exact (R1 x hx).1
      have F4 := RecordsFrame.enqueueRunnableOnCore _
        (determineTargetCore st vtid.val) vtid.val F3.invExt hR
      have W := W0.trans (.of_frame fun _ => F4)
      split at h
      · split at h
        · split at h
          · rename_i hH
            rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
            exact (W.trans (.of_frame fun _ =>
              RecordsFrame.handleRescheduleSgiOnCore F4.invExt hH)) hInv hC
          · cases h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact W hInv hC
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact W0 hInv hC
  · cases h

/-- **The resume's fault retire keeps the reply-waiter queues**: one TCB write of
its fault record and restart frame. -/
theorem retirePendingFaultForResume_waitersStage (st : SystemState) (t : SeLe4n.ThreadId) :
    WaitersStage st (retirePendingFaultForResume st t) := by
  unfold retirePendingFaultForResume
  split
  · split
    · split
      · unfold discardPendingFault; exact WaitersStage.updateTcb _ _ fun _ => rfl
      · unfold applyFaultRestart; exact WaitersStage.updateTcb _ _ fun _ => rfl
    · exact .of_eq rfl
  · exact .of_eq rfl

namespace RecordsStage

/-- **The thread suspend keeps the records.** -/
theorem suspendThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    RecordsStage st st' := fun h =>
  have hI := KernelRecords.objects_invExt h
  RecordsStage.of_step (RecordsStep.suspendThreadOnCore hI hStep)
    (fun hC => (suspendThreadOnCore_waitersStage hStep hI hC).2) h

/-- **The thread resume keeps the records**, for a thread `.ready` in IPC. -/
theorem resumeThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hReady : ∀ x, st.getTcb? vtid.val = some x → x.ipcState = .ready)
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    RecordsStage st st' := fun h =>
  have hI := KernelRecords.objects_invExt h
  RecordsStage.of_step (RecordsStep.resumeThreadOnCore hI hStep)
    (fun hC => (resumeThreadOnCore_waitersStage hReady hStep hI hC).2) h

/-- **The resume's fault retire keeps the records.** -/
theorem retirePendingFaultForResume (st : SystemState) (t : SeLe4n.ThreadId) :
    RecordsStage st (_root_.SeLe4n.Kernel.retirePendingFaultForResume st t) := fun h =>
  have hI := KernelRecords.objects_invExt h
  RecordsStage.of_step (RecordsStep.retirePendingFaultForResume st t hI)
    (fun hC => (retirePendingFaultForResume_waitersStage st t hI hC).2) h

end RecordsStage

end SeLe4n.Kernel
