-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Cancellation

/-!
# The suspend and the resume keep the records

WS-ZA ZA6.37.  The suspend cancels the thread's IPC (the restore retires its fault
record), takes it off its core and marks it `.Inactive`, a parked state; the
resume restores it with its fault record retired and marks it `.Ready`.  The head
cut, the context writes, the yield-link cancel and the scheduling points keep
every record view.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- A scheduling context rewritten in place. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    RecordsFrame st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc h _
    have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
    exact rewriteObject _ hInv (by rw [hRaw]; rfl)
  · exact refl hInv

/-- The cancelled caller's head cut: a reply store, a context's head, the
holder's binding owner and the key hook. -/
theorem cutCancelledCallerHead (st : SystemState) (tcb : TCB) (hInv : st.objects.invExt) :
    RecordsFrame st (Lifecycle.Suspend.cutCancelledCallerHead st tcb) :=
  Lifecycle.Suspend.cutCancelledCallerHead_closed (RecordsFrame st)
    (fun s s1 rid r scId F _ hR hS =>
      have F1 := F.trans (storeReply F.invExt
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hS)
      F1.trans (updateSchedContext _ scId _ F1.invExt))
    (fun s _ holder _ _ F _ _ _ =>
      have F1 := F.trans (updateTcb s holder F.invExt (f := fun t =>
        { t with scBindingOwnerCode := 0 }) fun _ => rfl)
      F1.trans (markKeyChangeFrom _ _ holder F1.invExt))
    st tcb (refl hInv)

theorem releaseRemoveThread (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (Lifecycle.Suspend.releaseRemoveThread st t) :=
  of_agreeOffReleaseLinks (Lifecycle.Suspend.releaseRemoveThread_agree st t)
    (by
      have h := congrArg SystemState.asidTable
        (Lifecycle.Suspend.releaseRemoveThread_releaseOnlyWrite st t).1
      exact h)
    (Lifecycle.Suspend.releaseRemoveThread_objects_invExt st t hInv)
    (by
      have h := congrArg (fun x : SystemState => x.machine.physicalAddressWidth)
        (Lifecycle.Suspend.releaseRemoveThread_releaseOnlyWrite st t).1
      exact h)

theorem resumeContext (st : SystemState) (t : SeLe4n.ThreadId) (home : CoreId)
    (hInv : st.objects.invExt) : RecordsFrame st (Lifecycle.Suspend.resumeContext st t home) := by
  rcases Lifecycle.Suspend.resumeContext_cases st t home with e | ⟨s, e⟩ <;> rw [e]
  · exact refl hInv
  · have F := updateSchedContext st s (fun sc => sc.refillUnblockCheck st.machine.timer) hInv
    exact F.trans (settleReturnedContext _ home s F.invExt)

/-- The yield-link cancel rewrites a context and a thread's link in place. -/
theorem cancelYieldTo (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.cancelYieldTo st t) := by
  unfold _root_.SeLe4n.Kernel.cancelYieldTo
  split
  · split
    · exact refl hInv
    · rename_i k _
      have F := updateSchedContext st ⟨k⟩ SchedContext.yieldCleared hInv
      exact F.trans (updateTcb _ t F.invExt fun _ => rfl)
  · exact refl hInv

end RecordsFrame

namespace RecordsStep

/-- seL4-MCS's `cancelIPC` as the suspend runs it: the head cut, then the
teardown. -/
theorem cancelIpcKeepingContexts (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    RecordsStep st (Lifecycle.Suspend.cancelIpcKeepingContexts st t tcb) :=
  have F := RecordsFrame.cutCancelledCallerHead st tcb hInv
  (of_frame F).trans (cancelIpcBlocking _ t tcb F.invExt)

/-- The suspend's scheduling point. -/
theorem suspendRescheduleOnCore {st st' : SystemState} {runningCore executingCore : CoreId}
    {wasCurrent localDeboosted : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore executingCore wasCurrent
      localDeboosted = .ok (st', sgi?)) : RecordsFrame st st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact RecordsFrame.handleRescheduleSgiOnCore hInv hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact RecordsFrame.refl hInv)

/-- **The thread suspend keeps the records**: the IPC cancel retires the thread's
fault record, the thread is marked `.Inactive`, and every other write keeps every
record view. -/
theorem suspendThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    RecordsStep st st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have S1 := cancelIpcKeepingContexts st vtid.val tcb hInv
      have S2 : RecordsStep st
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
      have S4 := S3.trans (show RecordsStep _ (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        exact updateTcb _ _ S3.invExt fun _ _ => TcbStaysParked.of_fields rfl rfl rfl)
      have S5 := S4.trans (updateTcb _ vtid.val S4.invExt
        (f := fun t => { t with threadState := .Inactive })
        fun _ _ => TcbStaysParked.of_parked (.inl rfl))
      have S6 := S5.trans (of_frame (RecordsFrame.releaseRemoveThread _ vtid.val S5.invExt))
      have S7 := S6.trans (of_frame (RecordsFrame.cancelYieldTo _ vtid.val S6.invExt))
      exact S7.trans (of_frame (suspendRescheduleOnCore S7.invExt hStep))

end RecordsStep

/-- The restore's field clear leaves the thread `.ready`. -/
theorem TCB.restoredToReady_ipcState (x : TCB) : x.restoredToReady.ipcState = .ready := by
  unfold TCB.restoredToReady; exact TCB.ipcState_setIpcState _ _

/-- The resume's ready mark leaves the thread `.ready` with no fault record. -/
theorem resumeReadyMidState_readyNoFault (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    ∀ x, (Lifecycle.Suspend.resumeReadyMidState st t).getTcb? t = some x →
      x.ipcState = .ready ∧ x.pendingFault = none := by
  intro x hx
  have hI1 : (Lifecycle.Suspend.restoreToReady st t).objects.invExt :=
    (RecordsStep.restoreToReadyStaging st t none hInv).invExt
  unfold Lifecycle.Suspend.resumeReadyMidState at hx
  dsimp only at hx
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1] at hx
  unfold Lifecycle.Suspend.restoreToReady Lifecycle.Suspend.restoreToReadyStaging at hx
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv] at hx
  cases hT : st.getTcb? t with
  | none => rw [hT] at hx; cases hx
  | some y =>
    rw [hT] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    exact ⟨TCB.restoredToReady_ipcState y, TCB.restoredToReady_pendingFault y⟩

namespace RecordsStep

/-- The resume's ready mark: the restore, then the thread state and boost. -/
theorem resumeReadyMidState (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsStep st (Lifecycle.Suspend.resumeReadyMidState st t) := by
  have S := restoreToReadyStaging st t none hInv
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only
  refine S.trans (updateTcb _ t S.invExt fun x hx => TcbStaysParked.of_noFault ?_)
  have := (threadHasPendingFault_eq_false_iff _ _).mp
    (threadHasPendingFault_restoreToReadyStaging st t none hInv) x hx
  exact this

/-- **The thread resume keeps the records**: the ready mark retires the fault
record, and the key hook, the context, the wake and the scheduling point keep
every record view. -/
theorem resumeThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    RecordsStep st st' := by
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

end RecordsStep

end SeLe4n.Kernel
