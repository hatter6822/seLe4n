-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.SchedulingPoint
import SeLe4n.Kernel.SchedContext.SchedControl

/-! # The thread-lifecycle and scheduling arms keep the mappings recorded

A finalisation-shaped write (`FinaliseFrameAny`) rewrites threads, endpoints,
notifications, scheduling contexts and replies alone, none of which carries a
mapping fact, so it is a `MappingStage`; that covers the suspend's teardown and
donation cancellation.  The priority, affinity, resume and scheduling-context
arms rewrite threads and contexts in place keeping the threads' space slots, and
re-bucket run queues, so each is a composition of stages.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **A finalisation-shaped write keeps the mappings recorded**
(`FinaliseFrameAny.liveMappingsRecorded`): it keeps every root, every frame and
every slot's capability. -/
theorem MappingStage.of_finaliseFrameAny {st st' : SystemState}
    (h : st.objects.invExt → FinaliseFrameAny st st') : MappingStage st st' :=
  fun hI => ⟨(h hI).invExt, (h hI).liveMappingsRecorded⟩

theorem MappingStage.of_finaliseFrame {st st' : SystemState}
    (h : st.objects.invExt → FinaliseFrame st st') : MappingStage st st' :=
  MappingStage.of_finaliseFrameAny fun hI => (h hI).any

/-- A scheduling context rewritten in place. -/
theorem updateSchedContext_mappingStage (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) : MappingStage st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc h _
    have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
    exact MappingStage.rewriteObject _ _ _ (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)
      (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)
  · exact MappingStage.refl _

/-- WS-ZA ZA6.6: the yield-link cancel rewrites a context and a thread in place. -/
theorem cancelYieldTo_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (cancelYieldTo st tid) := by
  unfold cancelYieldTo
  split
  · split
    · exact MappingStage.refl _
    · exact (updateSchedContext_mappingStage _ _ _).trans (updateTcb_mappingStage _ _ _)
  · exact MappingStage.refl _

/-- WS-ZA ZA6.6: `setConsumed` rewrites a context and a thread's two return
registers in place. -/
theorem setConsumed_mappingStage (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) : MappingStage st (setConsumed st s t) := by
  unfold setConsumed
  split
  · exact (updateSchedContext_mappingStage _ _ _).trans (updateTcb_mappingStage _ _ _)
  · exact MappingStage.refl _

/-- WS-ZA ZA6.6: the cancel from a context's end. -/
theorem cancelYieldFrom_mappingStage (st : SystemState) (s : SeLe4n.SchedContextId) :
    MappingStage st (cancelYieldFrom st s) := by
  unfold cancelYieldFrom
  split
  · split
    · exact MappingStage.refl _
    · exact (updateSchedContext_mappingStage _ _ _).trans (updateTcb_mappingStage _ _ _)
  · exact MappingStage.refl _

/-- WS-ZA ZA6.6: the completion of a context's recorded yield. -/
theorem completeYieldFrom_mappingStage (st : SystemState) (s : SeLe4n.SchedContextId) :
    MappingStage st (completeYieldFrom st s) := by
  unfold completeYieldFrom
  split
  · split
    · exact MappingStage.refl _
    · exact (setConsumed_mappingStage _ _ _).trans (cancelYieldFrom_mappingStage _ _)
  · exact MappingStage.refl _

/-! ### The suspend's teardown -/

/-- One queue neighbour's links patched, its space slots kept. -/
theorem queueNeighbourPatch_mappingStage (st : SystemState) (nid? : Option SeLe4n.ThreadId)
    (upd : TCB → TCB) (hU : ∀ t, (upd t).spaceCells = t.spaceCells ∧ (upd t).spaceLinks = t.spaceLinks) :
    MappingStage st { st with objects := queueNeighbourPatch st.objects nid? upd } := by
  unfold queueNeighbourPatch
  split
  · exact MappingStage.of_objects_eq rfl
  · split
    · rename_i t h
      exact MappingStage.insert rfl h rfl (by simp [KernelObject.objectType])
        (by simp only [KernelObject.tcbSlots, (hU t).1, (hU t).2]) rfl
    · exact MappingStage.of_objects_eq rfl

/-- The mid-queue splice patches the removed thread's two neighbours' links. -/
theorem spliceOutMidQueueNode_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (spliceOutMidQueueNode st tid) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact MappingStage.refl _
  · rename_i tcb _
    exact (queueNeighbourPatch_mappingStage st tcb.queuePrev (queueUnlinkPredecessor tcb)
      fun _ => ⟨rfl, rfl⟩).trans
      (queueNeighbourPatch_mappingStage _ tcb.queueNext (queueUnlinkSuccessor tcb) fun _ => ⟨rfl, rfl⟩)

/-- The endpoint sweep: the splice, then each endpoint whose queue ends name the
thread rewritten in place. -/
theorem removeFromAllEndpointQueues_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (removeFromAllEndpointQueues st tid) := by
  rw [removeFromAllEndpointQueues_eq_fold]
  refine (spliceOutMidQueueNode_mappingStage st tid).trans ?_
  refine RobinHood.RHTable.fold_preserves _ _ _ (MappingStage (spliceOutMidQueueNode st tid))
    (MappingStage.refl _) fun acc k v hA => hA.trans ?_
  unfold endpointSweepBody
  cases v with
  | endpoint _ =>
    simp only
    split
    · rename_i ep hEp _
      have hRaw := (SystemState.getEndpoint?_eq_some_iff acc k ep).mp hEp
      split
      · exact MappingStage.rewriteObject _ _ _ (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)
          (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)
      · exact MappingStage.refl _
    · exact MappingStage.refl _
  | _ => exact MappingStage.refl _

theorem restoreToReadyCancelled_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (Lifecycle.Suspend.restoreToReadyCancelled st tid) := by
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb_mappingStage _ _ _

/-- **The IPC teardown keeps the mappings recorded**: the endpoint sweep and the
restore for a sender or receiver, the finalisation-shaped reply and notification
arms. -/
theorem cancelIpcBlocking_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    MappingStage st (Lifecycle.Suspend.cancelIpcBlocking st tid tcb) := by
  cases hB : tcb.ipcState with
  | ready =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]; exact MappingStage.refl _
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    exact (removeFromAllEndpointQueues_mappingStage st tid).trans
      (restoreToReadyCancelled_mappingStage _ tid)
  | blockedOnReply _ _ =>
    exact MappingStage.of_finaliseFrameAny fun hI => FinaliseFrameAny.replyCancel st tid tcb hI hB
  | blockedOnNotification n =>
    exact MappingStage.of_finaliseFrame fun hI => FinaliseFrame.notificationCancel st tid tcb n hI hB

/-- The teardown with its reclaim: the cancel, then run-queue writes alone. -/
theorem cancelIpcBlockingReclaimed_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : MappingStage st (cancelIpcBlockingReclaimed tid tcb st) := fun hI =>
  have h1 := cancelIpcBlocking_mappingStage st tid tcb hI
  have h2 := MappingStage.of_objectsAgreeOffSchedulerLinks
    (cancelIpcBlockingMigrated_objects_invExt tid tcb st)
    (.of_releaseLinks (cancelIpcBlockingMigrated_agree tid tcb st)) h1.1
  have h3 := MappingStage.of_objectsAgreeOffRunLinks
    (fun _ => cancelIpcBlockingReclaimed_objects_invExt tid tcb st h1.1)
    (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks tid tcb st) h2.1
  ⟨h3.1, h3.2 ∘ h2.2 ∘ h1.2⟩

/-- The suspend's donation arm: nothing, the in-place unbind, or the return and
the replenishment migration. -/
theorem cancelSuspendDonation_mappingStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB}
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    MappingStage st st' := by
  revert hStep
  cases hBind : tcb.schedContextBinding with
  | unbound => intro hStep; cases hStep; exact MappingStage.refl st
  | bound _ =>
    intro hStep
    exact MappingStage.of_finaliseFrame fun hI => FinaliseFrame.cancelBoundDonationOnCore hI hStep
  | donated scId owner =>
    intro hStep
    unfold cancelDonatedDonationOnCore at hStep
    rw [hBind] at hStep
    simp only at hStep
    split at hStep
    · cases hStep
    · rename_i s1 hC
      cases hStep
      refine (?_ : MappingStage st s1).trans (migrateSchedContextReplenishment_mappingStage _ _ _ _)
      unfold cleanupDonatedSchedContext at hC
      split at hC
      · cases hC; exact MappingStage.refl _
      · split at hC
        · exact returnDonatedSchedContextResolved_mappingStage hC
        · cases hC; exact MappingStage.refl _

/-- The suspend's scheduling point: a reschedule on the executing core or nothing. -/
theorem suspendRescheduleOnCore_mappingStage {st st' : SystemState}
    {runningCore executingCore : CoreId} {wasCurrent localDeboosted : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore executingCore wasCurrent localDeboosted =
      .ok (st', sgi?)) : MappingStage st st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore_mappingStage hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact MappingStage.refl _)

/-- **The thread suspend keeps the mappings recorded**: the reclaimed teardown,
the chain revert, the donation arm, the deschedule, two thread rewrites and the
scheduling point. -/
theorem suspendThreadOnCore_mappingStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    MappingStage st st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    have hS1 := cancelIpcBlockingReclaimed_mappingStage st vtid.val tcb
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have hS12 : MappingStage (cancelIpcBlockingReclaimed vtid.val tcb st)
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact MappingStage.refl _
        | some serverId => exact propagatePipChainCrossCore_mappingStage
      revert hStep
      split
      · intro hStep; exact absurd hStep (by simp)
      · next s3 hDon =>
        intro hStep
        refine ((hS1.trans hS12).trans (cancelSuspendDonation_mappingStage hDon)).trans ?_
        refine (MappingStage.of_finaliseFrame fun hI =>
          FinaliseFrame.descheduleAt s3 vtid.val (placedCoreOf? st vtid.val) hI).trans ?_
        refine (show MappingStage _ (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
          unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
          exact updateTcb_mappingStage _ _ _).trans ?_
        exact ((updateTcb_mappingStage _ _ _).trans (cancelYieldTo_mappingStage _ _)).trans
          (suspendRescheduleOnCore_mappingStage hStep)

/-- The resume's ready mark: two thread rewrites. -/
theorem resumeReadyMidState_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (Lifecycle.Suspend.resumeReadyMidState st tid) := by
  unfold Lifecycle.Suspend.resumeReadyMidState Lifecycle.Suspend.restoreToReady
    Lifecycle.Suspend.restoreToReadyStaging
  exact (updateTcb_mappingStage _ _ _).trans (updateTcb_mappingStage _ _ _)

/-- **The thread resume keeps the mappings recorded**: the ready mark, the key
hook, the wake on the home core and the local scheduling point. -/
theorem resumeThreadOnCore_mappingStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    MappingStage st st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have hS := ((resumeReadyMidState_mappingStage st vtid.val).trans
        (markKeyChangeFrom_mappingStage st _ vtid.val)).trans
        (enqueueRunnableOnCore_mappingStage _ (determineTargetCore st vtid.val) vtid.val)
      split at h
      · split at h
        · rename_i hH
          rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
          exact hS.trans (handleRescheduleSgiOnCore_mappingStage hH)
        · cases h
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
  · cases h

/-! ### Priorities -/

/-- The priority's source write: the bound context's band and the thread's
priority, each in place. -/
theorem updatePrioritySource_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (p : SeLe4n.Priority) :
    MappingStage st (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · exact (updateSchedContext_mappingStage _ _ _).trans (updateTcb_mappingStage _ _ _)
  · exact updateTcb_mappingStage _ _ _

theorem migrateRunQueueBucketOnCore_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (homeCore : CoreId) :
    MappingStage st (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st tid p homeCore) := by
  unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
  split
  · exact runRequeueOnCore_mappingStage _ _ _ _
  · exact MappingStage.refl _

theorem repropagateFromWaiter_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) : MappingStage st (PriorityInheritance.repropagateFromWaiter st tid ec fuel) :=
  PriorityInheritance.repropagateFromWaiter_preserves (MappingStage st) st tid ec fuel
    (fun _ _ => propagatePipChainCrossCore_mappingStage) (MappingStage.refl st)

/-- The priority ops' preemption seam: the reschedule on the executing core or nothing. -/
theorem priorityRescheduleOnCore_mappingStage {st st' : SystemState}
    {running? : Option CoreId} {ec : CoreId} {sp : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : MappingStage st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · exact MappingStage.of_eq hEq
  · exact handleRescheduleSgiOnCore_mappingStage hH

/-- The priority ops' shared effect: the source write, the re-bucket, the key
hook, the chain re-walk and the preemption seam. -/
theorem applyPriorityChangeOnCore_mappingStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {p : SeLe4n.Priority} {ec : CoreId} {b : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p ec b =
      .ok (st', sgi?)) : MappingStage st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  exact ((((updatePrioritySource_mappingStage st tid tcb p).trans
    (migrateRunQueueBucketOnCore_mappingStage _ tid p (determineTargetCore st tid))).trans
    (markKeyChangeFor_mappingStage _ tid _)).trans
    (repropagateFromWaiter_mappingStage _ tid ec _)).trans
    (priorityRescheduleOnCore_mappingStage h)

theorem setPriorityOnCore_mappingStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : MappingStage st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore_mappingStage h
      · cases h
  · cases h

theorem setMCPriorityOnCore_mappingStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : MappingStage st st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        have hS := MappingStage.rewriteObject_tcb (t' := { targetTcb with maxControlledPriority := p })
          hTarget
        split at h
        · exact hS.trans (applyPriorityChangeOnCore_mappingStage h)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
      · cases h
  · cases h

/-! ### Scheduling contexts and affinity -/

/-- The release queue's re-placement writes contexts' release fields alone. -/
theorem releasePlace_mappingStage (st : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId) :
    MappingStage st (st.releasePlace c scId) :=
  MappingStage.of_objectsAgreeOffSchedulerLinks
    (fun h => SystemState.releasePlace_objects_invExt st c scId h)
    (.of_releaseLinks (SystemState.releasePlace_agree st c scId))

/-- A scheduling context rewritten through its witnessed lookup. -/
theorem MappingStage.rewriteObject_schedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {sc : SchedContext} (h : st.getSchedContext? scId = some sc) (sc' : SchedContext)
    (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) :
    MappingStage st (st.rewriteObject scId.toObjId (.schedContext sc') hA) := by
  have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
  exact MappingStage.rewriteObject _ _ _ (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)
    (fun old hOld => by rw [hRaw] at hOld; cases hOld; rfl)

/-- The bind writes the context's bound thread and the thread's binding and
priority in place, re-buckets or places the thread, then the key hook. -/
theorem schedContextBind_mappingStage {vScId : SeLe4n.ValidObjId} {vTid : SeLe4n.ValidThreadId}
    {st st' : SystemState} (h : SchedContextOps.schedContextBind vScId vTid st = .ok ((), st')) :
    MappingStage st st' := by
  unfold SchedContextOps.schedContextBind at h
  split at h
  · rename_i sc hSc _
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
                subst h
                refine MappingStage.trans ?_ (releasePlace_mappingStage _ _ _)
                refine MappingStage.trans ?_ (markKeyChangeFor_mappingStage _ _ _)
                split
                · refine MappingStage.trans ?_ (runRequeueOnCore_mappingStage _ _ _ _)
                  exact (MappingStage.rewriteObject_schedContext hSc _ _).trans
                    (updateTcb_mappingStage _ _ _)
                · split
                  · refine MappingStage.trans ?_ (MappingStage.of_objects_eq
                      (SystemState.markReschedulePendingOnCore_objects _ _))
                    refine MappingStage.trans ?_ (runEnqueueOnCore_mappingStage _ _ _ _)
                    exact (MappingStage.rewriteObject_schedContext hSc _ _).trans
                      (updateTcb_mappingStage _ _ _)
                  · exact (MappingStage.rewriteObject_schedContext hSc _ _).trans
                      (updateTcb_mappingStage _ _ _)
              all_goals cases h
        · cases h
  · cases h

/-- The configure's bound-thread propagation: thread rewrites in place and a
re-bucket. -/
theorem schedContextConfigureBoundPropagate_mappingStage (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat) :
    MappingStage stStored (SchedContextOps.schedContextConfigureBoundPropagate stStored scId
      boundTid boundTcb hBound priority domain) := by
  have hP : ∀ (P : Prop) [Decidable P], MappingStage stStored
      (if P then stStored else
        if (stStored.rewriteObject boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ })
            (SystemState.rewriteAdmissible_tcb hBound _)).queuedOn
            (determineTargetCore (stStored.rewriteObject boundTid.toObjId
              (.tcb { boundTcb with priority := ⟨priority⟩ })
              (SystemState.rewriteAdmissible_tcb hBound _)) boundTid) boundTid then
          (stStored.rewriteObject boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ })
            (SystemState.rewriteAdmissible_tcb hBound _)).runRequeueOnCore
            (determineTargetCore (stStored.rewriteObject boundTid.toObjId
              (.tcb { boundTcb with priority := ⟨priority⟩ })
              (SystemState.rewriteAdmissible_tcb hBound _)) boundTid) boundTid
            ({ boundTcb with priority := ⟨priority⟩ } : TCB).boostedPriority
        else stStored.rewriteObject boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ })
            (SystemState.rewriteAdmissible_tcb hBound _)) := by
    intro P _
    split
    · exact MappingStage.refl _
    · split
      · exact (MappingStage.rewriteObject_tcb hBound _).trans (runRequeueOnCore_mappingStage _ _ _ _)
      · exact MappingStage.rewriteObject_tcb hBound _
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only
  split
  · rename_i cur hCur hEq
    split
    · exact hP _
    · exact (hP _).trans (MappingStage.rewriteObject_tcb hCur _)
  · exact hP _

/-- The replenishment purge writes the release-queue links alone. -/
theorem purgeReplenishment_mappingStage (st : SystemState) (scId : SeLe4n.SchedContextId) :
    MappingStage st (SchedContextOps.purgeReplenishment st scId) :=
  MappingStage.of_kindPreservingWrite (SchedContextOps.purgeReplenishment_objects_invExt st scId)
    fun _ => (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
      (SchedContextOps.purgeReplenishment_agree st scId)).kindPreserving

/-- The configure's resume tail writes run-queue links alone. -/
theorem configureResumeBound_mappingStage (st : SystemState) (t : SeLe4n.ThreadId)
    (sc : SchedContext) : MappingStage st (SchedContextOps.configureResumeBound st t sc) :=
  MappingStage.of_objectsAgreeOffRunLinks (SchedContextOps.configureResumeBound_objects_invExt st t sc)
    (SchedContextOps.configureResumeBound_objectsAgreeOffRunLinks st t sc)

/-- The configure purges the context's replenishment, stores the reconfigured
context over the old one, and runs the bound-thread propagation, the key hook
and the chain re-walk. -/
theorem schedContextConfigure_mappingStage {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState}
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st =
      .ok ((), st')) : MappingStage st st' := by
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none =>
    unfold SchedContextOps.schedContextConfigure at h
    split at h
    · exact absurd h (by simp)
    · rw [hSc] at h; exact absurd h (by simp)
  | some sc =>
    have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
      (SchedContextId.ofObjId vScId.val) sc).mp hSc
    unfold SchedContextOps.schedContextConfigure at h
    split at h
    · exact absurd h (by simp)
    · rw [hSc] at h
      dsimp only at h
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i stStored hStore
          obtain ⟨scP, hScP, -⟩ := (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
            (SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩)).get_sc
            (show st.objects[vScId.val]? = _ from hScRaw)
          have hS1 : MappingStage st stStored :=
            (purgeReplenishment_mappingStage st _).trans
              (MappingStage.storeObject hStore (pre := .schedContext scP) hScP rfl
                (by simp [KernelObject.objectType]))
          split at h
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact hS1
          · split at h
            · rename_i boundTcb hBound _
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact ((hS1.trans (releasePlace_mappingStage _ _ _)).trans
                ((((schedContextConfigureBoundPropagate_mappingStage _ _ _ _ hBound _ _).trans
                  (markCandidacyGainFor_mappingStage _ _ _)).trans
                  (markKeyChangeFor_mappingStage _ _ _)).trans
                  (repropagateFromWaiter_mappingStage _ _ _ _))).trans
                  (configureResumeBound_mappingStage _ _ _)
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]; exact hS1.trans (releasePlace_mappingStage _ _ _)
      · exact absurd h (by simp)

/-- The unbind clears the context's bound thread and the thread's binding in
place, re-buckets the thread, purges the replenishment and runs the key hook. -/
theorem schedContextUnbind_mappingStage {vScId : SeLe4n.ValidObjId} {st st' : SystemState}
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) : MappingStage st st' := by
  unfold SchedContextOps.schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    · split at hStep
      · dsimp only [] at hStep
        split at hStep
        · contradiction
        · cases hStep
          refine MappingStage.trans ?_ (markKeyChangeFor_mappingStage _ _ _)
          refine MappingStage.trans ?_ (markCandidacyGainFor_mappingStage _ _ _)
          refine MappingStage.trans ?_
            (purgeReplenishment_mappingStage _ _)
          refine MappingStage.trans ?_ (MappingStage.of_objectsAgreeOffRunLinks
            (SchedContextOps.schedContextUnbindQueueStage_objects_invExt _ _ _ _ _)
            (SchedContextOps.schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _))
          refine MappingStage.trans ?_ (updateTcb_mappingStage _ _ _)
          exact MappingStage.of_objects_eq_left rfl (MappingStage.rewriteObject_schedContext hSc _
            (SystemState.rewriteAdmissible_schedContext hSc _))
      · cases hStep
        refine MappingStage.trans ?_
          (purgeReplenishment_mappingStage _ _)
        exact MappingStage.rewriteObject_schedContext hSc _ _
  · cases hStep

/-- The per-core context unbind: the unbind, then the preemption seam. -/
theorem schedContextUnbindOnCore_mappingStage {vScId : SeLe4n.ValidObjId} {ec : CoreId}
    {st st' : SystemState} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    MappingStage st st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hU
    exact (schedContextUnbind_mappingStage hU).trans (priorityRescheduleOnCore_mappingStage h)

/-- The affinity op: the vacate (the scheduler alone), the affinity field
written in place, the replenishment move (replenish queues only), the run-queue
migration and the requeue (run-queue links only). -/
theorem setThreadCpuAffinityWithMigration_mappingStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option CoreId} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (st', sgi?)) :
    MappingStage st st' := by
  obtain ⟨tcb, stSet, -, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have hS0 : MappingStage st (vacateForAffinityChange st tid
      (determineTargetCore st tid) (affinity.getD Concurrency.bootCoreId)) :=
    MappingStage.of_objectsAgreeOffRunLinks
      (fun hI => by rw [vacateForAffinityChange_objects]; exact hI)
      (vacateForAffinityChange_objectsAgreeOffRunLinks _ _ _ _)
  have hS1 : MappingStage (vacateForAffinityChange st tid
      (determineTargetCore st tid) (affinity.getD Concurrency.bootCoreId)) stSet := by
    unfold setThreadCpuAffinity at hSet
    split at hSet
    · rename_i t hT _
      rw [Except.ok.injEq] at hSet; subst hSet
      exact MappingStage.rewriteObject_tcb hT _
    · cases hSet
  refine hS0.trans (hS1.trans (MappingStage.trans ?_ ((MappingStage.of_objectsAgreeOffRunLinks
    (migrateRunQueueOnAffinityChange_preserves_objects_invExt _ _ _ _)
    (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _)).trans
    (MappingStage.of_objectsAgreeOffRunLinks
      (requeueVacatedOnNewHome_preserves_objects_invExt _ _ _ _)
      (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _)))))
  split
  · exact migrateSchedContextReplenishment_mappingStage _ _ _ _
  · exact MappingStage.refl _

/-- WS-ZA ZA6.4: the SchedControl configure moves the bound thread through the
affinity change and then configures on the moved state; both are stages. -/
theorem schedControlConfigure_mappingStage {core : CoreId} {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState}
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain
      st = .ok ((), st')) : MappingStage st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact schedContextConfigure_mappingStage h
  · exact (setThreadCpuAffinityWithMigration_mappingStage hM).trans
      (schedContextConfigure_mappingStage h)

/-! ### The timer path -/

theorem setThreadCpuAffinityOnCore_mappingStage {st st' : SystemState}
    {vTargetTid : SeLe4n.ValidThreadId} {affinity : Option CoreId} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityOnCore st vTargetTid affinity ec = .ok (st', sgi?)) :
    MappingStage st st' :=
  setThreadCpuAffinityWithMigration_mappingStage h

/-- The boost's write: one thread rewritten in place. -/
theorem pipBoostWrite_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (PriorityInheritance.pipBoostWrite st tid) := by
  unfold PriorityInheritance.pipBoostWrite
  split
  · rename_i tcb h _
    dsimp only
    split
    · exact MappingStage.refl _
    · exact MappingStage.rewriteObject_tcb h _
  · exact MappingStage.refl _

theorem updatePipBoostOnCore_mappingStage (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    MappingStage st (PriorityInheritance.updatePipBoostOnCore st c tid) :=
  MappingStage.of_invExt fun hI => (pipBoostWrite_mappingStage st tid).trans
    (MappingStage.of_objectsAgreeOffRunLinks
      (fun _ => PriorityInheritance.updatePipBoostOnCore_preserves_objects_invExt st c tid hI)
      (PriorityInheritance.updatePipBoostOnCore_objectsAgreeOffRunLinks st c tid))

/-- The chain revert: one boost per link. -/
theorem revertPriorityInheritance_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (fuel : Nat) : MappingStage st (PriorityInheritance.revertPriorityInheritance st tid fuel) := by
  induction fuel generalizing st tid with
  | zero => exact MappingStage.refl _
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    have h1 := updatePipBoostOnCore_mappingStage st Concurrency.bootCoreId tid
    split
    · exact h1.trans (ih _ _)
    · exact h1

/-- **The queue removal's writes**: the two neighbours patched, the endpoint and
the removed thread rewritten. -/
theorem endpointQueueRemove_objects_eq {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    ∃ ep ep' tcb, st.objects[endpointId]? = some (.endpoint ep) ∧ lookupTcb st tid = some tcb ∧
      st' = { st with objects := ((queueNeighbourPatch (queueNeighbourPatch st.objects tcb.queuePrev
        (queueUnlinkPredecessor tcb)) tcb.queueNext (queueUnlinkSuccessor tcb)).insert endpointId
          (.endpoint ep')).insert tid.toObjId (.tcb (tcbWithQueueLinks tcb none none none)) } := by
  unfold endpointQueueRemove SystemState.getObject? at h
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at h
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _
    | pageTable _ => simp [hObj] at h
    | endpoint ep =>
      simp only [hObj] at h
      cases hTcb : lookupTcb st tid with
      | none => simp [hTcb] at h
      | some tcb =>
        simp only [hTcb, Except.ok.injEq] at h
        exact ⟨ep, _, tcb, rfl, rfl, h.symm⟩

/-- The queue removal keeps the mappings recorded: two thread patches, an
endpoint rewrite and a thread rewrite, none touching a space slot. -/
theorem endpointQueueRemove_mappingStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') : MappingStage st st' := by
  obtain ⟨ep, ep', tcb, hEp, hT, rfl⟩ := endpointQueueRemove_objects_eq h
  refine MappingStage.of_invExt fun hI => ?_
  have hTo := lookupTcb_some_objects st tid tcb hT
  let A1 := queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb)
  let A2 := queueNeighbourPatch A1 tcb.queueNext (queueUnlinkSuccessor tcb)
  have hI1 : A1.invExt := queueNeighbourPatch_invExt _ _ _ hI
  have hI2 : A2.invExt := queueNeighbourPatch_invExt _ _ _ hI1
  have hEp2 : A2[endpointId]? = some (.endpoint ep) :=
    (queueNeighbourPatch_nonTcb _ _ _ hI1 _ _ (fun _ h => by cases h)).2
      ((queueNeighbourPatch_nonTcb _ _ _ hI _ _ (fun _ h => by cases h)).2 hEp)
  have hNe : ¬(endpointId == tid.toObjId) = true := by
    intro hb; rw [eq_of_beq hb, hTo] at hEp; cases hEp
  obtain ⟨t1, h1, e1⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (queueUnlinkPredecessor tcb) hI _ _ hTo
  obtain ⟨t2, h2, e2⟩ := queueNeighbourPatch_tcb_forward A1 tcb.queueNext
    (queueUnlinkSuccessor tcb) hI1 _ _ h1
  have hS2 : t2.spaceCells = tcb.spaceCells ∧ t2.spaceLinks = tcb.spaceLinks := by
    rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have hT3 : (A2.insert endpointId (.endpoint ep'))[tid.toObjId]? = some (.tcb t2) :=
    (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ hNe hI2).trans h2
  have s1 : MappingStage st { st with objects := A2 } :=
    (queueNeighbourPatch_mappingStage st tcb.queuePrev (queueUnlinkPredecessor tcb)
      fun _ => ⟨rfl, rfl⟩).trans (queueNeighbourPatch_mappingStage _ tcb.queueNext
      (queueUnlinkSuccessor tcb) fun _ => ⟨rfl, rfl⟩)
  have s2 : MappingStage { st with objects := A2 }
      { st with objects := A2.insert endpointId (.endpoint ep') } :=
    MappingStage.insert rfl hEp2 rfl (by simp [KernelObject.objectType])
  have s3 : MappingStage { st with objects := A2.insert endpointId (.endpoint ep') }
      { st with objects := ((A2.insert endpointId (.endpoint ep')).insert tid.toObjId
        (.tcb (tcbWithQueueLinks tcb none none none))) } :=
    MappingStage.insert rfl hT3 rfl (by simp [KernelObject.objectType])
      (by simp only [KernelObject.tcbSlots, tcbWithQueueLinks, hS2.1, hS2.2])
  exact s1.trans (s2.trans s3)

/-- The IPC abort: the queue removal, then the aborted thread rewritten. -/
theorem abortPendingIpcOnEndpoint_mappingStage {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') : MappingStage st st' := by
  unfold abortPendingIpcOnEndpoint at h
  split at h
  · cases h
  · rename_i st1 hR
    split at h
    · cases h
    · rename_i tcb hT
      dsimp only at h
      split at h
      · cases h
      · rename_i hS
        cases h
        exact (endpointQueueRemove_mappingStage hR).trans
          (MappingStage.storeObject hS (lookupTcb_some_objects _ _ _ hT) rfl
            (by simp [KernelObject.objectType]))

/-- A timeout: the abort, the wake, the reply-waiter unlink and the chain
revert. -/
theorem timeoutThread_mappingStage {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st : SystemState}
    {r : SystemState × Option (CoreId × Concurrency.SgiKind)}
    (h : timeoutThread epId isReceiveQ tid ec st = .ok r) : MappingStage st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    have hS := (abortPendingIpcOnEndpoint_mappingStage hA).trans (wakeThread_mappingStage st2 tid ec)
    dsimp only at h
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact hS.trans ((MappingStage.of_kindPreservingWrite
        (fun hI => SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hI)
        (fun _ => SystemState.unlinkReplyWaiter_kindPreservingWrite _ _ _)).trans
        (revertPriorityInheritance_mappingStage _ _ _))
    · rw [Except.ok.injEq] at h; subst h; exact hS

/-- The bound-context timeout pass: a fold of timeouts. -/
theorem timeoutBlockedThreads_mappingStage (st : SystemState) (scId : SeLe4n.SchedContextId)
    (ec : CoreId) : MappingStage st (timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × Concurrency.SgiKind)),
      MappingStage st acc.1 →
      MappingStage st (l.foldl (fun acc tid =>
        let (st', errs, sgis) := acc
        match st'.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match timeoutThread epId isReceiveQ tid ec st' with
            | .ok r => (r.1, errs, sgis ++ r.2.toList)
            | .error e => (st', errs ++ [(tid, e)], sgis)
          | none => (st', errs, sgis)
        | none => (st', errs, sgis)) acc).1 from
    H _ _ (MappingStage.refl st)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨s, e, g⟩ := acc
    dsimp only
    split
    · split
      · split
        · rename_i r hT
          exact h.trans (timeoutThread_mappingStage hT)
        · exact h
      · exact h
    · exact h

theorem sliceExpireOnCore_mappingStage (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    MappingStage st (sliceExpireOnCore st c tid tcb hTcb) :=
  (MappingStage.rewriteObject_tcb hTcb _).trans (runEnqueueOnCore_mappingStage _ _ _ _)

theorem spendBudgetOnCore_mappingStage (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) : MappingStage st (spendBudgetOnCore st c tid scId sc hSc start ticks) := by
  unfold spendBudgetOnCore
  refine MappingStage.trans ?_ (runEnqueueOnCore_mappingStage _ _ _ _)
  exact (MappingStage.rewriteObject_schedContext hSc _
    (SystemState.rewriteAdmissible_schedContext hSc _)).trans (releasePlace_mappingStage _ c scId)

theorem budgetExhaustOnCore_mappingStage (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) : MappingStage st (budgetExhaustOnCore st c tid k scId sc hSc ticks) :=
  (((spendBudgetOnCore_mappingStage st c tid scId sc hSc _ ticks).trans
    (markKeyChangeFor_mappingStage _ tid k)).trans
    (timeoutBlockedThreads_mappingStage _ scId c)).trans (MappingStage.of_objects_eq rfl)

/-- The tick's charge of a thread: a slice or budget step. -/
theorem timerTickBudgetOnCore_mappingStage {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {r : SystemState × Bool}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = r) : MappingStage st r.1 := by
  subst h
  unfold timerTickBudgetOnCore
  split
  · split
    · exact sliceExpireOnCore_mappingStage st c tid tcb hTcb
    · exact MappingStage.rewriteObject_tcb hTcb _
  all_goals
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore_mappingStage st c tid _ _ sc hSc 1
      · exact MappingStage.rewriteObject_schedContext hSc _
          (SystemState.rewriteAdmissible_schedContext hSc _)
    · exact MappingStage.refl _

theorem idleFallbackOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (idleFallbackOnCore st c) :=
  MappingStage.of_objectsAgreeOffRunLinks (idleFallbackOnCore_objects_invExt st c)
    (idleFallbackOnCore_objectsAgreeOffRunLinks st c)

/-- The reschedule: the register save, then the idle fallback or the dequeue,
restore and current-slot write of the chosen thread, then the flag clear. -/
theorem scheduleEffectiveOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    (h : scheduleEffectiveOnCore st c = .ok st') : MappingStage st st' := by
  unfold scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rw [Except.ok.injEq] at h; subst h
    exact ((saveOutgoingContextOnCore_mappingStage st c).trans
      (idleFallbackOnCore_mappingStage _ c)).trans (clearReschedulePendingOnCore_mappingStage _ c)
  · split at h
    · split at h
      · rw [Except.ok.injEq] at h; subst h
        rename_i tid _ _ _ _ _
        exact ((saveOutgoingContextOnCore_mappingStage st c).trans
          (runRemoveOnCore_mappingStage _ c tid)).trans
          (MappingStage.of_objects_eq (restoreIncomingContextOnCore_objects _ _ _))
      · cases h
    · cases h

/-- The yield's charge: the slice end, or the budget forfeit with the key hook. -/
theorem yieldChargeOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (h : yieldChargeOnCore st c tid = .ok st') : MappingStage st st' := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_mappingStage st c tid tcb hTcb
    all_goals
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore_mappingStage st c tid _ sc hSc _ _).trans
          (markKeyChangeFor_mappingStage _ _ _)
      · cases h

/-- **The yield keeps the mappings recorded**: the charge and the reschedule. -/
theorem yieldOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    (h : yieldOnCore st c = .ok st') : MappingStage st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore_mappingStage hC).trans (scheduleEffectiveOnCore_mappingStage h)

/-- One due replenishment: the refill and the wake, under the refill's key hook
(flags only). -/
theorem processOneReplenishmentOnCore_mappingStage (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    MappingStage st (processOneReplenishmentOnCore st c scId now) := by
  have hRefill : MappingStage st (refillSchedContext st scId now) := by
    unfold refillSchedContext; exact updateSchedContext_mappingStage _ _ _
  unfold processOneReplenishmentOnCore
  refine MappingStage.trans ?_ (MappingStage.of_objects_eq (markRefillKeyChange_objects _ _ _))
  unfold refillWakeOnCore
  dsimp only
  split
  · split
    · exact hRefill
    · exact (hRefill.trans (wakeThread_mappingStage _ _ c)).trans (MappingStage.of_objects_eq rfl)
  · exact hRefill

/-- The replenishment drain: the replenish-queue pop, then a fold of refills. -/
theorem processReplenishmentsDueOnCore_mappingStage (st : SystemState) (c : CoreId) (now : Nat) :
    MappingStage st (processReplenishmentsDueOnCore st c now) := by
  unfold processReplenishmentsDueOnCore
  exact drainDueOnCore_induction (MappingStage st) c now
    (fun s scId h => h.trans (processOneReplenishmentOnCore_mappingStage s c scId now))
    (fun s scId h => h.trans (releasePlace_mappingStage s c scId)) _ st (.refl st)

/-- **The timer tick keeps the mappings recorded**: the diagnostic clear, the
replenishment drain, the charge, and the reschedule or the scheduling point. -/
theorem timerTickOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (timerTickOnCore st c) := by
  have hP : MappingStage st (timerTickOnCorePrepared st c) :=
    (MappingStage.of_objects_eq (st := st)
      (st' := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }) rfl).trans
      (processReplenishmentsDueOnCore_mappingStage _ c st.machine.timer)
  refine timerTickOnCore_of (P := MappingStage st) st c hP ?_ ?_ ?_
  · intro s hs
    exact hs.trans (handleRescheduleSgiOnCore_mappingStage (handleRescheduleSgiOnCore_eq_state s c))
  · intro s hs
    exact hs.trans (scheduleEffectiveOnCore_mappingStage (scheduleEffectiveOnCore_eq_state s c))
  · intro tid tcb hTcb st3 b hb
    exact hP.trans (timerTickBudgetOnCore_mappingStage hb)

end SeLe4n.Kernel
