/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Ipc
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle

/-!
# Scheduling-context, thread-control and retype arms keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  The scheduling-context configure and bind, the thread
suspend, resume, priority, maximum-controlled-priority and affinity writes, the
yield and the retype are `RunQueueStage`s: every run-queue write they make goes
through the link-writing enqueue, removal and re-bucket, and every other object
write keeps each thread's run-queue entry.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open SeLe4n.Kernel.Lifecycle.Suspend

/-- The guarded enqueue keeps the agreement on either arm. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.runEnqueueOnCore (st : SystemState)
    (c : Concurrency.CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    RunQueueStage st (st.runEnqueueOnCore c t p) := fun hInv hR =>
  ⟨SystemState.runEnqueueOnCore_objects_invExt st c t p hInv, SystemState.runEnqueueOnCore_refined hR⟩

/-- A re-bucket of a thread its core's links queue (the guard the re-bucketing
operations test, WS-ZA ZA4.5). -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.runRequeueOnCore_of_queuedOn
    (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority)
    (h : st.queuedOn c t = true) : RunQueueStage st (st.runRequeueOnCore c t p) :=
  SystemState.RunQueueStage.runRequeueOnCore _ _ _ _
    ((SystemState.queuedOn_eq_runLinkOn _ _ _).symm.trans h)

/-- The bind writes the context's bound thread, the thread's binding and
priority, re-buckets or places the thread through the link-writing queue
operations, and then the thread index and reschedule flags. -/
theorem schedContextBind_runQueueStage {vScId : SeLe4n.ValidObjId} {vTid : SeLe4n.ValidThreadId}
    {st st' : SystemState} (h : SchedContextOps.schedContextBind vScId vTid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SchedContextOps.schedContextBind at h
  split at h
  · rename_i sc hSc _
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i tcb hTcb
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
                  (SchedContextId.ofObjId vScId.val) sc).mp hSc
                simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
                subst h
                refine RunQueueStage.trans ?_ (markKeyChangeFor_runQueueStage _ _ _)
                refine RunQueueStage.trans ?_ (RunQueueStage.withScThreadIndex _ _)
                split
                · rename_i hMem
                  refine RunQueueStage.trans ?_ (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hMem)
                  refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                  exact RunQueueStage.insert rfl rfl rfl
                    (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                · split
                  · refine RunQueueStage.trans ?_
                      (SystemState.RunQueueStage.markReschedulePendingOnCore _ _)
                    refine RunQueueStage.trans ?_ (RunQueueStage.runEnqueueOnCore _ _ _ _)
                    refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                    exact RunQueueStage.insert rfl rfl rfl
                      (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                  · refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                    exact RunQueueStage.insert rfl rfl rfl
                      (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              all_goals cases h
        · cases h
  · cases h

/-- A TCB rewritten through the witnessed lookup, keeping its run-queue fields. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_tcb {st : SystemState}
    {tid : SeLe4n.ThreadId} {t t' : TCB} (h : st.getTcb? tid = some t)
    (hL : ∀ c, t'.runLinkOn c = t.runLinkOn c) (hA : st.rewriteAdmissible tid.toObjId (.tcb t')) :
    RunQueueStage st (st.rewriteObject tid.toObjId (.tcb t') hA) :=
  RunQueueStage.insert (st' := st.rewriteObject tid.toObjId (.tcb t') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact hL c)

/-- The configure's bound-thread propagation: TCB rewrites that keep the
thread's run-queue fields, and a re-bucket of a thread its home queue holds. -/
theorem schedContextConfigureBoundPropagate_runQueueStage (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat) :
    RunQueueStage stStored (SchedContextOps.schedContextConfigureBoundPropagate stStored scId
      boundTid boundTcb hBound priority domain) := by
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only
  split
  · rename_i cur hCur hEq
    split
    · clear hEq hCur
      split
      · exact RunQueueStage.refl _
      · split
        · rename_i hM
          refine RunQueueStage.trans ?_ (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hM)
          exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _
        · exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _
    · refine RunQueueStage.trans ?_ (RunQueueStage.rewriteObject_tcb hCur (fun _ => by rfl) _)
      clear hEq hCur
      split
      · exact RunQueueStage.refl _
      · split
        · rename_i hM
          refine RunQueueStage.trans ?_ (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hM)
          exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _
        · exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _
  · rename_i hEq
    clear hEq
    split
    · exact RunQueueStage.refl _
    · split
      · rename_i hM
        refine RunQueueStage.trans ?_ (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hM)
        exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _
      · exact RunQueueStage.rewriteObject_tcb hBound (fun _ => by rfl) _

/-- The configure purges the context's replenishment (a replenish-queue write),
stores the reconfigured context over the old one, and runs the bound-thread
propagation, the key hook and the chain re-walk. -/
theorem schedContextConfigure_runQueueStage {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState}
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st =
      .ok ((), st')) : RunQueueStage st st' := by
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
          have hS1 : RunQueueStage st stStored :=
            (RunQueueStage.of_frame (st' := SchedContextOps.purgeReplenishmentOnCore st
              (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩) rfl rfl rfl).trans
              (RunQueueStage.storeObject hStore (fun c => by
                rw [SchedContextOps.purgeReplenishmentOnCore_objects,
                  show st.objects[vScId.val]? = _ from hScRaw]; rfl))
          split at h
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact hS1
          · split at h
            · rename_i boundTcb hBound _
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact hS1.trans
                (((schedContextConfigureBoundPropagate_runQueueStage _ _ _ _ hBound _ _).trans
                  (markKeyChangeFor_runQueueStage _ _ _)).trans
                  (PriorityInheritance.repropagateFromWaiter_runQueueStage _ _ _ _))
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]; exact hS1
      · exact absurd h (by simp)

/-- The preemption saves the outgoing thread's registers (a TCB rewrite keeping
its run-queue fields) and puts it back through the guarded enqueue. -/
theorem preemptCurrentOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) : RunQueueStage st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact RunQueueStage.refl _
  · split
    · exact RunQueueStage.refl _
    · split
      · rename_i prevTcb h _
        exact (RunQueueStage.rewriteObject_tcb h (fun _ => by rfl) _).trans
          (RunQueueStage.runEnqueueOnCore _ _ _ _)
      · exact RunQueueStage.refl _

/-- Clearing a core's reschedule flag writes neither objects nor run queues. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.clearReschedulePendingOnCore
    (st : SystemState) (c : Concurrency.CoreId) :
    RunQueueStage st (st.clearReschedulePendingOnCore c) :=
  RunQueueStage.of_frame rfl rfl rfl

/-- The conditional register restore writes only the machine. -/
theorem restoreIncomingContextOnCoreUnlessCurrent_objects_scheduler (st : SystemState)
    (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).objects = st.objects ∧
      (restoreIncomingContextOnCoreUnlessCurrent st c tid).scheduler = st.scheduler := by
  unfold restoreIncomingContextOnCoreUnlessCurrent restoreIncomingContextOnCore
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- The switch preempts, dequeues the incoming thread, restores its registers
and sets the current slot. -/
theorem switchToThreadOnCore_runQueueStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} (h : switchToThreadOnCore st c tid = .ok st') :
    RunQueueStage st st' := by
  unfold switchToThreadOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h
      subst h
      have hP := preemptCurrentOnCore_runQueueStage st c tid
      have hD := RunQueueStage.runRemoveOnCore (preemptCurrentOnCore st c tid) c tid
      refine (hP.trans hD).trans ?_
      have hR := restoreIncomingContextOnCoreUnlessCurrent_objects_scheduler
        ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid) c tid
      exact RunQueueStage.of_frame hR.1 (congrArg (·.runQueue) hR.2)
        (congrArg (·.runQueueEnds) hR.2)
    · cases h
  · cases h

/-- The drop of an out-of-domain incumbent: a preemption and a current-slot write. -/
theorem dropCurrentOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId) :
    RunQueueStage st (dropCurrentOnCore st c) :=
  (preemptCurrentOnCore_runQueueStage st c _).trans (RunQueueStage.of_frame rfl rfl rfl)

/-- The reschedule handler: a switch, a drop or nothing, then the flag clear. -/
theorem handleRescheduleSgiOnCore_runQueueStage {st st' : SystemState} {c : Concurrency.CoreId}
    (h : handleRescheduleSgiOnCore st c = .ok st') : RunQueueStage st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact (dropCurrentOnCore_runQueueStage st c).trans
        (RunQueueStage.clearReschedulePendingOnCore _ _)
    · rw [Except.ok.injEq] at h; subst h
      exact RunQueueStage.clearReschedulePendingOnCore _ _
  · split at h
    · split at h
      · rename_i hSw
        rw [Except.ok.injEq] at h; subst h
        exact (switchToThreadOnCore_runQueueStage hSw).trans
          (RunQueueStage.clearReschedulePendingOnCore _ _)
      · cases h
    · rw [Except.ok.injEq] at h; subst h
      exact RunQueueStage.clearReschedulePendingOnCore _ _

/-- The suspend's scheduling point: a reschedule on the executing core or nothing. -/
theorem suspendRescheduleOnCore_runQueueStage {st st' : SystemState}
    {runningCore executingCore : Concurrency.CoreId} {wasCurrent localDeboosted : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : suspendRescheduleOnCore st runningCore executingCore wasCurrent localDeboosted =
      .ok (st', sgi?)) : RunQueueStage st st' := by
  unfold suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore_runQueueStage hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact RunQueueStage.refl _)

/-- The thread suspend: the reclaimed teardown, the chain revert, the donation
arm, the placement removal, two scheduler-free TCB writes and the scheduling
point. -/
theorem suspendThreadOnCore_runQueueStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    RunQueueStage st st' := by
  simp only [suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb _ =>
    have hS1 := cancelIpcBlockingReclaimed_runQueueStage st vtid.val tcb
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse =>
      have hS2 : RunQueueStage st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hS1
        | some serverId =>
            exact hS1.trans (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
      revert hStep
      split
      · intro hStep; exact absurd hStep (by simp)
      · next s3 hDon =>
        intro hStep
        have hS3 := hS2.trans (cancelSuspendDonation_runQueueStage _ s3 vtid.val _
          (determineTargetCore st vtid.val) hDon)
        have hS4 := hS3.trans (descheduleAt_runQueueStage s3 vtid.val (placedCoreOf? st vtid.val))
        have hS6 : RunQueueStage st
            ((clearPendingStateValid (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val))
              vtid).updateTcb vtid.val (fun t => { t with threadState := .Inactive })) :=
          (hS4.trans (by
            unfold clearPendingStateValid clearPendingState
            exact RunQueueStage.updateTcb _ vtid.val (fun _ _ => rfl))).trans
          (RunQueueStage.updateTcb _ vtid.val (fun _ _ => rfl))
        exact hS6.trans (suspendRescheduleOnCore_runQueueStage hStep)

/-- The resume's fault retirement: one TCB rewrite of the restart frame. -/
theorem retirePendingFaultForResume_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    RunQueueStage st (retirePendingFaultForResume st tid) := by
  unfold retirePendingFaultForResume
  split
  · split
    · unfold applyFaultRestart; exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
    · exact RunQueueStage.refl _
  · exact RunQueueStage.refl _

/-- The resume's ready mark: two TCB rewrites keeping the run-queue fields. -/
theorem resumeReadyMidState_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    RunQueueStage st (resumeReadyMidState st tid) :=
  (show RunQueueStage st (restoreToReady st tid) from by
    unfold restoreToReady restoreToReadyStaging
    exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)).trans
    (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))

/-- The thread resume: the ready mark, the key hook, the wake on the home core
and the local scheduling point. -/
theorem resumeThreadOnCore_runQueueStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) : RunQueueStage st st' := by
  unfold resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have hS : RunQueueStage st (enqueueRunnableOnCore
          (markKeyChangeFrom st (resumeReadyMidState st vtid.val) vtid.val)
          (determineTargetCore st vtid.val) vtid.val) :=
        ((resumeReadyMidState_runQueueStage st vtid.val).trans
          (markKeyChangeFrom_runQueueStage _ _ _)).trans
          (enqueueRunnableOnCore_runQueueStage _ _ _)
      split at h
      · split at h
        · rename_i hH
          rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
          exact hS.trans (handleRescheduleSgiOnCore_runQueueStage hH)
        · cases h
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
  · cases h

/-- The priority ops' preemption seam: the reschedule on the executing core or nothing. -/
theorem priorityRescheduleOnCore_runQueueStage {st st' : SystemState}
    {running? : Option Concurrency.CoreId} {ec : Concurrency.CoreId} {sp : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : RunQueueStage st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · exact RunQueueStage.of_eq hEq
  · exact handleRescheduleSgiOnCore_runQueueStage hH

/-- The priority ops' shared effect: the source write, the re-bucket, the key
hook, the chain re-walk and the preemption seam. -/
theorem applyPriorityChangeOnCore_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {p : SeLe4n.Priority} {ec : Concurrency.CoreId} {b : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p ec b =
      .ok (st', sgi?)) : RunQueueStage st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  exact (((SchedContext.PriorityManagement.updatePrioritySource_runQueueStage st tid tcb p).trans
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_runQueueStage _ tid p
      (determineTargetCore st tid))).trans
    ((markKeyChangeFor_runQueueStage _ tid (effectiveSchedParams st tcb)).trans
      (PriorityInheritance.repropagateFromWaiter_runQueueStage _ tid ec st.objectIndex.length))).trans
    (priorityRescheduleOnCore_runQueueStage h)

theorem setPriorityOnCore_runQueueStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : RunQueueStage st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore_runQueueStage h
      · cases h
  · cases h

theorem setMCPriorityOnCore_runQueueStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : RunQueueStage st st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        have hS := RunQueueStage.rewriteObject_tcb (t' := { targetTcb with maxControlledPriority := p })
          hTarget (fun _ => by rfl) (SystemState.rewriteAdmissible_tcb hTarget _)
        split at h
        · exact hS.trans (applyPriorityChangeOnCore_runQueueStage h)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
      · cases h
  · cases h

/-- A thread core `c`'s queue holds is admitted there: its links name `c`. -/
theorem _root_.SeLe4n.Model.SystemState.runEnqueueAdmits_of_contains {st : SystemState}
    {c : Concurrency.CoreId} {t : SeLe4n.ThreadId} (hR : st.runQueueRefined)
    (h : (st.scheduler.runQueueOnCore c).contains t = true) : st.runEnqueueAdmits c t = true := by
  rw [← (hR c).contains] at h
  unfold SystemState.runLinkOn at h
  unfold SystemState.runEnqueueAdmits
  cases hT : st.getTcb? t with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    dsimp only at h
    unfold TCB.runLinkOn at h
    by_cases hc : tcb.runCoreCode = c.val + 1
    · simp [hc]
    · rw [if_neg hc] at h; cases h

/-- The affinity migration moves a thread from the queue that holds it to its
new home core's: after the removal it is on no queue, so the enqueue is admitted. -/
theorem migrateRunQueueOnAffinityChange_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (fromCore toCore : Concurrency.CoreId) :
    RunQueueStage st (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact RunQueueStage.refl _
  · rename_i hNe
    split
    · exact RunQueueStage.refl _
    · rename_i tcb hTcb
      split
      · rename_i hC
        refine RunQueueStage.trans ?_ (RunQueueStage.of_frame (st := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority) rfl rfl rfl)
        intro hInv hR
        have hS := RunQueueStage.runRemoveOnCore st fromCore tid hInv hR
        refine ⟨SystemState.runEnqueueAdmitted_objects_invExt _ _ _ _ hS.1,
          SystemState.runEnqueueAdmitted_refined hS.2 ?_ ?_⟩
        · rw [SystemState.runRemoveOnCore_getTcb?_isSome, hTcb]; rfl
        · intro c' hc'
          by_cases hf : c' = fromCore
          · subst hf
            rw [SystemState.runRemoveOnCore_runQueueOnCore_self, RunQueue.contains_remove]
            simp
          · rw [SystemState.runRemoveOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hf)]
            exact SystemState.runEnqueueAdmits_not_contains hR
              (SystemState.runEnqueueAdmits_of_contains hR
                ((hR fromCore).contains_of_runCoreCode hTcb hC)) c' hf
      · exact RunQueueStage.refl _

/-- The affinity op: the affinity field write, the replenishment move (replenish
queues only) and the run-queue migration. -/
theorem setThreadCpuAffinityOnCore_runQueueStage {st st' : SystemState}
    {vTargetTid : SeLe4n.ValidThreadId} {affinity : Option Concurrency.CoreId}
    {ec : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityOnCore st vTargetTid affinity ec = .ok (st', sgi?)) :
    RunQueueStage st st' := by
  unfold setThreadCpuAffinityOnCore setThreadCpuAffinityWithMigration at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i stSet hSet
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          have hS1 : RunQueueStage st stSet := by
            unfold setThreadCpuAffinity at hSet
            split at hSet
            · rename_i t hT _
              rw [Except.ok.injEq] at hSet; subst hSet
              exact RunQueueStage.rewriteObject_tcb hT (fun _ => by rfl) _
            · cases hSet
          refine hS1.trans (RunQueueStage.trans ?_ (migrateRunQueueOnAffinityChange_runQueueStage _ _ _ _))
          split
          · unfold migrateSchedContextReplenishment
            split
            · exact RunQueueStage.refl _
            · exact RunQueueStage.of_frame rfl rfl rfl
          · exact RunQueueStage.refl _
        · cases h
  · cases h

/-- The register save: one TCB rewrite of the register context. -/
theorem saveOutgoingContextOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId) :
    RunQueueStage st (saveOutgoingContextOnCore st c) := by
  unfold saveOutgoingContextOnCore
  split
  · exact RunQueueStage.refl _
  · exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)

/-- The register restore writes the machine alone. -/
theorem restoreIncomingContextOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : RunQueueStage st (restoreIncomingContextOnCore st c tid) := by
  unfold restoreIncomingContextOnCore
  split
  · exact RunQueueStage.of_frame rfl rfl rfl
  · exact RunQueueStage.refl _

/-- The idle dispatch: dequeue, restore, current-slot write. -/
theorem dispatchIdleOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId) :
    RunQueueStage st (dispatchIdleOnCore st c) :=
  ((RunQueueStage.runRemoveOnCore st c _).trans
    (restoreIncomingContextOnCore_runQueueStage _ c _)).trans (RunQueueStage.of_frame rfl rfl rfl)

theorem idleFallbackOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId) :
    RunQueueStage st (idleFallbackOnCore st c) := by
  unfold idleFallbackOnCore
  split
  · exact dispatchIdleOnCore_runQueueStage st c
  · exact RunQueueStage.of_frame rfl rfl rfl

/-- The drop-current reschedule: save, then the idle fallback or the dequeue,
restore and current-slot write of the chosen thread, then the flag clear. -/
theorem scheduleEffectiveOnCore_runQueueStage {st st' : SystemState} {c : Concurrency.CoreId}
    (h : scheduleEffectiveOnCore st c = .ok st') : RunQueueStage st st' := by
  unfold scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rw [Except.ok.injEq] at h; subst h
    exact ((saveOutgoingContextOnCore_runQueueStage st c).trans
      (idleFallbackOnCore_runQueueStage _ c)).trans (RunQueueStage.clearReschedulePendingOnCore _ _)
  · split at h
    · split at h
      · rw [Except.ok.injEq] at h; subst h
        exact (((saveOutgoingContextOnCore_runQueueStage st c).trans
          (RunQueueStage.runRemoveOnCore _ c _)).trans
          (restoreIncomingContextOnCore_runQueueStage _ c _)).trans
          (RunQueueStage.of_frame rfl rfl rfl)
      · cases h
    · cases h

/-- A SchedContext rewritten through its witnessed lookup. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_schedContext
    {st : SystemState} {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext}
    (h : st.getSchedContext? scId = some sc) (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) :
    RunQueueStage st (st.rewriteObject scId.toObjId (.schedContext sc') hA) :=
  RunQueueStage.insert (st' := st.rewriteObject scId.toObjId (.schedContext sc') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl)

theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.updateSchedContext (st : SystemState)
    (scId : SeLe4n.SchedContextId) (f : SchedContext → SchedContext) :
    RunQueueStage st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc h _
    exact RunQueueStage.rewriteObject_schedContext h _
  · exact RunQueueStage.refl _

/-- The priority-inheritance revert: one boost write per chain link. -/
theorem revertPriorityInheritance_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (fuel : Nat) : RunQueueStage st (PriorityInheritance.revertPriorityInheritance st tid fuel) := by
  induction fuel generalizing st tid with
  | zero => exact RunQueueStage.refl _
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    have hB := PriorityInheritance.updatePipBoostOnCore_runQueueStage st Concurrency.bootCoreId tid
    split
    · exact hB.trans (ih _ _)
    · exact hB

/-- The timeout of one IPC-blocked thread: the abort, the wake and the revert. -/
theorem timeoutThread_runQueueStage {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId} {st : SystemState}
    {r : SystemState × Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timeoutThread epId isReceiveQ tid ec st = .ok r) : RunQueueStage st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    have hS := (abortPendingIpcOnEndpoint_runQueueStage hA).trans (wakeThread_runQueueStage st2 tid ec)
    dsimp only at h
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact hS.trans (revertPriorityInheritance_runQueueStage _ _ _)
    · rw [Except.ok.injEq] at h; subst h; exact hS

/-- The bound-context timeout pass: a fold of timeouts. -/
theorem timeoutBlockedThreads_runQueueStage (st : SystemState) (scId : SeLe4n.SchedContextId)
    (ec : Concurrency.CoreId) : RunQueueStage st (timeoutBlockedThreads st scId ec).1 := by
  unfold timeoutBlockedThreads
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (Concurrency.CoreId × Concurrency.SgiKind)),
      RunQueueStage st acc.1 → RunQueueStage st (l.foldl (fun acc tid =>
        let (st', errs, sgis) := acc
        match st'.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match timeoutThread epId isReceiveQ tid ec st' with
            | .ok r => (r.1, errs, sgis ++ r.2.toList)
            | .error e => (st', errs ++ [(tid, e)], sgis)
          | none => (st', errs, sgis)
        | none => (st', errs, sgis)) acc).1 from H _ _ (RunQueueStage.refl _)
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
          exact h.trans (timeoutThread_runQueueStage hT)
        · exact h
      · exact h
    · exact h

/-- An unbound thread's slice end: a slice reset and the guarded enqueue. -/
theorem sliceExpireOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    RunQueueStage st (sliceExpireOnCore st c tid tcb hTcb) :=
  (RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl) _).trans
    (RunQueueStage.runEnqueueOnCore _ _ _ _)

/-- A bound thread's budget spend: the context rewrite, the replenish-queue
insert and the guarded enqueue. -/
theorem spendBudgetOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat) :
    RunQueueStage st (spendBudgetOnCore st c tid scId sc hSc ticks) := by
  unfold spendBudgetOnCore
  refine RunQueueStage.trans ?_ (RunQueueStage.runEnqueueOnCore _ _ _ _)
  unfold replenishOnCore
  exact (RunQueueStage.rewriteObject_schedContext hSc
    (SystemState.rewriteAdmissible_schedContext hSc _)).trans (RunQueueStage.of_frame rfl rfl rfl)

/-- The tick's exhausted bound arm: the spend, the timeouts and the diagnostic. -/
theorem budgetExhaustOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat) :
    RunQueueStage st (budgetExhaustOnCore st c tid scId sc hSc ticks).1 :=
  ((spendBudgetOnCore_runQueueStage st c tid scId sc hSc ticks).trans
    (timeoutBlockedThreads_runQueueStage _ scId c)).trans (RunQueueStage.of_frame rfl rfl rfl)

theorem timerTickBudgetOnCore_runQueueStage {st : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = .ok r) : RunQueueStage st r.1 := by
  unfold timerTickBudgetOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_runQueueStage st c tid tcb hTcb
    · rw [Except.ok.injEq] at h; subst h
      exact RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _)
  all_goals
    split at h
    · rename_i sc hSc _
      split at h
      · rw [Except.ok.injEq] at h; subst h
        exact budgetExhaustOnCore_runQueueStage st c tid _ sc hSc 1
      · rw [Except.ok.injEq] at h; subst h
        exact RunQueueStage.rewriteObject_schedContext hSc
          (SystemState.rewriteAdmissible_schedContext hSc _)
    · cases h

theorem timerTickChargeCurrentOnCore_runQueueStage {st : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickChargeCurrentOnCore st c tid = .ok r) : RunQueueStage st r.1 := by
  obtain ⟨_, _, hB⟩ := timerTickChargeCurrentOnCore_ok h
  exact timerTickBudgetOnCore_runQueueStage hB

/-- The yield's charge: the slice end or the budget forfeit with the key hook. -/
theorem yieldChargeOnCore_runQueueStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} (h : yieldChargeOnCore st c tid = .ok st') : RunQueueStage st st' := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_runQueueStage st c tid tcb hTcb
    all_goals
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore_runQueueStage st c tid _ sc hSc _).trans
          (markKeyChangeFor_runQueueStage _ _ _)
      · cases h

/-- The yield: the charge, then the reschedule. -/
theorem yieldOnCore_runQueueStage {st st' : SystemState} {c : Concurrency.CoreId}
    (h : yieldOnCore st c = .ok st') : RunQueueStage st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore_runQueueStage hC).trans (scheduleEffectiveOnCore_runQueueStage h)

/-- One due replenishment: the refill and, for a thread it makes eligible, the wake. -/
theorem processOneReplenishmentOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    RunQueueStage st (processOneReplenishmentOnCore st c scId now).1 := by
  have hRefill : RunQueueStage st (refillSchedContext st scId now) := by
    unfold refillSchedContext; exact RunQueueStage.updateSchedContext _ _ _
  unfold processOneReplenishmentOnCore
  dsimp only
  split
  · split
    · exact hRefill
    · exact hRefill.trans (wakeThread_runQueueStage _ _ c)
  · exact hRefill

/-- The replenishment drain: the replenish-queue pop, then a fold of refills. -/
theorem processReplenishmentsDueOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (now : Nat) : RunQueueStage st (processReplenishmentsDueOnCore st c now).1 := by
  unfold processReplenishmentsDueOnCore
  dsimp only
  suffices H : ∀ (l : List SeLe4n.SchedContextId)
      (acc : SystemState × List (Concurrency.CoreId × Concurrency.SgiKind) × Bool),
      RunQueueStage st acc.1 → RunQueueStage st (l.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1 from
    H _ _ (RunQueueStage.of_frame rfl rfl rfl)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (h.trans (processOneReplenishmentOnCore_runQueueStage _ c x now))

/-- The per-core timer tick: the diagnostic clear, the replenishment drain, the
charge, and the reschedule or the local reschedule decision. -/
theorem timerTickOnCore_runQueueStage {st : SystemState} {c : Concurrency.CoreId}
    {r : SystemState × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickOnCore st c = .ok r) : RunQueueStage st r.1 := by
  unfold timerTickOnCore at h
  dsimp only at h
  have hP : RunQueueStage st (processReplenishmentsDueOnCore
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer).1 :=
    (RunQueueStage.of_frame rfl rfl rfl).trans (processReplenishmentsDueOnCore_runQueueStage
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer)
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i hH
        rw [Except.ok.injEq] at h; subst h
        exact hP.trans (handleRescheduleSgiOnCore_runQueueStage hH)
    · rw [Except.ok.injEq] at h; subst h; exact hP
  · split at h
    · cases h
    · rename_i st2 pre sgis hC
      have hC2 := hP.trans (timerTickChargeCurrentOnCore_runQueueStage hC)
      split at h
      · split at h
        · cases h
        · rename_i hS
          rw [Except.ok.injEq] at h; subst h
          exact hC2.trans (scheduleEffectiveOnCore_runQueueStage hS)
      · split at h
        · split at h
          · cases h
          · rename_i hH
            rw [Except.ok.injEq] at h; subst h
            exact hC2.trans (handleRescheduleSgiOnCore_runQueueStage hH)
        · rw [Except.ok.injEq] at h; subst h; exact hC2

/-- A fresh replacement names no run queue. -/
theorem objRunLinkOn_of_retypeReplacementFresh {o : KernelObject} (h : retypeReplacementFresh o)
    (c : Concurrency.CoreId) : SystemState.objRunLinkOn (some o) c = RunQueue.RunQueueLink.none := by
  cases o with
  | tcb t =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hC⟩ := h
    show t.runLinkOn c = _
    unfold TCB.runLinkOn
    rw [if_neg (by omega)]
  | _ => rfl

/-- The destroy path under the detached-target pack: the cleanup and the scrub
write neither objects nor scheduler, the target thread is on no run queue (so
its entry is empty), and the replacement is fresh. -/
theorem lifecycleRetypeDirectWithCleanup_runQueueStage {st st' : SystemState}
    {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    RunQueueStage st st' := fun hInv hR => by
  obtain ⟨-, currentObj, stClean, hObj, hClean, hStore⟩ :=
    lifecycleRetypeDirectWithCleanup_ok_decompose hStep
  obtain ⟨hCO, hCS, -⟩ := lifecyclePreRetypeCleanup_detached_frame st stClean target currentObj
    newObj hInv hObj hDet hClean
  have hSO : (scrubObjectMemory stClean target currentObj.objectType).objects = st.objects :=
    (scrubObjectMemory_objects_eq stClean target currentObj.objectType).trans hCO
  have hSS : (scrubObjectMemory stClean target currentObj.objectType).scheduler = st.scheduler :=
    (scrubObjectMemory_scheduler_eq stClean target currentObj.objectType).trans hCS
  have h1 : RunQueueStage st (scrubObjectMemory stClean target currentObj.objectType) :=
    RunQueueStage.of_frame hSO (by rw [hSS]) (by rw [hSS])
  refine (h1.trans (RunQueueStage.storeObject hStore (fun c => ?_))) hInv hR
  rw [objRunLinkOn_of_retypeReplacementFresh hFresh c, hSO, hObj]
  cases currentObj with
  | tcb t =>
    have hT : st.getTcb? t.tid = some t := (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by rw [hDet.tcbSelfId t hObj]; exact hObj)
    have hq := (hDet.tcbDescheduled t hObj c).2.1
    rw [SystemState.queuedOn_eq_runLinkOn] at hq
    have hN := SystemState.runLinkOn_eq_none_of_not_queued hq
    unfold SystemState.runLinkOn at hN
    rw [hT] at hN
    exact hN.symm
  | _ => rfl

/-- The shootdown form: the destroy path, then ASID rounds that write neither
objects nor scheduler. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_runQueueStage {st st' : SystemState}
    {ec : Concurrency.CoreId} {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at hStep
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    simp only [hBase] at hStep
    rw [retypeShootdownAsids_eq] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    subst hStep
    exact (lifecycleRetypeDirectWithCleanup_runQueueStage hFresh hDet hBase).trans
      (RunQueueStage.of_frame (retypeAsidRoundFold_objects ec _ stB)
        (by rw [retypeAsidRoundFold_scheduler]) (by rw [retypeAsidRoundFold_scheduler]))

theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_runQueueStage {st st' : SystemState}
    {ec : Concurrency.CoreId} {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st =
      .ok ((), st')) : RunQueueStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at hStep
  cases hBase : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    simp only [hBase] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    subst hStep
    exact (lifecycleRetypeDirectWithCleanupShootdown_runQueueStage hFresh hDet hBase).trans
      (RunQueueStage.of_frame (retypeInitiatorDrain_objects ec _ stB)
        (by rw [retypeInitiatorDrain_scheduler]) (by rw [retypeInitiatorDrain_scheduler]))

/-- The live `.lifecycleRetype` arm: the per-core destroy path under the
instruction-cache broadcast, which writes neither objects nor scheduler. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_runQueueStage
    {st st' : SystemState} {ec : Concurrency.CoreId} {authCap : Capability}
    {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache ec authCap target newObj st =
      .ok ((), st')) : RunQueueStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at hStep
  cases hK : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
    contradiction
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    obtain ⟨hObjs, -, hSched, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
    exact (lifecycleRetypeDirectWithCleanupShootdownPerCore_runQueueStage hFresh hDet hK).trans
      (RunQueueStage.of_frame hObjs (by rw [hSched]) (by rw [hSched]))

/-- The live `.untypedRetype` arm: the carve. -/
theorem untypedRetypeFromCap_runQueueStage {tid : SeLe4n.ThreadId} {decoded : SyscallDecodeResult}
    {st st' : SystemState} (h : untypedRetypeFromCap tid decoded st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ := untypedRetypeFromCap_ok tid decoded st st' h
  exact untypedRetypeObject_runQueueStage hCarve

/-- The per-core context unbind: the unbind, then the preemption seam. -/
theorem schedContextUnbindOnCore_runQueueStage {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    RunQueueStage st st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hU
    exact (SchedContextOps.schedContextUnbind_runQueueStage vScId st stU hU).trans
      (priorityRescheduleOnCore_runQueueStage h)


end SeLe4n.Kernel
