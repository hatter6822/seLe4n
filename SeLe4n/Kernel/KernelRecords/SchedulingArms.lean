-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Capability
import SeLe4n.Kernel.SchedContext.SchedControl

/-!
# The priority and scheduling-context arms keep the records' reads

WS-ZA ZA6.37.  A priority write rewrites a thread's priority and its bound
context's band in place, re-buckets the run queues and re-walks the inheritance
chain; a scheduling-context write rewrites contexts and the threads' binding and
yield fields in place.  None of them writes a thread's reply view, IPC state,
thread state or fault record, a root or the ASID table, so each is a
`RecordsFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-! ### The remaining scheduling points -/

theorem runEnqueueAdmitted (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (st.runEnqueueAdmitted c t p) :=
  of_runLinkStep (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks st c t p)
    (SystemState.runEnqueueAdmitted_replyViews_eq st c t p)
    (SystemState.runEnqueueAdmitted_onlyObjectsSchedulerDiffer st c t p)
    (SystemState.runEnqueueAdmitted_objects_invExt st c t p hInv)

theorem runRequeueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (st.runRequeueOnCore c t p) :=
  of_runLinkStep (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks st c t p)
    (_root_.SeLe4n.Kernel.runRequeueOnCore_replyViews_eq st c t p)
    (SystemState.runRequeueOnCore_onlyObjectsSchedulerDiffer st c t p)
    (SystemState.runRequeueOnCore_objects_invExt st c t p hInv)

theorem markKeyChangeFor (st : SystemState) (t : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.markKeyChangeFor st t k) :=
  of_objects_eq hInv (markKeyChangeFor_objects st t k) (markKeyChangeFor_extract_frame SystemState.asidTable st t k fun _ _ => rfl)
    (markKeyChangeFor_extract_frame (fun x : SystemState => x.machine.physicalAddressWidth) st t k
      fun _ _ => rfl)

theorem markCandidacyGainFor (st : SystemState) (t : SeLe4n.ThreadId) (b : Bool)
    (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.markCandidacyGainFor st t b) :=
  of_objects_eq hInv (markCandidacyGainFor_objects st t b) (markCandidacyGainFor_extract_frame SystemState.asidTable st t b fun _ _ => rfl)
    (markCandidacyGainFor_extract_frame (fun x : SystemState => x.machine.physicalAddressWidth) st t b
      fun _ _ => rfl)

/-! ### Priorities -/

/-- The priority's source write: the bound context's band and the thread's
priority, each in place. -/
theorem updatePrioritySource (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContext.PriorityManagement.updatePrioritySource st t tcb p) := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · rename_i scId _
    have F := updateSchedContext st scId (fun sc => { sc with priority := p }) hInv
    exact F.trans (updateTcb _ t F.invExt fun _ => rfl)
  · exact updateTcb _ t hInv fun _ => rfl

theorem migrateRunQueueBucketOnCore (st : SystemState) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (home : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st t p home) := by
  unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
  split
  · exact runRequeueOnCore _ _ _ _ hInv
  · exact refl hInv

theorem repropagateFromWaiter (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.repropagateFromWaiter st t ec fuel) :=
  PriorityInheritance.repropagateFromWaiter_preserves (RecordsFrame st) st t ec fuel
    (fun s _ => propagatePipChainCrossCore st s ec fuel hInv) (refl hInv)

/-- The priority ops' preemption seam: the reschedule on the executing core or
nothing. -/
theorem priorityRescheduleOnCore {st st' : SystemState} {running? : Option CoreId} {ec : CoreId}
    {sp : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : RecordsFrame st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · exact of_eq hInv hEq
  · exact handleRescheduleSgiOnCore hInv hH

/-- The priority ops' shared effect: the source write, the re-bucket, the key
hook, the chain re-walk and the preemption seam. -/
theorem applyPriorityChangeOnCore {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    {p : SeLe4n.Priority} {ec : CoreId} {b : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st t tcb p ec b =
      .ok (st', sgi?)) : RecordsFrame st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  have F1 := updatePrioritySource st t tcb p hInv
  have F2 := F1.trans (migrateRunQueueBucketOnCore _ t p (determineTargetCore st t) F1.invExt)
  have F3 := F2.trans (markKeyChangeFor _ t (effectiveSchedParams st tcb) F2.invExt)
  have F4 := F3.trans (repropagateFromWaiter _ t ec st.objectIndex.length F3.invExt)
  exact F4.trans (priorityRescheduleOnCore F4.invExt h)

theorem setPriorityOnCore {st st' : SystemState} {vCaller vTarget : SeLe4n.ValidThreadId}
    {p : SeLe4n.Priority} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCaller vTarget p ec =
      .ok (st', sgi?)) : RecordsFrame st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore hInv h
      · cases h
  · cases h

theorem setMCPriorityOnCore {st st' : SystemState} {vCaller vTarget : SeLe4n.ValidThreadId}
    {p : SeLe4n.Priority} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCaller vTarget p ec =
      .ok (st', sgi?)) : RecordsFrame st st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        have hS := rewriteObject (o := .tcb { targetTcb with maxControlledPriority := p })
          (SystemState.rewriteAdmissible_tcb hTarget _) hInv
          (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTarget]; rfl)
        split at h
        · exact hS.trans (applyPriorityChangeOnCore hS.invExt h)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
      · cases h
  · cases h

/-! ### Scheduling contexts -/

/-- A step `F` followed by a step whose frame needs only the store's invariant. -/
theorem andThen {a b c : SystemState} (F : RecordsFrame a b)
    (G : b.objects.invExt → RecordsFrame b c) : RecordsFrame a c :=
  F.trans (G F.invExt)

/-- Two frames that need only the store's invariant, chained. -/
theorem chain {a b c : SystemState} (F : a.objects.invExt → RecordsFrame a b)
    (G : b.objects.invExt → RecordsFrame b c) : a.objects.invExt → RecordsFrame a c :=
  fun h => (F h).andThen G

theorem releasePlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : RecordsFrame st (st.releasePlace c s) :=
  of_agreeOffReleaseLinks (SystemState.releasePlace_agree st c s)
    (by have h := congrArg SystemState.asidTable (SystemState.releasePlace_releaseOnlyWrite st c s).1; exact h)
    (SystemState.releasePlace_objects_invExt st c s hInv)
    (by
      have h := congrArg (fun x : SystemState => x.machine.physicalAddressWidth)
        (SystemState.releasePlace_releaseOnlyWrite st c s).1
      exact h)

theorem purgeReplenishment (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : RecordsFrame st (SchedContextOps.purgeReplenishment st s) :=
  of_agreeOffReleaseLinks (SchedContextOps.purgeReplenishment_agree st s)
    (by have h := congrArg SystemState.asidTable (SchedContextOps.purgeReplenishment_releaseOnlyWrite st s).1; exact h)
    (SchedContextOps.purgeReplenishment_objects_invExt st s hInv)
    (by
      have h := congrArg (fun x : SystemState => x.machine.physicalAddressWidth)
        (SchedContextOps.purgeReplenishment_releaseOnlyWrite st s).1
      exact h)

/-- `setConsumed` rewrites a context and a thread's two return registers in
place. -/
theorem setConsumed (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.setConsumed st s t) := by
  unfold _root_.SeLe4n.Kernel.setConsumed
  split
  · exact (updateSchedContext st s _ hInv).andThen fun h => updateTcb _ t h fun _ => rfl
  · exact refl hInv

theorem schedContextConsumedOnCore {s : SeLe4n.SchedContextId} {c : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : schedContextConsumedOnCore s c st = .ok st') : RecordsFrame st st' := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok h
  exact setConsumed st s caller hInv

theorem runPrependLinks_replyViews_eq (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runPrependLinks c t p).replyViews = st.replyViews := by
  unfold SystemState.runPrependLinks; dsimp only
  rw [SystemState.updateTcbAtCode_replyViews_eq _ _ ?h1,
    SystemState.updateTcbAtCode_replyViews_eq _ _ ?h2,
    SystemState.mapTcbInPlace_replyViews_eq _ _ ?h3]
  all_goals intro x; rfl

theorem runEnqueueHeadOnCore_replyViews_eq (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueHeadOnCore c t p).replyViews = st.replyViews := by
  unfold SystemState.runEnqueueHeadOnCore
  split
  · have h := SystemState.runEnqueueHeadAdmitted_objects st c t p
    split at h
    · exact SystemState.replyViews_congr h
    · exact (SystemState.replyViews_congr h).trans (runPrependLinks_replyViews_eq st c t p)
  · rfl

/-- A head enqueue writes run-queue links alone. -/
theorem runEnqueueHeadOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (st.runEnqueueHeadOnCore c t p) :=
  of_runLinkStep (SystemState.runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p)
    (runEnqueueHeadOnCore_replyViews_eq st c t p)
    (SystemState.runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer st c t p)
    (SystemState.runEnqueueHeadOnCore_objects_invExt st c t p hInv)

theorem setYieldLink (st : SystemState) (s : SeLe4n.SchedContextId) (caller : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.setYieldLink st s caller) :=
  (updateSchedContext st s _ hInv).andThen fun h => updateTcb _ caller h fun _ => rfl

theorem yieldToRequeue (st : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContextOps.yieldToRequeue st home t p) := by
  unfold SchedContextOps.yieldToRequeue
  split
  · exact refl hInv
  · exact ((runRemoveOnCore st home t hInv).andThen fun h => runEnqueueHeadOnCore _ home t p h).andThen
      fun h => markReschedulePendingOnCore _ home h

theorem yieldToLink (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (caller t : SeLe4n.ThreadId) (pC pT : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContextOps.yieldToLink st c s caller t pC pT) := by
  unfold SchedContextOps.yieldToLink SchedContextOps.yieldToLinkPrefix
  refine ((((((setYieldLink st s caller hInv).andThen fun h => runRemoveOnCore _ c t h).andThen
    fun h => runDescheduleOnCore _ c caller h).andThen fun h => runEnqueueHeadOnCore _ c caller pC h).andThen
    fun h => runEnqueueHeadOnCore _ c t pT h).andThen fun h => ?_)
  exact handleRescheduleSgiOnCore h (handleRescheduleSgiOnCore_eq_state _ c)

theorem cancelYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.cancelYieldFrom st s) := by
  unfold _root_.SeLe4n.Kernel.cancelYieldFrom
  split
  · split
    · exact refl hInv
    · exact (updateSchedContext st s _ hInv).andThen fun h => updateTcb _ _ h fun _ => rfl
  · exact refl hInv

theorem completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.completeYieldFrom st s) := by
  unfold _root_.SeLe4n.Kernel.completeYieldFrom
  split
  · split
    · exact refl hInv
    · exact (setConsumed st s _ hInv).andThen fun h => cancelYieldFrom _ s h
  · exact refl hInv

/-- **The yieldTo invocation keeps the records' reads**: the completion, the
resume's placement, `setConsumed`, the requeue and the linked branch. -/
theorem schedContextYieldToOnCore {s : SeLe4n.SchedContextId} {c : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextYieldToOnCore s c st = .ok st') : RecordsFrame st st' := by
  obtain ⟨caller, -, t, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok h
  unfold SchedContextOps.yieldToBound
  dsimp only
  have F := (completeYieldFrom st s hInv).andThen fun h =>
    releasePlace _ (determineTargetCore (_root_.SeLe4n.Kernel.completeYieldFrom st s) t) s h
  refine F.andThen fun hI => ?_
  generalize (_root_.SeLe4n.Kernel.completeYieldFrom st s).releasePlace
    (determineTargetCore (_root_.SeLe4n.Kernel.completeYieldFrom st s) t) s = st2 at hI ⊢
  split
  · exact setConsumed _ _ _ hI
  · split
    · exact setConsumed _ _ _ hI
    · split
      · exact setConsumed _ _ _ hI
      · split
        · split
          · exact (yieldToRequeue _ _ _ _ hI).andThen fun h => setConsumed _ _ _ h
          · exact yieldToLink _ _ _ _ _ _ _ hI
        · exact setConsumed _ _ _ hI

/-- A scheduling context rewritten through its witnessed lookup. -/
theorem rewriteObject_schedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {sc : SchedContext} (h : st.getSchedContext? scId = some sc) (sc' : SchedContext)
    (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) (hInv : st.objects.invExt) :
    RecordsFrame st (st.rewriteObject scId.toObjId (.schedContext sc') hA) :=
  rewriteObject hA hInv (by rw [(SystemState.getSchedContext?_eq_some_iff st scId sc).mp h]; rfl)

/-- A thread rewritten through its witnessed lookup, keeping its record view. -/
theorem rewriteObject_tcb {st : SystemState} {t : SeLe4n.ThreadId} {x : TCB}
    (h : st.getTcb? t = some x) (x' : TCB) (hV : x'.recordView = x.recordView)
    (hA : st.rewriteAdmissible t.toObjId (.tcb x')) (hInv : st.objects.invExt) :
    RecordsFrame st (st.rewriteObject t.toObjId (.tcb x') hA) :=
  rewriteObject hA hInv (by rw [(SystemState.getTcb?_eq_some_iff st t x).mp h]; simp [hV])

/-- The bind writes the context's bound thread and the thread's binding and
priority in place, re-buckets or places the thread, then the key hook and the
context's placement. -/
theorem schedContextBind {vScId : SeLe4n.ValidObjId} {vTid : SeLe4n.ValidThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextBind vScId vTid st = .ok ((), st')) : RecordsFrame st st' := by
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
                refine chain ?_ (releasePlace _ _ _) hInv
                refine chain ?_ (markKeyChangeFor _ _ _)
                split
                · refine chain ?_ (runRequeueOnCore _ _ _ _)
                  exact chain (rewriteObject_schedContext hSc _ _) fun h => updateTcb _ _ h fun _ => rfl
                · split
                  · refine chain (chain ?_ (runEnqueueOnCore _ _ _ _)) (markReschedulePendingOnCore _ _)
                    exact chain (rewriteObject_schedContext hSc _ _) fun h => updateTcb _ _ h fun _ => rfl
                  · exact chain (rewriteObject_schedContext hSc _ _) fun h => updateTcb _ _ h fun _ => rfl
              all_goals cases h
        · cases h
  · cases h

/-- The configure's bound-thread propagation: thread rewrites in place and a
re-bucket. -/
theorem schedContextConfigureBoundPropagate (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (hInv : stStored.objects.invExt) :
    RecordsFrame stStored (SchedContextOps.schedContextConfigureBoundPropagate stStored scId
      boundTid boundTcb hBound priority domain) := by
  have hP : ∀ (P : Prop) [Decidable P], RecordsFrame stStored
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
    have F := rewriteObject_tcb hBound { boundTcb with priority := ⟨priority⟩ } rfl
      (SystemState.rewriteAdmissible_tcb hBound _) hInv
    split
    · exact refl hInv
    · split
      · exact F.andThen fun h => runRequeueOnCore _ _ _ _ h
      · exact F
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only
  split
  · rename_i cur hCur hEq
    split
    · exact hP _
    · refine (hP _).andThen fun h => rewriteObject_tcb hCur _ ?_ _ h
      rfl
  · exact hP _

/-- The configure's resume tail writes run-queue links and the scheduler alone. -/
theorem configureResumeBound (st : SystemState) (t : SeLe4n.ThreadId) (sc : SchedContext)
    (hInv : st.objects.invExt) : RecordsFrame st (SchedContextOps.configureResumeBound st t sc) := by
  unfold SchedContextOps.configureResumeBound
  dsimp only
  split
  · split
    · exact refl hInv
    · exact runRemoveOnCore _ _ _ hInv
  · split
    · split
      · exact (runEnqueueOnCore _ _ _ _ hInv).andThen fun h => markReschedulePendingOnCore _ _ h
      · split
        · exact markReschedulePendingOnCore _ _ hInv
        · exact refl hInv
    · exact refl hInv

/-- The configure purges the context's replenishment, stores the reconfigured
context over the old one, and runs the placement, the bound-thread
propagation, the key hooks, the chain re-walk and the resume tail. -/
theorem schedContextConfigure {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st =
      .ok ((), st')) : RecordsFrame st st' := by
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
          have Fp := purgeReplenishment st ⟨vScId.val.toNat⟩ hInv
          have F1 : RecordsFrame st stStored := Fp.trans (storeObject Fp.invExt hStore
            (by rw [Fp.views]; exact (congrArg recordViewOf hScRaw).symm) (fun _ h => by cases h))
          split at h
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact F1
          · split at h
            · rename_i boundTcb hBound _
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact (((((F1.andThen fun h => releasePlace _ _ _ h).andThen fun h =>
                schedContextConfigureBoundPropagate _ _ _ _ hBound _ _ h).andThen fun h =>
                markCandidacyGainFor _ _ _ h).andThen fun h => markKeyChangeFor _ _ _ h).andThen
                fun h => repropagateFromWaiter _ _ _ _ h).andThen fun h => configureResumeBound _ _ _ h
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]; exact F1.andThen fun h => releasePlace _ _ _ h
      · exact absurd h (by simp)

/-- The unbind's run-queue stage: a requeue, an enqueue and its flag, or
nothing. -/
theorem schedContextUnbindQueueStage (st : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (w : Bool) (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContextOps.schedContextUnbindQueueStage st home t p w) := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · exact runRequeueOnCore _ _ _ _ hInv
  · split
    · exact (runEnqueueOnCore _ _ _ _ hInv).andThen fun h => markReschedulePendingOnCore _ _ h
    · exact refl hInv

/-- The unbind clears the context's bound thread and the thread's binding in
place, re-buckets the thread, purges the replenishment and runs the key hooks. -/
theorem schedContextUnbind {vScId : SeLe4n.ValidObjId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) : RecordsFrame st st' := by
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
          refine chain ?_ (markKeyChangeFor _ _ _) hInv
          refine chain ?_ (markCandidacyGainFor _ _ _)
          refine chain ?_ (purgeReplenishment _ _)
          refine chain ?_ (schedContextUnbindQueueStage _ _ _ _ _)
          refine chain (chain (withScheduler _ _) fun h => rewriteObject _ h ?_) fun h =>
            updateTcb _ _ h fun _ => rfl
          refine Eq.trans ?_ (congrArg recordViewOf
            ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc)).symm
          rfl
      · cases hStep
        refine chain ?_ (purgeReplenishment _ _) hInv
        exact rewriteObject_schedContext hSc _ _
  · cases hStep

/-- The per-core context unbind: the unbind, then the preemption seam. -/
theorem schedContextUnbindOnCore {vScId : SeLe4n.ValidObjId} {ec : CoreId}
    {st st' : SystemState} {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    RecordsFrame st st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hU
    exact (schedContextUnbind hInv hU).andThen fun h' => priorityRescheduleOnCore h' h

/-! ### Affinity -/

theorem vacateForAffinityChange (st : SystemState) (t : SeLe4n.ThreadId) (o n : CoreId)
    (hInv : st.objects.invExt) : RecordsFrame st (vacateForAffinityChange st t o n) := by
  unfold _root_.SeLe4n.Kernel.vacateForAffinityChange
  split
  · exact withScheduler _ _ hInv
  · exact refl hInv

theorem migrateRunQueueOnAffinityChange (st : SystemState) (t : SeLe4n.ThreadId) (o n : CoreId)
    (hInv : st.objects.invExt) : RecordsFrame st (migrateRunQueueOnAffinityChange st t o n) := by
  unfold _root_.SeLe4n.Kernel.migrateRunQueueOnAffinityChange
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · split
      · exact ((runRemoveOnCore st o t hInv).andThen fun h => runEnqueueAdmitted _ n t _ h).andThen
          fun h => withScheduler _ _ h
      · exact refl hInv

theorem requeueVacatedOnNewHome (st : SystemState) (t : SeLe4n.ThreadId) (n : CoreId) (v : Bool)
    (hInv : st.objects.invExt) : RecordsFrame st (requeueVacatedOnNewHome st t n v) := by
  unfold _root_.SeLe4n.Kernel.requeueVacatedOnNewHome
  split
  · split
    · exact (runEnqueueOnCore st n t _ hInv).andThen fun h => withScheduler _ _ h
    · exact refl hInv
  · exact refl hInv

/-- The affinity op: the vacate, the affinity field written in place, the
replenishment move, the run-queue migration and the requeue. -/
theorem setThreadCpuAffinityWithMigration {st st' : SystemState} {t : SeLe4n.ThreadId}
    {affinity : Option CoreId} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.setThreadCpuAffinityWithMigration st t affinity ec = .ok (st', sgi?)) :
    RecordsFrame st st' := by
  obtain ⟨tcb, stSet, -, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have F0 := vacateForAffinityChange st t (determineTargetCore st t)
    (affinity.getD Concurrency.bootCoreId) hInv
  have F1 : RecordsFrame st stSet := by
    unfold setThreadCpuAffinity at hSet
    split at hSet
    · rename_i x hT _
      rw [Except.ok.injEq] at hSet; subst hSet
      refine F0.andThen fun h => rewriteObject_tcb hT _ ?_ _ h
      rfl
    · cases hSet
  refine chain (chain (fun _ => ?_) (migrateRunQueueOnAffinityChange _ _ _ _))
    (requeueVacatedOnNewHome _ _ _ _) hInv
  split
  · exact F1.andThen fun h => migrateSchedContextReplenishment _ _ _ _ h
  · exact F1

theorem setThreadCpuAffinityOnCore {st st' : SystemState} {vTarget : SeLe4n.ValidThreadId}
    {affinity : Option CoreId} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.setThreadCpuAffinityOnCore st vTarget affinity ec = .ok (st', sgi?)) :
    RecordsFrame st st' :=
  setThreadCpuAffinityWithMigration hInv h

/-- The SchedControl configure moves the bound thread through the affinity
change and then configures on the moved state. -/
theorem schedControlConfigure {core : CoreId} {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain
      st = .ok ((), st')) : RecordsFrame st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact schedContextConfigure hInv h
  · exact (setThreadCpuAffinityWithMigration hInv hM).andThen fun h' => schedContextConfigure h' h

/-! ### Priority inheritance -/

/-- The boost's write: one thread's boost rewritten in place. -/
theorem pipBoostWrite (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.pipBoostWrite st t) := by
  unfold PriorityInheritance.pipBoostWrite
  split
  · rename_i x h _
    dsimp only
    split
    · exact refl hInv
    · refine rewriteObject_tcb h _ ?_ _ hInv
      rfl
  · exact refl hInv

theorem updatePipBoostOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (PriorityInheritance.updatePipBoostOnCore st c t) :=
  have P := pipBoostWrite st t hInv
  P.trans (of_agreeOffRunLinks (PriorityInheritance.updatePipBoostOnCore_objectsAgreeOffRunLinks st c t)
    ((updatePipBoostOnCore_replyViews_eq st c t hInv).trans P.replyViews.symm)
    ((asid_of_onlyObjectsScheduler
      (PriorityInheritance.updatePipBoostOnCore_onlyObjectsSchedulerDiffer st c t)).trans P.asid.symm)
    (PriorityInheritance.updatePipBoostOnCore_preserves_objects_invExt st c t hInv)
    ((width_of_onlyObjectsScheduler
      (PriorityInheritance.updatePipBoostOnCore_onlyObjectsSchedulerDiffer st c t)).trans P.width.symm))

/-- The chain revert: one boost per link. -/
theorem revertPriorityInheritance (st : SystemState) (t : SeLe4n.ThreadId) (fuel : Nat)
    (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.revertPriorityInheritance st t fuel) := by
  induction fuel generalizing st t with
  | zero => exact refl hInv
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    have F := updatePipBoostOnCore st Concurrency.bootCoreId t hInv
    split
    · exact F.trans (ih _ _ F.invExt)
    · exact F

end RecordsFrame

end SeLe4n.Kernel
