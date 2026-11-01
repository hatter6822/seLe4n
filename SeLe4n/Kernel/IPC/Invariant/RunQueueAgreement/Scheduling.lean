/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Ipc
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.SchedContext.Invariant.Preservation

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

/-! The context switch's steps write no table that names objects by id. -/

@[simp] theorem saveOutgoingContextOnCore_referenceTables (st : SystemState)
    (c : Concurrency.CoreId) :
    (saveOutgoingContextOnCore st c).referenceTables = st.referenceTables := by
  unfold saveOutgoingContextOnCore; split
  · rfl
  · exact SystemState.updateTcb_referenceTables _ _ _

@[simp] theorem restoreIncomingContextOnCore_referenceTables (st : SystemState)
    (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCore st c tid).referenceTables = st.referenceTables := by
  unfold restoreIncomingContextOnCore; split <;> rfl

@[simp] theorem restoreIncomingContextOnCoreUnlessCurrent_referenceTables (st : SystemState)
    (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).referenceTables = st.referenceTables := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; split
  · rfl
  · exact restoreIncomingContextOnCore_referenceTables _ _ _

@[simp] theorem dispatchIdleOnCore_referenceTables (st : SystemState) (c : Concurrency.CoreId) :
    (dispatchIdleOnCore st c).referenceTables = st.referenceTables := by
  unfold dispatchIdleOnCore
  exact (restoreIncomingContextOnCore_referenceTables _ _ _).trans
    (SystemState.runRemoveOnCore_referenceTables _ _ _)

@[simp] theorem idleFallbackOnCore_referenceTables (st : SystemState) (c : Concurrency.CoreId) :
    (idleFallbackOnCore st c).referenceTables = st.referenceTables := by
  unfold idleFallbackOnCore; split
  · exact dispatchIdleOnCore_referenceTables _ _
  · rfl

@[simp] theorem preemptCurrentOnCore_referenceTables (st : SystemState) (c : Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c incoming).referenceTables = st.referenceTables := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · split
    · rfl
    · split
      · exact SystemState.runEnqueueOnCore_referenceTables _ _ _ _
      · rfl

macro_rules | `(tactic| table_frame) => `(tactic|
  (simp_all only [saveOutgoingContextOnCore_referenceTables,
    restoreIncomingContextOnCore_referenceTables,
    restoreIncomingContextOnCoreUnlessCurrent_referenceTables, dispatchIdleOnCore_referenceTables,
    idleFallbackOnCore_referenceTables, preemptCurrentOnCore_referenceTables,
    SystemState.runRemoveOnCore_referenceTables, SystemState.runEnqueueAdmitted_referenceTables,
    SystemState.runEnqueueOnCore_referenceTables, SystemState.updateTcb_referenceTables,
    SystemState.rewriteObject_referenceTables]; done))

/-- A thread the bind places is placed nowhere, so no core runs it. -/
theorem bindPlacesParkedThread_not_current {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {sc : SchedContext}
    (h : SchedContextOps.bindPlacesParkedThread st tid tcb sc = true) :
    ∀ c, st.scheduler.currentOnCore c ≠ some tid := by
  unfold SchedContextOps.bindPlacesParkedThread at h
  simp only [Bool.and_eq_true] at h
  exact fun c => ((placedCoreOf?_none_iff st tid).mp
    (Option.isNone_iff_eq_none.mp h.1.1.2) c).2

/-- A thread the bind places is runnable: the bind tests it. -/
theorem bindPlacesParkedThread_runnable {s st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {sc : SchedContext}
    (h : SchedContextOps.bindPlacesParkedThread s tid tcb sc = true)
    (hT : st.getTcb? tid = some tcb) : st.runnable tid := by
  unfold SchedContextOps.bindPlacesParkedThread at h
  simp only [Bool.and_eq_true] at h
  exact ⟨tcb, hT, TCB.runnable_of_isRunnable h.1.2⟩

/-- A re-bucket of a thread its core's links queue (the guard the re-bucketing
operations test, WS-ZA ZA4.5). -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.runRequeueOnCore_of_queuedOn
    (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority)
    (h : st.queuedOn c t = true) : RunQueueStage st (st.runRequeueOnCore c t p) :=
  SystemState.RunQueueStage.runRequeueOnCore _ _ _ _
    ((SystemState.queuedOn_eq_runLinkOn _ _ _).symm.trans h)

/-- The re-placement writes the contexts' release fields and the release
queues alone. -/
theorem releasePlace_runQueueFrameStage (st : SystemState) (c : Concurrency.CoreId)
    (s : SeLe4n.SchedContextId) :
    SystemState.RunQueueFrameStage (· = s) st (st.releasePlace c s) :=
  .of_releaseOnlyWrite (SystemState.releasePlace_releaseOnlyWrite st c s)
    (SystemState.releasePlace_agree st c s) (SystemState.releasePlace_objects_invExt st c s)
    (fun _ h => SystemState.releasePlace_refined h c s)
    (fun _ hS _ hq r => SystemState.releasePlace_refillsSoundExcept hq c s
      (fun hs => absurd (hS s rfl) hs) r)

/-- WS-ZA ZA6.4: **a write to context `s` closed by its placement**: a frame
stage off `s` up to `X`, in which `s` is free for core `c`, well formed, bound
while it has a place and bound wherever it is queued, is a stage up to `s`
placed on `c` — the bind's and the configure's shape. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueFrameStage.closePlace {st X : SystemState}
    {c : Concurrency.CoreId} {s : SeLe4n.SchedContextId}
    (hF : SystemState.RunQueueFrameStage (· = s) st X)
    (hX : ∀ S : SeLe4n.SchedContextId → Prop, ¬ S s → st.objects.invExt → st.runQueueRefined →
      st.releaseQueueRefined → st.refillsSoundExcept S → X.releaseQueueRefined →
      X.releaseFreeFor c s = true ∧
      (∀ a, X.getSchedContext? s = some a → schedContextWellFormed a) ∧
      (∀ sc, X.getSchedContext? s = some sc → sc.releaseKey? ≠ none →
        sc.boundThread.isSome = true) ∧
      (∀ c e, e ∈ (X.scheduler.replenishQueueOnCore c).entries → e.1 = s →
        ∃ a, X.getSchedContext? e.1 = some a ∧ a.boundThread.isSome = true)) :
    RunQueueStage st (X.releasePlace c s) :=
  have hT := hF.trans (releasePlace_runQueueFrameStage X c s)
  ⟨⟨hT.1.links, hT.1.tables, hT.1.release, fun S hI hR hQ hS => by
    by_cases hs : S s
    · exact hT.1.refills S (fun x hx => hx ▸ hs) hI hR hQ hS
    · have hXR := hF.1.release hI hR hQ
      obtain ⟨hFree, hWF, hB, hQB⟩ := hX S hs hI hR hQ hS hXR
      exact SystemState.releasePlace_close hXR c s hFree hWF hB hQB
        (hF.1.refills _ (fun x hx => Or.inr hx) hI hR hQ (hS.mono fun x hx => Or.inl hx)),
    hT.1.yield, hT.1.live⟩, hT.2⟩

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
    · rename_i hUnb
      split at h
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
                obtain ⟨-, -, -, -, -, -, -, -, -, hRel1, hRel2, hRel3⟩ :=
                  SchedContext.fields_of_refillsErased (sc.releaseReadyHead_refillsErased st.machine.timer)
                simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
                subst h
                -- The context written bound (a frame off it: its refills may be
                -- pending off every queue until the placement closes the write).
                have hIns : SystemState.RunQueueFrameStage (· = SchedContextId.ofObjId vScId.val) st
                    (st.rewriteObject vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vTid.val), donationOrigin := none })
                      (SystemState.rewriteAdmissible_schedContext hSc _)) :=
                  SystemState.RunQueueFrameStage.insert rfl rfl rfl
                    (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                    (SystemState.objStateMono_nonTcb
                      (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)
                    (hB := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                    (hY := by rw [show st.objects[vScId.val]? = _ from hScRaw]; simp [objYieldCodes])
                    (hR := fun _ => by
                      rw [show st.objects[vScId.val]? = _ from hScRaw]
                      simp only [SystemState.objReleaseLinkOn, SchedContext.releaseLinkOn, hRel1,
                        hRel2, hRel3])
                refine SystemState.RunQueueFrameStage.closePlace ?_ (fun S hs hI _ _ hS => ?_)
                · refine SystemState.RunQueueFrameStage.trans ?_
                    (SystemState.RunQueueStage.toFrame (markKeyChangeFor_runQueueStage _ _ _) _)
                  split
                  · rename_i hMem
                    refine SystemState.RunQueueFrameStage.trans ?_ (SystemState.RunQueueStage.toFrame
                      (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hMem) _)
                    exact hIns.trans (by exact (SystemState.RunQueueStage.toFrame
                      (RunQueueStage.updateTcb _ _ (by intro _ _; rfl)) _))
                  · split
                    · rename_i hPlace
                      refine SystemState.RunQueueFrameStage.trans ?_ (SystemState.RunQueueStage.toFrame
                        (SystemState.RunQueueStage.markReschedulePendingOnCore _ _) _)
                      exact SystemState.RunQueueFrameStage.then_enqueue (hIns.trans
                        (by exact (SystemState.RunQueueStage.toFrame (RunQueueStage.updateTcb _ _ (by intro _ _; rfl)) _)))
                        (bindPlacesParkedThread_not_current hPlace) (bindPlacesParkedThread_runnable hPlace hTcb)
                        (homedOn_determineTargetCore _ _)
                    · exact hIns.trans (by exact (SystemState.RunQueueStage.toFrame
                        (RunQueueStage.updateTcb _ _ (by intro _ _; rfl)) _))
                · -- The placement's facts: the context was unbound, so no entry
                  -- named it, and it is written well formed and bound.
                  have hN : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries →
                      e.1 ≠ ⟨vScId.val.toNat⟩ := by
                    intro c e he hes
                    obtain ⟨a, ha, hb⟩ := hS.2.2 c e (by rw [hes]; exact hs) he
                    rw [hes] at ha
                    have : a = sc := Option.some.inj (ha.symm.trans hSc)
                    subst this
                    exact hUnb hb
                  have hYs : (st.rewriteObject vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vTid.val), donationOrigin := none }) (SystemState.rewriteAdmissible_schedContext hSc _)).getSchedContext? ⟨vScId.val.toNat⟩ = some { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vTid.val), donationOrigin := none } :=
                    SystemState.rewriteObject_schedContext_getSchedContext?_self st
                      (SchedContextId.ofObjId vScId.val) _ (SystemState.rewriteAdmissible_schedContext hSc _) hI
                  have hWF : schedContextWellFormed { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vTid.val), donationOrigin := none } :=
                    releaseReadyHead_preserves_schedContextWellFormed sc _ (hS.1 _ sc hs hSc)
                  split
                  · intro hXR
                    exact SystemState.closePlace_facts hYs hN hWF rfl
                      ((markKeyChangeFor_refillsKeptOff _ _ _ _).trans
                        ((SystemState.RefillsKeptOff.runRequeueOnCore _ _ _ _ _).trans (SystemState.RefillsKeptOff.updateTcb _ _ _ _ (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hI)))) hXR _
                  · split
                    · intro hXR
                      exact SystemState.closePlace_facts hYs hN hWF rfl
                        ((markKeyChangeFor_refillsKeptOff _ _ _ _).trans
                          ((SystemState.RefillsKeptOff.markReschedulePendingOnCore _ _ _).trans
                            ((SystemState.RefillsKeptOff.runEnqueueOnCore _ _ _ _ _).trans (SystemState.RefillsKeptOff.updateTcb _ _ _ _ (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hI))))) hXR _
                    · intro hXR
                      exact SystemState.closePlace_facts hYs hN hWF rfl
                        ((markKeyChangeFor_refillsKeptOff _ _ _ _).trans (SystemState.RefillsKeptOff.updateTcb _ _ _ _ (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hI))) hXR _
              all_goals cases h
        · cases h
  · cases h

/-- A TCB rewritten through the witnessed lookup, keeping its run-queue fields. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_tcb {st : SystemState}
    {tid : SeLe4n.ThreadId} {t t' : TCB} (h : st.getTcb? tid = some t)
    (hL : ∀ c, t'.runLinkOn c = t.runLinkOn c) (hA : st.rewriteAdmissible tid.toObjId (.tcb t'))
    (hm : TCB.StepMono t t' := by exact ⟨id, id, by first | rfl | simp_all⟩)
    (hW : t'.taintWords = t.taintWords := by taint_words_kept)
    (hY : t'.yieldToCode = t.yieldToCode := by first | rfl | simp_all) :
    RunQueueStage st (st.rewriteObject tid.toObjId (.tcb t') hA) :=
  RunQueueStage.insert (st' := st.rewriteObject tid.toObjId (.tcb t') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact hL c)
    (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact SystemState.objStateMono_tcb hm)
    (hY := by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; simp only [objYieldCodes, hY])
    (hB := by
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]
      simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW])

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

/-- WS-ZA ZA6.4: the configure's resume tail: a removal of a queued thread the
context can no longer run, the guarded placement of a parked one (the bind's
guard), a reschedule flag, or nothing. -/
theorem configureResumeBound_runQueueStage (st : SystemState) (t : SeLe4n.ThreadId)
    (sc : SchedContext) : RunQueueStage st (SchedContextOps.configureResumeBound st t sc) := by
  unfold SchedContextOps.configureResumeBound
  dsimp only
  split
  · split
    · exact RunQueueStage.refl _
    · exact RunQueueStage.runRemoveOnCore _ _ _
  · split
    · rename_i tcb hTcb
      split
      · rename_i hPlace
        refine RunQueueStage.trans ?_ (SystemState.RunQueueStage.markReschedulePendingOnCore _ _)
        exact RunQueueStage.then_enqueue (RunQueueStage.refl _)
          (bindPlacesParkedThread_not_current hPlace) (bindPlacesParkedThread_runnable hPlace hTcb)
          (homedOn_determineTargetCore _ _)
      · split
        · exact SystemState.RunQueueStage.markReschedulePendingOnCore _ _
        · exact RunQueueStage.refl _
    · exact RunQueueStage.refl _

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
    · rename_i hValid
      rw [hSc] at h
      dsimp only at h
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i stStored hStore
          obtain ⟨scP, hScP, hScPw⟩ := (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
            (SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩)).get_sc
            (show st.objects[vScId.val]? = _ from hScRaw)
          have hScPy : scP.yieldFromCode = sc.yieldFromCode := by
            have e := congrArg SchedContext.yieldFromCode hScPw
            exact e
          -- The purge, then the store: a frame off the context, closed below by
          -- its placement (bound) or by its being unbound and on no queue.
          have hW : SystemState.RunQueueFrameStage (· = ⟨vScId.val.toNat⟩) st stStored :=
            (SchedContextOps.purgeReplenishment_runQueueFrameStage st ⟨vScId.val.toNat⟩).trans
              (SystemState.RunQueueFrameStage.storeObject hStore (fun c => by rw [hScP]; rfl)
                (by rw [hScP]; exact SystemState.objStateMono_nonTcb rfl rfl)
                (hB := by rw [hScP]; rfl)
                (hY := by rw [hScP]; simp [objYieldCodes, hScPy]) (hR := fun c => by
                  change _ = SystemState.objReleaseLinkOn (SchedContextOps.purgeReplenishment st
                    ⟨vScId.val.toNat⟩).objects[vScId.val]? c
                  have hN := (SystemState.releaseQueuedAnywhere_eq_false_iff _ _).mp
                    (SystemState.releaseRemoveAnywhere_not_queued st ⟨vScId.val.toNat⟩) c
                  rw [SystemState.releaseLinkOn_eq_obj] at hN
                  change SystemState.objReleaseLinkOn (SchedContextOps.purgeReplenishment st
                    ⟨vScId.val.toNat⟩).objects[vScId.val]? c = none at hN
                  rw [hScP] at hN
                  rw [hScP, hN]; simp [SystemState.objReleaseLinkOn, SchedContext.releaseLinkOn,
                    SchedContextOps.configuredSchedContext_releaseCoreCode]))
          -- What the store leaves: the configured context, on no queue.
          have hN : ∀ hI : st.objects.invExt, st.releaseQueueRefined → ∀ c e,
              e ∈ (stStored.scheduler.replenishQueueOnCore c).entries →
              e.1 ≠ ⟨vScId.val.toNat⟩ := fun hI hR c e he => by
            rw [storeObject_scheduler_eq _ _ _ _ hStore] at he
            exact SystemState.not_mem_entries_of_not_queued
              (SchedContextOps.purgeReplenishment_refined hR _)
              (SystemState.releaseRemoveAnywhere_not_queued st ⟨vScId.val.toNat⟩) c e he
          have hYs : ∀ hI : st.objects.invExt, stStored.getSchedContext? ⟨vScId.val.toNat⟩ =
              some (SchedContextOps.configuredSchedContext budget period priority deadline domain
                st.machine.timer (SchedContextOps.configureKeepsHead st sc budget period) sc) := fun hI =>
            (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
              (storeObject_objects_eq _ _ _ _ (SchedContextOps.purgeReplenishment_objects_invExt st _ hI) hStore)
          have hWF : ∀ S : SeLe4n.SchedContextId → Prop, ¬ S ⟨vScId.val.toNat⟩ →
              st.refillsSoundExcept S → schedContextWellFormed
                (SchedContextOps.configuredSchedContext budget period priority deadline domain
                  st.machine.timer (SchedContextOps.configureKeepsHead st sc budget period) sc) :=
            fun S hs hS => SchedContextOps.configuredSchedContext_schedContextWellFormed _ _ _ _ _ _ _
              hValid sc (schedContextWellFormed_refillsPositive (hS.1 _ sc hs hSc))
          split at h
          · rename_i hUnb
            rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            exact hW.withRefills fun S hs hI hRq hRel _ _ h0 h4 =>
              SystemState.refillsSoundExcept_close_unbound h4
                (fun a ha => by rw [hYs hI] at ha; cases ha; rfl)
                (by rw [SchedContextOps.configuredSchedContext_boundThread, hUnb]; rfl)
                (hWF S hs h0) (hN hI hRel)
          · rename_i boundTid hBnd
            have hP : RunQueueStage st (stStored.releasePlace (determineTargetCore st boundTid)
                ⟨vScId.val.toNat⟩) :=
              SystemState.RunQueueFrameStage.closePlace hW fun S hs hI _ hRel hS hXR =>
                SystemState.closePlace_facts (hYs hI) (hN hI hRel) (hWF S hs hS)
                  (by rw [SchedContextOps.configuredSchedContext_boundThread, hBnd]; rfl)
                  (.refl _ _) hXR _
            split at h
            · rename_i boundTcb hBound _
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact hP.trans
                (((((schedContextConfigureBoundPropagate_runQueueStage _ _ _ _ hBound _ _).trans
                  (markCandidacyGainFor_runQueueStage _ _ _)).trans
                  (markKeyChangeFor_runQueueStage _ _ _)).trans
                  (PriorityInheritance.repropagateFromWaiter_runQueueStage _ _ _ _)).trans
                  (configureResumeBound_runQueueStage _ _ _))
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]; exact hP
      · exact absurd h (by simp)

/-- The preemption saves the outgoing thread's registers (a TCB rewrite keeping
its run-queue fields) and puts it back through the guarded enqueue.  It keeps
the link agreement; it is not a stage of its own, because it queues a thread
that stays current until the dispatch that follows it. -/
theorem preemptCurrentOnCore_runQueueLinkStage (st : SystemState) (c : Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) :
    SystemState.RunQueueLinkStage st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact SystemState.RunQueueLinkStage.refl _
  · split
    · exact SystemState.RunQueueLinkStage.refl _
    · split
      · rename_i prevTcb h _
        exact (SystemState.RunQueueLinkStage.of_stage
          (RunQueueStage.rewriteObject_tcb h (fun _ => by rfl) _)).trans
          (SystemState.RunQueueLinkStage.runEnqueueOnCore _ _ _ _)
      · exact SystemState.RunQueueLinkStage.refl _

/-- A thread the preemption leaves queued was queued before, or is the core's
outgoing thread (never the incoming one, never an idle thread), now queued on
that core. -/
theorem preemptCurrentOnCore_queuedOn_imp {st : SystemState} {c : Concurrency.CoreId}
    {incoming : SeLe4n.ThreadId} (hInv : st.objects.invExt) {c' : Concurrency.CoreId}
    {x : SeLe4n.ThreadId} (h : (preemptCurrentOnCore st c incoming).queuedOn c' x = true) :
    st.queuedOn c' x = true ∨ (st.scheduler.currentOnCore c = some x ∧ c' = c ∧
      x ≠ incoming ∧ Kernel.isIdleThreadId x = false) := by
  unfold preemptCurrentOnCore at h
  split at h
  · exact .inl h
  · rename_i prev hCur
    split at h
    · exact .inl h
    · rename_i hNe
      split at h
      · rename_i prevTcb hT _
        rw [SystemState.runEnqueueOnCore_queuedOn] at h
        split at h
        · rename_i hx
          obtain ⟨rfl, hA⟩ := hx
          unfold SystemState.runEnqueueAdmits at hA
          exact .inr ⟨hCur, of_decide_eq_true h, fun e => hNe (by rw [e]; exact beq_self_eq_true _),
            by simpa using ((Bool.and_eq_true _ _).mp hA).1⟩
        · left
          rw [SystemState.queuedOn_eq_runLinkOn,
            SystemState.runLinkOn_rewriteObject_tcb
              (t' := { prevTcb with registerContext := st.machine.regsOnCore c }) _ hInv hT
              (fun _ => rfl)] at h
          rwa [SystemState.queuedOn_eq_runLinkOn]
      · exact .inl h

/-- The preemption's register save keeps the outgoing thread's state fields and
its requeue writes run-queue links alone. -/
theorem preemptCurrentOnCore_stateMono (st : SystemState) (c : Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.StateMono st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact SystemState.StateMono.refl _
  · split
    · exact SystemState.StateMono.refl _
    · split
      · rename_i prevTcb h _
        exact (SystemState.StateMono.insert hInv rfl (by
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]
          exact SystemState.objStateMono_tcb ⟨id, id, rfl⟩)).trans
          (SystemState.StateMono.of_agreeOffRunLinks
            (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
      · exact SystemState.StateMono.refl _

/-- **The preemption opens core `c`'s preemption point**: it puts `c`'s outgoing
thread back on `c`'s queue while that thread stays current. -/
theorem preemptCurrentOnCore_runQueueWindowStage (st : SystemState) (c : Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) :
    SystemState.RunQueueWindowStage (.preempt c) st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact SystemState.RunQueueWindowStage.refl _ _
  · rename_i prev hCur
    split
    · exact SystemState.RunQueueWindowStage.refl _ _
    · split
      · rename_i prevTcb h _
        exact ((RunQueueStage.rewriteObject_tcb h (fun _ => by rfl) _).window _).trans
          (SystemState.RunQueueWindowStage.requeueCurrent _ c prev _ hCur)
      · exact SystemState.RunQueueWindowStage.refl _ _

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
and sets the current slot: a switch on core `c`.  The incoming thread is one
core `c`'s links queue, `c`'s own current thread (the self-switch) or `c`'s idle
thread; each ends queued nowhere and current on `c` alone, and the outgoing
thread it queues is runnable, `c`'s point being no block. -/
theorem switchToThreadOnCore_runQueueSwitchStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} (h : switchToThreadOnCore st c tid = .ok st')
    (hSel : st.runQueueRefined → st.queuedOn c tid = true ∨
      st.scheduler.currentOnCore c = some tid ∨ tid = Kernel.idleThreadId c) :
    SystemState.RunQueueSwitchStage c st st' := by
  unfold switchToThreadOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h
      have hR := restoreIncomingContextOnCoreUnlessCurrent_objects_scheduler
        ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid) c tid
      have hO : st'.objects = ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).objects := by
        rw [← h]; exact hR.1
      have hS : st'.scheduler = ((preemptCurrentOnCore st c tid).runRemoveOnCore c
          tid).scheduler.setCurrentOnCore c (some tid) := by
        rw [← h]; exact congrArg (·.setCurrentOnCore c (some tid)) hR.2
      have hM : st.objects.invExt → SystemState.StateMono st st' := fun hInv =>
        ((preemptCurrentOnCore_stateMono st c tid hInv).trans
          (SystemState.StateMono.of_agreeOffRunLinks
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c tid))).trans
          (SystemState.StateMono.of_objects hO)
      refine ⟨((preemptCurrentOnCore_runQueueLinkStage st c tid).trans
        (SystemState.RunQueueLinkStage.of_stage
          (RunQueueStage.runRemoveOnCore (preemptCurrentOnCore st c tid) c tid))).trans
        (SystemState.RunQueueLinkStage.of_frame hO (by rw [hS]; rfl) (by rw [hS]; rfl)
          (by
            rw [← h]
            show (restoreIncomingContextOnCoreUnlessCurrent
              ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid) c tid).referenceTables = _
            simp) (by rw [hS]; rfl)
          (by rw [← h]; exact restoreIncomingContextOnCoreUnlessCurrent_residentCode _ _ _)), ?_,
        fun hInv _ => hM hInv⟩
      intro e e' he hb hInv hRf _ hD
      have hRunCur : ∀ x, st.scheduler.currentOnCore c = some x → st.runnable x := fun x hx =>
        (hD.current c x hx).2.2.resolve_left hb
      have hQ' : ∀ c' x, st'.queuedOn c' x =
          if x = tid ∧ c' = c then false else (preemptCurrentOnCore st c tid).queuedOn c' x :=
        fun c' x => by
          rw [SystemState.queuedOn_eq_runLinkOn, SystemState.runLinkOn_of_objects hO,
            ← SystemState.queuedOn_eq_runLinkOn, SystemState.runRemoveOnCore_queuedOn]
      have hNotElse : ∀ c', c' ≠ c → st.scheduler.currentOnCore c' ≠ some tid := by
        intro c' hne hc'
        rcases hSel hRf with hq | hc | hI
        · exact hne ((hD.current c' tid hc').1 c hq).2.symm
        · exact hne ((hD.current c tid hc).2.1 c' hc')
        · subst hI; exact hne (hD.idleHome c c' hc')
      refine SystemState.currentDequeuedUniqueExcept_of_dispatch (c := c) (new := some tid) hD he
        (fun c' => ?_) (fun t ht => ?_) (fun c0 h0 => ?_) (fun c' x hq => ?_) (hM hInv)
      · rw [hS]
        by_cases hc : c' = c
        · subst hc; simp
        · rw [if_neg hc, SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)]
          unfold SchedulerState.currentOnCore
          rw [SystemState.runRemoveOnCore_current]
          exact preemptCurrentOnCore_currentOnCore st c tid c'
      · cases ht
        have hRun0 : st.runnable tid := by
          rcases hSel hRf with hq | hc | hI
          · exact hD.queuedRunnable c tid hq
          · exact hRunCur tid hc
          · subst hI; exact hD.idleRunnable c
        refine ⟨fun c' => ?_, hNotElse, (hM hInv).runnable hRun0, (hM hInv).homedOn hRun0.activeAt ?_⟩
        rotate_left
        · rcases hSel hRf with hq | hc | hI
          · exact hD.queuedHome c tid hq
          · exact hD.currentHome c tid hc
          · subst hI; exact hD.idleHomed c
        · rw [hQ']
          by_cases hc : c' = c
          · simp [hc]
          · rw [if_neg (fun e => hc e.2)]
            cases hq : (preemptCurrentOnCore st c tid).queuedOn c' tid
            · rfl
            · rcases preemptCurrentOnCore_queuedOn_imp hInv hq with hq0 | ⟨_, _, hne, _⟩
              · rcases hSel hRf with hq1 | hc1 | hI
                · exact absurd (SystemState.queuedOn_core_unique hq0 hq1) hc
                · exact absurd ((hD.current c tid hc1).1 c' hq0).2 hc
                · subst hI
                  rw [hD.idleOff _ (Kernel.isIdleThreadId_idleThreadId c) c'] at hq0; cases hq0
              · exact absurd rfl hne
      · cases h0
        rcases hSel hRf with hq | hc | hI
        · rw [hD.idleOff _ (Kernel.isIdleThreadId_idleThreadId c0) c] at hq; cases hq
        · exact (hD.idleHome c0 c hc).symm
        · exact Kernel.idleThreadId_injective hI
      · rw [hQ'] at hq
        split at hq
        · cases hq
        · rcases preemptCurrentOnCore_queuedOn_imp hInv hq with hq0 | ⟨hc0, hcc, _, hI⟩
          · exact .inl hq0
          · exact .inr ⟨hc0, hI, (hM hInv).runnable (hRunCur _ hc0), hcc⟩
    · cases h
  · cases h

/-- The drop of an out-of-domain incumbent: a preemption and a current-slot
write that empties `c`'s slot, so the thread it queues runs nowhere — a switch
on `c` with nothing incoming. -/
theorem dropCurrentOnCore_runQueueSwitchStage (st : SystemState) (c : Concurrency.CoreId) :
    SystemState.RunQueueSwitchStage c st (dropCurrentOnCore st c) := by
  have hM : st.objects.invExt → SystemState.StateMono st (dropCurrentOnCore st c) := fun hInv =>
    (preemptCurrentOnCore_stateMono st c _ hInv).trans (SystemState.StateMono.of_objects rfl)
  refine ⟨(preemptCurrentOnCore_runQueueLinkStage st c _).trans
    (SystemState.RunQueueLinkStage.of_frame rfl rfl rfl), ?_, fun hInv _ => hM hInv⟩
  intro e e' he hb hInv _ _ hD
  refine SystemState.currentDequeuedUniqueExcept_of_dispatch (c := c) (new := none) hD he
    (fun c' => ?_) (fun t ht => by cases ht) (fun _ h0 => by cases h0) (fun c' x hq => ?_)
    (hM hInv)
  · show (SchedulerState.setCurrentOnCore _ c none).currentOnCore c' = _
    by_cases hc : c' = c
    · subst hc; simp
    · rw [if_neg hc, SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)]
      exact preemptCurrentOnCore_currentOnCore st c _ c'
  · rcases preemptCurrentOnCore_queuedOn_imp hInv hq with hq0 | ⟨hc0, hcc, _, hI⟩
    · exact .inl hq0
    · exact .inr ⟨hc0, hI, (hM hInv).runnable ((hD.current c x hc0).2.2.resolve_left hb), hcc⟩

/-- The reschedule handler: a switch, a drop or nothing, then the flag clear — a
kernel entry's scheduling point. -/
theorem handleRescheduleSgiOnCore_runQueueEntryStage {st st' : SystemState}
    {c : Concurrency.CoreId} (h : handleRescheduleSgiOnCore st c = .ok st') :
    SystemState.RunQueueEntryStage st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact ((dropCurrentOnCore_runQueueSwitchStage st c).trans_stage
        (RunQueueStage.clearReschedulePendingOnCore _ _)).entry
    · rw [Except.ok.injEq] at h; subst h
      exact (RunQueueStage.clearReschedulePendingOnCore _ _).entry
  · rename_i tid hChoose
    split at h
    · split at h
      · rename_i hSw
        rw [Except.ok.injEq] at h; subst h
        exact ((switchToThreadOnCore_runQueueSwitchStage hSw (fun hRf => .inl
          (SystemState.queuedOn_of_mem_runQueueOnCore hRf
            ((RunQueue.mem_toList_iff_mem _ _).mp
              (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c tid (hRf c)
                hChoose))))).trans_stage
          (RunQueueStage.clearReschedulePendingOnCore _ _)).entry
      · split at h
        · rw [Except.ok.injEq] at h; subst h
          exact ((dropCurrentOnCore_runQueueSwitchStage st c).trans_stage
            (RunQueueStage.clearReschedulePendingOnCore _ _)).entry
        · rw [Except.ok.injEq] at h; subst h
          exact (RunQueueStage.clearReschedulePendingOnCore _ _).entry
    · rw [Except.ok.injEq] at h; subst h
      exact (RunQueueStage.clearReschedulePendingOnCore _ _).entry

/-- The suspend's scheduling point: a reschedule on the executing core or nothing. -/
theorem suspendRescheduleOnCore_runQueueEntryStage {st st' : SystemState}
    {runningCore executingCore : Concurrency.CoreId} {wasCurrent localDeboosted : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : suspendRescheduleOnCore st runningCore executingCore wasCurrent localDeboosted =
      .ok (st', sgi?)) : SystemState.RunQueueEntryStage st st' := by
  unfold suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore_runQueueEntryStage hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact (RunQueueStage.refl _).entry)

/-- A valid thread id is not the reserved sentinel. -/
theorem ValidThreadId.isReserved_false (v : SeLe4n.ValidThreadId) : v.val.isReserved = false := by
  rcases v with ⟨⟨n⟩, hv⟩
  simp only [SeLe4n.ThreadId.isReserved, decide_eq_false_iff_not]
  intro h; subst h; exact hv rfl

/-- The thread suspend: the reclaimed teardown, the chain revert and the
donation arm — stages that leave the victim runnable and placed where the
pre-state placed it — then the removal from that placement, two writes to the
victim no core runs and no queue holds, and the scheduling point.  The victim
is no idle thread: the arm's validator refuses one. -/
theorem suspendThreadOnCore_runQueueEntryStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (hNI : isIdleThreadId vtid.val = false)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' := by
  simp only [suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    have hS1 := cancelIpcBlockingReclaimed_runQueueStage st vtid.val tcb
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have hS12 : RunQueueStage (cancelIpcBlockingReclaimed vtid.val tcb st)
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact RunQueueStage.refl _
        | some serverId => exact PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _
      have hP12 : (cancelIpcBlockingReclaimed vtid.val tcb st).objects.invExt →
          placedCoreOf? (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) vtid.val
            = placedCoreOf? (cancelIpcBlockingReclaimed vtid.val tcb st) vtid.val := by
        intro hInv1
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => rfl
        | some serverId =>
          exact placedCoreOf?_congr_of_bits _ fun c =>
            ⟨PriorityInheritance.propagatePipChainCrossCore_queuedOn _ _ _ _ _ _ hInv1,
              by rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]⟩
      revert hStep
      split
      · intro hStep; exact absurd hStep (by simp)
      · next s3 hDon =>
        intro hStep
        have hS23 := cancelSuspendDonation_runQueueStage _ s3 vtid.val _ hDon
        have hS3 := (hS1.trans hS12).trans hS23
        refine SystemState.RunQueueEntryStage.trans ?_
          (suspendRescheduleOnCore_runQueueEntryStage hStep)
        refine SystemState.RunQueueEntryStage.trans ?_
          (SystemState.cancelYieldTo_runQueueStage _ vtid.val).entry
        refine SystemState.RunQueueEntryStage.of_inv ?_ fun hInv hR _ => ?_
        · unfold clearPendingStateValid clearPendingState
          exact (hS3.1.trans (descheduleAt_runQueueStage s3 vtid.val _).1).trans
            ((SystemState.RunQueueLinkStage.updateTcb _ vtid.val
              (f := fun tcb => { tcb with
                pendingMessage := none
                timeoutBudget := none
                queuePrevCode := 0
                queueNextCode := 0
                queuePPrevCode := 0 })
              (fun _ _ => rfl)).trans
              (SystemState.RunQueueLinkStage.updateTcb _ vtid.val
                (f := fun t => { t with threadState := .Inactive }) (fun _ _ => rfl)))
        obtain ⟨hInv1, hR1⟩ := hS1.1 hInv hR
        obtain ⟨hInv2, hR2⟩ := hS12.1 hInv1 hR1
        have hP : placedCoreOf? st vtid.val = placedCoreOf? s3 vtid.val := by
          rw [cancelSuspendDonation_placedCoreOf? _ s3 _ _ vtid.val hInv2 hDon, hP12 hInv1,
            cancelIpcBlockingReclaimed_placedCoreOf?_victim _ _ _ hInv]
        have hRun3 : s3.runnable vtid.val :=
          ((hS12.trans hS23).mono hInv1 hR1).runnable
            (cancelIpcBlockingReclaimed_victim_runnable st _ tcb hInv
              (ValidThreadId.isReserved_false vtid) hT
              (fun h => hA (by rw [h]; first | rfl | decide | simp)))
        rw [hP]
        refine hS3.entry.trans ?_
        unfold clearPendingStateValid clearPendingState
        exact descheduleAtPlacedThenOffWrites_runQueueEntryStage s3 vtid.val
          (fun _ x hx => by
            obtain ⟨y, hy, hr⟩ := hRun3
            rw [hx] at hy; cases hy; exact hr.1)
          hNI (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)

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
and the local scheduling point.  The resumed thread was suspended, so between
scheduling points no core runs it; the ready mark makes it active. -/
theorem resumeThreadOnCore_runQueueEntryStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' := by
  unfold resumeThreadOnCore at h
  dsimp only at h
  split at h
  · rename_i tcb hT
    split at h
    · cases h
    · rename_i hIn
      have hS2 := (resumeReadyMidState_runQueueStage st vtid.val).trans
        (markKeyChangeFrom_runQueueStage st (resumeReadyMidState st vtid.val) vtid.val)
      have hS : SystemState.RunQueueEntryStage st (enqueueRunnableOnCore
          (markKeyChangeFrom st (resumeReadyMidState st vtid.val) vtid.val)
          (determineTargetCore st vtid.val) vtid.val) := by
        refine SystemState.RunQueueEntryStage.of_inv
          (hS2.1.trans (enqueueRunnableOnCore_runQueueLinkStage _ _ _)) fun hInv _ d => ?_
        have hIn' : tcb.threadState = .Inactive := by simpa using hIn
        refine (hS2.trans (enqueueRunnableOnCore_runQueueStage _ _ _ (fun c hc => ?_) ?_
          (fun x hx => ?_))).entry
        rotate_left 2
        · obtain ⟨tm, htm, ha⟩ :=
            PriorityInheritance.resumeReadyMidState_getTcb?_affinity st _ tcb hT hInv
          have hx' : (resumeReadyMidState st vtid.val).getTcb? vtid.val = some x := by
            unfold SystemState.getTcb? at hx ⊢; rw [markKeyChangeFrom_objects] at hx; exact hx
          rw [htm] at hx'; cases hx'
          rw [ha]; exact homedOn_determineTargetCore st _ tcb hT
        · rw [markKeyChangeFrom_currentOnCore] at hc
          have hc' : st.scheduler.currentOnCore c = some vtid.val := by
            unfold SchedulerState.currentOnCore at hc ⊢
            rw [PriorityInheritance.resumeReadyMidState_scheduler_eq] at hc; exact hc
          obtain ⟨x, hx, ha⟩ := d.currentActive c _ hc'
          rw [hT] at hx; cases hx
          exact ha hIn'
        · obtain ⟨tm, htm, hr⟩ := PriorityInheritance.resumeReadyMidState_getTcb?_ready st _ tcb hT hInv
          refine ⟨tm, ?_, by unfold TCB.Active; rw [hr]; decide⟩
          unfold SystemState.getTcb? at htm ⊢
          rw [markKeyChangeFrom_objects]; exact htm
      split at h
      · split at h
        · rename_i hH
          rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
          exact hS.trans (handleRescheduleSgiOnCore_runQueueEntryStage hH)
        · cases h
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
  · cases h

/-- The priority ops' preemption seam: the reschedule on the executing core or nothing. -/
theorem priorityRescheduleOnCore_runQueueEntryStage {st st' : SystemState}
    {running? : Option Concurrency.CoreId} {ec : Concurrency.CoreId} {sp : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : SystemState.RunQueueEntryStage st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · exact (RunQueueStage.of_eq hEq).entry
  · exact handleRescheduleSgiOnCore_runQueueEntryStage hH

/-- The priority ops' shared effect: the source write, the re-bucket, the key
hook, the chain re-walk and the preemption seam. -/
theorem applyPriorityChangeOnCore_runQueueEntryStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {p : SeLe4n.Priority} {ec : Concurrency.CoreId} {b : Bool}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p ec b =
      .ok (st', sgi?)) : SystemState.RunQueueEntryStage st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  exact ((((SchedContext.PriorityManagement.updatePrioritySource_runQueueStage st tid tcb p).trans
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_runQueueStage _ tid p
      (determineTargetCore st tid))).trans
    ((markKeyChangeFor_runQueueStage _ tid (effectiveSchedParams st tcb)).trans
      (PriorityInheritance.repropagateFromWaiter_runQueueStage _ tid ec
        st.objectIndex.length))).entry).trans
    (priorityRescheduleOnCore_runQueueEntryStage h)

theorem setPriorityOnCore_runQueueEntryStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : SystemState.RunQueueEntryStage st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore_runQueueEntryStage h
      · cases h
  · cases h

theorem setMCPriorityOnCore_runQueueEntryStage {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : SystemState.RunQueueEntryStage st st' := by
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
        · exact hS.entry.trans (applyPriorityChangeOnCore_runQueueEntryStage h)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS.entry
      · cases h
  · cases h

/-- A thread core `c`'s queue holds has links that admit `c`: they name it. -/
theorem _root_.SeLe4n.Model.SystemState.runLinksAdmit_of_contains {st : SystemState}
    {c : Concurrency.CoreId} {t : SeLe4n.ThreadId} (hR : st.runQueueRefined)
    (h : (st.scheduler.runQueueOnCore c).contains t = true) : st.runLinksAdmit c t = true := by
  rw [← (hR c).contains] at h
  unfold SystemState.runLinkOn at h
  unfold SystemState.runLinksAdmit
  cases hT : st.getTcb? t with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    dsimp only at h
    unfold TCB.runLinkOn at h
    by_cases hc : tcb.runCoreCode = c.val + 1
    · simp [hc]
    · rw [if_neg hc] at h; cases h

/-- The link half of a TCB rewritten through the witnessed lookup keeping its
run-queue fields, whatever it writes to its state fields and affinity. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueLinkStage.rewriteObject_tcb {st : SystemState}
    {tid : SeLe4n.ThreadId} {t t' : TCB} (h : st.getTcb? tid = some t)
    (hL : ∀ c, t'.runLinkOn c = t.runLinkOn c) (hA : st.rewriteAdmissible tid.toObjId (.tcb t'))
    (hW : t'.taintWords = t.taintWords := by taint_words_kept)
    (hY : t'.yieldToCode = t.yieldToCode := by first | rfl | simp_all) :
    SystemState.RunQueueLinkStage st (st.rewriteObject tid.toObjId (.tcb t') hA) :=
  SystemState.RunQueueLinkStage.insert (st' := st.rewriteObject tid.toObjId (.tcb t') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact hL c)
    (hY := by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; simp only [objYieldCodes, hY])
    (hB := by
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]
      simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW])

/-- The affinity migration moves a thread from the queue that holds it to its
new home core's: after the removal it is on no queue, so the enqueue is admitted
and the run queues stay in agreement with the threads.  Its placement half is
the affinity change's (`setThreadCpuAffinityOnCore_runQueueEntryStage`), which
reads where it leaves the thread (`migrateRunQueueOnAffinityChange_queuedOn`). -/
theorem migrateRunQueueOnAffinityChange_runQueueLinkStage (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : Concurrency.CoreId) :
    SystemState.RunQueueLinkStage st (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact .refl _
  · split
    · exact .refl _
    · rename_i tcb hTcb
      split
      · rename_i hC
        refine SystemState.RunQueueLinkStage.trans
          (st' := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority)
          ?_ (RunQueueStage.of_frame
            (st := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority)
            (st' := { (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                tcb.boostedPriority with
              scheduler := ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                tcb.boostedPriority).scheduler.markReschedulePendingOnCore toCore })
            rfl rfl rfl).1
        refine .of_tableFrame (fun hInv hR => ?_) (fun _ => .of_agreeOffRunLinks
          ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _)))
          (fun _ => .of_agreeOffRunLinks
          ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _))
            (by rw [SystemState.runEnqueueAdmitted_scheduler, SystemState.runRemoveOnCore_scheduler]; rfl))
          (fun _ => RefillViewsKept.of_agreeOffRunLinks
            ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
              (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _)))
          (fun _ => YieldLinksKept.of_agreeOffRunLinks
            ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
              (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _)))
        have hS := (RunQueueStage.runRemoveOnCore st fromCore tid).1 hInv hR
        refine ⟨SystemState.runEnqueueAdmitted_objects_invExt _ _ _ _ hS.1,
          SystemState.runEnqueueAdmitted_refined hS.2 ?_ ?_⟩
        · rw [SystemState.runRemoveOnCore_getTcb?_isSome, hTcb]; rfl
        · intro c' hc'
          by_cases hf : c' = fromCore
          · subst hf
            rw [SystemState.runRemoveOnCore_runQueueOnCore_self, RunQueue.contains_remove]
            simp
          · rw [SystemState.runRemoveOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hf)]
            exact SystemState.runLinksAdmit_not_contains hR
              (SystemState.runLinksAdmit_of_contains hR
                ((hR fromCore).contains_of_runCoreCode hTcb hC)) c' hf
      · exact .refl _

/-- The requeue of a vacated thread: the guarded enqueue, then the reschedule
flag. -/
theorem requeueVacatedOnNewHome_runQueueLinkStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (newCore : Concurrency.CoreId) (vacated : Bool) :
    SystemState.RunQueueLinkStage st (requeueVacatedOnNewHome st tid newCore vacated) := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · exact (SystemState.RunQueueLinkStage.runEnqueueOnCore _ _ _ _).trans
        (SystemState.RunQueueLinkStage.of_frame rfl rfl rfl)
    · exact .refl _
  · exact .refl _

/-- The vacate writes a `current` slot and a reschedule flag alone. -/
theorem vacateForAffinityChange_runQueueLinkStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : Concurrency.CoreId) :
    SystemState.RunQueueLinkStage st (vacateForAffinityChange st tid oldCore newCore) := by
  unfold vacateForAffinityChange
  split
  · exact SystemState.RunQueueLinkStage.of_frame rfl rfl rfl
  · exact .refl _

/-- **Where a committed affinity change leaves every thread** (WS-ZA ZA6.3): the
`current` slots are the vacate's, every other thread keeps its TCB off its
run-queue links and its queue, the target keeps its TCB but for the affinity,
and the target ends queued only on its new home or where it already was off its
old home — newly so only when it was queued on or running on the home it left. -/
theorem setThreadCpuAffinityWithMigration_placement {st st' : SystemState}
    {t : SeLe4n.ThreadId} {affinity : Option Concurrency.CoreId} {ec : Concurrency.CoreId}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : setThreadCpuAffinityWithMigration st t affinity ec = .ok (st', sgi)) :
    ∃ tcb, st.getTcb? t = some tcb ∧ Kernel.isIdleThreadId t = false ∧
      affinityRunningElsewhere st t (determineTargetCore st t) Concurrency.allCores = false ∧
      (∀ c, st'.scheduler.currentOnCore c = (vacateForAffinityChange st t
        (determineTargetCore st t) (affinity.getD Concurrency.bootCoreId)).scheduler.currentOnCore c) ∧
      (∀ u, u ≠ t → (st'.getTcb? u).map TCB.withoutRunLinks =
        (st.getTcb? u).map TCB.withoutRunLinks) ∧
      (st'.getTcb? t).map TCB.withoutRunLinks =
        some ({ tcb with cpuAffinity := affinity }).withoutRunLinks ∧
      (∀ c u, u ≠ t → st'.queuedOn c u = st.queuedOn c u) ∧
      (∀ c, st'.queuedOn c t = true → c = affinity.getD Concurrency.bootCoreId ∨
        (c ≠ determineTargetCore st t ∧ st.queuedOn c t = true)) ∧
      (∀ c, st'.queuedOn c t = true → st.queuedOn c t = true ∨
        (determineTargetCore st t ≠ affinity.getD Concurrency.bootCoreId ∧
          (st.queuedOn (determineTargetCore st t) t = true ∨
            st.scheduler.currentOnCore (determineTargetCore st t) = some t))) := by
  obtain ⟨tcb, stSet, hT, -, hI, hR, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have hInvV : (vacateForAffinityChange st t (determineTargetCore st t)
      (affinity.getD Concurrency.bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hInv
  have hTV : (vacateForAffinityChange st t (determineTargetCore st t)
      (affinity.getD Concurrency.bootCoreId)).getTcb? t = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  obtain ⟨hS1, hS2, hS3⟩ := setThreadCpuAffinity_getTcb?_view hInvV hTV hSet
  refine ⟨tcb, hT, hI, hR, ?_⟩
  cases hb : tcb.schedContextBinding.scId? with
  | none =>
    exact affinityChange_placement_of_mid hT hS1
      (fun u hu => by rw [hS2 u hu, vacateForAffinityChange_getTcb?]) (fun c => by rw [hS3])
  | some scId =>
    exact affinityChange_placement_of_mid hT
      (by rw [migrateSchedContextReplenishment_getTcb?]; exact hS1)
      (fun u hu => by
        rw [migrateSchedContextReplenishment_getTcb?, hS2 u hu, vacateForAffinityChange_getTcb?])
      (fun c => by rw [(migrateSchedContextReplenishment_runQueue_current_eq _ _ _ _ c).2, hS3])

/-- **The affinity op is a kernel entry** (WS-ZA ZA6.3): the vacate, the
affinity write, the replenishment move, the run-queue migration and the requeue
keep the run queues in agreement with the threads, and every thread current or
queued on a core stays homed on it — the target, moved, is current or queued
only on its new home (`currentDequeuedUniqueExcept_of_rehome`). -/
theorem setThreadCpuAffinityWithMigration_runQueueEntryStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option Concurrency.CoreId}
    {ec : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' := by
  refine ⟨?_, fun hInv _ _ hD => ?_⟩
  · obtain ⟨tcb, stSet, -, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
    have hL2 : SystemState.RunQueueLinkStage (vacateForAffinityChange st tid
        (determineTargetCore st tid) (affinity.getD Concurrency.bootCoreId)) stSet := by
      unfold setThreadCpuAffinity at hSet
      split at hSet
      · rename_i t0 hT0 _
        rw [Except.ok.injEq] at hSet; subst hSet
        exact SystemState.RunQueueLinkStage.rewriteObject_tcb
          (t' := { t0 with cpuAffinity := affinity }) hT0 (fun _ => rfl) _
      · cases hSet
    refine (vacateForAffinityChange_runQueueLinkStage _ _ _ _).trans (hL2.trans ?_)
    refine SystemState.RunQueueLinkStage.trans ?_
      ((migrateRunQueueOnAffinityChange_runQueueLinkStage _ _ _ _).trans
        (requeueVacatedOnNewHome_runQueueLinkStage _ _ _ _))
    split
    · exact (migrateSchedContextReplenishment_runQueueStage _ _ _ _).1
    · exact .refl _
  · obtain ⟨tcb, hT, hI, hR, hCur, hNe, hTv, hQne, hQself, hQnew⟩ :=
      setThreadCpuAffinityWithMigration_placement hInv h
    have hTv' : (st'.getTcb? tid).map TCB.withoutRunLinks =
        (some { tcb with cpuAffinity := affinity }).map TCB.withoutRunLinks := hTv
    have hHomeNew : st'.homedOn tid (affinity.getD Concurrency.bootCoreId) :=
      fun x' hx' => by
        have := TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.cpuAffinity) hTv'
        rw [hx'] at this
        simp only [Option.map_some, Option.some.injEq] at this
        rw [this]
    have hStay : ∀ c, st'.scheduler.currentOnCore c = some tid →
        c = determineTargetCore st tid ∧
          determineTargetCore st tid = affinity.getD Concurrency.bootCoreId := by
      intro c hc
      rw [hCur, vacateForAffinityChange_currentOnCore] at hc
      split at hc
      · cases hc
      · rename_i hn
        have hco := affinityRunningElsewhere_false hR c hc
        exact ⟨hco, Classical.byContradiction fun hon => hn ⟨hco, hon, hco ▸ hc⟩⟩
    have hPair : ∀ u, (st'.getTcb? u).map (fun x => (x.ipcState, x.threadState)) =
        (st.getTcb? u).map (fun x => (x.ipcState, x.threadState)) := fun u => by
      by_cases hu : u = tid
      · rw [hu, TCB.map_proj_eq_of_map_withoutRunLinks_eq
          (fun x => (x.ipcState, x.threadState)) hTv', hT]
        rfl
      · exact TCB.map_proj_eq_of_map_withoutRunLinks_eq _ (hNe u hu)
    have hM := SystemState.stateFieldsKept_of_pair hPair
    refine SystemState.currentDequeuedUniqueExcept_of_rehome (t := tid)
      (fun c u hc => ?_) (fun c u hc c' hq => ?_) (fun u hu c' hq => ?_) (fun c u hq => ?_)
      hM (fun u c hu _ hh => ?_) (fun c hq => ?_) (fun c hc => ?_) hI hD
    · rw [hCur, vacateForAffinityChange_currentOnCore] at hc
      split at hc
      · cases hc
      · exact hc
    · by_cases hu : u = tid
      · rw [hu] at hc hq ⊢
        rcases hQnew c' hq with h0 | ⟨hne, -⟩
        · exact h0
        · exact absurd (hStay c hc).2 hne
      · rw [hQne c' u hu] at hq; exact hq
    · have hut : u ≠ tid := fun e => by rw [e, hI] at hu; cases hu
      rw [hQne c' u hut] at hq; exact hq
    · by_cases hu : u = tid
      · rw [hu] at hq ⊢
        rcases hQnew c hq with h0 | ⟨-, h0⟩
        · exact .inl h0
        · refine .inr ⟨rfl, (hM _).1 ?_⟩
          rcases h0 with hq0 | hc0
          · exact hD.queuedRunnable _ _ hq0
          · exact hD.runnable hc0
      · rw [hQne c u hu] at hq; exact .inl hq
    · intro x' hx'
      have := TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.cpuAffinity) (hNe u hu)
      rw [hx'] at this
      cases hx : st.getTcb? u with
      | none => rw [hx] at this; cases this
      | some x =>
        rw [hx] at this
        simp only [Option.map_some, Option.some.injEq] at this
        rw [this]; exact hh x hx
    · rcases hQself c hq with h0 | ⟨hne, hq0⟩
      · rw [h0]; exact hHomeNew
      · exact absurd (SeLe4n.Kernel.determineTargetCore_eq_of_homedOn hT
          (hD.queuedHome c _ hq0)).symm hne
    · obtain ⟨h1, h2⟩ := hStay c hc
      rw [h1, h2]; exact hHomeNew

theorem setThreadCpuAffinityOnCore_runQueueEntryStage {st st' : SystemState}
    {vTargetTid : SeLe4n.ValidThreadId} {affinity : Option Concurrency.CoreId}
    {ec : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityOnCore st vTargetTid affinity ec = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' :=
  setThreadCpuAffinityWithMigration_runQueueEntryStage h

/-- WS-ZA ZA6.4: **a configure through a core's control is a kernel entry**: the
move of the context's thread to the control's core (the affinity change's entry
stage), then the configure there (a stage). -/
theorem schedControlConfigure_runQueueEntryStage {core : Concurrency.CoreId}
    {vScId : SeLe4n.ValidObjId} {budget period priority deadline domain : Nat}
    {st st' : SystemState}
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain st =
      .ok ((), st')) : SystemState.RunQueueEntryStage st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact RunQueueStage.entry (schedContextConfigure_runQueueStage h)
  · exact (setThreadCpuAffinityWithMigration_runQueueEntryStage hM).trans
      (RunQueueStage.entry (schedContextConfigure_runQueueStage h))

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

/-- A stage, then a dispatch that may assume the first state's store invariant
and link agreement, is a dispatch. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.dispatch_of_refined {c : Concurrency.CoreId}
    {st st' st'' : SystemState} (h1 : RunQueueStage st st')
    (hL2 : SystemState.RunQueueLinkStage st' st'')
    (h2 : st.objects.invExt → st.runQueueRefined → SystemState.RunQueueDispatchStage c st' st'') :
    SystemState.RunQueueDispatchStage c st st'' :=
  ⟨h1.1.trans hL2, fun e e' he h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    (h2 h r).2.1 e e' he h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans ((h2 h r).2.2 h' r')⟩

/-- The link half of a dequeue-and-run. -/
theorem dequeueRun_runQueueLinkStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId}
    (hO : st'.objects = (st.runRemoveOnCore c tid).objects)
    (hQ : st'.scheduler.runQueue = (st.runRemoveOnCore c tid).scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = (st.runRemoveOnCore c tid).scheduler.runQueueEnds)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = (st.runRemoveOnCore c tid).scheduler.releaseSlots := by
      release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    SystemState.RunQueueLinkStage st st' :=
  (RunQueueStage.runRemoveOnCore st c tid).1.trans
    (SystemState.RunQueueLinkStage.of_frame hO hQ hE
      (hT.trans (SystemState.runRemoveOnCore_referenceTables st c tid).symm) hS
      (hRes.trans (congrArg MachineState.residentCode
        (SystemState.runRemoveOnCore_machine st c tid)).symm))

/-- **A dequeue-and-run on core `c`**: `tid` leaves `c`'s queue and takes `c`'s
current slot, every other slot kept — a dispatch on `c`.  The incoming thread is
one `c`'s links queue or `c`'s idle thread, so it is runnable; it ends queued
nowhere and current on `c` alone. -/
theorem dequeueRun_runQueueDispatchStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId}
    (hO : st'.objects = (st.runRemoveOnCore c tid).objects)
    (hQ : st'.scheduler.runQueue = (st.runRemoveOnCore c tid).scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = (st.runRemoveOnCore c tid).scheduler.runQueueEnds)
    (hCur : ∀ c', st'.scheduler.currentOnCore c' =
      if c' = c then some tid else st.scheduler.currentOnCore c')
    (hSel : st.runQueueRefined → st.queuedOn c tid = true ∨ tid = Kernel.idleThreadId c)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = (st.runRemoveOnCore c tid).scheduler.releaseSlots := by
      release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    SystemState.RunQueueDispatchStage c st st' := by
  have hM : SystemState.StateMono st st' := SystemState.StateMono.of_agreeOffRunLinks
    ((SystemState.objectsAgreeOffRunLinks.of_objects_eq hO).trans
      (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c tid))
  refine ⟨dequeueRun_runQueueLinkStage hO hQ hE hT hS hRes, ?_, fun _ _ => hM⟩
  intro e e' he _ hRf _ hD
  have hQ' : ∀ c' x, st'.queuedOn c' x = if x = tid ∧ c' = c then false else st.queuedOn c' x :=
    fun c' x => by
      rw [SystemState.queuedOn_eq_runLinkOn, SystemState.runLinkOn_of_objects hO,
        ← SystemState.queuedOn_eq_runLinkOn, SystemState.runRemoveOnCore_queuedOn]
  refine SystemState.currentDequeuedUniqueExcept_of_dispatch (c := c) (new := some tid) hD he
    hCur (fun t ht => ?_) (fun c0 h0 => ?_) (fun c' x hq => ?_) hM
  · cases ht
    refine ⟨fun c' => ?_, fun c' hne hc' => ?_, ?_⟩
    · rw [hQ']
      by_cases hc : c' = c
      · simp [hc]
      · rw [if_neg (fun e => hc e.2)]
        cases hq : st.queuedOn c' tid
        · rfl
        · rcases hSel hRf with hq1 | hI
          · exact absurd (SystemState.queuedOn_core_unique hq hq1) hc
          · subst hI
            rw [hD.idleOff _ (Kernel.isIdleThreadId_idleThreadId c) c'] at hq; cases hq
    · rcases hSel hRf with hq1 | hI
      · exact hne ((hD.current c' tid hc').1 c hq1).2.symm
      · subst hI; exact hne (hD.idleHome c c' hc')
    · rcases hSel hRf with hq1 | hI
      · exact ⟨hM.runnable (hD.queuedRunnable c tid hq1),
          hM.homedOn (hD.queuedRunnable c tid hq1).activeAt (hD.queuedHome c tid hq1)⟩
      · subst hI
        exact ⟨hM.runnable (hD.idleRunnable c),
          hM.homedOn (hD.idleRunnable c).activeAt (hD.idleHomed c)⟩
  · cases h0
    rcases hSel hRf with hq1 | hI
    · rw [hD.idleOff _ (Kernel.isIdleThreadId_idleThreadId c0) c] at hq1; cases hq1
    · exact Kernel.idleThreadId_injective hI
  · rw [hQ'] at hq
    split at hq
    · cases hq
    · exact .inl hq

/-- An empty current slot on core `c`, every other slot kept and no queue
written: a dispatch on `c` with nothing incoming. -/
theorem vacateCurrent_runQueueDispatchStage {st st' : SystemState} {c : Concurrency.CoreId}
    (hO : st'.objects = st.objects) (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hS : ∀ c', st'.scheduler.currentOnCore c' =
      if c' = c then none else st.scheduler.currentOnCore c')
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hRS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    SystemState.RunQueueDispatchStage c st st' :=
  ⟨SystemState.RunQueueLinkStage.of_frame hO hQ hE hT hRS hRes, fun _ _ he _ _ _ hD =>
    SystemState.currentDequeuedUniqueExcept_of_dispatch (c := c) (new := none) hD he hS
      (fun _ ht => by cases ht) (fun _ h0 => by cases h0)
      (fun c' x hq => .inl (by
        rw [SystemState.queuedOn_eq_runLinkOn, SystemState.runLinkOn_of_objects hO] at hq
        rwa [SystemState.queuedOn_eq_runLinkOn]))
      (SystemState.StateMono.of_objects hO),
    fun _ _ => SystemState.StateMono.of_objects hO⟩

/-- The idle dispatch: dequeue, restore, current-slot write. -/
theorem dispatchIdleOnCore_runQueueDispatchStage (st : SystemState) (c : Concurrency.CoreId) :
    SystemState.RunQueueDispatchStage c st (dispatchIdleOnCore st c) :=
  dequeueRun_runQueueDispatchStage (restoreIncomingContextOnCore_objects _ _ _)
    (by simp [dispatchIdleOnCore]; rfl) (by simp [dispatchIdleOnCore]; rfl)
    (fun c' => by
      unfold dispatchIdleOnCore; dsimp only
      by_cases hc : c' = c
      · subst hc; simp
      · rw [if_neg hc, SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)]
        unfold SchedulerState.currentOnCore
        rw [restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_current])
    (fun _ => .inr rfl)
    (hS := by unfold dispatchIdleOnCore; dsimp only; rw [restoreIncomingContextOnCore_scheduler]; rfl)
    (hRes := by
      unfold dispatchIdleOnCore; dsimp only
      rw [restoreIncomingContextOnCore_residentCode, SystemState.runRemoveOnCore_machine])

theorem idleFallbackOnCore_runQueueDispatchStage (st : SystemState) (c : Concurrency.CoreId) :
    SystemState.RunQueueDispatchStage c st (idleFallbackOnCore st c) := by
  unfold idleFallbackOnCore
  split
  · exact dispatchIdleOnCore_runQueueDispatchStage st c
  · refine vacateCurrent_runQueueDispatchStage rfl rfl rfl fun c' => ?_
    by_cases hc : c' = c
    · subst hc; simp
    · rw [if_neg hc]
      exact SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)

/-- The drop-current reschedule: save, then the idle fallback or the dequeue,
restore and current-slot write of the chosen thread, then the flag clear — a
dispatch on `c`. -/
theorem scheduleEffectiveOnCore_runQueueDispatchStage {st st' : SystemState}
    {c : Concurrency.CoreId} (h : scheduleEffectiveOnCore st c = .ok st') :
    SystemState.RunQueueDispatchStage c st st' := by
  unfold scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rw [Except.ok.injEq] at h; subst h
    exact ((saveOutgoingContextOnCore_runQueueStage st c).dispatch
      (idleFallbackOnCore_runQueueDispatchStage _ c)).trans_stage
      (RunQueueStage.clearReschedulePendingOnCore _ _)
  · rename_i tid hChoose
    split at h
    · split at h
      · rw [Except.ok.injEq] at h; subst h
        refine (saveOutgoingContextOnCore_runQueueStage st c).dispatch_of_refined
          (dequeueRun_runQueueLinkStage (restoreIncomingContextOnCore_objects _ _ _)
            (by simp; rfl) (by simp; rfl)
            ((restoreIncomingContextOnCore_referenceTables _ _ _).trans
              (SystemState.runRemoveOnCore_referenceTables _ _ _))
            (by simp only [restoreIncomingContextOnCore_scheduler]; rfl)) fun _ hR =>
          dequeueRun_runQueueDispatchStage (restoreIncomingContextOnCore_objects _ _ _)
            (by simp; rfl) (by simp; rfl) (fun c' => ?_) (fun hRf => .inl ?_)
            ((restoreIncomingContextOnCore_referenceTables _ _ _).trans
              (SystemState.runRemoveOnCore_referenceTables _ _ _))
            (by simp only [restoreIncomingContextOnCore_scheduler]; rfl)
        · by_cases hc : c' = c
          · subst hc; simp
          · rw [if_neg hc]
            simp only [SchedulerState.clearReschedulePendingOnCore_currentOnCore]
            rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)]
            unfold SchedulerState.currentOnCore
            rw [restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_current]
        · refine SystemState.queuedOn_of_mem_runQueueOnCore hRf ?_
          rw [saveOutgoingContextOnCore_scheduler]
          exact (RunQueue.mem_toList_iff_mem _ _).mp
            (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c tid (hR c) hChoose)
      · cases h
    · cases h

/-- A SchedContext rewritten through its witnessed lookup: a frame stage off it
(WS-ZA ZA6.4: a charge writes its refills, and the charge's own end closes it). -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueFrameStage.rewriteObject_schedContext
    {st : SystemState} {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext}
    (h : st.getSchedContext? scId = some sc) (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc'))
    (hRL : ∀ c, sc'.releaseLinkOn c = sc.releaseLinkOn c)
    (hY : sc'.yieldFromCode = sc.yieldFromCode := by first | rfl | simp_all) :
    SystemState.RunQueueFrameStage (· = scId) st
      (st.rewriteObject scId.toObjId (.schedContext sc') hA) :=
  SystemState.RunQueueFrameStage.insert (st' := st.rewriteObject scId.toObjId (.schedContext sc') hA)
    (hY := by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; simp only [objYieldCodes, hY])
    rfl rfl rfl
    (fun c => by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl)
    (SystemState.objStateMono_nonTcb
      (by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl) rfl)
    (hR := fun c => by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; exact hRL c)

/-- WS-ZA ZA6.4: **a context write that leaves its head holding budget is a
stage**: the context stays well formed and bound as it was and has no place, so
no refill of it is stranded — the tick's charge that does not use the head up. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_schedContext_keyless
    {st : SystemState} {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext}
    (h : st.getSchedContext? scId = some sc) (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc'))
    (hRL : ∀ c, sc'.releaseLinkOn c = sc.releaseLinkOn c)
    (hWF : schedContextWellFormed sc → schedContextWellFormed sc')
    (hK : sc'.releaseKey? = none) (hBT : sc'.boundThread = sc.boundThread)
    (hY : sc'.yieldFromCode = sc.yieldFromCode := by first | rfl | simp_all) :
    RunQueueStage st (st.rewriteObject scId.toObjId (.schedContext sc') hA) :=
  (SystemState.RunQueueFrameStage.rewriteObject_schedContext h hA hRL hY).withRefills
    fun S hs hI _ _ _ _ h0 h4 => SystemState.refillsSoundExcept_close_keyless (st0 := st) (fun _ => rfl) hs h0 h4
      (SystemState.rewriteObject_schedContext_getSchedContext?_self st scId sc' hA hI) h
      (hWF (h0.1 scId sc hs h)) hK hBT

/-- The context a charge writes back names the thread it named. -/
theorem chargedSchedContext_boundThread (sc : SchedContext) (start ticks now : Nat) :
    (cbsUpdateDeadline (sc.chargeBudget start ticks now) now true).boundThread = sc.boundThread := by
  unfold SchedContext.boundThread
  rw [(cbsUpdateDeadline_refills _ now true).2.2.2.2.2,
    (SchedContext.fields_of_refillsErased (sc.chargeBudget_refillsErased start ticks now)).2.2.2.2.2.2.1]

theorem chargeBudget_boundThread (sc : SchedContext) (start ticks now : Nat) :
    (sc.chargeBudget start ticks now).boundThread = sc.boundThread := by
  unfold SchedContext.boundThread
  rw [(SchedContext.fields_of_refillsErased (sc.chargeBudget_refillsErased start ticks now)).2.2.2.2.2.2.1]

/-- The context a refill writes back names the thread it named. -/
theorem refilledSchedContext_boundThread (sc : SchedContext) (now : Nat) :
    (cbsUpdateDeadline (sc.releaseReadyHead now) now true).boundThread = sc.boundThread := by
  unfold SchedContext.boundThread
  rw [(cbsUpdateDeadline_refills _ now true).2.2.2.2.2,
    (SchedContext.fields_of_refillsErased (sc.releaseReadyHead_refillsErased now)).2.2.2.2.2.2.1]

/-- **A tick that does not use the head up leaves the context no place**: its
head still holds budget (`chargeBudget_tick_pos`). -/
theorem chargeBudget_tick_releaseKey (sc : SchedContext) (start now : Nat)
    (h : sc.tickExhausts start = false) : (sc.chargeBudget start 1 now).releaseKey? = none := by
  have hp := SchedContext.chargeBudget_tick_pos sc start now h
  unfold SchedContext.releaseKey?
  rw [if_neg (fun h' => absurd h'.1 (by omega))]

/-- WS-ZA ZA6.4: **core `c`'s current thread's context can be placed on `c`**:
the context its binding names is bound and linked on `c`'s release queue or on
none — what a charge's postpone needs, as seL4-MCS's `postpone` of the current
scheduling context goes on the current core's release queue.  The binding pair
and the placement invariants give it (`currentContextPlaceableOnCore_of_invariants`). -/
def _root_.SeLe4n.Model.SystemState.currentContextPlaceableOnCore (st : SystemState)
    (c : Concurrency.CoreId) : Prop :=
  ∀ tid tcb scId sc, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some tcb →
    tcb.schedContextBinding.scId? = some scId → st.getSchedContext? scId = some sc →
    sc.boundThread.isSome = true ∧ st.releaseFreeFor c scId = true

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

/-- The timeout of one IPC-blocked thread: the abort, the wake and the revert —
inside a scheduling point other than a block, where the blocked thread is no
core's current one. -/
theorem timeoutThread_runQueueWindowStage {p : SchedPoint}
    (hp : ∀ c, p ≠ .block c) {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId} {st : SystemState}
    {r : SystemState × Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timeoutThread epId isReceiveQ tid ec st = .ok r) (hB : blockedAt st tid) :
    SystemState.RunQueueWindowStage p st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    have hS := SystemState.RunQueueWindowStage.then_wake hp
      (abortPendingIpcOnEndpoint_runQueueStage hA) ec (fun c' hc => by
        unfold SchedulerState.currentOnCore at hc ⊢
        rwa [abortPendingIpcOnEndpoint_scheduler_eq _ _ _ _ _ hA] at hc) hB
    dsimp only at h
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact hS.trans (((SystemState.unlinkReplyWaiter_runQueueStage _ _ _).trans
        (revertPriorityInheritance_runQueueStage _ _ _)).window p)
    · rw [Except.ok.injEq] at h; subst h; exact hS

/-- The bound-context timeout pass: a fold of timeouts, each of a thread blocked
in IPC. -/
theorem timeoutBlockedThreads_runQueueWindowStage {p : SchedPoint}
    (hp : ∀ c, p ≠ .block c) (st : SystemState) (scId : SeLe4n.SchedContextId)
    (ec : Concurrency.CoreId) :
    SystemState.RunQueueWindowStage p st (timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (Concurrency.CoreId × Concurrency.SgiKind)),
      SystemState.RunQueueWindowStage p st acc.1 →
      SystemState.RunQueueWindowStage p st (l.foldl (fun acc tid =>
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
    H _ _ (SystemState.RunQueueWindowStage.refl p st)
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
    · rename_i tcb hTcb
      split
      · rename_i epId isRQ hInfo
        split
        · rename_i r hT
          refine h.trans (timeoutThread_runQueueWindowStage hp hT ⟨tcb, hTcb, fun hr => ?_⟩)
          simp [tcbBlockingInfo, hr] at hInfo
        · exact h
      · exact h
    · exact h

/-- An unbound thread's slice end: a slice reset and the guarded enqueue.  The
thread is core `c`'s current one, so the enqueue opens `c`'s scheduling point. -/
theorem sliceExpireOnCore_runQueueWindowStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    SystemState.RunQueueWindowStage (.preempt c) st (sliceExpireOnCore st c tid tcb hTcb) :=
  ((RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl) _).window (.preempt c)).trans
    (SystemState.RunQueueWindowStage.requeueCurrent _ c tid _ hCur)

/-- A bound thread's budget spend: the context rewrite, the replenish-queue
insert and the guarded enqueue of core `c`'s current thread. -/
theorem spendBudgetOnCore_runQueueWindowStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (start ticks : Nat)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hP : sc.boundThread.isSome = true ∧ st.releaseFreeFor c scId = true) :
    SystemState.RunQueueWindowStage (.preempt c) st
      (spendBudgetOnCore st c tid scId sc hSc start ticks) := by
  unfold spendBudgetOnCore
  refine SystemState.RunQueueWindowStage.trans (RunQueueStage.window ?_ (.preempt c))
    (SystemState.RunQueueWindowStage.requeueCurrent _ c tid _
      (by simpa [replenishOnCore_currentOnCore, SystemState.rewriteObject_scheduler] using hCur))
  obtain ⟨h1, h2, h3⟩ := spendRecord_release sc start ticks st.machine.timer
  exact SystemState.RunQueueFrameStage.closePlace
    (SystemState.RunQueueFrameStage.rewriteObject_schedContext hSc
      (SystemState.rewriteAdmissible_schedContext hSc _)
      (fun _ => by simp only [SchedContext.releaseLinkOn, h1, h2, h3]))
    (fun S hs hI _ _ hS _ => SystemState.closePlace_facts_bound
      (SystemState.rewriteObject_schedContext_getSchedContext?_self st scId _ _ hI)
      (cbsUpdateDeadline_preserves_schedContextWellFormed _ _ _
        (chargeBudget_preserves_schedContextWellFormed _ _ _ _ (hS.1 scId sc hs hSc)))
      (by rw [chargedSchedContext_boundThread]; exact hP.1)
      (by
        unfold SystemState.releaseFreeFor
        rw [SystemState.releaseCoreOf_rewriteObject_schedContext _ _ _ _ hSc hI h2]
        exact hP.2))

/-- The tick's exhausted bound arm: the spend, the timeouts and the diagnostic. -/
theorem budgetExhaustOnCore_runQueueWindowStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hP : sc.boundThread.isSome = true ∧ st.releaseFreeFor c scId = true) :
    SystemState.RunQueueWindowStage (.preempt c) st
      (budgetExhaustOnCore st c tid preKey scId sc hSc ticks) :=
  (((spendBudgetOnCore_runQueueWindowStage st c tid scId sc hSc _ ticks hCur hP).trans
    ((markKeyChangeFor_runQueueStage _ tid preKey).window (.preempt c))).trans
    (timeoutBlockedThreads_runQueueWindowStage (fun _ h => by cases h) _ scId c)).trans
    ((RunQueueStage.of_frame
      (st := (timeoutBlockedThreads (markKeyChangeFor
        (spendBudgetOnCore st c tid scId sc hSc (st.machine.timer - ticks) ticks)
        tid preKey) scId c).1)
      (st' := (budgetExhaustOnCore st c tid preKey scId sc hSc ticks)) rfl
      (by show (markRescheduleTargets _ _).runQueue = _; rw [markRescheduleTargets_eq]; rfl)
      (by show (markRescheduleTargets _ _).runQueueEnds = _; rw [markRescheduleTargets_eq]; rfl)
      (by show (markRescheduleTargets _ _).currentCode = _; rw [markRescheduleTargets_eq]; rfl)
      rfl
      (by show (markRescheduleTargets _ _).releaseSlots = _; rw [markRescheduleTargets_eq]; rfl)).window
      (.preempt c))

/-- The tick's charge of core `c`'s current thread: a slice or budget step, and
on its end the requeue that opens `c`'s scheduling point. -/
theorem timerTickBudgetOnCore_runQueueWindowStage {st : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {r : SystemState × Bool}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = r)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hH : st.currentContextPlaceableOnCore c) :
    SystemState.RunQueueWindowStage (.preempt c) st r.1 := by
  subst h
  unfold timerTickBudgetOnCore
  split
  · split
    · exact sliceExpireOnCore_runQueueWindowStage st c tid tcb hTcb hCur
    · exact (RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _)).window (.preempt c)
  all_goals
    rename_i hBd
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore_runQueueWindowStage st c tid _ _ sc hSc 1 hCur
          (hH tid tcb _ sc hCur hTcb (by rw [hBd]; rfl) hSc)
      · rename_i hEx
        exact (RunQueueStage.rewriteObject_schedContext_keyless hSc
          (SystemState.rewriteAdmissible_schedContext hSc _)
          (SchedContext.releaseLinkOn_of_refillsErased (sc.chargeBudget_refillsErased _ _ _))
          (chargeBudget_preserves_schedContextWellFormed _ _ _ _)
          (chargeBudget_tick_releaseKey _ _ _ (Bool.eq_false_iff.mpr hEx))
          (chargeBudget_boundThread _ _ _ _)).window (.preempt c)
    · exact (RunQueueStage.of_frame rfl rfl rfl).window (.preempt c)

/-- A charge that does not preempt requeues nothing: a stage. -/
theorem timerTickBudgetOnCore_runQueueStage_of_not_preempted {st : SystemState}
    {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {st3 : SystemState}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = (st3, false)) :
    RunQueueStage st st3 := by
  unfold timerTickBudgetOnCore at h
  split at h
  · split at h
    · simp only [Prod.mk.injEq] at h; exact absurd h.2 (by decide)
    · simp only [Prod.mk.injEq] at h; rw [← h.1]
      exact RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _)
  all_goals
    split at h
    · rename_i sc hSc _
      dsimp only at h
      split at h
      · simp only [Prod.mk.injEq] at h; exact absurd h.2 (by decide)
      · rename_i hEx
        simp only [Prod.mk.injEq] at h; rw [← h.1]
        exact RunQueueStage.rewriteObject_schedContext_keyless hSc
          (SystemState.rewriteAdmissible_schedContext hSc _)
          (SchedContext.releaseLinkOn_of_refillsErased (sc.chargeBudget_refillsErased _ _ _))
          (chargeBudget_preserves_schedContextWellFormed _ _ _ _)
          (chargeBudget_tick_releaseKey _ _ _ (Bool.eq_false_iff.mpr hEx))
          (chargeBudget_boundThread _ _ _ _)
    · simp only [Prod.mk.injEq] at h; rw [← h.1]
      exact RunQueueStage.of_frame rfl rfl rfl

/-- The yield's charge: the slice end or the budget forfeit with the key hook,
each requeueing core `c`'s current thread. -/
theorem yieldChargeOnCore_runQueueWindowStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} (h : yieldChargeOnCore st c tid = .ok st')
    (hCur : st.scheduler.currentOnCore c = some tid) (hH : st.currentContextPlaceableOnCore c) :
    SystemState.RunQueueWindowStage (.preempt c) st st' := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_runQueueWindowStage st c tid tcb hTcb hCur
    all_goals
      rename_i hBd
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore_runQueueWindowStage st c tid _ sc hSc _ _ hCur
          (hH tid tcb _ sc hCur hTcb (by rw [hBd]; rfl) hSc)).trans
          ((markKeyChangeFor_runQueueStage _ _ _).window (.preempt c))
      · cases h

/-- The yield: the charge opens core `c`'s scheduling point, the reschedule
closes it — a kernel entry. -/
theorem yieldOnCore_runQueueEntryStage {st st' : SystemState} {c : Concurrency.CoreId}
    (h : yieldOnCore st c = .ok st') (hH : st.currentContextPlaceableOnCore c) :
    SystemState.RunQueueEntryStage st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · rename_i tid hCur
    split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore_runQueueWindowStage hC hCur hH).dispatch
        (scheduleEffectiveOnCore_runQueueDispatchStage h)

/-- A replenishment wakes only a runnable thread: the target test asks it. -/
theorem replenishWakeTarget_runnable {stPre refilled : SystemState}
    {scId : SeLe4n.SchedContextId} {tid : SeLe4n.ThreadId}
    (h : replenishWakeTarget stPre refilled scId = some tid) : refilled.runnable tid := by
  unfold replenishWakeTarget at h
  dsimp only at h
  have key : ∀ o : Option SeLe4n.ThreadId,
      o.filter (fun t => (refilled.getTcb? t).any TCB.isRunnable) = some tid →
      refilled.runnable tid := by
    intro o ho
    obtain ⟨-, hp⟩ := Option.filter_eq_some_iff.mp ho
    cases hT : refilled.getTcb? tid with
    | none => rw [hT] at hp; cases hp
    | some x =>
      rw [hT] at hp
      exact ⟨x, hT, TCB.runnable_of_isRunnable (by simpa using hp)⟩
  repeat' split at h
  all_goals first | cases h | exact key _ h

/-- One due replenishment: the refill and, for a runnable thread it makes
eligible and no core runs, the wake, under the refill's key hook — a frame stage
off the refilled context (WS-ZA ZA6.4), which the drain's placement closes. -/
theorem processOneReplenishmentOnCore_runQueueFrameStage (st : SystemState)
    (c : Concurrency.CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) :
    SystemState.RunQueueFrameStage (· = scId) st (processOneReplenishmentOnCore st c scId now) := by
  have hRefill : SystemState.RunQueueFrameStage (· = scId) st (refillSchedContext st scId now) := by
    unfold refillSchedContext
    exact updateSchedContext_runQueueFrameStage _ _ _ (fun sc => refillRecord_release sc now)
  unfold processOneReplenishmentOnCore
  refine SystemState.RunQueueFrameStage.trans ?_
    (SystemState.RunQueueStage.toFrame (markRefillKeyChange_runQueueStage _ _ _) _)
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i tid hW
    split
    · exact hRefill
    · rename_i hRun
      refine hRefill.trans (SystemState.RunQueueStage.toFrame
        ((wakeThread_runQueueStage _ _ c
          (currentNowhere_of_runningOnSomeCore_false (Bool.eq_false_iff.mpr hRun))
          (replenishWakeTarget_runnable hW).activeAt).trans ?_) _)
      exact RunQueueStage.of_frame rfl rfl rfl
  · exact hRefill

/-- One pass of the drain: core `c`'s head context, refilled and placed again.
The head is queued on `c`, so it is bound (`releaseQueuedBound`) and free for
`c`; the refill keeps it well formed and bound. -/
theorem drainPass_runQueueStage (s : SystemState) (c : Concurrency.CoreId)
    (x : SeLe4n.SchedContextId) (now : Nat) (h0 : s.scheduler.releaseHeadOnCore c ≠ 0)
    (hx : ReleaseChain.decode (s.scheduler.releaseHeadOnCore c) = x) :
    RunQueueStage s ((processOneReplenishmentOnCore s c x now).releasePlace c x) := by
  refine SystemState.RunQueueFrameStage.closePlace
    (processOneReplenishmentOnCore_runQueueFrameStage s c x now)
    (fun S hs hI _ hQ hS _ => ?_)
  have hq : s.releaseQueuedOn c x = true := ((hQ c).queued x).mpr (hx ▸ releaseHead_mem (hQ c) h0)
  obtain ⟨b, hb, hbd⟩ := hS.2.2 c _ hs ((hQ c).mem_of_queued hq)
  have hA := processOneReplenishmentOnCore_releaseStateAgree s c x now hI
  refine SystemState.closePlace_facts_bound (u := cbsUpdateDeadline (b.releaseReadyHead now) now true)
    ?_ (cbsUpdateDeadline_preserves_schedContextWellFormed _ _ _
      (releaseReadyHead_preserves_schedContextWellFormed _ _ (hS.1 x b hs hb)))
    (by rw [refilledSchedContext_boundThread]; exact hbd) ?_
  · rw [processOneReplenishmentOnCore_getSchedContext? s c x now hI, refillSchedContext,
      SystemState.updateSchedContext_getSchedContext?_self _ _ _ hI, hb]
    rfl
  · have hq' : (processOneReplenishmentOnCore s c x now).releaseQueuedOn c x = true := by
      rw [hA.1.queuedOn c]; exact hq
    unfold SystemState.releaseFreeFor
    rw [SystemState.releaseCoreOf_of_queuedOn hq']
    simp

/-- The replenishment drain: each pass refills core `c`'s head and places it
again, a stage. -/
theorem processReplenishmentsDueOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (now : Nat) : RunQueueStage st (processReplenishmentsDueOnCore st c now) := by
  unfold processReplenishmentsDueOnCore
  exact drainDueOnCore_induction_pass (RunQueueStage st) c now
    (fun s x h h0 hx => h.trans (drainPass_runQueueStage s c x now h0 hx)) _ st
    (RunQueueStage.refl st)

/-- The per-core timer tick: the diagnostic clear, the replenishment drain, the
charge, and the reschedule or the local reschedule decision.  A charge that
preempts opens core `c`'s scheduling point and the reschedule closes it, so the
tick is a kernel entry. -/
theorem timerTickOnCore_runQueueEntryStage (st : SystemState) (c : Concurrency.CoreId)
    (hH : (timerTickOnCorePrepared st c).currentContextPlaceableOnCore c) :
    SystemState.RunQueueEntryStage st (timerTickOnCore st c) := by
  have hP : RunQueueStage st (timerTickOnCorePrepared st c) :=
    (RunQueueStage.of_frame (st := st)
      (st' := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] })
      rfl rfl rfl).trans
      (processReplenishmentsDueOnCore_runQueueStage
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer)
  have hR : ∀ s, RunQueueStage st s →
      SystemState.RunQueueEntryStage st (rescheduleIfPendingOnCore s c) := fun s hs => by
    unfold rescheduleIfPendingOnCore
    split
    · exact hs.entry.trans (handleRescheduleSgiOnCore_runQueueEntryStage
        (handleRescheduleSgiOnCore_eq_state s c))
    · exact hs.entry
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hP
  · exact hR _ hP
  · exact hP.entry.trans ((timerTickBudgetOnCore_runQueueWindowStage hB hCur hH).dispatch
      (scheduleEffectiveOnCore_runQueueDispatchStage (scheduleEffectiveOnCore_eq_state st3 c)))
  · exact hR _ (hP.trans (timerTickBudgetOnCore_runQueueStage_of_not_preempted hB))

/-- The live `.untypedRetype` arm: the carve. -/
theorem untypedRetypeFromCap_runQueueStage {tid : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} {srcAddr : SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (h : untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ :=
    untypedRetypeFromCap_ok tid ec srcAddr args? st st' h
  exact untypedRetypeObject_runQueueStage hCarve

/-- The per-core context unbind: the unbind, then the preemption seam. -/
theorem schedContextUnbindOnCore_runQueueEntryStage {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hU
    exact (SchedContextOps.schedContextUnbind_runQueueEntryStage vScId st stU hU).trans
      (priorityRescheduleOnCore_runQueueEntryStage h)


end SeLe4n.Kernel
