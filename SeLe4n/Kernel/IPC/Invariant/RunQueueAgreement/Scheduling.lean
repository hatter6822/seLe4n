/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Ipc
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

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
                split
                · rename_i hMem
                  refine RunQueueStage.trans ?_ (RunQueueStage.runRequeueOnCore_of_queuedOn _ _ _ _ hMem)
                  refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                  exact RunQueueStage.insert rfl rfl rfl
                    (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                      (SystemState.objStateMono_nonTcb
                        (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)
                · split
                  · rename_i hPlace
                    refine RunQueueStage.trans ?_
                      (SystemState.RunQueueStage.markReschedulePendingOnCore _ _)
                    refine RunQueueStage.then_enqueue ?_ (bindPlacesParkedThread_not_current hPlace)
                      (bindPlacesParkedThread_runnable hPlace hTcb)
                    refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                    exact RunQueueStage.insert rfl rfl rfl
                      (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                      (SystemState.objStateMono_nonTcb
                        (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)
                  · refine RunQueueStage.trans ?_ (RunQueueStage.updateTcb _ _ (fun _ _ => rfl))
                    exact RunQueueStage.insert rfl rfl rfl
                      (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                      (SystemState.objStateMono_nonTcb
                        (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)
              all_goals cases h
        · cases h
  · cases h

/-- A TCB rewritten through the witnessed lookup, keeping its run-queue fields. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_tcb {st : SystemState}
    {tid : SeLe4n.ThreadId} {t t' : TCB} (h : st.getTcb? tid = some t)
    (hL : ∀ c, t'.runLinkOn c = t.runLinkOn c) (hA : st.rewriteAdmissible tid.toObjId (.tcb t'))
    (hm : TCB.StepMono t t' := by exact ⟨id, id⟩) :
    RunQueueStage st (st.rewriteObject tid.toObjId (.tcb t') hA) :=
  RunQueueStage.insert (st' := st.rewriteObject tid.toObjId (.tcb t') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact hL c)
    (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; exact SystemState.objStateMono_tcb hm)

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
            (RunQueueStage.of_frame (st := st) (st' := SchedContextOps.purgeReplenishmentOnCore st
              (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩) rfl rfl rfl).trans
              (RunQueueStage.storeObject hStore (fun c => by
                rw [SchedContextOps.purgeReplenishmentOnCore_objects,
                  show st.objects[vScId.val]? = _ from hScRaw]; rfl)
                (SystemState.objStateMono_nonTcb (by
                  rw [SchedContextOps.purgeReplenishmentOnCore_objects,
                    show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl))
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
          exact SystemState.objStateMono_tcb ⟨id, id⟩)).trans
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
        (SystemState.RunQueueLinkStage.of_frame hO (by rw [hS]; rfl) (by rw [hS]; rfl)), ?_,
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
        refine ⟨fun c' => ?_, hNotElse, (hM hInv).runnable ?_⟩
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
        · rcases hSel hRf with hq | hc | hI
          · exact hD.queuedRunnable c tid hq
          · exact hRunCur tid hc
          · subst hI; exact hD.idleRunnable c
      · cases h0
        rcases hSel hRf with hq | hc | hI
        · rw [hD.idleOff _ (Kernel.isIdleThreadId_idleThreadId c0) c] at hq; cases hq
        · exact (hD.idleHome c0 c hc).symm
        · exact Kernel.idleThreadId_injective hI
      · rw [hQ'] at hq
        split at hq
        · cases hq
        · rcases preemptCurrentOnCore_queuedOn_imp hInv hq with hq0 | ⟨hc0, _, _, hI⟩
          · exact .inl hq0
          · exact .inr ⟨hc0, hI, (hM hInv).runnable (hRunCur _ hc0)⟩
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
  · rcases preemptCurrentOnCore_queuedOn_imp hInv hq with hq0 | ⟨hc0, _, _, hI⟩
    · exact .inl hq0
    · exact .inr ⟨hc0, hI, (hM hInv).runnable ((hD.current c x hc0).2.2.resolve_left hb)⟩

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
        have hS23 := cancelSuspendDonation_runQueueStage _ s3 vtid.val _
          (determineTargetCore st vtid.val) hDon
        have hS3 := (hS1.trans hS12).trans hS23
        refine SystemState.RunQueueEntryStage.trans ?_
          (suspendRescheduleOnCore_runQueueEntryStage hStep)
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
          rw [cancelSuspendDonation_placedCoreOf? _ s3 _ _ _ vtid.val hInv2 hDon, hP12 hInv1,
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
        refine (hS2.trans (enqueueRunnableOnCore_runQueueStage _ _ _ (fun c hc => ?_) ?_)).entry
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

/-- The affinity migration moves a thread from the queue that holds it to its
new home core's: after the removal it is on no queue, so the enqueue is admitted.
It is a kernel entry's step, not a stage: between scheduling points the thread
it moves is no core's current thread, but inside one it may be the outgoing
thread a preemption queued, which the move would take off its core. -/
theorem migrateRunQueueOnAffinityChange_runQueueEntryStage (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : Concurrency.CoreId) :
    SystemState.RunQueueEntryStage st (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact (RunQueueStage.refl _).entry
  · rename_i hNe
    split
    · exact (RunQueueStage.refl _).entry
    · rename_i tcb hTcb
      split
      · rename_i hC
        have hQd : st.queuedOn fromCore tid = true := by
          unfold SystemState.queuedOn; simp [hTcb, hC]
        refine SystemState.RunQueueEntryStage.trans
          (st' := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority)
          ?_ (RunQueueStage.of_frame
            (st := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority)
            (st' := { (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                tcb.boostedPriority with
              scheduler := ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                tcb.boostedPriority).scheduler.markReschedulePendingOnCore toCore })
            rfl rfl rfl).entry
        have hL : SystemState.RunQueueLinkStage st
            ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority) := ?_
        · have hM : SystemState.StateMono st
              ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid tcb.boostedPriority) :=
            SystemState.StateMono.of_agreeOffRunLinks
              ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
                (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _))
          refine ⟨hL, fun _ _ _ hD => SystemState.currentDequeuedUniqueExcept_of_frame ?_ ?_ ?_
            ?_ hM hD⟩
          · intro c t h
            rw [SystemState.runEnqueueAdmitted_currentOnCore] at h
            unfold SchedulerState.currentOnCore at h ⊢
            rwa [SystemState.runRemoveOnCore_current] at h
          · intro c t hc c' hq
            rw [SystemState.runEnqueueAdmitted_queuedOn] at hq
            split at hq
            · rename_i ht; subst ht
              cases ((hD.current c t hc).1 fromCore hQd).1
            · rw [SystemState.runRemoveOnCore_queuedOn] at hq
              split at hq
              · cases hq
              · exact hq
          · intro t ht c' hq
            rw [SystemState.runEnqueueAdmitted_queuedOn] at hq
            split at hq
            · rename_i ht'; subst ht'
              rw [hD.idleOff _ ht fromCore] at hQd; cases hQd
            · rw [SystemState.runRemoveOnCore_queuedOn] at hq
              split at hq
              · cases hq
              · exact hq
          · intro c t hq
            rw [SystemState.runEnqueueAdmitted_queuedOn] at hq
            split at hq
            · rename_i ht; subst ht
              exact .inr (hM.runnable (hD.queuedRunnable _ _ hQd))
            · rw [SystemState.runRemoveOnCore_queuedOn] at hq
              split at hq
              · cases hq
              · exact .inl hq
        intro hInv hR
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
      · exact (RunQueueStage.refl _).entry

/-- The affinity op: the affinity field write, the replenishment move (replenish
queues only) and the run-queue migration. -/
theorem setThreadCpuAffinityOnCore_runQueueEntryStage {st st' : SystemState}
    {vTargetTid : SeLe4n.ValidThreadId} {affinity : Option Concurrency.CoreId}
    {ec : Concurrency.CoreId} {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityOnCore st vTargetTid affinity ec = .ok (st', sgi?)) :
    SystemState.RunQueueEntryStage st st' := by
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
          refine hS1.entry.trans (SystemState.RunQueueEntryStage.trans (RunQueueStage.entry ?_)
            (migrateRunQueueOnAffinityChange_runQueueEntryStage _ _ _ _))
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
    (hE : st'.scheduler.runQueueEnds = (st.runRemoveOnCore c tid).scheduler.runQueueEnds) :
    SystemState.RunQueueLinkStage st st' :=
  (RunQueueStage.runRemoveOnCore st c tid).1.trans (SystemState.RunQueueLinkStage.of_frame hO hQ hE)

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
    (hSel : st.runQueueRefined → st.queuedOn c tid = true ∨ tid = Kernel.idleThreadId c) :
    SystemState.RunQueueDispatchStage c st st' := by
  have hM : SystemState.StateMono st st' := SystemState.StateMono.of_agreeOffRunLinks
    ((SystemState.objectsAgreeOffRunLinks.of_objects_eq hO).trans
      (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c tid))
  refine ⟨dequeueRun_runQueueLinkStage hO hQ hE, ?_, fun _ _ => hM⟩
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
      · exact hM.runnable (hD.queuedRunnable c tid hq1)
      · subst hI; exact hM.runnable (hD.idleRunnable c)
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
      if c' = c then none else st.scheduler.currentOnCore c') :
    SystemState.RunQueueDispatchStage c st st' :=
  ⟨SystemState.RunQueueLinkStage.of_frame hO hQ hE, fun _ _ he _ _ _ hD =>
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
            (by simp; rfl) (by simp; rfl)) fun _ hR =>
          dequeueRun_runQueueDispatchStage (restoreIncomingContextOnCore_objects _ _ _)
            (by simp; rfl) (by simp; rfl) (fun c' => ?_) fun hRf => .inl ?_
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

/-- A SchedContext rewritten through its witnessed lookup. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.rewriteObject_schedContext
    {st : SystemState} {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext}
    (h : st.getSchedContext? scId = some sc) (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) :
    RunQueueStage st (st.rewriteObject scId.toObjId (.schedContext sc') hA) :=
  RunQueueStage.insert (st' := st.rewriteObject scId.toObjId (.schedContext sc') hA) rfl rfl rfl
    (fun c => by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl)
    (SystemState.objStateMono_nonTcb
      (by rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl) rfl)

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
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    SystemState.RunQueueWindowStage (.preempt c) st (spendBudgetOnCore st c tid scId sc hSc ticks) := by
  unfold spendBudgetOnCore
  refine SystemState.RunQueueWindowStage.trans (RunQueueStage.window ?_ (.preempt c))
    (SystemState.RunQueueWindowStage.requeueCurrent _ c tid _ hCur)
  unfold replenishOnCore
  exact (RunQueueStage.rewriteObject_schedContext hSc
    (SystemState.rewriteAdmissible_schedContext hSc _)).trans (RunQueueStage.of_frame rfl rfl rfl)

/-- The tick's exhausted bound arm: the spend, the timeouts and the diagnostic. -/
theorem budgetExhaustOnCore_runQueueWindowStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    SystemState.RunQueueWindowStage (.preempt c) st (budgetExhaustOnCore st c tid scId sc hSc ticks).1 :=
  ((spendBudgetOnCore_runQueueWindowStage st c tid scId sc hSc ticks hCur).trans
    (timeoutBlockedThreads_runQueueWindowStage (fun _ h => by cases h) _ scId c)).trans
    ((RunQueueStage.of_frame
      (st := (timeoutBlockedThreads (spendBudgetOnCore st c tid scId sc hSc ticks) scId c).1)
      (st' := (budgetExhaustOnCore st c tid scId sc hSc ticks).1) rfl rfl rfl).window (.preempt c))

/-- The tick's charge of core `c`'s current thread: a slice or budget step, and
on its end the requeue that opens `c`'s scheduling point. -/
theorem timerTickBudgetOnCore_runQueueWindowStage {st : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = .ok r)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    SystemState.RunQueueWindowStage (.preempt c) st r.1 := by
  unfold timerTickBudgetOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_runQueueWindowStage st c tid tcb hTcb hCur
    · rw [Except.ok.injEq] at h; subst h
      exact (RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _)).window (.preempt c)
  all_goals
    split at h
    · rename_i sc hSc _
      split at h
      · rw [Except.ok.injEq] at h; subst h
        exact budgetExhaustOnCore_runQueueWindowStage st c tid _ sc hSc 1 hCur
      · rw [Except.ok.injEq] at h; subst h
        exact (RunQueueStage.rewriteObject_schedContext hSc
          (SystemState.rewriteAdmissible_schedContext hSc _)).window (.preempt c)
    · cases h

/-- A charge that does not preempt requeues nothing: a stage. -/
theorem timerTickBudgetOnCore_runQueueStage_of_not_preempted {st : SystemState}
    {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId} {tcb : TCB} {hTcb : st.getTcb? tid = some tcb}
    {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickBudgetOnCore st c tid tcb hTcb = .ok r) (hP : r.2.1 = false) :
    RunQueueStage st r.1 := by
  unfold timerTickBudgetOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h; subst h; cases hP
    · rw [Except.ok.injEq] at h; subst h
      exact RunQueueStage.rewriteObject_tcb hTcb (fun _ => by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _)
  all_goals
    split at h
    · rename_i sc hSc _
      split at h
      · rw [Except.ok.injEq] at h; subst h; cases hP
      · rw [Except.ok.injEq] at h; subst h
        exact RunQueueStage.rewriteObject_schedContext hSc
          (SystemState.rewriteAdmissible_schedContext hSc _)
    · cases h

theorem timerTickChargeCurrentOnCore_runQueueStage_of_not_preempted {st : SystemState}
    {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}
    {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickChargeCurrentOnCore st c tid = .ok r) (hP : r.2.1 = false) :
    RunQueueStage st r.1 := by
  obtain ⟨_, _, hB⟩ := timerTickChargeCurrentOnCore_ok h
  exact timerTickBudgetOnCore_runQueueStage_of_not_preempted hB hP

theorem timerTickChargeCurrentOnCore_runQueueWindowStage {st : SystemState}
    {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}
    {r : SystemState × Bool × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickChargeCurrentOnCore st c tid = .ok r)
    (hCur : st.scheduler.currentOnCore c = some tid) : SystemState.RunQueueWindowStage (.preempt c) st r.1 := by
  obtain ⟨_, _, hB⟩ := timerTickChargeCurrentOnCore_ok h
  exact timerTickBudgetOnCore_runQueueWindowStage hB hCur

/-- The yield's charge: the slice end or the budget forfeit with the key hook,
each requeueing core `c`'s current thread. -/
theorem yieldChargeOnCore_runQueueWindowStage {st st' : SystemState} {c : Concurrency.CoreId}
    {tid : SeLe4n.ThreadId} (h : yieldChargeOnCore st c tid = .ok st')
    (hCur : st.scheduler.currentOnCore c = some tid) : SystemState.RunQueueWindowStage (.preempt c) st st' := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore_runQueueWindowStage st c tid tcb hTcb hCur
    all_goals
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore_runQueueWindowStage st c tid _ sc hSc _ hCur).trans
          ((markKeyChangeFor_runQueueStage _ _ _).window (.preempt c))
      · cases h

/-- The yield: the charge opens core `c`'s scheduling point, the reschedule
closes it — a kernel entry. -/
theorem yieldOnCore_runQueueEntryStage {st st' : SystemState} {c : Concurrency.CoreId}
    (h : yieldOnCore st c = .ok st') : SystemState.RunQueueEntryStage st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · rename_i tid hCur
    split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore_runQueueWindowStage hC hCur).dispatch
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

/-- A thread no core runs is no core's current thread. -/
private theorem currentNowhere_of_runningOnSomeCore_false {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runningOnSomeCore st tid = false) (c : Concurrency.CoreId) :
    st.scheduler.currentOnCore c ≠ some tid := by
  simp only [runningOnSomeCore, SeLe4n.Kernel.Concurrency.allCores, List.any_eq_false] at h
  intro hc
  have hcc := h c (List.mem_finRange c)
  rw [hc] at hcc
  simp at hcc

/-- One due replenishment: the refill and, for a runnable thread it makes
eligible and no core runs, the wake. -/
theorem processOneReplenishmentOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    RunQueueStage st (processOneReplenishmentOnCore st c scId now).1 := by
  have hRefill : RunQueueStage st (refillSchedContext st scId now) := by
    unfold refillSchedContext; exact RunQueueStage.updateSchedContext _ _ _
  unfold processOneReplenishmentOnCore
  dsimp only
  split
  · rename_i tid hW
    split
    · exact hRefill
    · rename_i hRun
      exact hRefill.trans (wakeThread_runQueueStage _ _ c
        (currentNowhere_of_runningOnSomeCore_false (Bool.eq_false_iff.mpr hRun))
        (replenishWakeTarget_runnable hW).activeAt)
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
charge, and the reschedule or the local reschedule decision.  A charge that
preempts opens core `c`'s scheduling point and the reschedule closes it, so the
tick is a kernel entry. -/
theorem timerTickOnCore_runQueueEntryStage {st : SystemState} {c : Concurrency.CoreId}
    {r : SystemState × List (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : timerTickOnCore st c = .ok r) : SystemState.RunQueueEntryStage st r.1 := by
  unfold timerTickOnCore at h
  dsimp only at h
  have hP : RunQueueStage st (processReplenishmentsDueOnCore
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer).1 :=
    (RunQueueStage.of_frame (st := st)
      (st' := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] })
      rfl rfl rfl).trans
      (processReplenishmentsDueOnCore_runQueueStage
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer)
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i hH
        rw [Except.ok.injEq] at h; subst h
        exact hP.entry.trans (handleRescheduleSgiOnCore_runQueueEntryStage hH)
    · rw [Except.ok.injEq] at h; subst h; exact hP.entry
  · rename_i tid hCur
    split at h
    · cases h
    · rename_i st2 pre sgis hC
      split at h
      · rename_i hPre
        split at h
        · cases h
        · rename_i hS
          rw [Except.ok.injEq] at h; subst h; subst hPre
          exact hP.entry.trans ((timerTickChargeCurrentOnCore_runQueueWindowStage hC hCur).dispatch
            (scheduleEffectiveOnCore_runQueueDispatchStage hS))
      · rename_i hPre
        have hC2 := hP.trans (timerTickChargeCurrentOnCore_runQueueStage_of_not_preempted hC
          (by simpa using hPre))
        split at h
        · split at h
          · cases h
          · rename_i hH
            rw [Except.ok.injEq] at h; subst h
            exact hC2.entry.trans (handleRescheduleSgiOnCore_runQueueEntryStage hH)
        · rw [Except.ok.injEq] at h; subst h; exact hC2.entry

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
write neither objects nor scheduler, the target thread is on no core and no run
queue (so its entry is empty) and no idle thread, and the replacement is fresh.
A kernel entry's step, not a stage: a destroyed thread is no longer runnable. -/
theorem lifecycleRetypeDirectWithCleanup_runQueueEntryStage {st st' : SystemState}
    {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  obtain ⟨-, currentObj, stClean, hObj, hClean, hStore⟩ :=
    lifecycleRetypeDirectWithCleanup_ok_decompose hStep
  have hFr : st.objects.invExt →
      (scrubObjectMemory stClean target currentObj.objectType).objects = st.objects ∧
      (scrubObjectMemory stClean target currentObj.objectType).scheduler = st.scheduler :=
    fun hInv => by
      obtain ⟨hCO, hCS, -⟩ := lifecyclePreRetypeCleanup_detached_frame st stClean target currentObj
        newObj hInv hObj hDet hClean
      exact ⟨(scrubObjectMemory_objects_eq stClean target currentObj.objectType).trans hCO,
        (scrubObjectMemory_scheduler_eq stClean target currentObj.objectType).trans hCS⟩
  have h1 : st.objects.invExt → RunQueueStage st (scrubObjectMemory stClean target currentObj.objectType) :=
    fun hInv => RunQueueStage.of_frame (hFr hInv).1 (by rw [(hFr hInv).2]) (by rw [(hFr hInv).2])
      (by rw [(hFr hInv).2])
  have hLk : st.objects.invExt → ∀ c, SystemState.objRunLinkOn (some newObj) c =
      SystemState.objRunLinkOn (scrubObjectMemory stClean target currentObj.objectType).objects[target]? c :=
    fun hInv c => by
      rw [objRunLinkOn_of_retypeReplacementFresh hFresh c, (hFr hInv).1, hObj]
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
  have hNew : ∀ y, SystemState.objTcb? (some newObj) = some y → y.Coherent := fun y hy => by
    cases newObj with
    | tcb t => cases hy; exact .inl hFresh.1
    | _ => cases hy
  refine ⟨fun hInv hR => ((h1 hInv).1.trans
    (SystemState.RunQueueLinkStage.storeObject hStore (hLk hInv))) hInv hR, fun hInv hR hR' d => ?_⟩
  obtain ⟨hInv1, hR1⟩ := (h1 hInv).1 hInv hR
  have d1 := (h1 hInv).2.1 none hInv hR hR1 d
  have hO : st'.objects = (scrubObjectMemory stClean target currentObj.objectType).objects.insert
      target newObj := by unfold SeLe4n.Model.storeObject at hStore; cases hStore; rfl
  have hC : st'.scheduler = (scrubObjectMemory stClean target currentObj.objectType).scheduler := by
    unfold SeLe4n.Model.storeObject at hStore; cases hStore; rfl
  cases hCur : currentObj with
  | tcb x =>
    subst hCur
    have hSS := (hFr hInv).2
    refine SystemState.currentDequeuedUniqueExcept_insert_offTcb hInv1 hO (by rw [hC])
      (SystemState.runLinkOn_insert hInv1 hO (hLk hInv)) (hDet.tcbSelfId x hObj) d1
      (fun c h => (hDet.tcbDescheduled x hObj c).2.2 (by
        unfold SchedulerState.currentOnCore at h ⊢; rw [hSS] at h; exact h))
      (fun c => ?_) (hDet.tcbNotIdle x hObj) hNew
    rw [SystemState.queuedOn_eq_runLinkOn, SystemState.runLinkOn_of_objects (hFr hInv).1,
      ← SystemState.queuedOn_eq_runLinkOn]
    exact (hDet.tcbDescheduled x hObj c).2.1
  | _ =>
    subst hCur
    refine (SystemState.RunQueueStage.storeObject hStore (hLk hInv) ⟨fun y hy => ?_,
      fun y hy _ => hNew y hy⟩).2.1 none hInv1 hR1 hR' d1
    rw [(hFr hInv).1, hObj] at hy; cases hy

/-- The shootdown form: the destroy path, then ASID rounds that write neither
objects nor scheduler. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_runQueueEntryStage {st st' : SystemState}
    {ec : Concurrency.CoreId} {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at hStep
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    simp only [hBase] at hStep
    rw [retypeShootdownAsids_eq] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    subst hStep
    exact (lifecycleRetypeDirectWithCleanup_runQueueEntryStage hFresh hDet hBase).trans
      (RunQueueStage.of_frame (retypeAsidRoundFold_objects ec _ stB)
        (by rw [retypeAsidRoundFold_scheduler]) (by rw [retypeAsidRoundFold_scheduler])
        (by rw [retypeAsidRoundFold_scheduler])).entry

theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_runQueueEntryStage {st st' : SystemState}
    {ec : Concurrency.CoreId} {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st =
      .ok ((), st')) : SystemState.RunQueueEntryStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at hStep
  cases hBase : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    simp only [hBase] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    subst hStep
    exact (lifecycleRetypeDirectWithCleanupShootdown_runQueueEntryStage hFresh hDet hBase).trans
      (RunQueueStage.of_frame (retypeInitiatorDrain_objects ec _ stB)
        (by rw [retypeInitiatorDrain_scheduler]) (by rw [retypeInitiatorDrain_scheduler])
        (by rw [retypeInitiatorDrain_scheduler])).entry

/-- The live `.lifecycleRetype` arm: the per-core destroy path under the
instruction-cache broadcast, which writes neither objects nor scheduler. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_runQueueEntryStage
    {st st' : SystemState} {ec : Concurrency.CoreId} {authCap : Capability}
    {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hFresh : retypeReplacementFresh newObj) (hDet : retypeTargetDetached st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache ec authCap target newObj st =
      .ok ((), st')) : SystemState.RunQueueEntryStage st st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at hStep
  cases hK : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
    contradiction
  | ok pair =>
    obtain ⟨u, stB⟩ := pair; cases u
    obtain ⟨hObjs, -, hSched, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
    exact (lifecycleRetypeDirectWithCleanupShootdownPerCore_runQueueEntryStage hFresh hDet hK).trans
      (RunQueueStage.of_frame hObjs (by rw [hSched]) (by rw [hSched])).entry

/-- The live `.untypedRetype` arm: the carve. -/
theorem untypedRetypeFromCap_runQueueStage {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (h : untypedRetypeFromCap tid srcAddr args? st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ :=
    untypedRetypeFromCap_ok tid srcAddr args? st st' h
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
