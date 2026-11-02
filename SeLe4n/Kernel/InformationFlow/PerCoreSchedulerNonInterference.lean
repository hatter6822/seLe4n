-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.NonInterferencePerCore
import SeLe4n.Kernel.InformationFlow.Invariant.FinaliseProjection
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
import SeLe4n.Kernel.ReschedulePendingArms.Tick
import SeLe4n.Kernel.SecondaryEntry
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.TimerContextMatches
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersDispatch
import SeLe4n.Kernel.SchedContext.YieldLinkInvariant
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingSchedulingPoints

/-!
# The per-core scheduler steps inside the non-interference step relation

WS-ZA ZA6.30.  The per-core step relation of `NonInterferencePerCore`
(`KernelOperation`, `kernelOperationPerCoreNiTheorem`) covers the single-core
`timerTick` and `handleYield`; the steps the per-core kernel runs in their place
had no low-equivalence theorem.  This module proves one for each:

* the per-core tick (`timerTickOnCore`), with its parts: the replenishment
  drain (`processReplenishmentsDueOnCore`), the charge
  (`timerTickBudgetOnCore`), the exhaustion (`budgetExhaustOnCore`) and the
  scheduling points it ends in (`scheduleEffectiveOnCoreState`,
  `handleRescheduleOnCoreState`);
* the yield's charge (`yieldChargeOnCore`) and the yield (`yieldOnCore`);
* the yieldTo invocation (`schedContextYieldToOnCore`), with its charge's
  consumed-time return;
* the activation at entry exit (`activateThreadOnCore`), on every core, and in
  its two-sided form for an observable yielder;
* the reschedule SGI (`handleRescheduleSgiOnCore`, `perCoreRescheduleStep`),
  the residency settle (`settleResidencyOnCore`, `deferResidentElsewhere`) and
  the reschedule entry's committed state, which is also the secondary core's
  entry (`secondaryKernelMain`).

Each theorem is one-sided, as the relation's other constructors are: the step
leaves every core's view unchanged when what it touches is hidden.  §9 adds the
steps to the per-core step relation (`PerCoreNonInterferenceStep`) and re-anchors
the coverage count over the extended taxonomy (`PerCoreOperation`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Composing low-equivalences
-- ============================================================================

section Basics

variable {ctx : LabelingContext} {observer : IfObserver}

/-- A thread the observer sees nothing of: neither its identity in the
scheduler's views nor its object. -/
def threadHidden (ctx : LabelingContext) (observer : IfObserver) (t : SeLe4n.ThreadId) : Prop :=
  threadObservable ctx observer t = false ∧ objectObservable ctx observer t.toObjId = false

theorem lowEquivalent_smp_refl (st : SystemState) : lowEquivalent_smp ctx observer st st :=
  fun _ => rfl

/-- Two steps each invisible on every core are one. -/
theorem lowEquivalent_smp_trans {a b d : SystemState}
    (h₂ : lowEquivalent_smp ctx observer d b) (h₁ : lowEquivalent_smp ctx observer b a) :
    lowEquivalent_smp ctx observer d a :=
  fun c => (h₂ c).trans (h₁ c)

/-- **Every core's view is read off its parts**: the shared fragment, and on
each core the filtered run queue, the projected current thread, the three
domain slots and the projected register bank. -/
theorem lowEquivalent_smp_of_views {st st' : SystemState}
    (hShared : sharedViewUnchanged ctx observer st st')
    (hRun : ∀ c, projectRunnableOnCore ctx observer st' c = projectRunnableOnCore ctx observer st c)
    (hCur : ∀ c, projectCurrentOnCore ctx observer st' c = projectCurrentOnCore ctx observer st c)
    (hAD : ∀ c, st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDTR : ∀ c, st'.scheduler.domainTimeRemainingOnCore c =
      st.scheduler.domainTimeRemainingOnCore c)
    (hDSI : ∀ c, st'.scheduler.domainScheduleIndexOnCore c =
      st.scheduler.domainScheduleIndexOnCore c)
    (hRegs : ∀ c, projectMachineRegsOnCore ctx observer st' c =
      projectMachineRegsOnCore ctx observer st c) :
    lowEquivalent_smp ctx observer st' st := by
  intro c
  refine ObservableState.ext_fragments ?_ ?_
  · simp only [projectStateOnCore_sharedFragment, SharedObservableFragment.mk.injEq]
    exact ⟨hShared.objects, hShared.irqHandlers, hShared.objectIndex,
      hShared.domainSchedule, hShared.memory⟩
  · simp only [projectStateOnCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    exact ⟨hRun c, hCur c, projectActiveDomainOnCore_frame _ _ (hAD c),
      projectDomainTimeRemainingOnCore_frame _ _ (hDTR c),
      projectDomainScheduleIndexOnCore_frame _ _ (hDSI c), hRegs c⟩

end Basics

-- ============================================================================
-- §2  The primitive writes
-- ============================================================================

section Primitives

variable {ctx : LabelingContext} {observer : IfObserver}

/-- A reschedule flag raised is no view's. -/
theorem markReschedulePendingOnCore_lowEquivalent (st : SystemState) (c : CoreId) :
    lowEquivalent_smp ctx observer (st.markReschedulePendingOnCore c) st := fun _ => rfl

/-- A reschedule flag cleared is no view's. -/
theorem clearReschedulePendingOnCore_lowEquivalent (st : SystemState) (c : CoreId) :
    lowEquivalent_smp ctx observer (st.clearReschedulePendingOnCore c) st := fun _ => rfl

/-- A conditional flag is no view's. -/
theorem markReschedulePendingOnCoreIf_lowEquivalent (st : SystemState) (c : CoreId) (b : Bool) :
    lowEquivalent_smp ctx observer
      { st with scheduler := st.scheduler.markReschedulePendingOnCoreIf c b } st := fun _ => rfl

/-- The timeout diagnostic is no view's. -/
theorem setLastTimeoutErrorsOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (v : List (SeLe4n.ThreadId × KernelError)) :
    lowEquivalent_smp ctx observer
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c v } st := fun _ => rfl

/-- The shared fragment from its parts: the projected store, and the index, the
IRQ table, memory and the domain schedule kept. -/
theorem sharedViewUnchanged_of_parts {st st' : SystemState}
    (hObj : projectObjects ctx observer st' = projectObjects ctx observer st)
    (hIndex : st'.objectIndex = st.objectIndex) (hIrq : st'.irqHandlers = st.irqHandlers)
    (hMemory : st'.machine.memory = st.machine.memory)
    (hDomSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    sharedViewUnchanged ctx observer st st' := by
  refine ⟨hObj, ?_, ?_, ?_, ?_⟩
  · funext irq; simp only [projectIrqHandlers]; rw [hIrq]
  · simp only [projectObjectIndex]; rw [hIndex]
  · simp only [projectDomainSchedule]; rw [hDomSched]
  · exact projectMemory_eq_of_memory_eq _ _ _ _ hMemory

/-- **A write to the objects and the scheduler alone** is invisible on every
core when the projected store, every core's filtered run queue, its current
slot, its three domain slots and the domain schedule are kept: the registers
are untouched. -/
theorem lowEquivalent_smp_of_objectsSchedulerWrite {st st' : SystemState}
    (hD : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hObj : projectObjects ctx observer st' = projectObjects ctx observer st)
    (hRun : ∀ c, projectRunnableOnCore ctx observer st' c = projectRunnableOnCore ctx observer st c)
    (hCur : ∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hAD : ∀ c, st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDTR : ∀ c, st'.scheduler.domainTimeRemainingOnCore c =
      st.scheduler.domainTimeRemainingOnCore c)
    (hDSI : ∀ c, st'.scheduler.domainScheduleIndexOnCore c =
      st.scheduler.domainScheduleIndexOnCore c)
    (hDS : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    lowEquivalent_smp ctx observer st' st := by
  have hM : st'.machine = st.machine := by rw [hD]
  have hI : st'.objectIndex = st.objectIndex := by rw [hD]
  have hQ : st'.irqHandlers = st.irqHandlers := by rw [hD]
  exact lowEquivalent_smp_of_views
    (sharedViewUnchanged_of_parts hObj hI hQ (by rw [hM]) hDS) hRun
    (fun c => projectCurrentOnCore_frame _ _ (hCur c)) hAD hDTR hDSI
    (fun c => projectMachineRegsOnCore_frame _ _ (hCur c) (by rw [hM]))

/-- A head insert of a thread the filter drops leaves the filtered order. -/
theorem RunQueue.toList_filter_insertHead_neg (rq : RunQueue) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (f : SeLe4n.ThreadId → Bool) (hf : f t = false) :
    (rq.insertHead t p).toList.filter f = rq.toList.filter f := by
  by_cases h : t ∈ rq
  · rw [RunQueue.insertHead_of_mem rq t p h]
  · rw [RunQueue.toList_insertHead_not_mem rq t p h, List.filter_cons, hf]
    rfl

/-- **A hidden thread's tail enqueue** is invisible on every core: its run
links and its neighbours' are erased by the projection, and the filtered queue
drops it. -/
theorem runEnqueueOnCore_lowEquivalent (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hT : threadObservable ctx observer t = false) :
    lowEquivalent_smp ctx observer (st.runEnqueueOnCore c t p) st := by
  have hS := SystemState.runEnqueueOnCore_scheduler st c t p
  refine lowEquivalent_smp_of_objectsSchedulerWrite
    (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p)
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro c'
    unfold projectRunnableOnCore
    by_cases hc : c = c'
    · subst hc
      by_cases hA : st.runEnqueueAdmits c t = true
      · rw [SystemState.runEnqueueOnCore_runQueueOnCore_self p hA]
        exact RunQueue.toList_filter_insert_neg' _ t p _ hT
      · rw [hS, if_neg hA]
    · rw [SystemState.runEnqueueOnCore_runQueueOnCore_ne st c c' t p hc]
  all_goals first
    | (intro c'; rw [hS]; split <;> rfl)
    | (rw [hS]; split <;> rfl)

/-- **A hidden thread's head enqueue** is invisible on every core. -/
theorem runEnqueueHeadOnCore_lowEquivalent (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hT : threadObservable ctx observer t = false) :
    lowEquivalent_smp ctx observer (st.runEnqueueHeadOnCore c t p) st := by
  have hS := SystemState.runEnqueueHeadOnCore_scheduler st c t p
  refine lowEquivalent_smp_of_objectsSchedulerWrite
    (SystemState.runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer st c t p)
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro c'
    unfold projectRunnableOnCore
    by_cases hc : c = c'
    · subst hc
      rw [hS]
      split
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.toList_filter_insertHead_neg _ t p _ hT
      · rfl
    · rw [SystemState.runEnqueueHeadOnCore_runQueueOnCore_ne st c c' t p hc]
  all_goals first
    | (intro c'; rw [hS]; split <;> rfl)
    | (rw [hS]; split <;> rfl)

/-- **A hidden thread's dequeue** is invisible on every core.  The current
slots are kept: the dequeue writes the queue alone. -/
theorem runRemoveOnCore_lowEquivalent (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hT : threadObservable ctx observer t = false) :
    lowEquivalent_smp ctx observer (st.runRemoveOnCore c t) st := by
  refine lowEquivalent_smp_of_objectsSchedulerWrite
    (SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c t)
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c t)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro c'
    unfold projectRunnableOnCore
    by_cases hc : c = c'
    · subst hc
      rw [SystemState.runRemoveOnCore_runQueueOnCore_self]
      exact RunQueue.toList_filter_remove_neg _ t _ hT
    · rw [SystemState.runRemoveOnCore_runQueueOnCore_ne st c c' t hc]
  · intro c'
    unfold SchedulerState.currentOnCore
    rw [SystemState.runRemoveOnCore_current]
  all_goals
    (try intro c'); unfold SystemState.runRemoveOnCore; dsimp only
    split <;> simp [SystemState.runUnlinkLinks_scheduler, SchedulerState.setRunQueueOnCore,
      SchedulerState.setRunQueueEndsOnCore, SchedulerState.activeDomainOnCore,
      SchedulerState.domainTimeRemainingOnCore, SchedulerState.domainScheduleIndexOnCore]

/-- **A write the observer sees nothing of** (`projectedObjectsWrite`) is
invisible on every core: only the store changes, and it projects as before. -/
theorem lowEquivalent_smp_of_projectedObjectsWrite {st st' : SystemState}
    (h : projectedObjectsWrite ctx observer st st') : lowEquivalent_smp ctx observer st' st := by
  intro c
  have e := h.1
  exact projectStateOnCore_congr ctx observer h.projection (by rw [e]) (by rw [e]) (by rw [e])
    (by rw [e]) (by rw [e]) (by rw [e])

/-- Core `c`'s current thread is hidden from the observer's views, or it has
none. -/
def currentHiddenOn (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop :=
  ∀ t, st.scheduler.currentOnCore c = some t → threadObservable ctx observer t = false

theorem projectCurrentOnCore_of_currentHiddenOn {st : SystemState} {c : CoreId}
    (h : currentHiddenOn ctx observer st c) : projectCurrentOnCore ctx observer st c = none := by
  unfold projectCurrentOnCore
  cases e : st.scheduler.currentOnCore c with
  | none => rfl
  | some t => simp [h t e]

theorem projectMachineRegsOnCore_of_currentHiddenOn {st : SystemState} {c : CoreId}
    (h : currentHiddenOn ctx observer st c) : projectMachineRegsOnCore ctx observer st c = none := by
  unfold projectMachineRegsOnCore
  cases e : st.scheduler.currentOnCore c with
  | none => rfl
  | some t => simp [h t e]

/-- **A register write on a core whose current thread is hidden** is invisible
on every core: that core's bank is shown only while its current thread is
observable, and every other bank is kept. -/
theorem lowEquivalent_smp_of_regsWrite {st st' : SystemState} (c : CoreId)
    (hSt : st' = { st with machine := st'.machine })
    (hMem : st'.machine.memory = st.machine.memory)
    (hRegs : ∀ d, d ≠ c → st'.machine.regsOnCore d = st.machine.regsOnCore d)
    (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer st' st := by
  have hO : st'.objects = st.objects := by rw [hSt]
  have hS : st'.scheduler = st.scheduler := by rw [hSt]
  have hI : st'.objectIndex = st.objectIndex := by rw [hSt]
  have hQ : st'.irqHandlers = st.irqHandlers := by rw [hSt]
  have hProjObj : projectObjects ctx observer st' = projectObjects ctx observer st := by
    unfold projectObjects SystemState.getObject?; rw [hO]
  refine lowEquivalent_smp_of_views
    (sharedViewUnchanged_of_parts hProjObj hI hQ hMem (by rw [hS]))
    (fun d => projectRunnableOnCore_frame _ _ (by rw [hS]))
    (fun d => projectCurrentOnCore_frame _ _ (by rw [hS]))
    (fun d => by rw [hS]) (fun d => by rw [hS]) (fun d => by rw [hS]) ?_
  intro d
  by_cases hd : d = c
  · subst hd
    have hC' : currentHiddenOn ctx observer st' d := fun t e => hCur t (by rw [← hS]; exact e)
    rw [projectMachineRegsOnCore_of_currentHiddenOn hC',
      projectMachineRegsOnCore_of_currentHiddenOn hCur]
  · exact projectMachineRegsOnCore_frame _ _ (by rw [hS]) (hRegs d hd)

/-- A bank written on a core whose current thread is hidden. -/
theorem setRegsOnCore_lowEquivalent (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile)
    (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer { st with machine := st.machine.setRegsOnCore c rf } st :=
  lowEquivalent_smp_of_regsWrite c rfl (MachineState.setRegsOnCore_memory _ _ _)
    (fun _ hd => MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ (Ne.symm hd)) hCur

/-- **The incoming thread's context restored** on a core whose current thread
is hidden. -/
theorem restoreIncomingContextOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (restoreIncomingContextOnCore st c t) st := by
  unfold restoreIncomingContextOnCore
  split
  · exact setRegsOnCore_lowEquivalent st c _ hCur
  · exact lowEquivalent_smp_refl st

/-- The restore, skipped on a self-switch. -/
theorem restoreIncomingContextOnCoreUnlessCurrent_lowEquivalent (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (restoreIncomingContextOnCoreUnlessCurrent st c t) st := by
  unfold restoreIncomingContextOnCoreUnlessCurrent
  split
  · exact lowEquivalent_smp_refl st
  · exact restoreIncomingContextOnCore_lowEquivalent st c t hCur

/-- **A current slot rewritten from a hidden thread (or none) to a hidden
thread (or none)** is invisible on every core: the slot and the bank it gates
project as none before and after. -/
theorem lowEquivalent_smp_of_currentWrite {st st' : SystemState} (c : CoreId)
    (hSt : st' = { st with scheduler := st'.scheduler })
    (hRQ : ∀ d, st'.scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d)
    (hCurNe : ∀ d, d ≠ c → st'.scheduler.currentOnCore d = st.scheduler.currentOnCore d)
    (hAD : ∀ d, st'.scheduler.activeDomainOnCore d = st.scheduler.activeDomainOnCore d)
    (hDTR : ∀ d, st'.scheduler.domainTimeRemainingOnCore d =
      st.scheduler.domainTimeRemainingOnCore d)
    (hDSI : ∀ d, st'.scheduler.domainScheduleIndexOnCore d =
      st.scheduler.domainScheduleIndexOnCore d)
    (hDS : st'.scheduler.domainSchedule = st.scheduler.domainSchedule)
    (hOld : currentHiddenOn ctx observer st c) (hNew : currentHiddenOn ctx observer st' c) :
    lowEquivalent_smp ctx observer st' st := by
  have hO : st'.objects = st.objects := by rw [hSt]
  have hM : st'.machine = st.machine := by rw [hSt]
  have hI : st'.objectIndex = st.objectIndex := by rw [hSt]
  have hQ : st'.irqHandlers = st.irqHandlers := by rw [hSt]
  have hProjObj : projectObjects ctx observer st' = projectObjects ctx observer st := by
    unfold projectObjects SystemState.getObject?; rw [hO]
  refine lowEquivalent_smp_of_views
    (sharedViewUnchanged_of_parts hProjObj hI hQ (by rw [hM]) hDS)
    (fun d => projectRunnableOnCore_frame _ _ (hRQ d)) ?_ hAD hDTR hDSI ?_
  · intro d
    by_cases hd : d = c
    · subst hd
      rw [projectCurrentOnCore_of_currentHiddenOn hNew, projectCurrentOnCore_of_currentHiddenOn hOld]
    · exact projectCurrentOnCore_frame _ _ (hCurNe d hd)
  · intro d
    by_cases hd : d = c
    · subst hd
      rw [projectMachineRegsOnCore_of_currentHiddenOn hNew,
        projectMachineRegsOnCore_of_currentHiddenOn hOld]
    · exact projectMachineRegsOnCore_frame _ _ (hCurNe d hd) (by rw [hM])

/-- Core `c`'s current slot set, from and to hidden threads (or none). -/
theorem setCurrentOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (v : Option SeLe4n.ThreadId) (hOld : currentHiddenOn ctx observer st c)
    (hNew : ∀ t, v = some t → threadObservable ctx observer t = false) :
    lowEquivalent_smp ctx observer { st with scheduler := st.scheduler.setCurrentOnCore c v } st :=
  lowEquivalent_smp_of_currentWrite c rfl (fun _ => rfl)
    (fun d hd => SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hd))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl hOld
    (fun t e => hNew t (by rw [← e]; exact (SchedulerState.setCurrentOnCore_currentOnCore_self _ _ _).symm))

end Primitives

-- ============================================================================
-- §3  The scheduling points
-- ============================================================================

section SchedulingPoints

variable {ctx : LabelingContext} {observer : IfObserver}

/-- Every thread on core `c`'s run queue is hidden from the observer's views. -/
def queueHiddenOn (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop :=
  ∀ t, t ∈ st.scheduler.runQueueOnCore c → threadObservable ctx observer t = false

/-- **What a scheduling point on core `c` reads, hidden**: the threads it can
choose (core `c`'s run queue, its idle thread) and the one it can take off the
core (its current thread).  With the store's table invariant and core `c`'s
queue in agreement with the links, by which the chosen thread is queued. -/
structure schedulingPointHidden (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) : Prop where
  objects : st.objects.invExt
  refined : st.runQueueRefinedOnCore c
  queue : queueHiddenOn ctx observer st c
  current : currentHiddenOn ctx observer st c
  idle : threadObservable ctx observer (Kernel.idleThreadId c) = false

/-- **The outgoing context saved** is invisible on every core: it writes the
saved register file the projection erases. -/
theorem saveOutgoingContextOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (saveOutgoingContextOnCore st c) st := by
  unfold saveOutgoingContextOnCore
  split
  · exact lowEquivalent_smp_refl st
  · exact lowEquivalent_smp_of_projectedObjectsWrite
      (projectedObjectsWrite.updateTcb _ _ _ hInv (fun _ => rfl))

/-- **A hidden current thread preempted back onto its queue** is invisible on
every core: its saved registers are erased, and the queue's filter drops it. -/
theorem preemptCurrentOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (preemptCurrentOnCore st c incoming) st := by
  rw [preemptCurrentOnCore_eq_impl]
  unfold preemptCurrentOnCoreImpl
  split
  · exact lowEquivalent_smp_refl st
  · rename_i prev hC
    split
    · exact lowEquivalent_smp_refl st
    · split
      · exact lowEquivalent_smp_trans
          (runEnqueueOnCore_lowEquivalent _ c prev _ (hCur prev hC))
          (lowEquivalent_smp_of_projectedObjectsWrite
            (projectedObjectsWrite.updateTcb _ _ _ hInv (fun _ => rfl)))
      · exact lowEquivalent_smp_refl st

/-- **A hidden current thread dropped** — preempted, the slot cleared. -/
theorem dropCurrentOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (dropCurrentOnCore st c) st := by
  unfold dropCurrentOnCore
  have hP := preemptCurrentOnCore_lowEquivalent (ctx := ctx) (observer := observer) st c
    (Kernel.idleThreadId c) hInv hCur
  refine lowEquivalent_smp_trans (setCurrentOnCore_lowEquivalent _ c none ?_ ?_) hP
  · intro t e
    rw [preemptCurrentOnCore_currentOnCore] at e
    exact hCur t e
  · intro t e; cases e

theorem currentHiddenOn_of_currentCode {st st' : SystemState} {c : CoreId}
    (e : st'.scheduler.currentCode = st.scheduler.currentCode)
    (h : currentHiddenOn ctx observer st c) : currentHiddenOn ctx observer st' c := by
  intro t ht
  unfold SchedulerState.currentOnCore at ht
  rw [e] at ht
  exact h t ht

/-- **The idle fallback** on a core whose current thread and idle thread are
hidden. -/
theorem idleFallbackOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (hCur : currentHiddenOn ctx observer st c)
    (hIdle : threadObservable ctx observer (Kernel.idleThreadId c) = false) :
    lowEquivalent_smp ctx observer (idleFallbackOnCore st c) st := by
  unfold idleFallbackOnCore
  split
  · unfold dispatchIdleOnCore
    have hDeq := runRemoveOnCore_lowEquivalent (ctx := ctx) (observer := observer) st c _ hIdle
    have hCurDeq : currentHiddenOn ctx observer (st.runRemoveOnCore c (Kernel.idleThreadId c)) c :=
      currentHiddenOn_of_currentCode (SystemState.runRemoveOnCore_current _ _ _) hCur
    have hRes := restoreIncomingContextOnCore_lowEquivalent (ctx := ctx) (observer := observer)
      _ c (Kernel.idleThreadId c) hCurDeq
    refine lowEquivalent_smp_trans (setCurrentOnCore_lowEquivalent _ c _ ?_ ?_)
      (lowEquivalent_smp_trans hRes hDeq)
    · intro t e
      rw [restoreIncomingContextOnCore_scheduler] at e
      exact hCurDeq t e
    · intro t e; cases e; exact hIdle
  · exact setCurrentOnCore_lowEquivalent st c none hCur (fun _ e => by cases e)

/-- **`scheduleEffectiveOnCoreState` is invisible on every core** when what it
reads is hidden (`schedulingPointHidden`): the outgoing context's save is
erased, the thread it chooses is queued on core `c` and so hidden, and the
current slot and the bank go from a hidden thread to a hidden thread. -/
theorem scheduleEffectiveOnCoreState_lowEquivalent (st : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (scheduleEffectiveOnCoreState st c) st := by
  have hSave := saveOutgoingContextOnCore_lowEquivalent (ctx := ctx) (observer := observer)
    st c h.objects
  have hCurSave : currentHiddenOn ctx observer (saveOutgoingContextOnCore st c) c :=
    currentHiddenOn_of_currentCode (by rw [saveOutgoingContextOnCore_scheduler]) h.current
  unfold scheduleEffectiveOnCoreState
  split
  · exact lowEquivalent_smp_trans (clearReschedulePendingOnCore_lowEquivalent _ c)
      (lowEquivalent_smp_trans (idleFallbackOnCore_lowEquivalent _ c hCurSave h.idle) hSave)
  · rename_i k hk
    have hMem : (⟨k⟩ : SeLe4n.ThreadId) ∈ st.scheduler.runQueueOnCore c := by
      have hc := chooseThreadEffectiveOnCore_eq_code st c
      rw [hk] at hc
      exact (RunQueue.mem_toList_iff_mem _ _).mp
        (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c _ h.refined hc)
    have hT := h.queue _ hMem
    have hDeq := runRemoveOnCore_lowEquivalent (ctx := ctx) (observer := observer)
      (saveOutgoingContextOnCore st c) c _ hT
    have hCurDeq : currentHiddenOn ctx observer
        ((saveOutgoingContextOnCore st c).runRemoveOnCore c ⟨k⟩) c :=
      currentHiddenOn_of_currentCode (SystemState.runRemoveOnCore_current _ _ _) hCurSave
    have hRes := restoreIncomingContextOnCore_lowEquivalent (ctx := ctx) (observer := observer)
      _ c ⟨k⟩ hCurDeq
    refine lowEquivalent_smp_trans (setCurrentOnCore_lowEquivalent _ c (some ⟨k⟩) ?_ ?_)
      (lowEquivalent_smp_trans hRes (lowEquivalent_smp_trans hDeq hSave))
    · intro t e
      rw [restoreIncomingContextOnCore_scheduler] at e
      exact hCurDeq t e
    · intro t e; cases e; exact hT

/-- Core `c`'s decision with nothing to dispatch: an out-of-domain incumbent
dropped, the flag cleared. -/
theorem rescheduleNoCandidateOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (rescheduleNoCandidateOnCore st c) st := by
  unfold rescheduleNoCandidateOnCore
  split
  · exact lowEquivalent_smp_trans (clearReschedulePendingOnCore_lowEquivalent _ c)
      (dropCurrentOnCore_lowEquivalent st c hInv hCur)
  · exact clearReschedulePendingOnCore_lowEquivalent st c

/-- **Core `c`'s reschedule decision (`handleRescheduleOnCoreState`) is
invisible on every core** when what it reads is hidden: the candidate is queued
on core `c`, the incumbent it preempts is core `c`'s current thread. -/
theorem handleRescheduleOnCoreState_lowEquivalent (st : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (handleRescheduleOnCoreState st c) st := by
  unfold handleRescheduleOnCoreState
  split
  · exact rescheduleNoCandidateOnCore_lowEquivalent st c h.objects h.current
  · rename_i k hk
    have hMem : (⟨k⟩ : SeLe4n.ThreadId) ∈ st.scheduler.runQueueOnCore c := by
      have hc := chooseThreadEffectiveOnCore_eq_code st c
      rw [hk] at hc
      exact (RunQueue.mem_toList_iff_mem _ _).mp
        (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c _ h.refined hc)
    have hT := h.queue _ hMem
    dsimp only
    split
    · split
      · split
        · have hP := preemptCurrentOnCore_lowEquivalent (ctx := ctx) (observer := observer)
            st c ⟨k⟩ h.objects h.current
          have hCurP : currentHiddenOn ctx observer (preemptCurrentOnCore st c ⟨k⟩) c :=
            fun t e => h.current t (by rw [preemptCurrentOnCore_currentOnCore] at e; exact e)
          have hDeq := runRemoveOnCore_lowEquivalent (ctx := ctx) (observer := observer)
            (preemptCurrentOnCore st c ⟨k⟩) c _ hT
          have hCurDeq : currentHiddenOn ctx observer
              ((preemptCurrentOnCore st c ⟨k⟩).runRemoveOnCore c ⟨k⟩) c :=
            currentHiddenOn_of_currentCode (SystemState.runRemoveOnCore_current _ _ _) hCurP
          have hRes := restoreIncomingContextOnCoreUnlessCurrent_lowEquivalent
            (ctx := ctx) (observer := observer) _ c ⟨k⟩ hCurDeq
          refine lowEquivalent_smp_trans (setCurrentOnCore_lowEquivalent _ c (some ⟨k⟩) ?_ ?_)
            (lowEquivalent_smp_trans hRes (lowEquivalent_smp_trans hDeq hP))
          · intro t e
            rw [restoreIncomingContextOnCoreUnlessCurrent_scheduler] at e
            exact hCurDeq t e
          · intro t e; cases e; exact hT
        · exact rescheduleNoCandidateOnCore_lowEquivalent st c h.objects h.current
      · exact rescheduleNoCandidateOnCore_lowEquivalent st c h.objects h.current
    · exact clearReschedulePendingOnCore_lowEquivalent st c

/-- The reschedule SGI's handler, in its `Except` form. -/
theorem handleRescheduleSgiOnCore_lowEquivalent (st st' : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c)
    (hStep : handleRescheduleSgiOnCore st c = .ok st') :
    lowEquivalent_smp ctx observer st' st := by
  rw [handleRescheduleSgiOnCore_eq_state] at hStep
  cases hStep
  exact handleRescheduleOnCoreState_lowEquivalent st c h

/-- The tick's local decision: the reschedule when core `c`'s flag is up. -/
theorem rescheduleIfPendingOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (rescheduleIfPendingOnCore st c) st :=
  rescheduleIfPendingOnCore_of (P := fun s => lowEquivalent_smp ctx observer s st) st c
    (lowEquivalent_smp_refl st) (handleRescheduleOnCoreState_lowEquivalent st c h)

/-- **The reschedule run-loop step** (`perCoreRescheduleStep`), which is also
the secondary core's bring-up: core `c`'s reschedule decision, the identity on a
raw id that names no core. -/
theorem perCoreRescheduleStep_lowEquivalent (st : SystemState) (coreId : UInt64)
    (h : ∀ hc : coreId.toNat < Concurrency.numCores,
      schedulingPointHidden ctx observer st ⟨coreId.toNat, hc⟩) :
    lowEquivalent_smp ctx observer (perCoreRescheduleStep st coreId) st := by
  rw [perCoreRescheduleStep_eq_impl]
  unfold perCoreRescheduleStepImpl
  split
  · rename_i hc
    exact handleRescheduleOnCoreState_lowEquivalent st _ (h hc)
  · exact lowEquivalent_smp_refl st

end SchedulingPoints

-- ============================================================================
-- §4  The release-queue edits
-- ============================================================================

section ReleaseEdits

variable {ctx : LabelingContext} {observer : IfObserver}

/-- **A release edit of a hidden context is invisible on every core**: it
writes the store at that context and its neighbours' successor links, and the
scheduler's release slots, which no view reads. -/
theorem lowEquivalent_smp_of_releaseEdit {s : SeLe4n.SchedContextId} {st st' : SystemState}
    (hW : SystemState.releaseOnlyWrite st' st) (hA : releaseWriteAt s st' st)
    (hS : objectObservable ctx observer s.toObjId = false) :
    lowEquivalent_smp ctx observer st' st :=
  lowEquivalent_smp_of_objectsSchedulerWrite hW.1 (projectObjects_of_releaseWriteAt ctx observer hA hS)
    (fun c => projectRunnableOnCore_frame _ _ (hW.runQueueOnCore c)) hW.currentOnCore
    hW.activeDomainOnCore hW.domainTimeRemainingOnCore hW.domainScheduleIndexOnCore
    (by rw [hW.2])

theorem releasePlace_lowEquivalent (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hS : objectObservable ctx observer s.toObjId = false) :
    lowEquivalent_smp ctx observer (st.releasePlace c s) st :=
  lowEquivalent_smp_of_releaseEdit (SystemState.releasePlace_releaseOnlyWrite st c s)
    (releaseWriteAt.releasePlace st c s) hS

theorem replenishOnCore_lowEquivalent (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hS : objectObservable ctx observer s.toObjId = false) :
    lowEquivalent_smp ctx observer (replenishOnCore st c s) st :=
  releasePlace_lowEquivalent st c s hS

end ReleaseEdits

/-! ## §5 The drain

A pass of the drain refills the context at the core's release-queue head, may
wake its bound thread, raises flags and places the context again.  It is
invisible when every context on the core's release queue is hidden and binds a
hidden thread, which the pass keeps: it re-places only the context it took. -/

section Drain

variable {ctx : LabelingContext} {observer : IfObserver}

/-- A key hook raises reschedule flags only. -/
theorem markKeyChangeFor_lowEquivalent (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    lowEquivalent_smp ctx observer (markKeyChangeFor st tid k) st :=
  fun d => markKeyChangeFor_extract_frame (fun s => projectStateOnCore ctx observer s d) st tid k
    (fun _ _ => rfl)

/-- The refill's key hook raises reschedule flags only. -/
theorem markRefillKeyChange_lowEquivalent (pre post : SystemState) (scId : SeLe4n.SchedContextId) :
    lowEquivalent_smp ctx observer (markRefillKeyChange pre post scId) post :=
  fun d => markRefillKeyChange_extract_frame (fun s => projectStateOnCore ctx observer s d) pre post
    scId (fun _ _ => rfl)

/-- **A refill of a hidden context** is invisible: it rewrites that context alone. -/
theorem refillSchedContext_lowEquivalent (st : SystemState) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hInv : st.objects.invExt) (hS : objectObservable ctx observer scId.toObjId = false) :
    lowEquivalent_smp ctx observer (refillSchedContext st scId now) st :=
  lowEquivalent_smp_of_projectedObjectsWrite
    (projectedObjectsWrite.of_hidden (hiddenObjectsWrite.updateSchedContext st scId _ hInv hS))

/-- **A wake of a hidden thread** is invisible on every core. -/
theorem wakeThread_lowEquivalent (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hT : threadHidden ctx observer tid) (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (wakeThread st tid c).1 st :=
  fun d => wakeThread_preserves_projectionOnCore ctx observer st tid c d hT.1 hT.2 hInv

/-- The wake's target is the refilled context's bound thread. -/
theorem replenishWakeTarget_boundThread {pre refilled : SystemState} {scId : SeLe4n.SchedContextId}
    {tid : SeLe4n.ThreadId} (h : replenishWakeTarget pre refilled scId = some tid) :
    ∃ sc, refilled.getSchedContext? scId = some sc ∧ sc.boundThread = some tid := by
  unfold replenishWakeTarget at h
  dsimp only at h
  cases hsc : refilled.getSchedContext? scId with
  | none => rw [hsc] at h; cases h
  | some sc =>
    refine ⟨sc, rfl, ?_⟩
    simp only [hsc] at h
    split at h <;> (split at h <;> first | exact Option.eq_some_of_filter_eq_some h | cases h)

/-- A context's bound thread is hidden, as is the context. -/
def contextHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (scId : SeLe4n.SchedContextId) : Prop :=
  objectObservable ctx observer scId.toObjId = false ∧
    ∀ sc t, st.getSchedContext? scId = some sc → sc.boundThread = some t → threadHidden ctx observer t

/-- **A refill and its wake** are invisible when the context and its bound thread
are hidden. -/
theorem refillWakeOnCore_lowEquivalent (st : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (hH : contextHidden ctx observer st scId) :
    lowEquivalent_smp ctx observer (refillWakeOnCore st c scId now) st := by
  have hR := refillSchedContext_lowEquivalent (ctx := ctx) (observer := observer) st scId now hInv hH.1
  have hRI := refillSchedContext_preserves_objects_invExt st scId now hInv
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i tid htgt
    split
    · exact hR
    · obtain ⟨sc, hsc, hb⟩ := replenishWakeTarget_boundThread htgt
      have hBT := refillSchedContext_boundThread st scId now hInv scId
      rw [hsc] at hBT
      cases hst : st.getSchedContext? scId with
      | none => rw [hst] at hBT; cases hBT
      | some sc0 =>
        rw [hst] at hBT
        have e : sc0.boundThread = some tid := by
          have := Option.some.inj hBT; simp only at this; rw [← this]; exact hb
        exact lowEquivalent_smp_trans
          (lowEquivalent_smp_trans (markReschedulePendingOnCoreIf_lowEquivalent _ _ _)
            (wakeThread_lowEquivalent _ tid c (hH.2 sc0 tid hst e) hRI)) hR
  · exact hR

theorem processOneReplenishmentOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (hH : contextHidden ctx observer st scId) :
    lowEquivalent_smp ctx observer (processOneReplenishmentOnCore st c scId now) st :=
  lowEquivalent_smp_trans (markRefillKeyChange_lowEquivalent _ _ _)
    (refillWakeOnCore_lowEquivalent st c scId now hInv hH)

/-- **Every context on core `c`'s release queue is hidden and binds a hidden
thread** — what the drain's passes read. -/
def releaseHiddenOn (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop :=
  ∀ s sc, st.getSchedContext? s = some sc → sc.releaseCoreCode = c.val + 1 →
    objectObservable ctx observer s.toObjId = false ∧
      ∀ t, sc.boundThread = some t → threadHidden ctx observer t

/-- A queued context of a hidden release queue is hidden. -/
theorem contextHidden_of_releaseQueuedOn {st : SystemState} {c : CoreId}
    {s : SeLe4n.SchedContextId} (hRH : releaseHiddenOn ctx observer st c)
    (hq : st.releaseQueuedOn c s = true) : contextHidden ctx observer st s := by
  unfold SystemState.releaseQueuedOn at hq
  cases hsc : st.getSchedContext? s with
  | none => rw [hsc] at hq; cases hq
  | some sc =>
    rw [hsc] at hq
    have hcode : sc.releaseCoreCode = c.val + 1 := by simpa using hq
    refine ⟨(hRH s sc hsc hcode).1, fun sc' t hsc' hb => ?_⟩
    rw [hsc] at hsc'
    cases hsc'
    exact (hRH s sc hsc hcode).2 t hb

/-- Off the edited context, a release edit keeps every context up to its
successor link. -/
theorem releaseWriteAt.getSchedContext? {s x : SeLe4n.SchedContextId} {st st' : SystemState}
    (h : releaseWriteAt s st' st) (hx : x ≠ s) :
    (st'.getSchedContext? x).map SchedContext.withoutReleaseNext =
      (st.getSchedContext? x).map SchedContext.withoutReleaseNext := by
  have e := h x.toObjId (fun e => hx (SeLe4n.SchedContextId.toObjId_injective _ _ e))
  unfold SystemState.getSchedContext?
  cases h1 : st'.objects[x.toObjId]? with
  | none =>
    cases h2 : st.objects[x.toObjId]? with
    | none => rfl
    | some o => rw [h1, h2] at e; cases e
  | some o' =>
    cases h2 : st.objects[x.toObjId]? with
    | none => rw [h1, h2] at e; cases e
    | some o =>
      rw [h1, h2] at e
      have e' := Option.some.inj e
      cases o' <;> cases o <;> simp_all [KernelObject.withoutReleaseNext]

/-- **A pass keeps the release queue hidden**: it places again only the context
it took, which was queued and so hidden, and it keeps every other context's
release core and bound thread. -/
theorem releaseHiddenOn_pass (s : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : s.objects.invExt) (hRH : releaseHiddenOn ctx observer s c)
    (hq : s.releaseQueuedOn c scId = true) :
    releaseHiddenOn ctx observer
      ((processOneReplenishmentOnCore s c scId now).releasePlace c scId) c := by
  intro x sc' hx hcode
  by_cases hxs : x = scId
  · subst hxs
    have hH := contextHidden_of_releaseQueuedOn hRH hq
    refine ⟨hH.1, fun t hb => ?_⟩
    have hB1 := replenishOnCore_boundThread (processOneReplenishmentOnCore s c x now) c x x
    have hB2 := processOneReplenishmentOnCore_boundThread s c x now hInv x
    unfold replenishOnCore at hB1
    rw [hx] at hB1
    rw [hB2] at hB1
    cases hsc : s.getSchedContext? x with
    | none => rw [hsc] at hB1; cases hB1
    | some sc =>
      rw [hsc] at hB1
      have e : sc.boundThread = some t := by
        have := Option.some.inj hB1; simp only at this; rw [← this]; exact hb
      exact hH.2 sc t hsc e
  · have e1 := releaseWriteAt.getSchedContext?
      (releaseWriteAt.releasePlace (processOneReplenishmentOnCore s c scId now) c scId) hxs
    rw [processOneReplenishmentOnCore_getSchedContext? s c scId now hInv x] at e1
    unfold refillSchedContext at e1
    rw [SystemState.updateSchedContext_getSchedContext?_ne _ _ _ hInv x
      (fun e => hxs (SeLe4n.SchedContextId.toObjId_injective _ _ e).symm), hx] at e1
    cases hsc : s.getSchedContext? x with
    | none => rw [hsc] at e1; cases e1
    | some sc =>
      rw [hsc] at e1
      have e := Option.some.inj e1
      have hc : sc.releaseCoreCode = c.val + 1 := by
        rw [← hcode]; exact (congrArg SchedContext.releaseCoreCode e).symm
      have hb : sc.boundThread = sc'.boundThread :=
        (congrArg SchedContext.boundThread e).symm
      exact ⟨(hRH x sc hsc hc).1, fun t ht => (hRH x sc hsc hc).2 t (hb.trans ht)⟩

/-- A hidden queue stays hidden under an enqueue of a hidden thread, on every
core. -/
theorem queueHiddenOn_enqueueRunnableOnCore {st : SystemState} {cc d : CoreId}
    {tid : SeLe4n.ThreadId} (hT : threadObservable ctx observer tid = false)
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (enqueueRunnableOnCore st cc tid) d := by
  intro x hx
  rcases enqueueRunnableOnCore_scheduler_cases st cc tid with h | ⟨E, p, h⟩ <;> rw [h] at hx
  · exact hQ x hx
  · rw [SchedulerState.markReschedulePendingOnCore_runQueueOnCore] at hx
    by_cases hcc : d = cc
    · subst hcc
      rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hx
      rcases (RunQueue.mem_insert _ _ _ _).mp hx with hm | e
      · exact hQ x hm
      · rw [e]; exact hT
    · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hcc),
        SchedulerState.setRunQueueEndsOnCore_runQueueOnCore] at hx
      exact hQ x hx

theorem queueHiddenOn_of_runQueueOnCore_eq {st st' : SystemState} {d : CoreId}
    (e : st'.scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d)
    (hQ : queueHiddenOn ctx observer st d) : queueHiddenOn ctx observer st' d :=
  fun x hx => hQ x (e ▸ hx)

/-- **A replenishment keeps every hidden queue hidden**: the only thread it
queues is the context's bound thread. -/
theorem queueHiddenOn_processOneReplenishmentOnCore (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (d : CoreId) (hInv : st.objects.invExt)
    (hH : contextHidden ctx observer st scId) (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (processOneReplenishmentOnCore st c scId now) d := by
  unfold processOneReplenishmentOnCore
  refine queueHiddenOn_of_runQueueOnCore_eq (markRefillKeyChange_runQueueOnCore _ _ _ d) ?_
  have hQR : queueHiddenOn ctx observer (refillSchedContext st scId now) d :=
    queueHiddenOn_of_runQueueOnCore_eq (by rw [refillSchedContext_scheduler_eq]) hQ
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i tid htgt
    split
    · exact hQR
    · obtain ⟨sc, hsc, hb⟩ := replenishWakeTarget_boundThread htgt
      have hBT := refillSchedContext_boundThread st scId now hInv scId
      rw [hsc] at hBT
      cases hst : st.getSchedContext? scId with
      | none => rw [hst] at hBT; cases hBT
      | some sc0 =>
        rw [hst] at hBT
        have e : sc0.boundThread = some tid := by
          have := Option.some.inj hBT; simp only at this; rw [← this]; exact hb
        refine queueHiddenOn_of_runQueueOnCore_eq
          (SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore _ _ _ _) ?_
        show queueHiddenOn ctx observer (wakeThread _ tid c).1 d
        rw [wakeThread_state_eq_enqueue]
        exact queueHiddenOn_enqueueRunnableOnCore (hH.2 sc0 tid hst e).1 hQR
  · exact hQR

/-- What the drain keeps of core `c` and core `d`'s views. -/
def drainHidden (ctx : LabelingContext) (observer : IfObserver) (st0 : SystemState) (c d : CoreId)
    (s : SystemState) : Prop :=
  lowEquivalent_smp ctx observer s st0 ∧ s.objects.invExt ∧ s.releaseQueueRefined ∧
    releaseHiddenOn ctx observer s c ∧ queueHiddenOn ctx observer s d

/-- **The drain is invisible on every core**, and keeps every hidden queue
hidden, when core `c`'s release queue is hidden. -/
theorem processReplenishmentsDueOnCore_drainHidden (st : SystemState) (c d : CoreId) (now : Nat)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hRH : releaseHiddenOn ctx observer st c) (hQ : queueHiddenOn ctx observer st d) :
    drainHidden ctx observer st c d (processReplenishmentsDueOnCore st c now) := by
  unfold processReplenishmentsDueOnCore
  refine drainDueOnCore_induction_pass (drainHidden ctx observer st c d) c now ?_ _ st
    ⟨lowEquivalent_smp_refl st, hInv, hRef, hRH, hQ⟩
  rintro s scId ⟨hL, hI, hR, hRHs, hQs⟩ h0 hId
  have hmem := releaseHead_mem (hR c) h0
  rw [hId] at hmem
  have hq : s.releaseQueuedOn c scId = true := ((hR c).queued scId).mpr hmem
  have hH := contextHidden_of_releaseQueuedOn hRHs hq
  have hI1 := processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI
  refine ⟨lowEquivalent_smp_trans (releasePlace_lowEquivalent _ c scId hH.1)
      (lowEquivalent_smp_trans (processOneReplenishmentOnCore_lowEquivalent s c scId now hI hH) hL),
    SystemState.releasePlace_objects_invExt _ c scId hI1,
    SystemState.releasePlace_refined
      ((processOneReplenishmentOnCore_releaseStateAgree s c scId now hI).refined hR) c scId,
    releaseHiddenOn_pass s c scId now hI hRHs hq,
    queueHiddenOn_of_runQueueOnCore_eq
      ((SystemState.releasePlace_releaseOnlyWrite _ c scId).runQueueOnCore d)
      (queueHiddenOn_processOneReplenishmentOnCore s c scId now d hI hH hQs)⟩

theorem processReplenishmentsDueOnCore_lowEquivalent (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hRH : releaseHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (processReplenishmentsDueOnCore st c now) st := by
  exact (drainDueOnCore_induction_pass
    (fun s => lowEquivalent_smp ctx observer s st ∧ s.objects.invExt ∧ s.releaseQueueRefined ∧
      releaseHiddenOn ctx observer s c) c now
    (fun s scId ⟨hL, hI, hR, hRHs⟩ h0 hId => by
      have hmem := releaseHead_mem (hR c) h0
      rw [hId] at hmem
      have hq : s.releaseQueuedOn c scId = true := ((hR c).queued scId).mpr hmem
      have hH := contextHidden_of_releaseQueuedOn hRHs hq
      have hI1 := processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI
      exact ⟨lowEquivalent_smp_trans (releasePlace_lowEquivalent _ c scId hH.1)
          (lowEquivalent_smp_trans (processOneReplenishmentOnCore_lowEquivalent s c scId now hI hH) hL),
        SystemState.releasePlace_objects_invExt _ c scId hI1,
        SystemState.releasePlace_refined
          ((processOneReplenishmentOnCore_releaseStateAgree s c scId now hI).refined hR) c scId,
        releaseHiddenOn_pass s c scId now hI hRHs hq⟩)
    _ st ⟨lowEquivalent_smp_refl st, hInv, hRef, hRH⟩).1

end Drain

/-! ## §6 The charges

The tick's charge of a hidden current thread, the yield's charge, and the
tick itself.  The charge writes the thread's TCB or its context, places the
context on the core's release queue, and requeues the thread: all hidden when
the thread and its context are.  The exhausting charge's timeout pass is
required to be quiet (`timeoutPassQuiet`): the context's bound thread is the
running thread, which is not blocked in IPC. -/

section Charges

variable {ctx : LabelingContext} {observer : IfObserver}

/-- An object rewritten at a hidden key is invisible on every core. -/
theorem rewriteObject_lowEquivalent (st : SystemState) (x : SeLe4n.ObjId) (o : KernelObject)
    (h : st.rewriteAdmissible x o) (hInv : st.objects.invExt)
    (hX : objectObservable ctx observer x = false) :
    lowEquivalent_smp ctx observer (st.rewriteObject x o h) st :=
  lowEquivalent_smp_of_projectedObjectsWrite
    (projectedObjectsWrite.of_hidden (hiddenObjectsWrite.rewriteObject st x o h hInv hX))

/-- **An unbound thread's slice expiry** is invisible when the thread is hidden. -/
theorem sliceExpireOnCore_lowEquivalent (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hT : threadHidden ctx observer tid)
    (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (sliceExpireOnCore st c tid tcb hTcb) st :=
  lowEquivalent_smp_trans (runEnqueueOnCore_lowEquivalent _ c tid _ hT.1)
    (rewriteObject_lowEquivalent st _ _ _ hInv hT.2)

/-- **A spent budget** is invisible when the thread and its context are hidden. -/
theorem spendBudgetOnCore_lowEquivalent (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) (hT : threadHidden ctx observer tid)
    (hS : objectObservable ctx observer scId.toObjId = false) (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (spendBudgetOnCore st c tid scId sc hSc start ticks) st := by
  unfold spendBudgetOnCore
  dsimp only
  exact lowEquivalent_smp_trans (runEnqueueOnCore_lowEquivalent _ c tid _ hT.1)
    (lowEquivalent_smp_trans (replenishOnCore_lowEquivalent _ c scId hS)
      (rewriteObject_lowEquivalent st _ _ _ hInv hS))

/-- The exhausting charge's timeout pass, at the spent state, has nothing to do. -/
def exhaustQuiet (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (scId : SchedContextId)
    (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc) (ticks : Nat) : Prop :=
  timeoutPassQuiet (markKeyChangeFor
    (spendBudgetOnCore st c tid scId sc hSc (st.machine.timer - ticks) ticks) tid k) scId = true

/-- **A budget exhausted on the tick** is invisible when the thread and its
context are hidden and the timeout pass is quiet. -/
theorem budgetExhaustOnCore_lowEquivalent (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (scId : SchedContextId)
    (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hT : threadHidden ctx observer tid) (hS : objectObservable ctx observer scId.toObjId = false)
    (hInv : st.objects.invExt) (hQ : exhaustQuiet st c tid k scId sc hSc ticks) :
    lowEquivalent_smp ctx observer (budgetExhaustOnCore st c tid k scId sc hSc ticks) st := by
  unfold budgetExhaustOnCore
  dsimp only
  rw [timeoutBlockedThreads_of_quiet hQ c]
  exact lowEquivalent_smp_trans (fun _ => rfl)
    (lowEquivalent_smp_trans (markKeyChangeFor_lowEquivalent _ tid k)
      (spendBudgetOnCore_lowEquivalent st c tid scId sc hSc _ ticks hT hS hInv))

/-- **What the tick's charge of `tid` reads, hidden**: the context its binding
names, and the exhausting arm's timeout pass quiet. -/
def chargeHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  (∀ scId, tcb.schedContextBinding.scId? = some scId →
    objectObservable ctx observer scId.toObjId = false) ∧
  ∀ scId sc (hSc : st.getSchedContext? scId = some sc),
    tcb.schedContextBinding.scId? = some scId →
    exhaustQuiet st c tid (effectiveSchedParams st tcb) scId sc hSc 1

/-- **The tick's charge** is invisible when the charged thread, its context and
the timeout pass are hidden. -/
theorem timerTickBudgetOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hT : threadHidden ctx observer tid) (hC : chargeHidden ctx observer st c tid tcb)
    (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (timerTickBudgetOnCore st c tid tcb hTcb).1 st := by
  unfold timerTickBudgetOnCore
  split
  · split
    · exact sliceExpireOnCore_lowEquivalent st c tid tcb hTcb hT hInv
    · exact rewriteObject_lowEquivalent st _ _ (SystemState.rewriteAdmissible_tcb hTcb _) hInv hT.2
  all_goals
    rename_i hBind
    split
    · rename_i sc hSc _
      dsimp only
      have hS := hC.1 _ (by rw [hBind]; rfl)
      split
      · exact budgetExhaustOnCore_lowEquivalent st c tid _ _ sc hSc 1 hT hS hInv
          (hC.2 _ sc hSc (by rw [hBind]; rfl))
      · exact rewriteObject_lowEquivalent st _ _ (SystemState.rewriteAdmissible_schedContext hSc _)
          hInv hS
    · exact lowEquivalent_smp_refl st

/-- A hidden queue stays hidden under a requeue of a hidden thread. -/
theorem queueHiddenOn_runEnqueueOnCore {st : SystemState} {c d : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (hT : threadObservable ctx observer t = false)
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (st.runEnqueueOnCore c t p) d := by
  intro x hx
  by_cases hcd : c = d
  · subst hcd
    cases hA : st.runEnqueueAdmits c t
    · rw [SystemState.runEnqueueOnCore_of_not_admits p hA] at hx; exact hQ x hx
    · rw [SystemState.runEnqueueOnCore_runQueueOnCore_self p hA] at hx
      rcases (RunQueue.mem_insert _ _ _ _).mp hx with hm | e
      · exact hQ x hm
      · rw [e]; exact hT
  · rw [SystemState.runEnqueueOnCore_runQueueOnCore_ne st c d t p hcd] at hx; exact hQ x hx

theorem queueHiddenOn_spendBudgetOnCore (st : SystemState) (c d : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) (hT : threadObservable ctx observer tid = false)
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (spendBudgetOnCore st c tid scId sc hSc start ticks) d := by
  unfold spendBudgetOnCore
  dsimp only
  exact queueHiddenOn_runEnqueueOnCore _ hT (queueHiddenOn_of_runQueueOnCore_eq
    ((SystemState.releasePlace_releaseOnlyWrite _ c scId).runQueueOnCore d) hQ)

/-- **The tick's charge keeps a hidden queue hidden**: the one thread it
queues is the charged one. -/
theorem queueHiddenOn_timerTickBudgetOnCore (st : SystemState) (c d : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hT : threadObservable ctx observer tid = false) (hC : chargeHidden ctx observer st c tid tcb)
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (timerTickBudgetOnCore st c tid tcb hTcb).1 d := by
  unfold timerTickBudgetOnCore
  split
  · split
    · exact queueHiddenOn_runEnqueueOnCore _ hT hQ
    · exact hQ
  all_goals
    rename_i hBind
    split
    · rename_i sc hSc _
      dsimp only
      split
      · unfold budgetExhaustOnCore
        dsimp only
        rw [timeoutBlockedThreads_of_quiet (hC.2 _ sc hSc (by rw [hBind]; rfl)) c]
        refine queueHiddenOn_of_runQueueOnCore_eq (by
          show (markRescheduleTargets _ _).runQueueOnCore d = _
          rw [markRescheduleTargets_eq]; rfl) ?_
        refine queueHiddenOn_of_runQueueOnCore_eq (markKeyChangeFor_extract_frame
          (fun s => s.scheduler.runQueueOnCore d) _ tid _ (fun _ _ => by simp)) ?_
        exact queueHiddenOn_spendBudgetOnCore st c d tid _ sc hSc _ 1 hT hQ
      · exact hQ
    · exact hQ

/-- **What core `c`'s tick reads, hidden**: core `c`'s release queue, run queue,
current thread and idle thread, with the placement invariants; at the prepared
state (after the drain), the current thread's context placeable on `c` and its
charge hidden. -/
structure tickHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop where
  objects : st.objects.invExt
  runRefined : st.runQueueRefined
  releaseRefined : st.releaseQueueRefined
  release : releaseHiddenOn ctx observer st c
  queue : queueHiddenOn ctx observer st c
  current : ∀ t, st.scheduler.currentOnCore c = some t → threadHidden ctx observer t
  idle : threadObservable ctx observer (Kernel.idleThreadId c) = false
  placeable : (timerTickOnCorePrepared st c).currentContextPlaceableOnCore c
  charge : ∀ tid tcb, (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
    (timerTickOnCorePrepared st c).getTcb? tid = some tcb →
    chargeHidden ctx observer (timerTickOnCorePrepared st c) c tid tcb

/-- **The per-core timer tick is invisible on every core** when what it reads
is hidden (`tickHidden`): the diagnostic clear, the drain of core `c`'s release
queue, the charge of its current thread, and the dispatch or the local
reschedule decision. -/
theorem timerTickOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (h : tickHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (timerTickOnCore st c) st := by
  have hRef0 : ({ st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } :
      SystemState).releaseQueueRefined :=
    SystemState.releaseStateAgree.refined
      (SystemState.releaseStateAgree.of_objects_eq (st := st) (by rfl) (by rfl)) h.releaseRefined
  have hD := processReplenishmentsDueOnCore_drainHidden
    { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c c st.machine.timer
    h.objects hRef0 h.release h.queue
  have hL0 : lowEquivalent_smp ctx observer (timerTickOnCorePrepared st c) st :=
    lowEquivalent_smp_trans hD.1 (setLastTimeoutErrorsOnCore_lowEquivalent st c [])
  have hStage : SystemState.RunQueueStage st (timerTickOnCorePrepared st c) :=
    (SystemState.RunQueueStage.of_frame (st := st)
      (st' := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] })
      rfl rfl rfl).trans
      (processReplenishmentsDueOnCore_runQueueStage
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer)
  obtain ⟨hIP, hRP⟩ := hStage.1 h.objects h.runRefined
  have hCurP : ∀ t, (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some t →
      threadHidden ctx observer t := fun t ht => by
    unfold timerTickOnCorePrepared at ht
    rw [processReplenishmentsDueOnCore_currentOnCore_eq] at ht
    exact h.current t ht
  have hSPP : schedulingPointHidden ctx observer (timerTickOnCorePrepared st c) c :=
    ⟨hIP, hRP c, hD.2.2.2.2, fun t ht => (hCurP t ht).1, h.idle⟩
  have hPoint : ∀ tid tcb (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb) st3 b,
      (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
      st3.objects.invExt → st3.runQueueRefined →
      lowEquivalent_smp ctx observer st3 st ∧ schedulingPointHidden ctx observer st3 c := by
    intro tid tcb hTcb st3 b hCur hB hI3 hR3
    have hC := h.charge tid tcb hCur hTcb
    have hL := timerTickBudgetOnCore_lowEquivalent _ c tid tcb hTcb (hCurP tid hCur) hC hIP
    have hQ := queueHiddenOn_timerTickBudgetOnCore _ c c tid tcb hTcb (hCurP tid hCur).1 hC
      hD.2.2.2.2
    have hK := timerTickBudgetOnCore_currentOnCore _ c tid tcb hTcb c
    rw [hB] at hL hQ hK
    exact ⟨lowEquivalent_smp_trans hL hL0, hI3, hR3 c, hQ,
      fun t ht => (hCurP t (hK ▸ ht)).1, h.idle⟩
  rcases timerTickOnCore_cases st c with ⟨_, e⟩ | ⟨_, _, _, e⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, e⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, e⟩ <;> rw [e]
  · exact lowEquivalent_smp_trans (rescheduleIfPendingOnCore_lowEquivalent _ c hSPP) hL0
  · exact lowEquivalent_smp_trans (rescheduleIfPendingOnCore_lowEquivalent _ c hSPP) hL0
  · obtain ⟨hI3, hR3⟩ := (timerTickBudgetOnCore_runQueueWindowStage hB hCur h.placeable).1 hIP hRP
    obtain ⟨hL3, hS3⟩ := hPoint tid tcb hTcb st3 true hCur hB hI3 hR3
    exact lowEquivalent_smp_trans (scheduleEffectiveOnCoreState_lowEquivalent st3 c hS3) hL3
  · obtain ⟨hI3, hR3⟩ := (timerTickBudgetOnCore_runQueueStage_of_not_preempted hB).1 hIP hRP
    obtain ⟨hL3, hS3⟩ := hPoint tid tcb hTcb st3 false hCur hB hI3 hR3
    exact lowEquivalent_smp_trans (rescheduleIfPendingOnCore_lowEquivalent st3 c hS3) hL3

/-- **The yield's charge** is invisible when the caller and the context its
binding names are hidden, and keeps every hidden queue hidden.  It runs no
timeout pass. -/
theorem yieldChargeOnCore_lowEquivalent {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (h : yieldChargeOnCore st c tid = .ok st') (hT : threadHidden ctx observer tid)
    (hS : ∀ tcb scId, st.getTcb? tid = some tcb → tcb.schedContextBinding.scId? = some scId →
      objectObservable ctx observer scId.toObjId = false)
    (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer st' st ∧
      ∀ d, queueHiddenOn ctx observer st d → queueHiddenOn ctx observer st' d := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact ⟨sliceExpireOnCore_lowEquivalent st c tid tcb hTcb hT hInv,
        fun d hQ => queueHiddenOn_runEnqueueOnCore _ hT.1 hQ⟩
    all_goals
      rename_i hBd
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        have hSc0 := hS tcb _ hTcb (by rw [hBd]; rfl)
        exact ⟨lowEquivalent_smp_trans (markKeyChangeFor_lowEquivalent _ tid _)
            (spendBudgetOnCore_lowEquivalent st c tid _ sc hSc _ _ hT hSc0 hInv),
          fun d hQ => queueHiddenOn_of_runQueueOnCore_eq (markKeyChangeFor_extract_frame
            (fun s => s.scheduler.runQueueOnCore d) _ tid _ (fun _ _ => by simp))
            (queueHiddenOn_spendBudgetOnCore st c d tid _ sc hSc _ _ hT.1 hQ)⟩
      · cases h

/-- **What core `c`'s yield reads, hidden**: its run queue, current thread,
idle thread and the current thread's context, with the placement invariants. -/
structure yieldHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop where
  objects : st.objects.invExt
  runRefined : st.runQueueRefined
  queue : queueHiddenOn ctx observer st c
  current : ∀ t, st.scheduler.currentOnCore c = some t → threadHidden ctx observer t
  context : ∀ t tcb scId, st.scheduler.currentOnCore c = some t → st.getTcb? t = some tcb →
    tcb.schedContextBinding.scId? = some scId → objectObservable ctx observer scId.toObjId = false
  idle : threadObservable ctx observer (Kernel.idleThreadId c) = false
  placeable : st.currentContextPlaceableOnCore c

/-- **The yield syscall is invisible on every core** when what it reads is
hidden: the charge, then core `c`'s dispatch. -/
theorem yieldOnCore_lowEquivalent {st st' : SystemState} {c : CoreId}
    (h : yieldOnCore st c = .ok st') (hH : yieldHidden ctx observer st c) :
    lowEquivalent_smp ctx observer st' st := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · rename_i tid hCur
    split at h
    · cases h
    · rename_i st2 hC
      obtain ⟨hL, hQ⟩ := yieldChargeOnCore_lowEquivalent hC (hH.current tid hCur)
        (fun tcb scId hT hB => hH.context tid tcb scId hCur hT hB) hH.objects
      obtain ⟨hI2, hR2⟩ := (yieldChargeOnCore_runQueueWindowStage hC hCur hH.placeable).1
        hH.objects hH.runRefined
      rw [scheduleEffectiveOnCore_eq_state, Except.ok.injEq] at h
      subst h
      have hK := yieldChargeOnCore_currentOnCore hC c
      refine lowEquivalent_smp_trans (scheduleEffectiveOnCoreState_lowEquivalent st2 c
        ⟨hI2, hR2 c, hQ c hH.queue, fun t ht => (hH.current t (hK ▸ ht)).1, hH.idle⟩) hL

end Charges

/-! ## §7 The activation and yieldTo

The activation completes core `c`'s current thread's yield: it hands the
yielder the consumed time of the context it yielded to and clears both link
ends.  A hidden yielder's activation is invisible on every core.  An observable
yielder's bank is written visibly, with the context's consumed time: the step
is then shown low-equivalent across two low-equivalent states that agree on
what it reads (`activationRead`), the yielder's own link and that reading. -/

section Activation

variable {ctx : LabelingContext} {observer : IfObserver}

theorem lowEquivalent_smp_symm {a b : SystemState} (h : lowEquivalent_smp ctx observer a b) :
    lowEquivalent_smp ctx observer b a :=
  fun c => (h c).symm

/-- The context core `c`'s current thread yielded to is hidden. -/
def activationContextHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) : Prop :=
  ∀ tid t k, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some t →
    t.yieldToCode = k + 1 →
    objectObservable ctx observer (⟨k⟩ : SeLe4n.SchedContextId).toObjId = false

/-- **The completion's hidden write**: the yielder's link and saved registers
(erased by the projection) and the hidden context it yielded to. -/
theorem completeYieldTo_lowEquivalent (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hX : activationContextHidden ctx observer st c)
    (hC : st.scheduler.currentOnCore c = some tid) :
    lowEquivalent_smp ctx observer (completeYieldTo st tid) st :=
  lowEquivalent_smp_of_projectedObjectsWrite
    (projectedObjectsWrite.completeYieldTo st tid hInv (fun t k hT hY => hX tid t k hC hT hY))

/-- **The activation of a hidden yielder** is invisible on every core. -/
theorem activateThreadOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hX : activationContextHidden ctx observer st c)
    (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (activateThreadOnCore st c) st := by
  rcases activateThreadOnCore_cases st c with h | ⟨tid, t, k, hC, hT, hY, h⟩
  · rw [h]; exact lowEquivalent_smp_refl st
  rw [h]
  have hP := completeYieldTo_lowEquivalent st c tid hInv hX hC
  have hSch : (completeYieldTo st tid).scheduler = st.scheduler := by
    rw [SystemState.completeYieldTo_eq_objects st tid]
  unfold completeCurrentYield
  split
  · dsimp only
    rw [MachineState.modifyRegsOnCore_eq]
    exact lowEquivalent_smp_trans
      (setRegsOnCore_lowEquivalent _ c _ (fun t e => hCur t (by rw [← hSch]; exact e))) hP
  · exact hP

/-- What core `c`'s activation reads: its current thread, the context that
thread's link names, and that context's consumed time. -/
def activationRead (st : SystemState) (c : CoreId) :
    Option (SeLe4n.ThreadId × Nat × Option UInt64) :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    match st.getTcb? tid with
    | some t =>
      match t.yieldToCode with
      | 0 => none
      | k + 1 => some (tid, k, (st.getSchedContext? ⟨k⟩).map (·.consumedReading.toUInt64))
    | none => none
  | none => none

/-- The activation, read off what it reads. -/
theorem activateThreadOnCore_eq_read (st : SystemState) (c : CoreId) :
    activateThreadOnCore st c =
      match activationRead st c with
      | some (tid, _, some w) =>
        { completeYieldTo st tid with
          machine := (completeYieldTo st tid).machine.modifyRegsOnCore c (·.withConsumed w) }
      | some (tid, _, none) => completeYieldTo st tid
      | none => st := by
  unfold activateThreadOnCore activationRead
  cases hC : st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    dsimp only
    cases hT : st.getTcb? tid with
    | none => rfl
    | some t =>
      dsimp only
      cases hY : t.yieldToCode with
      | zero => rfl
      | succ k =>
        dsimp only
        unfold completeCurrentYield
        cases hS : st.getSchedContext? ⟨k⟩ with
        | none => rfl
        | some sc => rfl

/-- A bank rewritten on core `c` is shown, mapped, while core `c`'s current
thread is observable. -/
theorem projectMachineRegsOnCore_modifyRegs_self (st : SystemState) (c : CoreId)
    (g : RegisterFile → RegisterFile) :
    projectMachineRegsOnCore ctx observer { st with machine := st.machine.modifyRegsOnCore c g } c =
      (projectMachineRegsOnCore ctx observer st c).map g := by
  unfold projectMachineRegsOnCore
  dsimp only
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    dsimp only
    split <;> simp [MachineState.modifyRegsOnCore_eq]

/-- **One bank function on core `c`, applied to two low-equivalent states**,
leaves them low-equivalent: the bank is shown on both or on neither, and shown
equal before. -/
theorem lowEquivalent_smp_modifyRegs_pair {s₁ s₂ : SystemState} (c : CoreId)
    (g : RegisterFile → RegisterFile) (hL : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent_smp ctx observer { s₁ with machine := s₁.machine.modifyRegsOnCore c g }
      { s₂ with machine := s₂.machine.modifyRegsOnCore c g } := by
  intro d
  have hd := hL d
  have hS := congrArg ObservableState.sharedFragment hd
  have hP := congrArg ObservableState.perCoreFragment hd
  simp only [projectStateOnCore_sharedFragment, projectStateOnCore_perCoreFragment,
    SharedObservableFragment.mk.injEq, PerCoreObservableFragment.mk.injEq] at hS hP
  have hMem : ∀ s : SystemState,
      projectMemory ctx observer { s with machine := s.machine.modifyRegsOnCore c g } =
        projectMemory ctx observer s := fun s =>
    projectMemory_eq_of_memory_eq _ _ _ _
      (by show (s.machine.modifyRegsOnCore c g).memory = _
          rw [MachineState.modifyRegsOnCore_eq]; exact MachineState.setRegsOnCore_memory _ _ _)
  refine ObservableState.ext_fragments ?_ ?_
  · simp only [projectStateOnCore_sharedFragment, SharedObservableFragment.mk.injEq]
    exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, by rw [hMem, hMem]; exact hS.2.2.2.2⟩
  · simp only [projectStateOnCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    refine ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, ?_⟩
    by_cases hdc : d = c
    · subst hdc
      rw [projectMachineRegsOnCore_modifyRegs_self, projectMachineRegsOnCore_modifyRegs_self,
        hP.2.2.2.2.2]
    · have hF : ∀ s : SystemState,
          projectMachineRegsOnCore ctx observer
            { s with machine := s.machine.modifyRegsOnCore c g } d =
          projectMachineRegsOnCore ctx observer s d := fun s =>
        projectMachineRegsOnCore_frame _ _ rfl (by
          show (s.machine.modifyRegsOnCore c g).regsOnCore d = _
          rw [MachineState.modifyRegsOnCore_eq]
          exact MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ (Ne.symm hdc))
      rw [hF, hF]; exact hP.2.2.2.2.2

/-- A write the observer sees nothing of stays so under a common machine. -/
theorem lowEquivalent_smp_withMachine {s s' : SystemState}
    (h : projectedObjectsWrite ctx observer s s') (M : MachineState) :
    lowEquivalent_smp ctx observer { s' with machine := M } { s with machine := M } := by
  refine lowEquivalent_smp_of_projectedObjectsWrite ⟨?_, h.2⟩
  exact (congrArg (fun x : SystemState => { x with machine := M }) h.1).trans rfl

theorem activationRead_currentOnCore {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    {k : Nat} {w : Option UInt64} (h : activationRead st c = some (tid, k, w)) :
    st.scheduler.currentOnCore c = some tid := by
  unfold activationRead at h
  split at h
  · rename_i tid' hC
    split at h
    · split at h
      · cases h
      · cases h; exact hC
    · cases h
  · cases h

/-- **The activation of an observable yielder**: two low-equivalent states
whose activations read the same — the same current thread, linked to the same
hidden context, whose consumed time reads the same — stay low-equivalent.  The
consumed time is the one flow the step makes visible: seL4-MCS's
`schedContext_completeYieldTo` hands it to the yielder through its capability
to the context, the read `seL4_SchedContext_YieldTo` was authorised for. -/
theorem activateThreadOnCore_lowEquivalent_pair {s₁ s₂ : SystemState} (c : CoreId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hInv₁ : s₁.objects.invExt)
    (hInv₂ : s₂.objects.invExt) (hX₁ : activationContextHidden ctx observer s₁ c)
    (hX₂ : activationContextHidden ctx observer s₂ c)
    (hRead : activationRead s₁ c = activationRead s₂ c) :
    lowEquivalent_smp ctx observer (activateThreadOnCore s₁ c) (activateThreadOnCore s₂ c) := by
  rw [activateThreadOnCore_eq_read, activateThreadOnCore_eq_read, ← hRead]
  cases h₁ : activationRead s₁ c with
  | none => exact hL
  | some r =>
    obtain ⟨tid, k, w⟩ := r
    have hC₁ := activationRead_currentOnCore h₁
    have hC₂ := activationRead_currentOnCore (hRead ▸ h₁)
    have hW₁ := projectedObjectsWrite.completeYieldTo s₁ tid hInv₁
      (fun t k hT hY => hX₁ tid t k hC₁ hT hY)
    have hW₂ := projectedObjectsWrite.completeYieldTo s₂ tid hInv₂
      (fun t k hT hY => hX₂ tid t k hC₂ hT hY)
    cases w with
    | none =>
      exact lowEquivalent_smp_trans (lowEquivalent_smp_of_projectedObjectsWrite hW₁)
        (lowEquivalent_smp_trans hL
          (lowEquivalent_smp_symm (lowEquivalent_smp_of_projectedObjectsWrite hW₂)))
    | some w =>
      dsimp only
      have hM : ∀ s, (completeYieldTo s tid).machine = s.machine := fun s => by
        rw [SystemState.completeYieldTo_eq_objects s tid]
      rw [hM, hM]
      exact lowEquivalent_smp_trans (lowEquivalent_smp_withMachine hW₁ _)
        (lowEquivalent_smp_trans (lowEquivalent_smp_modifyRegs_pair c _ hL)
          (lowEquivalent_smp_symm (lowEquivalent_smp_withMachine hW₂ _)))

end Activation

section YieldTo

variable {ctx : LabelingContext} {observer : IfObserver}

theorem queueHiddenOn_runRemoveOnCore {st : SystemState} {c d : CoreId} {t : SeLe4n.ThreadId}
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (st.runRemoveOnCore c t) d := by
  intro x hx
  by_cases hcd : c = d
  · subst hcd
    rw [SystemState.runRemoveOnCore_runQueueOnCore_self] at hx
    exact hQ x ((RunQueue.mem_remove _ _ _).mp hx).1
  · rw [SystemState.runRemoveOnCore_runQueueOnCore_ne st c d t hcd] at hx; exact hQ x hx

theorem queueHiddenOn_runEnqueueHeadOnCore {st : SystemState} {c d : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (hT : threadObservable ctx observer t = false)
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (st.runEnqueueHeadOnCore c t p) d := by
  intro x hx
  by_cases hcd : c = d
  · subst hcd
    rw [SystemState.runEnqueueHeadOnCore_scheduler] at hx
    split at hx
    · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hx
      have hc := RunQueue.mem_iff_contains.mp hx
      rw [RunQueue.contains_insertHead] at hc
      rcases Bool.or_eq_true _ _ |>.mp hc with hm | e
      · exact hQ x (RunQueue.mem_iff_contains.mpr hm)
      · rw [beq_iff_eq.mp e]; exact hT
    · exact hQ x hx
  · rw [SystemState.runEnqueueHeadOnCore_runQueueOnCore_ne st c d t p hcd] at hx; exact hQ x hx

theorem queueHiddenOn_runDescheduleOnCore {st : SystemState} {c d : CoreId} {t : SeLe4n.ThreadId}
    (hQ : queueHiddenOn ctx observer st d) :
    queueHiddenOn ctx observer (st.runDescheduleOnCore c t) d :=
  queueHiddenOn_of_runQueueOnCore_eq (st := st.runRemoveOnCore c t)
    (by unfold SystemState.runDescheduleOnCore; simp) (queueHiddenOn_runRemoveOnCore hQ)

theorem currentHiddenOn_runRemoveOnCore {st : SystemState} {c d : CoreId} {t : SeLe4n.ThreadId}
    (h : currentHiddenOn ctx observer st d) :
    currentHiddenOn ctx observer (st.runRemoveOnCore c t) d := fun x hx =>
  h x (by simpa only [SchedulerState.currentOnCore, SystemState.runRemoveOnCore_current] using hx)

/-- **A hidden thread descheduled** from core `c`'s queue and slot is invisible
on every core. -/
theorem runDescheduleOnCore_lowEquivalent (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hT : threadObservable ctx observer t = false) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (st.runDescheduleOnCore c t) st := by
  unfold SystemState.runDescheduleOnCore
  dsimp only
  refine lowEquivalent_smp_trans (lowEquivalent_smp_trans (fun _ => rfl)
    (setCurrentOnCore_lowEquivalent (st.runRemoveOnCore c t) c _
      (currentHiddenOn_runRemoveOnCore hCur) ?_)) (runRemoveOnCore_lowEquivalent st c t hT)
  intro x hx
  split at hx
  · cases hx
  · exact hCur x hx

/-- **The link set** is invisible: both ends are erased by the projection. -/
theorem setYieldLink_lowEquivalent (st : SystemState) (s : SeLe4n.SchedContextId)
    (caller : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (setYieldLink st s caller) st := by
  unfold setYieldLink
  exact lowEquivalent_smp_of_projectedObjectsWrite
    ((projectedObjectsWrite.updateSchedContext st s
        (fun sc => { sc with yieldFromCode := caller.val + 1 }) hInv (fun _ => rfl)).trans
      (projectedObjectsWrite.updateTcb _ caller (fun t => { t with yieldToCode := s.val + 1 })
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl)))

/-- **The requeue of a hidden target** on its home core is invisible. -/
theorem yieldToRequeue_lowEquivalent (st : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hT : threadObservable ctx observer t = false) :
    lowEquivalent_smp ctx observer (SchedContextOps.yieldToRequeue st home t p) st := by
  unfold SchedContextOps.yieldToRequeue
  split
  · exact lowEquivalent_smp_refl st
  · exact lowEquivalent_smp_trans (markReschedulePendingOnCore_lowEquivalent _ home)
      (lowEquivalent_smp_trans (runEnqueueHeadOnCore_lowEquivalent _ home t p hT)
        (runRemoveOnCore_lowEquivalent st home t hT))

/-- **The linked branch** of a hidden caller to a hidden target is invisible:
the link (erased), the target off core `c`'s queue, the caller off its slot,
both at their bands' heads, and core `c`'s scheduling point, which can choose
only them or a thread already queued. -/
theorem yieldToLink_lowEquivalent_of (st2 : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (caller t : SeLe4n.ThreadId) (pC pT : SeLe4n.Priority) (hI2 : st2.objects.invExt)
    (hR2 : st2.runQueueRefined) (hQ2 : queueHiddenOn ctx observer st2 c)
    (hCur2 : st2.scheduler.currentOnCore c = some caller) (hCH : threadHidden ctx observer caller)
    (hTH : threadHidden ctx observer t)
    (hIdle : threadObservable ctx observer (Kernel.idleThreadId c) = false)
    {st : SystemState} (hL : lowEquivalent_smp ctx observer st2 st) :
    lowEquivalent_smp ctx observer (SchedContextOps.yieldToLink st2 c s caller t pC pT) st := by
  unfold SchedContextOps.yieldToLink SchedContextOps.yieldToLinkPrefix
  have hSch := SystemState.setYieldLink_scheduler st2 s caller
  have hA := SystemState.setYieldLink_objectsAgreeOffYield st2 s caller hI2
  have hI0 := SchedContextOps.setYieldLink_objects_invExt st2 s caller hI2
  have hR0 : (setYieldLink st2 s caller).runQueueRefined := by
    refine SystemState.runQueueRefined_of_frame (fun d x => ?_) (by rw [hSch]) (by rw [hSch]) hR2
    have e := hA.getTcb?_map (fun y => y.runLinkOn d) (t := x)
    unfold SystemState.runLinkOn
    cases h1 : (setYieldLink st2 s caller).getTcb? x <;> cases h2 : st2.getTcb? x <;>
      rw [h1, h2] at e <;> first | rfl | cases e | exact Option.some.inj e
  have hL0 : lowEquivalent_smp ctx observer (setYieldLink st2 s caller) st2 :=
    setYieldLink_lowEquivalent st2 s caller hI2
  generalize setYieldLink st2 s caller = P0 at hSch hI0 hR0 hL0
  have hCur0 : P0.scheduler.currentOnCore c = some caller := by rw [hSch]; exact hCur2
  have hQ0 : queueHiddenOn ctx observer P0 c := queueHiddenOn_of_runQueueOnCore_eq (by rw [hSch]) hQ2
  obtain ⟨hI1, hR1⟩ := (SystemState.RunQueueStage.runRemoveOnCore P0 c t).1 hI0 hR0
  have hCur1 : (P0.runRemoveOnCore c t).scheduler.currentOnCore c = some caller := by
    simpa only [SchedulerState.currentOnCore, SystemState.runRemoveOnCore_current] using hCur0
  have hCH1 : currentHiddenOn ctx observer (P0.runRemoveOnCore c t) c := fun x hx => by
    rw [hCur1] at hx; cases hx; exact hCH.1
  obtain ⟨hI2', hR2'⟩ :=
    (SystemState.RunQueueStage.runDescheduleOnCore (P0.runRemoveOnCore c t) c caller).1 hI1 hR1
  obtain ⟨hI3, hR3⟩ := (SystemState.RunQueueLinkStage.runEnqueueHeadOnCore
    ((P0.runRemoveOnCore c t).runDescheduleOnCore c caller) c caller pC) hI2' hR2'
  obtain ⟨hI4, hR4⟩ := (SystemState.RunQueueLinkStage.runEnqueueHeadOnCore
    (((P0.runRemoveOnCore c t).runDescheduleOnCore c caller).runEnqueueHeadOnCore c caller pC)
    c t pT) hI3 hR3
  have hNone : ((((P0.runRemoveOnCore c t).runDescheduleOnCore c caller).runEnqueueHeadOnCore
      c caller pC).runEnqueueHeadOnCore c t pT).scheduler.currentOnCore c = none := by
    rw [SystemState.runEnqueueHeadOnCore_currentOnCore, SystemState.runEnqueueHeadOnCore_currentOnCore,
      SystemState.runDescheduleOnCore_currentOnCore_of_current _ c caller hCur1 c, if_pos rfl]
  refine lowEquivalent_smp_trans (handleRescheduleOnCoreState_lowEquivalent _ c
    ⟨hI4, hR4 c, queueHiddenOn_runEnqueueHeadOnCore _ hTH.1
      (queueHiddenOn_runEnqueueHeadOnCore _ hCH.1
        (queueHiddenOn_runDescheduleOnCore (queueHiddenOn_runRemoveOnCore hQ0))),
      (fun x hx => by rw [hNone] at hx; cases hx), hIdle⟩) ?_
  exact lowEquivalent_smp_trans (runEnqueueHeadOnCore_lowEquivalent _ c t pT hTH.1)
    (lowEquivalent_smp_trans (runEnqueueHeadOnCore_lowEquivalent _ c caller pC hCH.1)
      (lowEquivalent_smp_trans (runDescheduleOnCore_lowEquivalent _ c caller hCH.1 hCH1)
        (lowEquivalent_smp_trans (runRemoveOnCore_lowEquivalent P0 c t hTH.1)
          (lowEquivalent_smp_trans hL0 hL))))

/-- **What core `c`'s yieldTo of context `s` reads, hidden**: the caller (core
`c`'s current thread), the context and the thread it is bound to, core `c`'s
run queue and idle thread, with the placement invariants. -/
structure yieldToHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) (s : SeLe4n.SchedContextId) : Prop where
  objects : st.objects.invExt
  runRefined : st.runQueueRefined
  caller : ∀ t, st.scheduler.currentOnCore c = some t → threadHidden ctx observer t
  context : objectObservable ctx observer s.toObjId = false
  target : ∀ sc t, st.getSchedContext? s = some sc → sc.boundThread = some t →
    threadHidden ctx observer t
  queue : queueHiddenOn ctx observer st c
  idle : threadObservable ctx observer (Kernel.idleThreadId c) = false

/-- **The yieldTo invocation is invisible on every core** when what it reads is
hidden: the completion of the context's earlier yield, its resume, then the
consumed time returned, the requeue, or the link and core `c`'s scheduling
point.  The consumed-time return writes the caller's saved registers, which the
projection erases, and the hidden context's count. -/
theorem schedContextYieldToOnCore_lowEquivalent {s : SeLe4n.SchedContextId} {c : CoreId}
    {st st' : SystemState} (h : SchedContextOps.schedContextYieldToOnCore s c st = .ok st')
    (hH : yieldToHidden ctx observer st c s) : lowEquivalent_smp ctx observer st' st := by
  obtain ⟨caller, sc0, t, -, -, hCur, hS, hb, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok h
  have hInv := hH.objects
  have hCH := hH.caller caller hCur
  have hTH : threadHidden ctx observer t :=
    hH.target sc0 t hS (by simp [SchedContext.boundThread, SeLe4n.ThreadId.ofOptCode, hb])
  have hI1 := SystemState.completeYieldFrom_preserves_objects_invExt st s hInv
  have hL1 : lowEquivalent_smp ctx observer (completeYieldFrom st s) st :=
    lowEquivalent_smp_of_projectedObjectsWrite (projectedObjectsWrite.completeYieldFrom st s hInv hH.context)
  have hR1 := ((SystemState.completeYieldFrom_runQueueStage st s).1 hInv hH.runRefined).2
  unfold SchedContextOps.yieldToBound
  dsimp only
  generalize determineTargetCore (completeYieldFrom st s) t = home
  have hW := SystemState.releasePlace_releaseOnlyWrite (completeYieldFrom st s) home s
  have hAg := SystemState.releasePlace_agree (completeYieldFrom st s) home s
  have hL2 := releasePlace_lowEquivalent (ctx := ctx) (observer := observer) (completeYieldFrom st s) home s hH.context
  have hI2 := SystemState.releasePlace_objects_invExt (completeYieldFrom st s) home s hI1
  have hR2 : ((completeYieldFrom st s).releasePlace home s).runQueueRefined :=
    SystemState.runQueueRefined_of_frame (fun d x => SystemState.runLinkOn_of_getTcb? (hAg.getTcb? x) d)
      (by rw [hW.2]) (by rw [hW.2]) hR1
  have hQ2 : queueHiddenOn ctx observer ((completeYieldFrom st s).releasePlace home s) c :=
    queueHiddenOn_of_runQueueOnCore_eq
      (by rw [hW.runQueueOnCore c, SystemState.completeYieldFrom_scheduler]) hH.queue
  have hCur2 : ((completeYieldFrom st s).releasePlace home s).scheduler.currentOnCore c = some caller := by
    rw [hW.currentOnCore c, SystemState.completeYieldFrom_scheduler]; exact hCur
  generalize (completeYieldFrom st s).releasePlace home s = st2 at hL2 hI2 hR2 hQ2 hCur2
  have hL12 := lowEquivalent_smp_trans hL2 hL1
  have hSet : ∀ X : SystemState, X.objects.invExt → lowEquivalent_smp ctx observer X st →
      lowEquivalent_smp ctx observer (setConsumed X s caller) st := fun X hX hXL =>
    lowEquivalent_smp_trans (lowEquivalent_smp_of_projectedObjectsWrite
      (projectedObjectsWrite.setConsumed X s caller hX hH.context)) hXL
  split
  · exact hSet _ hI2 hL12
  · split
    · exact hSet _ hI2 hL12
    · split
      · exact hSet _ hI2 hL12
      · split
        · split
          · exact hSet _ (SchedContextOps.yieldToRequeue_objects_invExt _ _ _ _ hI2)
              (lowEquivalent_smp_trans (yieldToRequeue_lowEquivalent _ home t _ hTH.1) hL12)
          · rename_i cT _ _ _ _ _
            exact yieldToLink_lowEquivalent_of st2 c s caller t _ _ hI2 hR2 hQ2 hCur2 hCH hTH
              hH.idle hL12
        · exact hSet _ hI2 hL12

end YieldTo

/-! ## §8 The entry's save, the residency settle and the reschedule entry

The reschedule SGI's handler and the secondary core's entry commit one state:
the captured frame saved, the bracketed reschedule, the residency settle, the
activation, and the two hardware ledgers cleared (`perCoreRescheduleEntryState`,
the state `perCoreRescheduleEntry` commits, `rfl`). -/

section Entry

variable {ctx : LabelingContext} {observer : IfObserver}

/-- A core whose current thread is hidden, or that has none, is seen to have
none: so a step invisible on that core keeps it so. -/
theorem currentHiddenOn_of_lowEquivalent {st st' : SystemState} {c : CoreId}
    (hL : lowEquivalent_smp ctx observer st' st) (h : currentHiddenOn ctx observer st c) :
    currentHiddenOn ctx observer st' c := by
  intro t ht
  have e := congrArg ObservableState.current (hL c)
  have e' : projectCurrentOnCore ctx observer st' c = projectCurrentOnCore ctx observer st c := e
  rw [projectCurrentOnCore_of_currentHiddenOn h] at e'
  unfold projectCurrentOnCore at e'
  rw [ht] at e'
  cases hT : threadObservable ctx observer t
  · rfl
  · simp only [hT, if_true] at e'; cases e'

/-- **The current thread's frame saved**: its saved context, which the
projection erases, and its core's bank, which the projection hides with it. -/
theorem saveTrapFrameOnCore_lowEquivalent (st : SystemState) (c : CoreId) (rf : RegisterFile)
    (hInv : st.objects.invExt) (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (Architecture.saveTrapFrameOnCore st c rf) st := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    · rename_i tid _
      split
      · dsimp only
        have hW := projectedObjectsWrite.updateTcb (ctx := ctx) (observer := observer) st tid
          (fun t => { t with registerContext := rf }) hInv (fun _ => rfl)
        have hSch : (st.updateTcb tid fun t => { t with registerContext := rf }).scheduler =
            st.scheduler := by rw [hW.1]
        exact lowEquivalent_smp_trans (setRegsOnCore_lowEquivalent _ c rf
          (fun t e => hCur t (by rw [← hSch]; exact e)))
          (lowEquivalent_smp_of_projectedObjectsWrite hW)
      · exact lowEquivalent_smp_refl st
    · exact lowEquivalent_smp_refl st
  · exact lowEquivalent_smp_refl st

/-- **A vacated core's frame saved** into its resident thread's saved context,
which the projection erases. -/
theorem saveVacatedFrameOnCore_lowEquivalent (st : SystemState) (c : CoreId) (rf saved : RegisterFile)
    (hInv : st.objects.invExt) :
    lowEquivalent_smp ctx observer (Architecture.saveVacatedFrameOnCore st c rf saved) st := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · rename_i tid _ _
      split
      · exact lowEquivalent_smp_of_projectedObjectsWrite
          (projectedObjectsWrite.updateTcb st tid (fun t => { t with registerContext := saved }) hInv
            (fun _ => rfl))
      · exact lowEquivalent_smp_refl st
    · exact lowEquivalent_smp_refl st
  · exact lowEquivalent_smp_refl st

/-- **The entry's save** is invisible when the core's current thread is hidden. -/
theorem saveCapturedTrapFrame_lowEquivalent (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt)
    (hCur : currentHiddenOn ctx observer st c) :
    lowEquivalent_smp ctx observer (Architecture.saveCapturedTrapFrame st c frame) st := by
  cases frame with
  | none => exact lowEquivalent_smp_refl st
  | some ic =>
    show lowEquivalent_smp ctx observer (Architecture.saveVacatedFrameOnCore
      (Architecture.saveTrapFrameOnCore st c ic.snapshot) c ic.snapshot ic.snapshot) st
    exact lowEquivalent_smp_trans (saveVacatedFrameOnCore_lowEquivalent _ c _ _
      (Architecture.saveTrapFrameOnCore_preserves_objects_invExt st c _ hInv))
      (saveTrapFrameOnCore_lowEquivalent st c _ hInv hCur)

/-- The hardware ledgers are no view's. -/
theorem clearPhysicalWrites_lowEquivalent (st : SystemState) :
    lowEquivalent_smp ctx observer (Architecture.clearPhysicalWrites st) st := fun _ => rfl

theorem clearIcacheMaintenance_lowEquivalent (st : SystemState) :
    lowEquivalent_smp ctx observer (Architecture.clearIcacheMaintenance st) st := fun _ => rfl

/-- **A switch to a hidden thread** on a core whose current thread is hidden is
invisible on every core. -/
theorem switchToThreadOnCore_lowEquivalent {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (h : switchToThreadOnCore st c tid = .ok st') (hInv : st.objects.invExt)
    (hCur : currentHiddenOn ctx observer st c) (hT : threadObservable ctx observer tid = false) :
    lowEquivalent_smp ctx observer st' st := by
  unfold switchToThreadOnCore at h
  split at h
  · split at h
    · rw [Except.ok.injEq] at h
      subst h
      have hP := preemptCurrentOnCore_lowEquivalent st c tid hInv hCur
      have hD := lowEquivalent_smp_trans (runRemoveOnCore_lowEquivalent _ c tid hT) hP
      have hR := lowEquivalent_smp_trans (restoreIncomingContextOnCoreUnlessCurrent_lowEquivalent _ c tid
        (currentHiddenOn_of_lowEquivalent hD hCur)) hD
      exact lowEquivalent_smp_trans (setCurrentOnCore_lowEquivalent _ c (some tid)
        (currentHiddenOn_of_lowEquivalent hR hCur) (fun x e => by cases e; exact hT)) hR
    · cases h
  · cases h

/-- **The deferral of a thread resident on another core**: its saved context
reloaded into the hidden bank, and the core switched to its hidden idle thread
or left with none. -/
theorem deferResidentElsewhere_lowEquivalent (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hCur : currentHiddenOn ctx observer st c)
    (hIdle : threadObservable ctx observer (Kernel.idleThreadId c) = false) :
    lowEquivalent_smp ctx observer (PriorityInheritance.deferResidentElsewhere st c) st := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · rename_i tid _
    split
    · dsimp only
      have hL0 := restoreIncomingContextOnCore_lowEquivalent st c tid hCur
      have hI0 : (restoreIncomingContextOnCore st c tid).objects.invExt := by
        rw [restoreIncomingContextOnCore_objects]; exact hInv
      have hC0 := currentHiddenOn_of_lowEquivalent hL0 hCur
      split
      · rename_i st' hSw
        exact lowEquivalent_smp_trans (switchToThreadOnCore_lowEquivalent hSw hI0 hC0 hIdle) hL0
      · exact lowEquivalent_smp_trans (dropCurrentOnCore_lowEquivalent _ c hI0 hC0) hL0
    · exact lowEquivalent_smp_refl st
  · exact lowEquivalent_smp_refl st

/-- **A vacated core's dispatch** is a scheduling point: invisible when what it
reads is hidden. -/
theorem dispatchVacatedCore_lowEquivalent (st : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (PriorityInheritance.dispatchVacatedCore st c) st := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact lowEquivalent_smp_refl st
  · split
    · rename_i st' hStep
      exact handleRescheduleSgiOnCore_lowEquivalent st st' c h hStep
    · exact lowEquivalent_smp_refl st

/-- **The residency settle** is invisible on every core when core `c`'s
scheduling point is hidden: the vacated core's dispatch, the deferral, the
resident record (no view's) and the released resident's poke (a flag). -/
theorem settleResidencyOnCore_lowEquivalent (st : SystemState) (c : CoreId)
    (h : schedulingPointHidden ctx observer st c) :
    lowEquivalent_smp ctx observer (PriorityInheritance.settleResidencyOnCore st c) st := by
  have hL1 := dispatchVacatedCore_lowEquivalent st c h
  have hI1 := dispatchVacatedCore_preserves_objects_invExt c st h.objects
  have hL2 := lowEquivalent_smp_trans (deferResidentElsewhere_lowEquivalent _ c hI1
    (currentHiddenOn_of_lowEquivalent hL1 h.current) h.idle) hL1
  unfold PriorityInheritance.settleResidencyOnCore
  dsimp only
  generalize PriorityInheritance.deferResidentElsewhere (PriorityInheritance.dispatchVacatedCore st c) c
    = st2 at hL2
  refine lowEquivalent_smp_trans ?_ hL2
  rcases PriorityInheritance.pokeReleasedResident_cases
      { st2 with machine := st2.machine.setResidentOnCore c _ } c _ _ with e | ⟨q, -, e⟩ <;>
    rw [e] <;> exact fun _ => rfl

/-- **The state the per-core reschedule entry commits** on core `c` for the
raw id `coreId`, with the frame the HAL handed over: the frame saved, the
bracketed reschedule, the residency settle, the activation, and both hardware
ledgers cleared. -/
def perCoreRescheduleEntryState (st : SystemState) (c : CoreId) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) : SystemState :=
  Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
    (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
      ((rescheduleBracket coreId).run (Architecture.saveCapturedTrapFrame st c frame)).2 c) c))

/-- **What the reschedule entry reads, hidden**: core `c`'s current thread at
the save, the scheduling point the bracketed step opens, the one the settle
opens, and the context the activated thread yielded to. -/
structure rescheduleEntryHidden (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (c : CoreId) (coreId : UInt64) (frame : Option Architecture.InFlightContext) : Prop where
  objects : st.objects.invExt
  current : currentHiddenOn ctx observer st c
  step : ∀ hc : coreId.toNat < Concurrency.numCores, schedulingPointHidden ctx observer
    (Architecture.saveCapturedTrapFrame st c frame) ⟨coreId.toNat, hc⟩
  settle : schedulingPointHidden ctx observer
    ((rescheduleBracket coreId).run (Architecture.saveCapturedTrapFrame st c frame)).2 c
  activation : activationContextHidden ctx observer (PriorityInheritance.settleResidencyOnCore
    ((rescheduleBracket coreId).run (Architecture.saveCapturedTrapFrame st c frame)).2 c) c

/-- **The reschedule entry's commit is invisible on every core** when what it
reads is hidden. -/
theorem perCoreRescheduleEntryState_lowEquivalent (st : SystemState) (c : CoreId) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext)
    (h : rescheduleEntryHidden ctx observer st c coreId frame) :
    lowEquivalent_smp ctx observer (perCoreRescheduleEntryState st c coreId frame) st := by
  have hL0 := saveCapturedTrapFrame_lowEquivalent st c frame h.objects h.current
  have hL1 := lowEquivalent_smp_trans
    (perCoreRescheduleStep_lowEquivalent _ coreId h.step) hL0
  have hL2 := lowEquivalent_smp_trans (settleResidencyOnCore_lowEquivalent _ c h.settle) hL1
  have hL3 := lowEquivalent_smp_trans (activateThreadOnCore_lowEquivalent _ c
    (settleResidencyOnCore_preserves_objects_invExt c _ h.settle.objects) h.activation
    (currentHiddenOn_of_lowEquivalent (settleResidencyOnCore_lowEquivalent _ c h.settle)
      h.settle.current)) hL2
  exact lowEquivalent_smp_trans (clearIcacheMaintenance_lowEquivalent _)
    (lowEquivalent_smp_trans (clearPhysicalWrites_lowEquivalent _) hL3)

/-- **The reschedule SGI's entry commits `perCoreRescheduleEntryState`**: the
state its atomic step writes back is that function's (`rfl`), and every value
it reads out is read off the same post-state. -/
theorem perCoreRescheduleEntry_commits (coreId : UInt64) :
    perCoreRescheduleEntry coreId =
      (match Concurrency.coreIdOfUInt64? coreId with
      | none => pure ()
      | some c => do
        let frame ← Platform.FFI.ffiTrapContext
        let (pokes, kind, context, tableBase, asid, code, writes, icache) ←
          Platform.FFI.modifyGetKernelState (fun st =>
            let mid := ((rescheduleBracket coreId).run (Architecture.saveCapturedTrapFrame st c frame)).2
            let pending := mid.scheduler.reschedulePending
            let post := activateThreadOnCore (PriorityInheritance.settleResidencyOnCore mid c) c
            ((pending.raised post.scheduler.reschedulePending, Architecture.restoreCommitKindOnCore post c,
              Architecture.restoreContextOnCore post c,
              Architecture.restoreTableBaseOnCore post c, Architecture.restoreAsidOnCore post c,
              post.scheduler.currentCode.get c, post.drainedPhysicalWrites,
              post.pendingIcacheMaintenance),
              perCoreRescheduleEntryState st c coreId frame))
        Platform.FFI.completePhysicalWrites writes
        Concurrency.fireRaisedReschedules pokes
        Platform.FFI.completeIcacheMaintenance icache
        Concurrency.releaseSwitchedFpOwnerOnCore c
        Platform.FFI.restoreTrapFrameParts kind context tableBase asid
        Concurrency.recordCommittedCurrentThreadHw (some (c, SeLe4n.ThreadId.ofOptCode code))) :=
  rfl

/-- **The secondary core's entry commits the same state**: it is the reschedule
entry (`secondaryKernelMain_eq_perCoreRescheduleEntry`). -/
theorem secondaryKernelMain_commits (coreId : UInt64) :
    secondaryKernelMain coreId =
      (match Concurrency.coreIdOfUInt64? coreId with
      | none => pure ()
      | some c => do
        let frame ← Platform.FFI.ffiTrapContext
        let (pokes, kind, context, tableBase, asid, code, writes, icache) ←
          Platform.FFI.modifyGetKernelState (fun st =>
            let mid := ((rescheduleBracket coreId).run (Architecture.saveCapturedTrapFrame st c frame)).2
            let pending := mid.scheduler.reschedulePending
            let post := activateThreadOnCore (PriorityInheritance.settleResidencyOnCore mid c) c
            ((pending.raised post.scheduler.reschedulePending, Architecture.restoreCommitKindOnCore post c,
              Architecture.restoreContextOnCore post c,
              Architecture.restoreTableBaseOnCore post c, Architecture.restoreAsidOnCore post c,
              post.scheduler.currentCode.get c, post.drainedPhysicalWrites,
              post.pendingIcacheMaintenance),
              perCoreRescheduleEntryState st c coreId frame))
        Platform.FFI.completePhysicalWrites writes
        Concurrency.fireRaisedReschedules pokes
        Platform.FFI.completeIcacheMaintenance icache
        Concurrency.releaseSwitchedFpOwnerOnCore c
        Platform.FFI.restoreTrapFrameParts kind context tableBase asid
        Concurrency.recordCommittedCurrentThreadHw (some (c, SeLe4n.ThreadId.ofOptCode code))) :=
  (secondaryKernelMain_eq_perCoreRescheduleEntry coreId).trans (perCoreRescheduleEntry_commits coreId)

end Entry

/-! ## §9 The per-core step relation and its coverage

`PerCoreNonInterferenceStep` is the per-core relation: every single-core step
the per-core theorems lift (`NonInterferenceStep` under the boot-core
confinement and the store's table invariants), and every per-core scheduler
step proven above.  Its soundness is one theorem.  The coverage taxonomy
(`PerCoreOperation`) is `KernelOperation` with the per-core scheduler steps
beside it, and its count is re-anchored over the whole of it. -/

section Coverage

/-- **The per-core scheduler steps** proven invisible above. -/
inductive PerCoreSchedulerOperation where
  | tick
  | replenishmentDrain
  | budgetExhaust
  | yieldCharge
  | yieldStep
  | activateHiddenYielder
  | activateObservableYielder
  | schedContextYieldTo
  | rescheduleSgi
  | rescheduleStep
  | rescheduleEntry
  | secondaryEntry
  | residencySettle
  | residencyDefer
  deriving DecidableEq, Repr

/-- Every per-core scheduler step, once. -/
def PerCoreSchedulerOperation.all : List PerCoreSchedulerOperation :=
  [.tick, .replenishmentDrain, .budgetExhaust, .yieldCharge, .yieldStep,
    .activateHiddenYielder, .activateObservableYielder, .schedContextYieldTo, .rescheduleSgi,
    .rescheduleStep, .rescheduleEntry, .secondaryEntry, .residencySettle, .residencyDefer]

theorem PerCoreSchedulerOperation.mem_all (op : PerCoreSchedulerOperation) :
    op ∈ PerCoreSchedulerOperation.all := by
  cases op <;> simp [PerCoreSchedulerOperation.all]

/-- **The per-core operation taxonomy**: the single-core operations, lifted,
and the per-core scheduler steps. -/
inductive PerCoreOperation where
  | kernel (op : KernelOperation)
  | scheduler (op : PerCoreSchedulerOperation)
  deriving DecidableEq

def PerCoreOperation.all : List PerCoreOperation :=
  KernelOperation.all.map .kernel ++ PerCoreSchedulerOperation.all.map .scheduler

theorem PerCoreOperation.mem_all (op : PerCoreOperation) : op ∈ PerCoreOperation.all := by
  cases op with
  | kernel op => exact List.mem_append_left _ (List.mem_map_of_mem (KernelOperation.mem_all op))
  | scheduler op =>
    exact List.mem_append_right _ (List.mem_map_of_mem (PerCoreSchedulerOperation.mem_all op))

/-- The theorem that covers each per-core scheduler step.  The secondary core's
entry is covered by the reschedule entry's theorem through
`secondaryKernelMain_commits`, which proves it commits the same state; the
observable yielder's activation by the two-state theorem. -/
def perCoreSchedulerNiTheorem : PerCoreSchedulerOperation → String
  | .tick                      => niName! timerTickOnCore_lowEquivalent
  | .replenishmentDrain        => niName! processReplenishmentsDueOnCore_lowEquivalent
  | .budgetExhaust             => niName! budgetExhaustOnCore_lowEquivalent
  | .yieldCharge               => niName! yieldChargeOnCore_lowEquivalent
  | .yieldStep                 => niName! yieldOnCore_lowEquivalent
  | .activateHiddenYielder     => niName! activateThreadOnCore_lowEquivalent
  | .activateObservableYielder => niName! activateThreadOnCore_lowEquivalent_pair
  | .schedContextYieldTo       => niName! schedContextYieldToOnCore_lowEquivalent
  | .rescheduleSgi             => niName! handleRescheduleSgiOnCore_lowEquivalent
  | .rescheduleStep            => niName! perCoreRescheduleStep_lowEquivalent
  | .rescheduleEntry           => niName! perCoreRescheduleEntryState_lowEquivalent
  | .secondaryEntry            => niName! secondaryKernelMain_commits
  | .residencySettle           => niName! settleResidencyOnCore_lowEquivalent
  | .residencyDefer            => niName! deferResidentElsewhere_lowEquivalent

/-- The theorem that covers each per-core operation. -/
def perCoreOperationNiTheorem : PerCoreOperation → String
  | .kernel op => kernelOperationPerCoreNiTheorem op
  | .scheduler op => perCoreSchedulerNiTheorem op

/-- **Fifty distinct per-core theorem names**: the thirty-six single-core
operations' lifts and the fourteen per-core scheduler steps, counted over the
enumeration (`PerCoreOperation.mem_all` ties it to the type). -/
theorem niStepCoverage_perCore_count :
    (PerCoreOperation.all.map perCoreOperationNiTheorem).eraseDups.length = 50 := by
  decide

/-- The per-core theorem names are pairwise distinct. -/
theorem perCoreOperationNiTheorem_injective :
    ∀ op₁ op₂ : PerCoreOperation,
      perCoreOperationNiTheorem op₁ = perCoreOperationNiTheorem op₂ → op₁ = op₂ := by
  intro op₁ op₂ hEq
  cases op₁ with
  | kernel a =>
    cases op₂ with
    | kernel b => exact congrArg _ (niStepCoverage_perCore_injective a b hEq)
    | scheduler b => cases a <;> cases b <;> simp [perCoreOperationNiTheorem,
        kernelOperationPerCoreNiTheorem, perCoreSchedulerNiTheorem] at hEq
  | scheduler a =>
    cases op₂ with
    | kernel b => cases a <;> cases b <;> simp [perCoreOperationNiTheorem,
        kernelOperationPerCoreNiTheorem, perCoreSchedulerNiTheorem] at hEq
    | scheduler b => cases a <;> cases b <;> (first | rfl | simp [perCoreOperationNiTheorem,
        perCoreSchedulerNiTheorem] at hEq)

/-- **The per-core non-interference step relation**: a single-core step the
per-core theorems lift, confined to the boot core's slots, or one of the
per-core scheduler steps, each under the hypotheses its theorem takes. -/
inductive PerCoreNonInterferenceStep (ctx : LabelingContext) (observer : IfObserver) :
    SystemState → SystemState → Prop where
  | kernel {st st' : SystemState} (hObjInv : st.objects.invExt) (hIdx : objectIndexSetComplete st)
      (hSet : st.objectIndexSet.table.invExt) (hStep : NonInterferenceStep ctx observer st st')
      (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
      PerCoreNonInterferenceStep ctx observer st st'
  | tick {st : SystemState} (c : CoreId) (h : tickHidden ctx observer st c) :
      PerCoreNonInterferenceStep ctx observer st (timerTickOnCore st c)
  | replenishmentDrain {st : SystemState} (c : CoreId) (now : Nat) (hInv : st.objects.invExt)
      (hRef : st.releaseQueueRefined) (hRH : releaseHiddenOn ctx observer st c) :
      PerCoreNonInterferenceStep ctx observer st (processReplenishmentsDueOnCore st c now)
  | budgetExhaust {st : SystemState} (c : CoreId) (tid : SeLe4n.ThreadId)
      (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (scId : SchedContextId)
      (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
      (hT : threadHidden ctx observer tid) (hS : objectObservable ctx observer scId.toObjId = false)
      (hInv : st.objects.invExt) (hQ : exhaustQuiet st c tid k scId sc hSc ticks) :
      PerCoreNonInterferenceStep ctx observer st (budgetExhaustOnCore st c tid k scId sc hSc ticks)
  | yieldCharge {st st' : SystemState} (c : CoreId) (tid : SeLe4n.ThreadId)
      (h : yieldChargeOnCore st c tid = .ok st') (hT : threadHidden ctx observer tid)
      (hS : ∀ tcb scId, st.getTcb? tid = some tcb → tcb.schedContextBinding.scId? = some scId →
        objectObservable ctx observer scId.toObjId = false)
      (hInv : st.objects.invExt) : PerCoreNonInterferenceStep ctx observer st st'
  | yieldStep {st st' : SystemState} (c : CoreId) (h : yieldOnCore st c = .ok st')
      (hH : yieldHidden ctx observer st c) : PerCoreNonInterferenceStep ctx observer st st'
  | activateHiddenYielder {st : SystemState} (c : CoreId) (hInv : st.objects.invExt)
      (hX : activationContextHidden ctx observer st c) (hCur : currentHiddenOn ctx observer st c) :
      PerCoreNonInterferenceStep ctx observer st (activateThreadOnCore st c)
  | schedContextYieldTo {st st' : SystemState} (s : SeLe4n.SchedContextId) (c : CoreId)
      (h : SchedContextOps.schedContextYieldToOnCore s c st = .ok st')
      (hH : yieldToHidden ctx observer st c s) : PerCoreNonInterferenceStep ctx observer st st'
  | rescheduleSgi {st st' : SystemState} (c : CoreId) (h : schedulingPointHidden ctx observer st c)
      (hStep : handleRescheduleSgiOnCore st c = .ok st') : PerCoreNonInterferenceStep ctx observer st st'
  | rescheduleStep {st : SystemState} (coreId : UInt64)
      (h : ∀ hc : coreId.toNat < Concurrency.numCores,
        schedulingPointHidden ctx observer st ⟨coreId.toNat, hc⟩) :
      PerCoreNonInterferenceStep ctx observer st (perCoreRescheduleStep st coreId)
  | rescheduleEntry {st : SystemState} (c : CoreId) (coreId : UInt64)
      (frame : Option Architecture.InFlightContext)
      (h : rescheduleEntryHidden ctx observer st c coreId frame) :
      PerCoreNonInterferenceStep ctx observer st (perCoreRescheduleEntryState st c coreId frame)
  | residencySettle {st : SystemState} (c : CoreId) (h : schedulingPointHidden ctx observer st c) :
      PerCoreNonInterferenceStep ctx observer st (PriorityInheritance.settleResidencyOnCore st c)
  | residencyDefer {st : SystemState} (c : CoreId) (hInv : st.objects.invExt)
      (hCur : currentHiddenOn ctx observer st c)
      (hIdle : threadObservable ctx observer (Kernel.idleThreadId c) = false) :
      PerCoreNonInterferenceStep ctx observer st (PriorityInheritance.deferResidentElsewhere st c)

/-- **The per-core relation is sound**: every step of it is invisible on every
core. -/
theorem perCoreNonInterferenceStep_sound {ctx : LabelingContext} {observer : IfObserver}
    {st st' : SystemState} (h : PerCoreNonInterferenceStep ctx observer st st') :
    lowEquivalent_smp ctx observer st' st := by
  cases h with
  | kernel hObjInv hIdx hSet hStep hConfined =>
    exact nonInterference_perCore ctx observer _ _ hObjInv hIdx hSet hStep hConfined
  | tick c h => exact timerTickOnCore_lowEquivalent _ c h
  | replenishmentDrain c now hInv hRef hRH =>
    exact processReplenishmentsDueOnCore_lowEquivalent _ c now hInv hRef hRH
  | budgetExhaust c tid k scId sc hSc ticks hT hS hInv hQ =>
    exact budgetExhaustOnCore_lowEquivalent _ c tid k scId sc hSc ticks hT hS hInv hQ
  | yieldCharge c tid h hT hS hInv => exact (yieldChargeOnCore_lowEquivalent h hT hS hInv).1
  | yieldStep c h hH => exact yieldOnCore_lowEquivalent h hH
  | activateHiddenYielder c hInv hX hCur => exact activateThreadOnCore_lowEquivalent _ c hInv hX hCur
  | schedContextYieldTo s c h hH => exact schedContextYieldToOnCore_lowEquivalent h hH
  | rescheduleSgi c h hStep => exact handleRescheduleSgiOnCore_lowEquivalent _ _ c h hStep
  | rescheduleStep coreId h => exact perCoreRescheduleStep_lowEquivalent _ coreId h
  | rescheduleEntry c coreId frame h => exact perCoreRescheduleEntryState_lowEquivalent _ c coreId frame h
  | residencySettle c h => exact settleResidencyOnCore_lowEquivalent _ c h
  | residencyDefer c hInv hCur hIdle => exact deferResidentElsewhere_lowEquivalent _ c hInv hCur hIdle

/-- **The secondary core's entry is the reschedule entry's constructor**: the
state it commits is `perCoreRescheduleEntryState` (`secondaryKernelMain_commits`),
so the `rescheduleEntry` step covers it. -/
theorem secondaryKernelMain_covered {ctx : LabelingContext} {observer : IfObserver}
    (st : SystemState) (c : CoreId) (coreId : UInt64) (frame : Option Architecture.InFlightContext)
    (h : rescheduleEntryHidden ctx observer st c coreId frame) :
    PerCoreNonInterferenceStep ctx observer st (perCoreRescheduleEntryState st c coreId frame) :=
  .rescheduleEntry c coreId frame h

end Coverage

end SeLe4n.Kernel
