-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.PerCoreSchedulerNonInterference

/-!
# Two runs, one write

The non-interference theorems of `PerCoreSchedulerNonInterference` are
one-sided: a write the observer sees nothing of leaves its view.  A write the
observer *does* see needs the two-run form: the same write, made to two
low-equivalent states, leaves them low-equivalent.  This module proves it for
the five writes seL4-MCS's `maybeDonateSchedContext` makes
(`schedContextBindPerform`): the context rewritten in its slot
(`rewriteObject`), the thread's binding written (`updateTcb`), the thread
placed on its home core (`runEnqueueOnCore`), that core flagged
(`markReschedulePendingOnCore`) and the context placed on its release queue
(`releasePlace`).

Each lemma holds for every observer.  Where the write lands in hidden state it
is the one-sided theorem twice; where it is visible, it reads only what the
two views agree on, or the lemma names what else it reads.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

section Pairs

variable {ctx : LabelingContext} {observer : IfObserver}

/-- Two low-equivalent states agree on the projected store. -/
theorem lowEquivalent_smp.objects {s₁ s₂ : SystemState}
    (h : lowEquivalent_smp ctx observer s₁ s₂) :
    projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
  congrArg ObservableState.objects (h bootCoreId)

/-- ...and on every core's filtered run queue. -/
theorem lowEquivalent_smp.runnable {s₁ s₂ : SystemState}
    (h : lowEquivalent_smp ctx observer s₁ s₂) (c : CoreId) :
    projectRunnableOnCore ctx observer s₁ c = projectRunnableOnCore ctx observer s₂ c :=
  congrArg ObservableState.runnable (h c)

/-- **A write to the store and the run queues alone**, as the views read
them: every view component other than the projected store and the filtered
run queues reads state the write keeps. -/
structure storeAndQueueWrite (st st' : SystemState) : Prop where
  objectIndex : st'.objectIndex = st.objectIndex
  irqSignalLines : st'.irqSignalLines = st.irqSignalLines
  memory : st'.machine.memory = st.machine.memory
  domainSchedule : st'.scheduler.domainSchedule = st.scheduler.domainSchedule
  current : ∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c
  activeDomain : ∀ c, st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c
  domainTimeRemaining : ∀ c, st'.scheduler.domainTimeRemainingOnCore c =
    st.scheduler.domainTimeRemainingOnCore c
  domainScheduleIndex : ∀ c, st'.scheduler.domainScheduleIndexOnCore c =
    st.scheduler.domainScheduleIndexOnCore c
  regs : ∀ c, st'.machine.regsOnCore c = st.machine.regsOnCore c

/-- A write to the object table alone is one. -/
theorem storeAndQueueWrite.of_objects {st st' : SystemState}
    (h : st' = { st with objects := st'.objects }) : storeAndQueueWrite st st' := by
  rw [h]; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

/-- **The two-run frame**: two low-equivalent states, each written in its store
and run queues alone, stay low-equivalent where the written stores project the
same and every core's filtered run queue reads the same. -/
theorem lowEquivalent_smp_pair_of_storeAndQueueWrite {s₁ s₂ s₁' s₂' : SystemState}
    (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (h₁ : storeAndQueueWrite s₁ s₁') (h₂ : storeAndQueueWrite s₂ s₂')
    (hObj : projectObjects ctx observer s₁' = projectObjects ctx observer s₂')
    (hRun : ∀ c, projectRunnableOnCore ctx observer s₁' c =
      projectRunnableOnCore ctx observer s₂' c) :
    lowEquivalent_smp ctx observer s₁' s₂' := by
  intro c
  have hd := hL c
  have hS := congrArg ObservableState.sharedFragment hd
  have hP := congrArg ObservableState.perCoreFragment hd
  simp only [projectStateOnCore_sharedFragment, projectStateOnCore_perCoreFragment,
    SharedObservableFragment.mk.injEq, PerCoreObservableFragment.mk.injEq] at hS hP
  refine ObservableState.ext_fragments ?_ ?_
  · simp only [projectStateOnCore_sharedFragment, SharedObservableFragment.mk.injEq]
    refine ⟨hObj, ?_, ?_, ?_, ?_⟩
    · have e₁ : projectIrqSignalLines ctx observer s₁' = projectIrqSignalLines ctx observer s₁ := by
        unfold projectIrqSignalLines; rw [h₁.irqSignalLines]
      have e₂ : projectIrqSignalLines ctx observer s₂' = projectIrqSignalLines ctx observer s₂ := by
        unfold projectIrqSignalLines; rw [h₂.irqSignalLines]
      rw [e₁, e₂]; exact hS.2.1
    · have e₁ : projectObjectIndex ctx observer s₁' = projectObjectIndex ctx observer s₁ := by
        unfold projectObjectIndex; rw [h₁.objectIndex]
      have e₂ : projectObjectIndex ctx observer s₂' = projectObjectIndex ctx observer s₂ := by
        unfold projectObjectIndex; rw [h₂.objectIndex]
      rw [e₁, e₂]; exact hS.2.2.1
    · have e₁ : projectDomainSchedule ctx observer s₁' = projectDomainSchedule ctx observer s₁ := by
        unfold projectDomainSchedule; rw [h₁.domainSchedule]
      have e₂ : projectDomainSchedule ctx observer s₂' = projectDomainSchedule ctx observer s₂ := by
        unfold projectDomainSchedule; rw [h₂.domainSchedule]
      rw [e₁, e₂]; exact hS.2.2.2.1
    · rw [projectMemory_eq_of_memory_eq _ _ _ _ h₁.memory,
        projectMemory_eq_of_memory_eq _ _ _ _ h₂.memory]
      exact hS.2.2.2.2
  · simp only [projectStateOnCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    refine ⟨hRun c, ?_, ?_, ?_, ?_, ?_⟩
    · rw [projectCurrentOnCore_frame _ _ (h₁.current c),
        projectCurrentOnCore_frame _ _ (h₂.current c)]; exact hP.2.1
    · rw [projectActiveDomainOnCore_frame _ _ (h₁.activeDomain c),
        projectActiveDomainOnCore_frame _ _ (h₂.activeDomain c)]; exact hP.2.2.1
    · rw [projectDomainTimeRemainingOnCore_frame _ _ (h₁.domainTimeRemaining c),
        projectDomainTimeRemainingOnCore_frame _ _ (h₂.domainTimeRemaining c)]
      exact hP.2.2.2.1
    · rw [projectDomainScheduleIndexOnCore_frame _ _ (h₁.domainScheduleIndex c),
        projectDomainScheduleIndexOnCore_frame _ _ (h₂.domainScheduleIndex c)]
      exact hP.2.2.2.2.1
    · rw [projectMachineRegsOnCore_frame _ _ (h₁.current c) (h₁.regs c),
        projectMachineRegsOnCore_frame _ _ (h₂.current c) (h₂.regs c)]
      exact hP.2.2.2.2.2

/-- **A reschedule flag raised in two runs**: no view reads it. -/
theorem markReschedulePendingOnCore_lowEquivalent_pair {s₁ s₂ : SystemState} (c : CoreId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent_smp ctx observer (s₁.markReschedulePendingOnCore c)
      (s₂.markReschedulePendingOnCore c) :=
  lowEquivalent_smp_trans (markReschedulePendingOnCore_lowEquivalent s₁ c)
    (lowEquivalent_smp_trans hL (lowEquivalent_smp_symm
      (markReschedulePendingOnCore_lowEquivalent s₂ c)))

/-- **One object rewritten in two runs**: the slot projects as the object
written in both, or is hidden in both; every other slot is kept. -/
theorem rewriteObject_lowEquivalent_pair {s₁ s₂ : SystemState} (x : SeLe4n.ObjId)
    (o : KernelObject) (h₁ : s₁.rewriteAdmissible x o) (h₂ : s₂.rewriteAdmissible x o)
    (hI₁ : s₁.objects.invExt) (hI₂ : s₂.objects.invExt)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent_smp ctx observer (s₁.rewriteObject x o h₁) (s₂.rewriteObject x o h₂) := by
  refine lowEquivalent_smp_pair_of_storeAndQueueWrite hL (storeAndQueueWrite.of_objects rfl)
    (storeAndQueueWrite.of_objects rfl) ?_ (fun c => hL.runnable c)
  funext k
  have hk := congrFun hL.objects k
  unfold projectObjects SystemState.getObject? at hk ⊢
  split
  · rename_i hO
    simp only [hO, if_true] at hk
    by_cases e : x = k
    · subst e
      rw [SystemState.rewriteObject_objects_self _ _ _ _ hI₁,
        SystemState.rewriteObject_objects_self _ _ _ _ hI₂]
    · rw [SystemState.rewriteObject_objects_ne _ _ _ _ _ e hI₁,
        SystemState.rewriteObject_objects_ne _ _ _ _ _ e hI₂]
      exact hk
  · rfl

/-- Two stores that project the same at a key hold a thread there in both or
in neither, and the two threads project the same. -/
theorem tcb_of_projected_eq {o₂ : Option KernelObject} {k : SeLe4n.ObjId} {s₁ : SystemState}
    {x₁ : TCB} (h : s₁.objects[k]? = some (.tcb x₁))
    (hO : (s₁.objects[k]?).map (projectKernelObject ctx observer) =
      o₂.map (projectKernelObject ctx observer)) :
    ∃ x₂, o₂ = some (.tcb x₂) ∧
      projectKernelObject ctx observer (.tcb x₁) = projectKernelObject ctx observer (.tcb x₂) := by
  rw [h] at hO
  cases o₂ with
  | none => cases hO
  | some y =>
    simp only [Option.map_some, Option.some.injEq] at hO
    have hT := congrArg KernelObject.objectType hO
    rw [projectKernelObject_objectType, projectKernelObject_objectType] at hT
    cases y <;> simp [KernelObject.objectType] at hT
    exact ⟨_, rfl, hO⟩

/-- **One thread update made in two runs**, by an update that keeps two
threads projecting the same (`hf`): the thread projects the same after in both
runs, or is hidden in both, or is in neither store. -/
theorem updateTcb_lowEquivalent_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId)
    (f : TCB → TCB) (hI₁ : s₁.objects.invExt) (hI₂ : s₂.objects.invExt)
    (hf : ∀ a b, projectKernelObject ctx observer (.tcb a) =
      projectKernelObject ctx observer (.tcb b) →
      projectKernelObject ctx observer (.tcb (f a)) = projectKernelObject ctx observer (.tcb (f b)))
    (hL : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent_smp ctx observer (s₁.updateTcb t f) (s₂.updateTcb t f) := by
  have hR : ∀ (s : SystemState) c, projectRunnableOnCore ctx observer (s.updateTcb t f) c =
      projectRunnableOnCore ctx observer s c := fun s c => by
    rw [SystemState.updateTcb_eq_objects_update]; rfl
  refine lowEquivalent_smp_pair_of_storeAndQueueWrite hL
    (storeAndQueueWrite.of_objects (SystemState.updateTcb_eq_objects_update _ _ _))
    (storeAndQueueWrite.of_objects (SystemState.updateTcb_eq_objects_update _ _ _)) ?_
    (fun c => by rw [hR, hR]; exact hL.runnable c)
  funext k
  have hk := congrFun hL.objects k
  unfold projectObjects SystemState.getObject? at hk ⊢
  split
  · rename_i hO
    simp only [hO, if_true] at hk
    by_cases e : t.toObjId = k
    · subst e
      cases h₁ : s₁.getTcb? t with
      | some x₁ =>
        have hO₁ := (SystemState.getTcb?_eq_some_iff _ _ _).mp h₁
        obtain ⟨x₂, hO₂, hP⟩ := tcb_of_projected_eq hO₁ hk
        rw [updateTcb_objects_self_of_tcb f hI₁ hO₁, updateTcb_objects_self_of_tcb f hI₂ hO₂]
        exact congrArg some (hf x₁ x₂ hP)
      | none =>
        cases h₂ : s₂.getTcb? t with
        | some x₂ =>
          have hO₂ := (SystemState.getTcb?_eq_some_iff _ _ _).mp h₂
          obtain ⟨x₁, hO₁, -⟩ := tcb_of_projected_eq hO₂ hk.symm
          rw [← SystemState.getTcb?_eq_some_iff] at hO₁
          rw [h₁] at hO₁; cases hO₁
        | none =>
          rw [SystemState.updateTcb_eq_self_of_none h₁, SystemState.updateTcb_eq_self_of_none h₂]
          exact hk
    · rw [SystemState.updateTcb_objects_ne _ _ _ _ e hI₁, SystemState.updateTcb_objects_ne _ _ _ _ e hI₂]
      exact hk
  · rfl

/-- A thread the filter keeps, inserted: the filtered order is read off the
filtered order alone (the queue's order is first-in first-out). -/
theorem RunQueue.toList_filter_insert_pos (rq : RunQueue) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (f : SeLe4n.ThreadId → Bool) (hf : f t = true) :
    (rq.insert t p).toList.filter f =
      if t ∈ rq.toList.filter f then rq.toList.filter f else rq.toList.filter f ++ [t] := by
  have hm : (t ∈ rq.toList.filter f) ↔ t ∈ rq := by
    rw [List.mem_filter, RunQueue.mem_toList_iff_mem]; simp [hf]
  rw [RunQueue.toList_insert]
  by_cases h : t ∈ rq
  · rw [if_pos h, if_pos (hm.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hm.mp h')), List.filter_append]; simp [hf]

/-- The enqueue writes the store and the run queues alone. -/
theorem storeAndQueueWrite.runEnqueueOnCore (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    storeAndQueueWrite st (st.runEnqueueOnCore c t p) := by
  have hD := SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p
  have hS := SystemState.runEnqueueOnCore_scheduler st c t p
  refine ⟨by rw [hD], by rw [hD], by rw [hD], ?_, ?_, ?_, ?_, ?_, fun _ => by rw [hD]⟩
  all_goals first
    | (intro c'; rw [hS]; split <;> rfl)
    | (rw [hS]; split <;> rfl)

/-- **One enqueue made in two runs.**  A hidden thread's is no view's.  An
observable thread's shows on its core's filtered queue, appended unless it is
already there, which the filtered queue shows, whatever priority each run
inserts it at (the filtered queue is read in first-in first-out order, so the
priority, which reads the erased boost, is no view's); the two runs must also agree on
whether the enqueue is admitted at all (`runEnqueueAdmits`), which reads the
thread's run-core word, a field the projection erases. -/
theorem runEnqueueOnCore_lowEquivalent_pair {s₁ s₂ : SystemState} (c : CoreId)
    (t : SeLe4n.ThreadId) (p₁ p₂ : SeLe4n.Priority) (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hA : threadObservable ctx observer t = true →
      s₁.runEnqueueAdmits c t = s₂.runEnqueueAdmits c t) :
    lowEquivalent_smp ctx observer (s₁.runEnqueueOnCore c t p₁) (s₂.runEnqueueOnCore c t p₂) := by
  have hO : ∀ (s : SystemState) p, projectObjects ctx observer (s.runEnqueueOnCore c t p) =
      projectObjects ctx observer s := fun s p =>
    projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks s c t p)
  refine lowEquivalent_smp_pair_of_storeAndQueueWrite hL
    (storeAndQueueWrite.runEnqueueOnCore s₁ c t p₁) (storeAndQueueWrite.runEnqueueOnCore s₂ c t p₂)
    (by rw [hO, hO]; exact hL.objects) ?_
  intro d
  have hd := hL.runnable d
  unfold projectRunnableOnCore at hd ⊢
  by_cases hc : c = d
  · subst hc
    rw [SystemState.runEnqueueOnCore_runQueueOnCore_self_eq,
      SystemState.runEnqueueOnCore_runQueueOnCore_self_eq]
    cases hT : threadObservable ctx observer t with
    | false =>
      have e : ∀ (s : SystemState) p,
          (if s.runEnqueueAdmits c t then (s.scheduler.runQueueOnCore c).insert t p
            else s.scheduler.runQueueOnCore c).toList.filter (threadObservable ctx observer) =
          (s.scheduler.runQueueOnCore c).toList.filter (threadObservable ctx observer) :=
        fun s p => by
          split
          · exact RunQueue.toList_filter_insert_neg' _ t p _ hT
          · rfl
      rw [e, e]; exact hd
    | true =>
      rw [hA hT]
      split
      · rw [RunQueue.toList_filter_insert_pos _ t p₁ _ hT,
          RunQueue.toList_filter_insert_pos _ t p₂ _ hT, hd]
      · exact hd
  · rw [SystemState.runEnqueueOnCore_runQueueOnCore_ne _ c d t p₁ hc,
      SystemState.runEnqueueOnCore_runQueueOnCore_ne _ c d t p₂ hc]
    exact hd

/-! ### The release placement -/

/-- A release-only write keeps every view but the store's. -/
theorem storeAndQueueWrite.of_releaseOnlyWrite {st st' : SystemState}
    (h : SystemState.releaseOnlyWrite st' st) : storeAndQueueWrite st st' :=
  ⟨by rw [h.1], by rw [h.1], by rw [h.1], by rw [h.2], h.currentOnCore,
    h.activeDomainOnCore, h.domainTimeRemainingOnCore, h.domainScheduleIndexOnCore,
    fun _ => by rw [h.1]⟩

/-- **Context `s`'s slot reads the same in two states**, as the observer
projects it. -/
def releaseSlotAgrees (ctx : LabelingContext) (observer : IfObserver) (s : SeLe4n.SchedContextId)
    (a b : SystemState) : Prop :=
  (a.objects[s.toObjId]?).map (projectKernelObject ctx observer) =
    (b.objects[s.toObjId]?).map (projectKernelObject ctx observer)

/-- Two states whose slot at `s` projects the same hold a context there in both
or in neither, with the same release core and the same place. -/
theorem releaseSlotAgrees.shape {s : SeLe4n.SchedContextId} {a b : SystemState}
    (h : releaseSlotAgrees ctx observer s a b) :
    (a.getSchedContext? s = none ∧ b.getSchedContext? s = none) ∨
      ∃ sc₁ sc₂, a.getSchedContext? s = some sc₁ ∧ b.getSchedContext? s = some sc₂ ∧
        sc₁.releaseCoreCode = sc₂.releaseCoreCode ∧ sc₁.releaseKey? = sc₂.releaseKey? := by
  unfold releaseSlotAgrees at h
  unfold SystemState.getSchedContext?
  cases ha : a.objects[s.toObjId]? with
  | none =>
    rw [ha] at h
    cases hb : b.objects[s.toObjId]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y => rw [hb] at h; cases h
  | some x =>
    rw [ha] at h
    cases hb : b.objects[s.toObjId]? with
    | none => rw [hb] at h; cases h
    | some y =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hT := congrArg KernelObject.objectType h
      rw [projectKernelObject_objectType, projectKernelObject_objectType] at hT
      cases x <;> cases y <;> simp [KernelObject.objectType] at hT <;> try exact Or.inl ⟨rfl, rfl⟩
      rename_i sc₁ sc₂
      injection h with h
      have e₁ := congrArg SchedContext.releaseCoreCode h
      have e₂ := congrArg SchedContext.releaseKey? h
      exact Or.inr ⟨sc₁, sc₂, rfl, rfl, e₁, e₂⟩

namespace releaseSlotAgrees

variable {s : SeLe4n.SchedContextId}

theorem trans {a b d : SystemState} (h₁ : releaseSlotAgrees ctx observer s a b)
    (h₂ : releaseSlotAgrees ctx observer s b d) : releaseSlotAgrees ctx observer s a d :=
  Eq.trans h₁ h₂

theorem symm {a b : SystemState} (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s b a :=
  Eq.symm h

/-- A successor link rewritten, anywhere, is erased. -/
theorem withReleaseNext (st : SystemState) (y : SeLe4n.SchedContextId) (n : Nat) :
    releaseSlotAgrees ctx observer s (st.mapSchedContextInPlace y (SchedContext.withReleaseNext n))
      st := by
  unfold releaseSlotAgrees
  rw [SystemState.objects_mapSchedContextInPlace]
  split
  · cases st.objects[s.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

/-- Context `s` rewritten in its slot in both runs, by rewrites that keep two
contexts projecting the same. -/
theorem mapSelf {a b : SystemState} (g₁ g₂ : SchedContext → SchedContext)
    (hg : ∀ x y, projectKernelObject ctx observer (.schedContext x) =
      projectKernelObject ctx observer (.schedContext y) →
      projectKernelObject ctx observer (.schedContext (g₁ x)) =
        projectKernelObject ctx observer (.schedContext (g₂ y)))
    (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s (a.mapSchedContextInPlace s g₁)
      (b.mapSchedContextInPlace s g₂) := by
  unfold releaseSlotAgrees at h ⊢
  rw [SystemState.objects_mapSchedContextInPlace, SystemState.objects_mapSchedContextInPlace,
    if_pos (beq_self_eq_true _), if_pos (beq_self_eq_true _)]
  cases ha : a.objects[s.toObjId]? with
  | none =>
    rw [ha] at h
    cases hb : b.objects[s.toObjId]? with
    | none => rfl
    | some y => rw [hb] at h; cases h
  | some x =>
    rw [ha] at h
    cases hb : b.objects[s.toObjId]? with
    | none => rw [hb] at h; cases h
    | some y =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      have hT := congrArg KernelObject.objectType h
      rw [projectKernelObject_objectType, projectKernelObject_objectType] at hT
      cases x <;> cases y <;> simp [KernelObject.objectType] at hT <;>
        first | exact h | exact hg _ _ h

end releaseSlotAgrees

namespace releaseSlotAgrees

variable {s : SeLe4n.SchedContextId}

/-- **Every question the placement asks of context `s`** reads its release core
and its place, which the projection keeps: two states whose slot at `s`
projects the same answer each the same. -/
theorem reads {a b : SystemState} (h : releaseSlotAgrees ctx observer s a b) (c : CoreId) :
    a.releaseQueuedOn c s = b.releaseQueuedOn c s ∧
    a.releaseFreeFor c s = b.releaseFreeFor c s ∧
    a.releaseKeyOf s = b.releaseKeyOf s ∧
    a.releaseQueuedAnywhere s = b.releaseQueuedAnywhere s ∧
    (a.getSchedContext? s).isNone = (b.getSchedContext? s).isNone := by
  unfold SystemState.releaseQueuedOn SystemState.releaseFreeFor SystemState.releaseCoreOf
    SystemState.releaseKeyOf SystemState.releaseQueuedAnywhere
  rcases h.shape with ⟨ha, hb⟩ | ⟨sc₁, sc₂, ha, hb, e₁, e₂⟩
  · rw [ha, hb]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [ha, hb]
    simp only [Option.bind_some, SchedContext.releaseCore?, e₁, e₂]
    exact ⟨trivial, trivial, trivial, trivial, rfl⟩

theorem project_leaveRelease (x : SchedContext) :
    projectKernelObject ctx observer (.schedContext x.leaveRelease) =
      SystemState.mapSchedContextObject SchedContext.leaveRelease
        (projectKernelObject ctx observer (.schedContext x)) := rfl

theorem project_joinRelease (c : CoreId) (n t : Nat) (x : SchedContext) :
    projectKernelObject ctx observer (.schedContext (x.joinRelease c n t)) =
      SystemState.mapSchedContextObject (SchedContext.joinRelease c 0 t)
        (projectKernelObject ctx observer (.schedContext x)) := rfl

/-- The unlink of a queued context writes it off the queue, and a successor
link the projection erases. -/
theorem releaseUnlinkOn_slot (a : SystemState) (c : CoreId) (hq : a.releaseQueuedOn c s = true) :
    releaseSlotAgrees ctx observer s (a.releaseUnlinkOn c s)
      (a.mapSchedContextInPlace s SchedContext.leaveRelease) := by
  unfold SystemState.releaseUnlinkOn
  rw [if_pos hq]
  dsimp only
  split
  · rfl
  · exact withReleaseNext _ _ _

/-- The link-in writes the context on the queue at its place before a
successor, and a successor link the projection erases. -/
theorem releaseLinkIn_slot (a : SystemState) (c : CoreId) (t : Nat) :
    ∃ n, releaseSlotAgrees ctx observer s (a.releaseLinkIn c s t)
      (a.mapSchedContextInPlace s (SchedContext.joinRelease c n t)) := by
  unfold SystemState.releaseLinkIn
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, withReleaseNext _ _ _⟩

end releaseSlotAgrees

namespace releaseSlotAgrees

variable {s : SeLe4n.SchedContextId}

theorem releaseUnlinkOn_pair {a b : SystemState} (c : CoreId)
    (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s (a.releaseUnlinkOn c s) (b.releaseUnlinkOn c s) := by
  have hq := (h.reads c).1
  cases hb : b.releaseQueuedOn c s with
  | true =>
    have ha : a.releaseQueuedOn c s = true := hq.trans hb
    exact (releaseUnlinkOn_slot a c ha).trans ((mapSelf _ _ (fun x y e => by
      rw [project_leaveRelease, project_leaveRelease, e]) h).trans
      (releaseUnlinkOn_slot b c hb).symm)
  | false =>
    have ha : a.releaseQueuedOn c s = false := hq.trans hb
    unfold SystemState.releaseUnlinkOn
    rw [if_neg (by simp [ha]), if_neg (by simp [hb])]
    exact h

theorem releaseRemoveOn_pair {a b : SystemState} (c : CoreId)
    (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s (a.releaseRemoveOn c s) (b.releaseRemoveOn c s) :=
  releaseUnlinkOn_pair c h

theorem releaseInsertOn_pair {a b : SystemState} (c : CoreId) (t : Nat)
    (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s (a.releaseInsertOn c s t) (b.releaseInsertOn c s t) := by
  obtain ⟨-, -, -, hAny, hNone⟩ := h.reads c
  unfold SystemState.releaseInsertOn
  rw [hAny, hNone]
  split
  · exact h
  · obtain ⟨n₁, h₁⟩ := releaseLinkIn_slot (ctx := ctx) (observer := observer) (s := s) a c t
    obtain ⟨n₂, h₂⟩ := releaseLinkIn_slot (ctx := ctx) (observer := observer) (s := s) b c t
    exact h₁.trans ((mapSelf _ _ (fun x y e => by
      rw [project_joinRelease, project_joinRelease, e]) h).trans h₂.symm)

theorem releasePlace_pair {a b : SystemState} (c : CoreId)
    (h : releaseSlotAgrees ctx observer s a b) :
    releaseSlotAgrees ctx observer s (a.releasePlace c s) (b.releasePlace c s) := by
  obtain ⟨-, hFree, hKey, -, -⟩ := h.reads c
  unfold SystemState.releasePlace
  rw [hFree, hKey]
  split
  · split
    · exact releaseInsertOn_pair c _ (releaseRemoveOn_pair c h)
    · exact releaseRemoveOn_pair c h
  · exact h

end releaseSlotAgrees

/-- **One release placement made in two runs.**  A hidden context's is no
view's.  An observable context's reads its release core and its place, which
the projection keeps, and writes its release core and place, which the
projection shows, and successor links, which it erases. -/
theorem releasePlace_lowEquivalent_pair {s₁ s₂ : SystemState} (c : CoreId)
    (s : SeLe4n.SchedContextId) (hL : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent_smp ctx observer (s₁.releasePlace c s) (s₂.releasePlace c s) := by
  have hW₁ := SystemState.releasePlace_releaseOnlyWrite s₁ c s
  have hW₂ := SystemState.releasePlace_releaseOnlyWrite s₂ c s
  refine lowEquivalent_smp_pair_of_storeAndQueueWrite hL
    (storeAndQueueWrite.of_releaseOnlyWrite hW₁) (storeAndQueueWrite.of_releaseOnlyWrite hW₂) ?_
    (fun d => by
      rw [projectRunnableOnCore_frame _ _ (hW₁.runQueueOnCore d),
        projectRunnableOnCore_frame _ _ (hW₂.runQueueOnCore d)]
      exact hL.runnable d)
  funext k
  have hk := congrFun hL.objects k
  unfold projectObjects SystemState.getObject? at hk ⊢
  split
  · rename_i hO
    simp only [hO, if_true] at hk
    by_cases e : k = s.toObjId
    · subst e
      exact releaseSlotAgrees.releasePlace_pair c hk
    · have hR : ∀ st : SystemState,
          ((st.releasePlace c s).objects[k]?).map (projectKernelObject ctx observer) =
            (st.objects[k]?).map (projectKernelObject ctx observer) := fun st => by
        have e' := congrArg (Option.map (projectKernelObject ctx observer))
          (releaseWriteAt.releasePlace st c s k e)
        simpa only [Option.map_map, Function.comp_def,
          projectKernelObject_withoutReleaseNext] using e'
      rw [hR, hR]; exact hk
  · rfl

end Pairs

end SeLe4n.Kernel
