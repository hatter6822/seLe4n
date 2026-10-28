-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.RobinHood.Bridge

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- D4-O: Frame lemmas for updatePipBoost
-- ============================================================================

/-- WS-ZA ZA4.5: a re-key over an object write lands in the shape
`updatePipBoost_frame`'s `h_insert_sched` names. -/
private theorem extract_runRequeueOnCore_of_objects {F : Type} (extract : SystemState → F)
    (st : SystemState) (objs : SeLe4n.Kernel.RobinHood.RHTable ObjId KernelObject)
    (c : Concurrency.CoreId) (t : ThreadId) (p : SeLe4n.Priority)
    (h_insert_sched : ∀ objs c e rq, extract { st with objects := objs, scheduler :=
      (st.scheduler.setRunQueueEndsOnCore c e).setRunQueueOnCore c rq } = extract st) :
    extract (({ st with objects := objs } : SystemState).runRequeueOnCore c t p) = extract st := by
  have hD := SystemState.runRequeueOnCore_onlyObjectsSchedulerDiffer
    ({ st with objects := objs } : SystemState) c t p
  unfold SystemState.onlyObjectsSchedulerDiffer at hD
  rw [hD, SystemState.runRequeueOnCore_scheduler]
  exact h_insert_sched _ _ _ _

/-- D4-O: Helper — all paths through `updatePipBoost` preserve a given
SystemState field that is not `objects`, `scheduler.runQueue`, or `scheduler.current`. -/
private theorem updatePipBoost_frame {F : Type}
    (extract : SystemState → F)
    (st : SystemState) (tid : ThreadId)
    (h_insert : ∀ objs, extract { st with objects := objs } = extract st)
    (h_insert_sched : ∀ objs c e rq, extract { st with objects := objs, scheduler :=
      (st.scheduler.setRunQueueEndsOnCore c e).setRunQueueOnCore c rq } = extract st)
    (h_pending : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (updatePipBoost st tid) = extract st := by
  simp only [updatePipBoost, updatePipBoostOnCore, SystemState.rewriteObject]
  split
  · rename_i tcb hObj _
    split
    · rfl
    · split
      · split
        · -- the re-key writes run-queue links and the core's queue (WS-ZA ZA4.5)
          exact (markKeyChangeFor_extract_frame extract _ _ _ h_pending).trans
            (extract_runRequeueOnCore_of_objects extract st _ _ _ _ h_insert_sched)
        · exact (markKeyChangeFor_extract_frame extract _ _ _ h_pending).trans (h_insert _)
      · exact (markKeyChangeFor_extract_frame extract _ _ _ h_pending).trans (h_insert _)
  · rfl

/-- D4-O (every-core form, PR #880 round 8): `updatePipBoost` preserves every
core's `current` slot — it writes only `objects` and (at most) the boot run
queue, and `currentOnCore` reads neither. -/
theorem updatePipBoost_currentOnCore_eq (st : SystemState) (tid : ThreadId)
    (c' : Concurrency.CoreId) :
    ((updatePipBoost st tid).scheduler.currentOnCore c') = (st.scheduler.currentOnCore c') :=
  updatePipBoost_frame (fun s => (s.scheduler.currentOnCore c')) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-O: `updatePipBoost` preserves the scheduler's `current` field. -/
theorem updatePipBoost_preserves_current (st : SystemState) (tid : ThreadId) :
    ((updatePipBoost st tid).scheduler.currentOnCore bootCoreId) = (st.scheduler.currentOnCore bootCoreId) :=
  updatePipBoost_currentOnCore_eq st tid bootCoreId

/-- D4-O: `updatePipBoost` preserves the scheduler's `activeDomain`. -/
theorem updatePipBoost_preserves_activeDomain (st : SystemState) (tid : ThreadId) :
    ((updatePipBoost st tid).scheduler.activeDomainOnCore bootCoreId) = (st.scheduler.activeDomainOnCore bootCoreId) :=
  updatePipBoost_frame (fun s => (s.scheduler.activeDomainOnCore bootCoreId)) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves the machine state. -/
theorem updatePipBoost_preserves_machine (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).machine = st.machine :=
  updatePipBoost_frame (fun s => s.machine) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves the `lifecycle` field. -/
theorem updatePipBoost_preserves_lifecycle (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).lifecycle = st.lifecycle :=
  updatePipBoost_frame (fun s => s.lifecycle) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `irqHandlers`. -/
theorem updatePipBoost_preserves_irqHandlers (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).irqHandlers = st.irqHandlers :=
  updatePipBoost_frame (fun s => s.irqHandlers) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `asidTable`. -/
theorem updatePipBoost_preserves_asidTable (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).asidTable = st.asidTable :=
  updatePipBoost_frame (fun s => s.asidTable) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `objectIndex`. -/
theorem updatePipBoost_preserves_objectIndex (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).objectIndex = st.objectIndex :=
  updatePipBoost_frame (fun s => s.objectIndex) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `objectIndexSet`. -/
theorem updatePipBoost_preserves_objectIndexSet (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).objectIndexSet = st.objectIndexSet :=
  updatePipBoost_frame (fun s => s.objectIndexSet) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `cdt`. -/
theorem updatePipBoost_preserves_cdt (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).cdt = st.cdt :=
  updatePipBoost_frame (fun s => s.cdt) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `interfaceRegistry`. -/
theorem updatePipBoost_preserves_interfaceRegistry (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).interfaceRegistry = st.interfaceRegistry :=
  updatePipBoost_frame (fun s => s.interfaceRegistry) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `tlb`. -/
theorem updatePipBoost_preserves_tlb (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).tlb = st.tlb :=
  updatePipBoost_frame (fun s => s.tlb) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainTimeRemaining`. -/
theorem updatePipBoost_preserves_domainTimeRemaining (st : SystemState) (tid : ThreadId) :
    ((updatePipBoost st tid).scheduler.domainTimeRemainingOnCore bootCoreId) =
    (st.scheduler.domainTimeRemainingOnCore bootCoreId) :=
  updatePipBoost_frame (fun s => (s.scheduler.domainTimeRemainingOnCore bootCoreId)) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainSchedule`. -/
theorem updatePipBoost_preserves_domainSchedule (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.domainSchedule =
    st.scheduler.domainSchedule :=
  updatePipBoost_frame (fun s => s.scheduler.domainSchedule) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainScheduleIndex`. -/
theorem updatePipBoost_preserves_domainScheduleIndex (st : SystemState) (tid : ThreadId) :
    ((updatePipBoost st tid).scheduler.domainScheduleIndexOnCore bootCoreId) =
    (st.scheduler.domainScheduleIndexOnCore bootCoreId) :=
  updatePipBoost_frame (fun s => (s.scheduler.domainScheduleIndexOnCore bootCoreId)) st tid
    (by intro _; rfl) (by intro _ _ _ _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `objects.invExt`. -/
theorem updatePipBoost_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (hInv : st.objects.invExt) :
    (updatePipBoost st tid).objects.invExt :=
  updatePipBoostOnCore_preserves_objects_invExt st bootCoreId tid hInv

/-- AE1-F: `updatePipBoost` does not change `objects[oid]?` for `oid ≠ tid.toObjId`,
off the run-queue links its bucket re-key rewrites (WS-ZA ZA4.5). -/
theorem updatePipBoost_objects_ne (st : SystemState) (tid : ThreadId) (oid : ObjId)
    (hNe : ¬(tid.toObjId == oid) = true) (hInv : st.objects.invExt) :
    ((updatePipBoost st tid).objects[oid]?).map KernelObject.withoutRunLinks
      = (st.objects[oid]?).map KernelObject.withoutRunLinks :=
  updatePipBoostOnCore_objects_ne st bootCoreId tid oid hNe hInv

/-- AE1-F: `updatePipBoost` preserves any filter over `runQueue.toList` when
the filter excludes `tid`. This is the key lemma for `projectRunnable`
preservation: since `tid` is non-observable, `threadObservable` excludes it,
so the filtered runnable list is unchanged. -/
theorem updatePipBoost_toList_filter_neg (st : SystemState) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    ((updatePipBoost st tid).scheduler.runQueueOnCore bootCoreId).toList.filter p =
    (st.scheduler.runQueueOnCore bootCoreId).toList.filter p := by
  simp only [updatePipBoost, updatePipBoostOnCore, SystemState.rewriteObject]
  split
  · split
    · rfl
    · split
      · split
        · rw [markKeyChangeFor_runQueueOnCore, SystemState.runRequeueOnCore_scheduler]
          simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [RunQueue.toList_filter_rekey_neg _ tid _ _ hp]
        · rw [markKeyChangeFor_runQueueOnCore]
      · rw [markKeyChangeFor_runQueueOnCore]
  · rfl

-- ============================================================================
-- D4-O/P: Chain propagation frame lemmas
-- ============================================================================

/-- D4-P (every-core form, PR #880 round 8): the chain walk is `updatePipBoost`
at each step, so it too preserves every core's `current` slot. -/
theorem propagate_currentOnCore_eq (st : SystemState) (tid : ThreadId)
    (fuel : Nat) (c' : Concurrency.CoreId) :
    ((propagatePriorityInheritance st tid fuel).scheduler.currentOnCore c') =
    (st.scheduler.currentOnCore c') := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_currentOnCore_eq st tid c'
    · exact updatePipBoost_currentOnCore_eq st tid c'

/-- D4-P: `propagatePriorityInheritance` preserves the scheduler's `current`. -/
theorem propagate_preserves_current (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    ((propagatePriorityInheritance st tid fuel).scheduler.currentOnCore bootCoreId) =
    (st.scheduler.currentOnCore bootCoreId) :=
  propagate_currentOnCore_eq st tid fuel bootCoreId

/-- D4-P: `propagatePriorityInheritance` preserves `activeDomain`. -/
theorem propagate_preserves_activeDomain (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    ((propagatePriorityInheritance st tid fuel).scheduler.activeDomainOnCore bootCoreId) =
    (st.scheduler.activeDomainOnCore bootCoreId) := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_activeDomain st tid
    · exact updatePipBoost_preserves_activeDomain st tid

/-- D4-P: `propagatePriorityInheritance` preserves the machine state. -/
theorem propagate_preserves_machine (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).machine = st.machine := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_machine st tid
    · exact updatePipBoost_preserves_machine st tid

/-- D4-P: `propagatePriorityInheritance` preserves `lifecycle`. -/
theorem propagate_preserves_lifecycle (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).lifecycle = st.lifecycle := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_lifecycle st tid
    · exact updatePipBoost_preserves_lifecycle st tid

/-- D4-P: `propagatePriorityInheritance` preserves `irqHandlers`. -/
theorem propagate_preserves_irqHandlers (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).irqHandlers = st.irqHandlers := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_irqHandlers st tid
    · exact updatePipBoost_preserves_irqHandlers st tid

/-- D4-P: `propagatePriorityInheritance` preserves `asidTable`. -/
theorem propagate_preserves_asidTable (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).asidTable = st.asidTable := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_asidTable st tid
    · exact updatePipBoost_preserves_asidTable st tid

/-- D4-P: `propagatePriorityInheritance` preserves `objectIndex`. -/
theorem propagate_preserves_objectIndex (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).objectIndex = st.objectIndex := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_objectIndex st tid
    · exact updatePipBoost_preserves_objectIndex st tid

/-- D4-P: `propagatePriorityInheritance` preserves `objectIndexSet`. -/
theorem propagate_preserves_objectIndexSet (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).objectIndexSet =
    st.objectIndexSet := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_objectIndexSet st tid
    · exact updatePipBoost_preserves_objectIndexSet st tid

/-- D4-P: `propagatePriorityInheritance` preserves `cdt`. -/
theorem propagate_preserves_cdt (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).cdt = st.cdt := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_cdt st tid
    · exact updatePipBoost_preserves_cdt st tid

/-- D4-P: `propagatePriorityInheritance` preserves `interfaceRegistry`. -/
theorem propagate_preserves_interfaceRegistry (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).interfaceRegistry =
    st.interfaceRegistry := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_interfaceRegistry st tid
    · exact updatePipBoost_preserves_interfaceRegistry st tid

/-- D4-P: `propagatePriorityInheritance` preserves `tlb`. -/
theorem propagate_preserves_tlb (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).tlb = st.tlb := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_tlb st tid
    · exact updatePipBoost_preserves_tlb st tid

/-- AE1-F: `propagatePriorityInheritance` preserves `scheduler.domainTimeRemaining`. -/
theorem propagate_preserves_domainTimeRemaining (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    ((propagatePriorityInheritance st tid fuel).scheduler.domainTimeRemainingOnCore bootCoreId) =
    (st.scheduler.domainTimeRemainingOnCore bootCoreId) := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_domainTimeRemaining st tid
    · exact updatePipBoost_preserves_domainTimeRemaining st tid

/-- AE1-F: `propagatePriorityInheritance` preserves `scheduler.domainSchedule`. -/
theorem propagate_preserves_domainSchedule (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).scheduler.domainSchedule =
    st.scheduler.domainSchedule := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_domainSchedule st tid
    · exact updatePipBoost_preserves_domainSchedule st tid

/-- AE1-F: `propagatePriorityInheritance` preserves `scheduler.domainScheduleIndex`. -/
theorem propagate_preserves_domainScheduleIndex (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    ((propagatePriorityInheritance st tid fuel).scheduler.domainScheduleIndexOnCore bootCoreId) =
    (st.scheduler.domainScheduleIndexOnCore bootCoreId) := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_domainScheduleIndex st tid
    · exact updatePipBoost_preserves_domainScheduleIndex st tid

-- ============================================================================
-- D4-P: Revert frame lemmas (derived from revert_eq_propagate)
-- ============================================================================

/-- D4-P (every-core form, PR #880 round 8): the reversion walk preserves every
core's `current` slot. -/
theorem revert_currentOnCore_eq (st : SystemState) (tid : ThreadId) (fuel : Nat)
    (c' : Concurrency.CoreId) :
    ((revertPriorityInheritance st tid fuel).scheduler.currentOnCore c') =
    (st.scheduler.currentOnCore c') := by
  rw [revert_eq_propagate]; exact propagate_currentOnCore_eq st tid fuel c'

/-- D4-P: `revertPriorityInheritance` preserves `scheduler.current`. -/
theorem revert_preserves_current (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    ((revertPriorityInheritance st tid fuel).scheduler.currentOnCore bootCoreId) =
    (st.scheduler.currentOnCore bootCoreId) :=
  revert_currentOnCore_eq st tid fuel bootCoreId

/-- D4-P: `revertPriorityInheritance` preserves `scheduler.activeDomain`. -/
theorem revert_preserves_activeDomain (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    ((revertPriorityInheritance st tid fuel).scheduler.activeDomainOnCore bootCoreId) =
    (st.scheduler.activeDomainOnCore bootCoreId) := by
  rw [revert_eq_propagate]; exact propagate_preserves_activeDomain st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `machine`. -/
theorem revert_preserves_machine (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).machine = st.machine := by
  rw [revert_eq_propagate]; exact propagate_preserves_machine st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `lifecycle`. -/
theorem revert_preserves_lifecycle (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).lifecycle = st.lifecycle := by
  rw [revert_eq_propagate]; exact propagate_preserves_lifecycle st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `irqHandlers`. -/
theorem revert_preserves_irqHandlers (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).irqHandlers = st.irqHandlers := by
  rw [revert_eq_propagate]; exact propagate_preserves_irqHandlers st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `asidTable`. -/
theorem revert_preserves_asidTable (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).asidTable = st.asidTable := by
  rw [revert_eq_propagate]; exact propagate_preserves_asidTable st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `objectIndex`. -/
theorem revert_preserves_objectIndex (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).objectIndex = st.objectIndex := by
  rw [revert_eq_propagate]; exact propagate_preserves_objectIndex st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `cdt`. -/
theorem revert_preserves_cdt (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).cdt = st.cdt := by
  rw [revert_eq_propagate]; exact propagate_preserves_cdt st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `tlb`. -/
theorem revert_preserves_tlb (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).tlb = st.tlb := by
  rw [revert_eq_propagate]; exact propagate_preserves_tlb st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `interfaceRegistry`. -/
theorem revert_preserves_interfaceRegistry (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).interfaceRegistry =
    st.interfaceRegistry := by
  rw [revert_eq_propagate]; exact propagate_preserves_interfaceRegistry st tid fuel

end SeLe4n.Kernel.PriorityInheritance
