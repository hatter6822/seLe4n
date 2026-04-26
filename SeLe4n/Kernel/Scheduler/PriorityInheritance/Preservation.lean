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

-- ============================================================================
-- D4-O: Frame lemmas for updatePipBoost
-- ============================================================================

/-- D4-O: Helper — all paths through `updatePipBoost` preserve a given
SystemState field that is not `objects`, `scheduler.runQueue`, or `scheduler.current`. -/
private theorem updatePipBoost_frame {F : Type}
    (extract : SystemState → F)
    (st : SystemState) (tid : ThreadId)
    (h_insert : ∀ objs, extract { st with objects := objs } = extract st)
    (_h_sched : ∀ rq, extract { st with scheduler := { st.scheduler with runQueue := rq } } = extract st)
    (h_insert_sched : ∀ objs rq,
      extract { st with objects := objs, scheduler := { st.scheduler with runQueue := rq } } = extract st) :
    extract (updatePipBoost st tid) = extract st := by
  simp only [updatePipBoost]
  split
  · rename_i tcb hObj
    split
    · rfl
    · split
      · split
        · exact h_insert_sched _ _
        · exact h_insert _
      · exact h_insert _
  · rfl

/-- D4-O: `updatePipBoost` preserves the scheduler's `current` field. -/
theorem updatePipBoost_preserves_current (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.current = st.scheduler.current :=
  updatePipBoost_frame (fun s => s.scheduler.current) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-O: `updatePipBoost` preserves the scheduler's `activeDomain`. -/
theorem updatePipBoost_preserves_activeDomain (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.activeDomain = st.scheduler.activeDomain :=
  updatePipBoost_frame (fun s => s.scheduler.activeDomain) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves the machine state. -/
theorem updatePipBoost_preserves_machine (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).machine = st.machine :=
  updatePipBoost_frame (fun s => s.machine) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves the `lifecycle` field. -/
theorem updatePipBoost_preserves_lifecycle (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).lifecycle = st.lifecycle :=
  updatePipBoost_frame (fun s => s.lifecycle) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `irqHandlers`. -/
theorem updatePipBoost_preserves_irqHandlers (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).irqHandlers = st.irqHandlers :=
  updatePipBoost_frame (fun s => s.irqHandlers) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `asidTable`. -/
theorem updatePipBoost_preserves_asidTable (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).asidTable = st.asidTable :=
  updatePipBoost_frame (fun s => s.asidTable) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `serviceRegistry`. -/
theorem updatePipBoost_preserves_serviceRegistry (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).serviceRegistry = st.serviceRegistry :=
  updatePipBoost_frame (fun s => s.serviceRegistry) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `objectIndex`. -/
theorem updatePipBoost_preserves_objectIndex (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).objectIndex = st.objectIndex :=
  updatePipBoost_frame (fun s => s.objectIndex) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `objectIndexSet`. -/
theorem updatePipBoost_preserves_objectIndexSet (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).objectIndexSet = st.objectIndexSet :=
  updatePipBoost_frame (fun s => s.objectIndexSet) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `cdt`. -/
theorem updatePipBoost_preserves_cdt (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).cdt = st.cdt :=
  updatePipBoost_frame (fun s => s.cdt) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `cdtSlotNode`. -/
theorem updatePipBoost_preserves_cdtSlotNode (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).cdtSlotNode = st.cdtSlotNode :=
  updatePipBoost_frame (fun s => s.cdtSlotNode) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `cdtNodeSlot`. -/
theorem updatePipBoost_preserves_cdtNodeSlot (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).cdtNodeSlot = st.cdtNodeSlot :=
  updatePipBoost_frame (fun s => s.cdtNodeSlot) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `cdtNextNode`. -/
theorem updatePipBoost_preserves_cdtNextNode (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).cdtNextNode = st.cdtNextNode :=
  updatePipBoost_frame (fun s => s.cdtNextNode) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `interfaceRegistry`. -/
theorem updatePipBoost_preserves_interfaceRegistry (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).interfaceRegistry = st.interfaceRegistry :=
  updatePipBoost_frame (fun s => s.interfaceRegistry) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `services`. -/
theorem updatePipBoost_preserves_services (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).services = st.services :=
  updatePipBoost_frame (fun s => s.services) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- D4-P: `updatePipBoost` preserves `tlb`. -/
theorem updatePipBoost_preserves_tlb (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).tlb = st.tlb :=
  updatePipBoost_frame (fun s => s.tlb) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainTimeRemaining`. -/
theorem updatePipBoost_preserves_domainTimeRemaining (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.domainTimeRemaining =
    st.scheduler.domainTimeRemaining :=
  updatePipBoost_frame (fun s => s.scheduler.domainTimeRemaining) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainSchedule`. -/
theorem updatePipBoost_preserves_domainSchedule (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.domainSchedule =
    st.scheduler.domainSchedule :=
  updatePipBoost_frame (fun s => s.scheduler.domainSchedule) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `scheduler.domainScheduleIndex`. -/
theorem updatePipBoost_preserves_domainScheduleIndex (st : SystemState) (tid : ThreadId) :
    (updatePipBoost st tid).scheduler.domainScheduleIndex =
    st.scheduler.domainScheduleIndex :=
  updatePipBoost_frame (fun s => s.scheduler.domainScheduleIndex) st tid
    (by intro _; rfl) (by intro _; rfl) (by intro _ _; rfl)

/-- AE1-F: `updatePipBoost` preserves `objects.invExt`. -/
theorem updatePipBoost_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (hInv : st.objects.invExt) :
    (updatePipBoost st tid).objects.invExt := by
  simp only [updatePipBoost]
  split
  · rename_i tcb _
    split
    · exact hInv
    · split
      · split
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
      · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
  · exact hInv

/-- AE1-F: `updatePipBoost` does not change `objects[oid]?` for `oid ≠ tid.toObjId`. -/
theorem updatePipBoost_objects_ne (st : SystemState) (tid : ThreadId) (oid : ObjId)
    (hNe : ¬(tid.toObjId == oid) = true) (hInv : st.objects.invExt) :
    (updatePipBoost st tid).objects[oid]? = st.objects[oid]? := by
  simp only [updatePipBoost]
  split
  · split
    · rfl
    · split
      · split
        · show (st.objects.insert tid.toObjId _)[oid]? = _
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
        · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
      · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
  · rfl

/-- AE1-F: `updatePipBoost` preserves any filter over `runQueue.toList` when
the filter excludes `tid`. This is the key lemma for `projectRunnable`
preservation: since `tid` is non-observable, `threadObservable` excludes it,
so the filtered runnable list is unchanged. -/
theorem updatePipBoost_toList_filter_neg (st : SystemState) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (updatePipBoost st tid).scheduler.runQueue.toList.filter p =
    st.scheduler.runQueue.toList.filter p := by
  simp only [updatePipBoost]
  split
  · split
    · rfl
    · split
      · split
        · simp only []
          rw [RunQueue.toList_filter_insert_neg' _ tid _ _ hp,
              RunQueue.toList_filter_remove_neg _ tid _ hp]
        · rfl
      · rfl
  · rfl

-- ============================================================================
-- D4-O/P: Chain propagation frame lemmas
-- ============================================================================

/-- D4-P: `propagatePriorityInheritance` preserves the scheduler's `current`. -/
theorem propagate_preserves_current (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).scheduler.current =
    st.scheduler.current := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_current st tid
    · exact updatePipBoost_preserves_current st tid

/-- D4-P: `propagatePriorityInheritance` preserves `activeDomain`. -/
theorem propagate_preserves_activeDomain (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).scheduler.activeDomain =
    st.scheduler.activeDomain := by
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

/-- D4-P: `propagatePriorityInheritance` preserves `serviceRegistry`. -/
theorem propagate_preserves_serviceRegistry (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).serviceRegistry =
    st.serviceRegistry := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_serviceRegistry st tid
    · exact updatePipBoost_preserves_serviceRegistry st tid

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

/-- D4-P: `propagatePriorityInheritance` preserves `cdtSlotNode`. -/
theorem propagate_preserves_cdtSlotNode (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).cdtSlotNode = st.cdtSlotNode := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_cdtSlotNode st tid
    · exact updatePipBoost_preserves_cdtSlotNode st tid

/-- D4-P: `propagatePriorityInheritance` preserves `cdtNodeSlot`. -/
theorem propagate_preserves_cdtNodeSlot (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).cdtNodeSlot = st.cdtNodeSlot := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_cdtNodeSlot st tid
    · exact updatePipBoost_preserves_cdtNodeSlot st tid

/-- D4-P: `propagatePriorityInheritance` preserves `cdtNextNode`. -/
theorem propagate_preserves_cdtNextNode (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).cdtNextNode = st.cdtNextNode := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_cdtNextNode st tid
    · exact updatePipBoost_preserves_cdtNextNode st tid

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

/-- D4-P: `propagatePriorityInheritance` preserves `services`. -/
theorem propagate_preserves_services (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (propagatePriorityInheritance st tid fuel).services = st.services := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePriorityInheritance]
  | succ n ih =>
    simp only [propagatePriorityInheritance]
    split
    · rw [ih]; exact updatePipBoost_preserves_services st tid
    · exact updatePipBoost_preserves_services st tid

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
    (propagatePriorityInheritance st tid fuel).scheduler.domainTimeRemaining =
    st.scheduler.domainTimeRemaining := by
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
    (propagatePriorityInheritance st tid fuel).scheduler.domainScheduleIndex =
    st.scheduler.domainScheduleIndex := by
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

/-- D4-P: `revertPriorityInheritance` preserves `scheduler.current`. -/
theorem revert_preserves_current (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).scheduler.current =
    st.scheduler.current := by
  rw [revert_eq_propagate]; exact propagate_preserves_current st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `scheduler.activeDomain`. -/
theorem revert_preserves_activeDomain (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).scheduler.activeDomain =
    st.scheduler.activeDomain := by
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

/-- D4-P: `revertPriorityInheritance` preserves `serviceRegistry`. -/
theorem revert_preserves_serviceRegistry (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).serviceRegistry =
    st.serviceRegistry := by
  rw [revert_eq_propagate]; exact propagate_preserves_serviceRegistry st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `objectIndex`. -/
theorem revert_preserves_objectIndex (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).objectIndex = st.objectIndex := by
  rw [revert_eq_propagate]; exact propagate_preserves_objectIndex st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `cdt`. -/
theorem revert_preserves_cdt (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).cdt = st.cdt := by
  rw [revert_eq_propagate]; exact propagate_preserves_cdt st tid fuel

/-- D4-P: `revertPriorityInheritance` preserves `services`. -/
theorem revert_preserves_services (st : SystemState) (tid : ThreadId) (fuel : Nat) :
    (revertPriorityInheritance st tid fuel).services = st.services := by
  rw [revert_eq_propagate]; exact propagate_preserves_services st tid fuel

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
