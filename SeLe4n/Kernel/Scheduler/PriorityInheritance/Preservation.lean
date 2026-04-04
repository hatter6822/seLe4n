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

end SeLe4n.Kernel.PriorityInheritance
