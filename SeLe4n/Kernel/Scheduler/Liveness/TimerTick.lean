-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.TraceModel

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-D: Timer-tick budget monotonicity
-- ============================================================================

/-- D5-D (Z4-F1): For unbound threads, `timerTickBudget` always succeeds. -/
theorem timerTickBudget_F1_succeeds
    (st : SystemState) (tid : ThreadId) (tcb : TCB)
    (hUnbound : tcb.schedContextBinding = .unbound) :
    ∃ st' preempted, timerTickBudget st tid tcb = .ok (st', preempted) := by
  simp only [timerTickBudget, hUnbound]
  by_cases h : tcb.timeSlice ≤ 1 <;> simp [h]

/-- D5-D (Z4-F2/F3): For bound threads with a valid SchedContext lookup,
`timerTickBudget` always succeeds with preemption iff budget ≤ 1. -/
theorem timerTickBudget_bound_succeeds
    (st : SystemState) (tid : ThreadId) (tcb : TCB)
    (scId : SchedContextId) (sc : SchedContext)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hLookup : st.objects[scId.toObjId]? = some (.schedContext sc)) :
    ∃ st' preempted,
      timerTickBudget st tid tcb = .ok (st', preempted) ∧
      (preempted = true ↔ sc.budgetRemaining.val ≤ 1) := by
  simp only [timerTickBudget, hBound, hLookup]
  by_cases h : sc.budgetRemaining.val ≤ 1 <;> simp [h]

/-- D5-D (Z4-F2/F3 donated variant): Same for donated SchedContexts. -/
theorem timerTickBudget_donated_succeeds
    (st : SystemState) (tid : ThreadId) (tcb : TCB)
    (scId : SchedContextId) (owner : ThreadId) (sc : SchedContext)
    (hDonated : tcb.schedContextBinding = .donated scId owner)
    (hLookup : st.objects[scId.toObjId]? = some (.schedContext sc)) :
    ∃ st' preempted,
      timerTickBudget st tid tcb = .ok (st', preempted) ∧
      (preempted = true ↔ sc.budgetRemaining.val ≤ 1) := by
  simp only [timerTickBudget, hDonated, hLookup]
  by_cases h : sc.budgetRemaining.val ≤ 1 <;> simp [h]

/-- D5-D: `consumeBudget` decreases budget by the specified tick count
(saturating at 0). Direct from definition. -/
theorem consumeBudget_val_eq (sc : SchedContext) (ticks : Nat) :
    (consumeBudget sc ticks).budgetRemaining.val =
    sc.budgetRemaining.val - ticks := by
  simp [consumeBudget, Budget.decrement]

/-- D5-D: `consumeBudget` by 1 tick monotonically decreases budget. -/
theorem consumeBudget_one_le (sc : SchedContext) :
    (consumeBudget sc 1).budgetRemaining.val ≤ sc.budgetRemaining.val :=
  consumeBudget_budgetRemaining_le sc 1

-- ============================================================================
-- D5-F: Time-slice preemption bound
-- ============================================================================

/-- D5-F: Combined preemption bound — for any thread, preemption occurs within
`min(timeSlice, budgetRemaining)` ticks for bound threads, or `timeSlice` ticks
for unbound threads. This is the per-thread preemption interval bound. -/
def maxPreemptionInterval (tcb : TCB) (sc? : Option SchedContext) : Nat :=
  match tcb.schedContextBinding, sc? with
  | .unbound, _ => tcb.timeSlice
  | .bound _, some sc | .donated _ _, some sc =>
    Nat.min tcb.timeSlice sc.budgetRemaining.val
  | _, none => tcb.timeSlice

/-- D5-F: `maxPreemptionInterval` for unbound threads equals `timeSlice`. -/
theorem maxPreemptionInterval_unbound (tcb : TCB) (sc? : Option SchedContext)
    (h : tcb.schedContextBinding = .unbound) :
    maxPreemptionInterval tcb sc? = tcb.timeSlice := by
  simp [maxPreemptionInterval, h]

/-- D5-F: `maxPreemptionInterval` for bound threads with known SchedContext
equals `min(timeSlice, budgetRemaining)`. -/
theorem maxPreemptionInterval_bound (tcb : TCB) (sc : SchedContext)
    (scId : SchedContextId)
    (h : tcb.schedContextBinding = .bound scId) :
    maxPreemptionInterval tcb (some sc) =
    Nat.min tcb.timeSlice sc.budgetRemaining.val := by
  simp [maxPreemptionInterval, h]

/-- D5-F: `maxPreemptionInterval` is positive when both timeSlice and budget
are positive. Required for WCRT progress argument. -/
theorem maxPreemptionInterval_pos (tcb : TCB) (sc? : Option SchedContext)
    (hTs : tcb.timeSlice > 0)
    (hBudget : ∀ sc, sc? = some sc → sc.budgetRemaining.val > 0) :
    maxPreemptionInterval tcb sc? > 0 := by
  simp only [maxPreemptionInterval]
  match h : tcb.schedContextBinding, sc? with
  | .unbound, _ => exact hTs
  | .bound _, some sc => exact Nat.lt_min.mpr ⟨hTs, hBudget sc rfl⟩
  | .donated _ _, some sc => exact Nat.lt_min.mpr ⟨hTs, hBudget sc rfl⟩
  | .bound _, none => exact hTs
  | .donated _ _, none => exact hTs

end SeLe4n.Kernel.Liveness
