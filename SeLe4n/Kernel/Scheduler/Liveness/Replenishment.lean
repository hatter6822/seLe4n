-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.TimerTick

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-E: Replenishment bound
-- ============================================================================

/-- D5-E: a charge schedules the used part of the head one period after the
head's release (seL4-MCS's `refill_budget_check` handing `schedule_used` the
refill released at `rTime + period`). -/
theorem refillBudgetCheck_schedules_used_one_period_on
    (sc : SchedContext) (usage : Nat)
    (hU : 0 < usage) (hB : 0 < sc.budgetRemaining.val) :
    ∃ s : SchedContext, sc.refillBudgetCheck usage =
      s.scheduleUsed (min sc.budgetRemaining.val usage) (sc.periodStart + sc.period.val) := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  rw [if_neg (by omega)]
  split
  · exact ⟨_, by rw [Nat.min_eq_left (by omega)]⟩
  · exact ⟨_, by rw [Nat.min_eq_right (by omega)]⟩

/-- D5-E: the release of a used-up head never lowers the head's budget. -/
theorem releaseReadyHead_budget_ge (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).budgetRemaining.val ≥ sc.budgetRemaining.val := by
  have key : ∀ (n : Nat) (s : SchedContext),
      (SchedContext.releaseReadyHeadN n s now).budgetRemaining.val ≥ s.budgetRemaining.val := by
    intro n
    induction n with
    | zero => intro s; exact Nat.le_refl _
    | succ n ih =>
      intro s
      unfold SchedContext.releaseReadyHeadN
      split
      · rename_i hDue
        have h0 : s.budgetRemaining.val = 0 := by
          simp only [SchedContext.releaseDue, Bool.and_eq_true, beq_iff_eq] at hDue
          exact hDue.1.1
        omega
      · exact Nat.le_refl _
  exact key _ sc

/-- D5-E: a charge conserves the context's refills: the head and the pending
refills always sum to the same total (`chargeBudget_refillTotal`), so the head
never exceeds that total. -/
theorem chargeBudget_head_le_refillTotal (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).budgetRemaining.val ≤ sc.refillTotal := by
  rw [← sc.chargeBudget_refillTotal start usage now]
  unfold SchedContext.refillTotal
  omega

/-- D5-E: The replenishment queue sorted insertion preserves sorted order. -/
theorem replenishQueue_insert_sorted
    (rq : ReplenishQueue) (scId : SchedContextId) (eligibleAt : Nat)
    (hSorted : replenishQueueSorted rq) :
    replenishQueueSorted (rq.insert scId eligibleAt) :=
  insert_preserves_sorted hSorted

/-- D5-E: a refill released one period after the head it was used from leaves
a dead time of exactly one period: the maximum delay before the context regains
that budget. -/
theorem replenishment_within_period
    (exhaustionTime : Nat) (period : Period) (eligibleAt : Nat)
    (hEligible : eligibleAt = exhaustionTime + period.val) :
    eligibleAt - exhaustionTime = period.val := by
  subst hEligible; omega

/-- D5-E: a charge keeps the pending refills within their capacity. -/
theorem scheduleUsed_bounded (sc : SchedContext) (a t : Nat)
    (h : sc.refillSize ≤ maxReplenishments)
    (hB : sc.budgetRemaining.val = 0 ∨ sc.refillSize < maxReplenishments ∨
      sc.replenishments ≠ []) :
    (sc.scheduleUsed a t).refillSize ≤ maxReplenishments :=
  sc.scheduleUsed_refillSize_le a t h hB

end SeLe4n.Kernel.Liveness
