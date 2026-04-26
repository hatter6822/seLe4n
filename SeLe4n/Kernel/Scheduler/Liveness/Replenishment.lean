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

/-- D5-E: `mkReplenishmentEntry` creates an entry eligible at `currentTime + period`.
Direct from the definition — the fundamental CBS timing property. -/
theorem mkReplenishmentEntry_eligibleAt
    (consumed : Budget) (currentTime : Nat) (period : Period) :
    (mkReplenishmentEntry consumed currentTime period).eligibleAt =
    currentTime + period.val := by
  rfl

/-- D5-E: `mkReplenishmentEntry` preserves the consumed amount. -/
theorem mkReplenishmentEntry_amount
    (consumed : Budget) (currentTime : Nat) (period : Period) :
    (mkReplenishmentEntry consumed currentTime period).amount = consumed := by
  rfl

/-- D5-E: `applyRefill` with well-formed SchedContext monotonically increases budget.
Requires `budgetRemaining ≤ budget` (from `SchedContext.wellFormed`). -/
theorem applyRefill_budget_ge_when_wf (sc : SchedContext) (refillAmount : Nat)
    (hWf : sc.budgetRemaining.val ≤ sc.budget.val) :
    (applyRefill sc refillAmount).budgetRemaining.val ≥ sc.budgetRemaining.val := by
  simp [applyRefill]
  omega

/-- D5-E: After `processReplenishments` with well-formed SchedContext,
budget is ≥ the pre-state budget. -/
theorem processReplenishments_budget_ge
    (sc : SchedContext) (currentTime : Nat)
    (hWf : sc.budgetRemaining.val ≤ sc.budget.val) :
    (processReplenishments sc currentTime).budgetRemaining.val ≥
    sc.budgetRemaining.val := by
  simp [processReplenishments]
  exact applyRefill_budget_ge_when_wf _ _ hWf

/-- D5-E: The replenishment queue sorted insertion preserves sorted order. -/
theorem replenishQueue_insert_sorted
    (rq : ReplenishQueue) (scId : SchedContextId) (eligibleAt : Nat)
    (hSorted : replenishQueueSorted rq) :
    replenishQueueSorted (rq.insert scId eligibleAt) :=
  insert_preserves_sorted hSorted

/-- D5-E: After CBS budget exhaustion at time T, the replenishment queue entry
is eligible at time `T + period`. The replenishment "dead time" (time between
budget exhaustion and replenishment eligibility) equals exactly one period.
This bounds the maximum delay before a thread regains its budget. -/
theorem replenishment_within_period
    (exhaustionTime : Nat) (period : Period) (eligibleAt : Nat)
    (hEligible : eligibleAt = exhaustionTime + period.val) :
    eligibleAt - exhaustionTime = period.val := by
  subst hEligible; omega

/-- D5-E: The replenishment dead time is bounded by the period. For any entry
created by `mkReplenishmentEntry`, the gap between creation time and eligibility
is exactly `period.val` ticks. This is the fundamental CBS timing invariant. -/
theorem replenishment_dead_time_exact
    (consumed : Budget) (currentTime : Nat) (period : Period) :
    (mkReplenishmentEntry consumed currentTime period).eligibleAt - currentTime =
    period.val := by
  simp [mkReplenishmentEntry]

/-- D5-E: `truncateReplenishments` preserves the length bound. -/
theorem truncateReplenishments_bounded (rs : List ReplenishmentEntry) :
    (truncateReplenishments rs).length ≤ maxReplenishments :=
  truncateReplenishments_length_le rs

end SeLe4n.Kernel.Liveness
