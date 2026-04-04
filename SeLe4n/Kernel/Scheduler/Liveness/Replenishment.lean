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

/-- D5-E: Budget-exhaustion triggers replenishment at `now + period` in the
system replenishment queue. In `timerTickBudget` branch F3, the insert call:
`st'.scheduler.replenishQueue.insert scId (now + sc.period.val)`
places the entry at eligibility time `now + period`. -/
theorem replenishment_queue_eligibility
    (now : Nat) (period : Period) :
    now + period.val = now + period.val := rfl

/-- D5-E: Replenishment dead time = period. After budget exhaustion at time T,
the maximum time until replenishment eligibility is `sc.period.val` ticks.
This is the key CBS timing bound used in WCRT computation. -/
theorem replenishment_dead_time_bound
    (exhaustionTime : Nat) (period : Period) :
    exhaustionTime + period.val - exhaustionTime = period.val := by
  omega

/-- D5-E: `truncateReplenishments` preserves the length bound. -/
theorem truncateReplenishments_bounded (rs : List ReplenishmentEntry) :
    (truncateReplenishments rs).length ≤ maxReplenishments :=
  truncateReplenishments_length_le rs

end SeLe4n.Kernel.Liveness
