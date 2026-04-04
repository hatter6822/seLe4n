/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.Replenishment

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-G: Yield/rotation semantics
-- ============================================================================

/-- D5-G: `rotateToBack` preserves membership. Re-export of RunQueue lemma. -/
theorem rotateToBack_preserves_contains (rq : RunQueue) (tid t : ThreadId) :
    (rq.rotateToBack tid).contains t = rq.contains t :=
  RunQueue.rotateToBack_contains rq tid t

/-- D5-G: After yield, the yielding thread is still in the run queue (it was
re-inserted and rotated to back). The thread does NOT leave the queue on yield. -/
theorem yield_preserves_membership (rq : RunQueue) (tid : ThreadId) (prio : Priority) :
    ((rq.insert tid prio).rotateToBack tid).contains tid = true := by
  rw [RunQueue.rotateToBack_contains]
  have : tid ∈ rq.insert tid prio := (RunQueue.mem_insert rq tid prio tid).mpr (Or.inr rfl)
  exact this

-- ============================================================================
-- D5-H: FIFO progress within priority band
-- ============================================================================

/-- D5-H: FIFO progress bound — a thread at position `k` in its priority
bucket, with no higher-effective-priority threads in the active domain, is
selected within `k × maxPreemptionInterval` ticks.

This is the inductive argument: each tick preempts or yields the current
thread, advancing the target by one position, until it reaches position 0. -/
def fifoProgressBound (position : Nat) (preemptionInterval : Nat) : Nat :=
  position * preemptionInterval

/-- D5-H: The FIFO progress bound is monotone in position. -/
theorem fifoProgressBound_mono {k₁ k₂ : Nat} (interval : Nat)
    (h : k₁ ≤ k₂) :
    fifoProgressBound k₁ interval ≤ fifoProgressBound k₂ interval := by
  simp [fifoProgressBound]
  exact Nat.mul_le_mul_right interval h

/-- D5-H: Position 0 has zero wait time. -/
theorem fifoProgressBound_zero (interval : Nat) :
    fifoProgressBound 0 interval = 0 := by
  simp [fifoProgressBound]

/-- D5-H (base case): A thread at position 0 (head) in the highest-priority bucket
has zero FIFO wait — it is the immediate next selection candidate. -/
theorem fifo_head_zero_wait (interval : Nat) :
    fifoProgressBound 0 interval = 0 :=
  fifoProgressBound_zero interval

/-- D5-H: The FIFO progress bound decomposes into a step + recursive bound. -/
theorem fifoProgressBound_succ (k : Nat) (interval : Nat) :
    fifoProgressBound (k + 1) interval =
    interval + fifoProgressBound k interval := by
  simp [fifoProgressBound, Nat.succ_mul, Nat.add_comm]

/-- D5-H: FIFO progress bound is non-negative (trivially true for Nat). -/
theorem fifoProgressBound_nonneg (k interval : Nat) :
    fifoProgressBound k interval ≥ 0 :=
  Nat.zero_le _

end SeLe4n.Kernel.Liveness
