/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.Yield

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-I: Priority-band exhaustion
-- ============================================================================

/-- D5-I: A thread leaves the run queue when any of these conditions hold:
(1) budget exhausted (Z4-F3: preempted and enqueued in replenish queue);
(2) blocked on IPC (enters blocking state, removed from run queue);
(3) suspended (D1: explicitly removed from run queue);
(4) yielded (temporarily at tail, but still in queue — does NOT leave). -/
inductive ThreadExitReason where
  | budgetExhausted (scId : SchedContextId)
  | blockedOnIpc
  | suspended
  | completed
  deriving Repr

/-- D5-I: Predicate asserting a thread will eventually exit the run queue.
This is the liveness hypothesis required for priority-band exhaustion.

**AF1-F: Status** — `eventuallyExits` is an EXTERNALIZED HYPOTHESIS, not a
derived property. It is used as a precondition in `higherBandExhausted` (below)
but never derived from kernel invariants in the current codebase.

- For CBS-bound threads: should follow from budget finiteness — once
  `budgetRemaining` hits 0, `timerTick` removes the thread from the run queue.
- For unbound threads: NOT satisfiable without an external progress assumption
  (e.g., all threads eventually block, yield, or complete).

Future work: derive `eventuallyExits` from CBS budget finiteness for bound
threads, connecting `consumeBudget` monotonic decrease to run queue removal.

**AI6-A (M-24) — Deployment scope**: `eventuallyExits` is externalized for
unbound threads because no kernel mechanism guarantees their termination.
Deployers must provide an external progress assumption (e.g., all threads
eventually block, yield, or complete) as a scheduling liveness guarantee.
See `WCRT.lean:bounded_scheduling_latency_exists` for integration into the
WCRT bound theorem, where `hBandProgress` subsumes this hypothesis. -/
def eventuallyExits (trace : SchedulerTrace) (tid : ThreadId) (startIdx : Nat) : Prop :=
  ∃ k, k > startIdx ∧ match traceStateAt trace k with
    | some st => st.scheduler.runQueue.contains tid = false ∧
                 st.scheduler.current ≠ some tid
    | none => False

/-- D5-I: Conditional band exhaustion — if all threads with effective priority
strictly greater than `targetPrio` in domain `d` eventually exit the run queue,
then a thread at priority `targetPrio` in domain `d` will eventually be at
the head of its priority bucket.

This is conditional on the liveness of higher-priority threads (they must
either block, exhaust budget, or be suspended). The condition is trivially
satisfied when there are no higher-priority threads. -/
def higherBandExhausted (trace : SchedulerTrace) (st : SystemState)
    (targetPrio : Priority) (targetDomain : DomainId) (startIdx : Nat) : Prop :=
  ∀ tid,
    tid ∈ st.scheduler.runQueue.flat →
    (match resolveEffectivePriority st tid with
     | some (p, _, d) => d.val = targetDomain.val ∧ p.val > targetPrio.val
     | none => False) →
    eventuallyExits trace tid startIdx

/-- D5-I: When no higher-priority threads exist, the band exhaustion condition
is trivially satisfied (vacuous quantification over the empty set of
higher-priority threads). -/
theorem higherBandExhausted_when_no_higher
    (trace : SchedulerTrace) (st : SystemState) (targetPrio : Priority)
    (targetDomain : DomainId) (startIdx : Nat)
    (hNoHigher : ∀ tid, tid ∈ st.scheduler.runQueue.flat →
      match resolveEffectivePriority st tid with
      | some (p, _, d) => ¬(d.val = targetDomain.val ∧ p.val > targetPrio.val)
      | none => True) :
    higherBandExhausted trace st targetPrio targetDomain startIdx := by
  intro tid hMem hMatch
  exact absurd hMatch (by
    have := hNoHigher tid hMem
    revert this hMatch
    split <;> simp_all)

/-- D5-I: The count of higher-or-equal priority threads is a natural bound
on the number of preemption cycles before the target thread is selected.
Each such thread consumes at most `B + P` ticks (budget + replenishment period). -/
def bandExhaustionBound (threadCount : Nat) (maxBudget : Nat) (maxPeriod : Nat) : Nat :=
  threadCount * (maxBudget + maxPeriod)

/-- D5-I: Band exhaustion bound is monotone in thread count. -/
theorem bandExhaustionBound_mono {n₁ n₂ : Nat} (B P : Nat)
    (h : n₁ ≤ n₂) :
    bandExhaustionBound n₁ B P ≤ bandExhaustionBound n₂ B P := by
  simp [bandExhaustionBound]
  exact Nat.mul_le_mul_right (B + P) h

/-- D5-I: Band exhaustion bound with zero threads is zero. -/
theorem bandExhaustionBound_zero (B P : Nat) :
    bandExhaustionBound 0 B P = 0 := by
  simp [bandExhaustionBound]

/-- D5-I: Band exhaustion bound decomposes. -/
theorem bandExhaustionBound_succ (n B P : Nat) :
    bandExhaustionBound (n + 1) B P = (B + P) + bandExhaustionBound n B P := by
  simp [bandExhaustionBound, Nat.succ_mul, Nat.add_comm]

end SeLe4n.Kernel.Liveness
