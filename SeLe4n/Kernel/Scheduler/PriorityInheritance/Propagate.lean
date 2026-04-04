/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model

-- ============================================================================
-- D4-G: updatePipBoost (single-thread priority update)
-- ============================================================================

/-- D4-G: Update the `pipBoost` field for a single thread based on its
current waiters. If the thread has higher-priority waiters than its base
priority, sets `pipBoost` to the maximum waiter priority. Otherwise clears it.

If the thread is in the run queue and effective priority changed, performs
remove-then-insert for bucket migration (D2-E pattern). -/
def updatePipBoost (st : SystemState) (tid : ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (KernelObject.tcb tcb) =>
    let newBoost := computeMaxWaiterPriority st tid
    -- Only update if pipBoost actually changed
    if tcb.pipBoost == newBoost then st
    else
      -- Update TCB with new pipBoost
      let tcb' := { tcb with pipBoost := newBoost }
      let st' := { st with objects := st.objects.insert tid.toObjId (KernelObject.tcb tcb') }
      -- Conditional run queue bucket migration
      if tid ∈ st.scheduler.runQueue then
        let oldPrio := (resolveEffectivePrioDeadline st tcb).1
        let newPrio := (resolveEffectivePrioDeadline st' tcb').1
        if oldPrio != newPrio then
          { st' with
            scheduler := {
              st'.scheduler with
              runQueue := (st'.scheduler.runQueue.remove tid).insert tid newPrio
            }
          }
        else st'
      else st'
  | _ => st

-- ============================================================================
-- D4-H: propagatePriorityInheritance (chain walk)
-- ============================================================================

/-- D4-H: Walk the blocking chain upward from `startTid`, applying
`updatePipBoost` at each step. If the thread is itself blocked on
another server via Reply, continues propagation upward.

Terminates when fuel exhausted, thread not blocked, or no server found.
Default fuel = objectIndex.length (sufficient by D4-E). -/
def propagatePriorityInheritance (st : SystemState) (startTid : ThreadId)
    (fuel : Nat := st.objectIndex.length) : SystemState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    -- Apply updatePipBoost to the current thread
    let st' := updatePipBoost st startTid
    -- Check if this thread is itself blocked on a server
    match blockingServer st startTid with
    | some nextServer =>
      -- Propagate upward through the chain
      propagatePriorityInheritance st' nextServer fuel'
    | none => st'

-- ============================================================================
-- D4-I: revertPriorityInheritance (chain reversion)
-- ============================================================================

/-- D4-I: Revert priority inheritance for `tid` and its blocking chain.
Called when a client is unblocked (Reply completes) — recomputes `pipBoost`
for `tid` based on remaining waiters, then propagates upward.

Structurally identical to propagation: the `updatePipBoost` function
uniformly handles both boost and reversion because it always recomputes
from the current `waitersOf`. -/
def revertPriorityInheritance (st : SystemState) (tid : ThreadId)
    (fuel : Nat := st.objectIndex.length) : SystemState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    let st' := updatePipBoost st tid
    match blockingServer st tid with
    | some nextServer =>
      revertPriorityInheritance st' nextServer fuel'
    | none => st'

-- ============================================================================
-- D4-J: Propagation correctness
-- ============================================================================

/-- D4-J: Propagation with zero fuel is identity. -/
theorem propagate_zero (st : SystemState) (tid : ThreadId) :
    propagatePriorityInheritance st tid 0 = st := by
  rfl

/-- D4-J: Propagation with nonzero fuel applies updatePipBoost first. -/
theorem propagate_step (st : SystemState) (tid : ThreadId) (n : Nat) :
    propagatePriorityInheritance st tid (n + 1) =
      match blockingServer st tid with
      | some nextServer => propagatePriorityInheritance (updatePipBoost st tid) nextServer n
      | none => updatePipBoost st tid := by
  rfl

-- ============================================================================
-- D4-K: Reversion correctness
-- ============================================================================

/-- D4-K: Reversion is functionally identical to propagation on the
current state. Both compute from current `waitersOf`. -/
theorem revert_eq_propagate (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    revertPriorityInheritance st tid fuel =
    propagatePriorityInheritance st tid fuel := by
  induction fuel generalizing st tid with
  | zero => simp [revertPriorityInheritance, propagatePriorityInheritance]
  | succ n ih =>
    simp only [revertPriorityInheritance, propagatePriorityInheritance]
    split
    · exact ih ..
    · rfl

end SeLe4n.Kernel.PriorityInheritance
