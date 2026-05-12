-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph
import SeLe4n.Kernel.Scheduler.Operations.Selection

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model

-- ============================================================================
-- D4-F: computeMaxWaiterPriority
-- ============================================================================

/-- D4-F: Compute the maximum effective priority among all threads
directly blocked on `tid` via Reply IPC. Returns `none` if no waiters.

WS-RC R5.C (DEEP-SCH-02): migrated from the partial `effectivePriority`
helper (which returned `Option`) to the total `effectiveSchedParams`
helper.  Under `schedContextStoreConsistent` (part of
`crossSubsystemInvariant`), the pre-R5 `effectivePriority` `none` branch
was unreachable; under `effectiveSchedParams`, the SC-missing case falls
back to the waiter's TCB priority/deadline/domain.  The two helpers
agree pointwise where `effectivePriority` returns `some _` (witness:
`effectivePriority_some_eq_effectiveSchedParams`), so this migration is
semantics-preserving under the runtime invariant.  The migration is
part of R5.C's API-uniformity goal: callers no longer thread `Option`
propagation through the priority-inheritance fold. -/
def computeMaxWaiterPriority (st : SystemState) (tid : ThreadId)
    : Option Priority :=
  let waiters := waitersOf st tid
  waiters.foldl (fun acc waiterTid =>
    match st.objects[waiterTid.toObjId]? with
    | some (KernelObject.tcb waiterTcb) =>
      let (prio, _, _) := effectiveSchedParams st waiterTcb
      match acc with
      | none => some prio
      | some curMax => some ⟨Nat.max curMax.val prio.val⟩
    | _ => acc) none

/-- D4-F: computeMaxWaiterPriority of a thread with no waiters is none. -/
theorem computeMaxWaiterPriority_no_waiters (st : SystemState) (tid : ThreadId)
    (h : waitersOf st tid = []) :
    computeMaxWaiterPriority st tid = none := by
  simp [computeMaxWaiterPriority, h]

end SeLe4n.Kernel.PriorityInheritance
