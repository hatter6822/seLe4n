-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.IPC.Operations.Fault
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.SchedFootprint

/-!
# The `.tcbResume` arm's scheduler footprint

`resumeThreadOnCoreWriteSet` and `schedLockSet_resumeThreadOnCore`, beside the
transition they are about (`resumeThreadOnCore`, `Lifecycle/Suspend.lean`),
with the exactness frame and the per-member coverage theorems.  Moved here from
`SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged: that module held the
arms whose own modules could not name a `LockKey` while the constructor sat
above them, and `Scheduler/SchedFootprint.lean` ended that.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §1  The `.tcbResume` arm
-- ============================================================================

/-- **The cores the live `.tcbResume` may write** — the resumed thread's home
core, where it re-enters the run queue, and the executing core, which runs the
reschedule inline when it *is* the home core.  A remote resume writes only the
home core and hands it an SGI, so the declared set over-approximates by one core
on that path; over-approximating is the safe direction.

SM8.B.2's write set, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.167` so the footprint
below can read it (see this module's header). -/
def resumeThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  [determineTargetCore st vtid.val, executingCore]

/-- `v0.35.167`: the resume writes **no** replenish queue on any core.

Its three legs are the ready-restore (which writes one TCB and no scheduler
state), the home-core enqueue, and — only when the home core is the executing one
— the inline reschedule handler; none of the three moves a scheduling context.
The exactness half of the empty replenish segment below. -/
theorem resumeThreadOnCore_replenishQueueOnCore (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · cases hR : handleRescheduleSgiOnCore
            (enqueueRunnableOnCore (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
              (determineTargetCore st vtid.val) vtid.val) executingCore with
        | error e => rw [hR] at h; exact absurd h (by simp)
        | ok stR =>
          rw [hR] at h
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1,
            handleRescheduleSgiOnCore_replenishQueueOnCore _ executingCore stR c hR,
            enqueueRunnableOnCore_replenishQueueOnCore, markKeyChangeFrom_replenishQueueOnCore,
            PriorityInheritance.resumeReadyMidState_scheduler_eq]
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, enqueueRunnableOnCore_replenishQueueOnCore,
            markKeyChangeFrom_replenishQueueOnCore, PriorityInheritance.resumeReadyMidState_scheduler_eq]
  · exact absurd h (by simp)

/-- **`v0.35.167`: the live `.tcbResume` arm's scheduler-domain footprint.**

`schedFootprintOfCores` of the arm's own SM8.B write set, with an **empty**
replenish segment: a resume moves no scheduling context, which
`resumeThreadOnCore_replenishQueueOnCore` is the statement of.

The fault retire the arm runs first (`retirePendingFaultForResume`, WS-RR RR4.11)
needs no member of its own: it writes one TCB's `pendingFault` and no scheduler
state at all (`retirePendingFaultForResume_scheduler_eq`). -/
def schedLockSet_resumeThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (resumeThreadOnCoreWriteSet st vtid executingCore) []

/-- **WS-LS LS2.3**: the fault retire the live `.tcbResume` arm runs first
rewrites the target's register file and clears its pending fault; the home core
reads the TCB's affinity alone, so it is the same at both states. -/
theorem retirePendingFaultForResume_determineTargetCore (st : SystemState)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    determineTargetCore (retirePendingFaultForResume st t) t = determineTargetCore st t := by
  unfold retirePendingFaultForResume
  cases hT : st.getTcb? t with
  | none => rfl
  | some tcb =>
    simp only
    cases hF : tcb.pendingFault with
    | none => rfl
    | some tf =>
      simp only [applyFaultRestart]
      unfold determineTargetCore
      rw [SystemState.updateTcb_getTcb?_self st t _ hInv, hT, Option.map_some]
      rfl

/-- **WS-LS LS2.3**: so the resume footprint resolved at the entry state is the
one the arm's transition runs under after the retire. -/
theorem schedLockSet_resumeThreadOnCore_retire (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (hInv : st.objects.invExt) :
    schedLockSet_resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore
      = schedLockSet_resumeThreadOnCore st vtid executingCore := by
  unfold schedLockSet_resumeThreadOnCore resumeThreadOnCoreWriteSet
  rw [retirePendingFaultForResume_determineTargetCore st vtid.val hInv]

/-- `v0.35.167`: the footprint holds the resumed thread's home core's run-queue
write lock — the enqueue's own. -/
theorem schedLockSet_resumeThreadOnCore_contains_home_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    (LockKey.runQueue (determineTargetCore st vtid.val), Concurrency.AccessMode.write)
      ∈ schedLockSet_resumeThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [resumeThreadOnCoreWriteSet])

/-- `v0.35.167`: ...and the executing core's, which the local reschedule writes. -/
theorem schedLockSet_resumeThreadOnCore_contains_executing_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write)
      ∈ schedLockSet_resumeThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [resumeThreadOnCoreWriteSet])

/-- `v0.35.167`: and **no** replenish-queue lock, on any core — the declaration's
exact half, against `resumeThreadOnCore_replenishQueueOnCore`'s. -/
theorem schedLockSet_resumeThreadOnCore_no_replenishQueue (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∉ schedLockSet_resumeThreadOnCore st vtid executingCore := by
  intro hMem
  exact absurd ((mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem) (by simp)

end SeLe4n.Kernel
