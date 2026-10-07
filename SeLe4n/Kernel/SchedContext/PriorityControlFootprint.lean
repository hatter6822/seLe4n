-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.SchedFootprint

/-!
# The `.tcbSetPriority` and `.tcbSetMCPriority` arms' scheduler footprint

`priorityControlWriteSet` and `schedLockSet_priorityControlOnCore`, beside the
transitions they are about (`setPriorityOnCore`, `setMCPriorityOnCore`,
`SchedContext/PriorityManagementPerCore.lean`), with the exactness frames and
the per-member coverage theorems.  Moved here from
`SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §2  The `.tcbSetPriority` and `.tcbSetMCPriority` arms
-- ============================================================================

open SeLe4n.Kernel.SchedContext.PriorityManagement in
/-- **The cores the live `.tcbSetPriority` / `.tcbSetMCPriority` may write** — the
target's home core, where its run-queue bucket migrates; the executing core,
which runs the demotion's preemption point inline; and, when the target is
reply-blocked on a server, the home cores of the inheritance chain the change
re-walks (`waiterChainWriteSet`).  A remote preemption is posted as an SGI, so
the set over-approximates by one core there.

The chain segment is read from the **pre-state**, though the walk runs after the
priority write: the write moves neither a home core nor a blocking edge, so the
two name the same cores (`priorityChangeMid_chainShape`).

SM8.B.2's write set, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.167`. -/
def priorityControlWriteSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : List CoreId :=
  [determineTargetCore st tid, executingCore] ++
    waiterChainWriteSet st tid executingCore st.objectIndex.length

/-- `v0.35.167`: the model-level preemption seam writes no replenish queue — it
either returns its input or runs the reschedule handler, which writes run queues
and current slots. -/
theorem priorityRescheduleOnCore_replenishQueueOnCore (st st' : SystemState)
    (running? : Option CoreId) (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? executingCore
      shouldPreempt = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCore at h
  split at h
  · split at h
    · split at h
      · cases hR : handleRescheduleSgiOnCore st executingCore with
        | error e => rw [hR] at h; exact absurd h (by simp)
        | ok stR =>
          rw [hR] at h
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact handleRescheduleSgiOnCore_replenishQueueOnCore st executingCore stR c hR
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
    · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]

/-- `v0.35.167`: the whole priority change — the source store (which writes
objects only), the bucket migration (one run queue) and the preemption seam. -/
theorem applyPriorityChangeOnCore_replenishQueueOnCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb newPriority
      executingCore shouldPreempt = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  rw [priorityRescheduleOnCore_replenishQueueOnCore _ st' _ executingCore shouldPreempt
      sgi c h, PriorityInheritance.repropagateFromWaiter_replenishQueueOnCore,
    markKeyChangeFor_replenishQueueOnCore,
    SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_replenishQueueOnCore]
  obtain ⟨objs, hEq⟩ :=
    SchedContext.PriorityManagement.updatePrioritySource_only_modifies_objects st tid tcb
      newPriority
  rw [hEq]

/-- **`v0.35.167`: the live `.tcbSetPriority` arm moves no reservation.** -/
theorem setPriorityOnCore_replenishQueueOnCore (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid newPriority
      executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · dsimp only at h
        exact applyPriorityChangeOnCore_replenishQueueOnCore _ st' _ _ newPriority
          executingCore _ sgi c h
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`v0.35.167`: and the live `.tcbSetMCPriority` arm**, whose ceiling write is
a typed object rewrite and so leaves the scheduler alone on the non-biting
path. -/
theorem setMCPriorityOnCore_replenishQueueOnCore (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid newMCP
      executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        split at h
        · rw [applyPriorityChangeOnCore_replenishQueueOnCore _ st' _ _ newMCP executingCore _
            sgi c h]
          rw [SystemState.rewriteObject_scheduler]
        · rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          rw [SystemState.rewriteObject_scheduler]
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`v0.35.167`: the live `.tcbSetPriority` / `.tcbSetMCPriority` arms'
scheduler-domain footprint.**

`schedFootprintOfCores` of the arms' shared SM8.B write set, with an **empty**
replenish segment: a priority change re-buckets a run queue and may take a
scheduling point, and moves no scheduling context. -/
def schedLockSet_priorityControlOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (priorityControlWriteSet st tid executingCore) []

/-- `v0.35.167`: the footprint holds the target's home core's run-queue write
lock — the bucket migration's own. -/
theorem schedLockSet_priorityControlOnCore_contains_home_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_priorityControlOnCore st tid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [priorityControlWriteSet])

/-- `v0.35.167`: ...and the executing core's, which the demotion's local
preemption point writes. -/
theorem schedLockSet_priorityControlOnCore_contains_executing_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write)
      ∈ schedLockSet_priorityControlOnCore st tid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [priorityControlWriteSet])

/-- `v0.35.167`: and **no** replenish-queue lock, on any core. -/
theorem schedLockSet_priorityControlOnCore_no_replenishQueue (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∉ schedLockSet_priorityControlOnCore st tid executingCore := by
  intro hMem
  exact absurd ((mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem) (by simp)

end SeLe4n.Kernel
