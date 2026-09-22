-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# `v0.35.167` (WS-RR RR8.12 Cut C3b-i) — the syscall arms whose own modules cannot name a `SchedLockId`

Every scheduler-domain footprint declared so far sits beside the transition it is
about: `schedLockSet_endpointSendOnCore` in `EndpointSend.lean`,
`schedLockSet_endpointCallOnCore` in `EndpointCallDispatch.lean`,
`schedLockSet_endpointReplyRecvOnCore` in `API.lean`, and so on.  That placement
is not a convention this module abandons — it is one this module cannot follow,
for a reason worth stating once rather than rediscovering per arm.

## Why these arms are here

`SchedLockId` — the cross-domain lock identifier every scheduler footprint is a
list of — is declared in `Scheduler/Operations/PerCoreChooseThread.lean`, and
that module imports `Lifecycle/Suspend.lean` and `IPC/Operations/Endpoint.lean`.
So it sits **above** the modules holding the lifecycle, priority, affinity,
SchedContext and retype transitions, and none of them can name a `SchedLockId`
at all.  Measured: `Lifecycle/Suspend.lean`, `SchedContext/Operations.lean`,
`SchedContext/PriorityManagementPerCore.lean`, `Scheduler/Operations/Core.lean`
and `Lifecycle/Operations/RetypeWrappers.lean` are all outside
`PerCoreChooseThread`'s reverse closure.

Moving `SchedLockId` down was considered and rejected: it is declared with
`RunQueueLockId` and `ReplenishQueueLockId` and the cross-domain order over them
(`object_lt_runQueue`, `runQueue_lt_replenishQueue`), and that order is what
`schedCoreSegment` and `schedFootprintOfCores` are *about* — the constructor's own
docstring records the decision to keep the three together.  So the rule this
module states instead is:

> **A resolved scheduler footprint lives beside its transition where that module
> can name a `SchedLockId`, and here where it cannot.**

The write sets follow the footprints for the same reason: a write set exists to
be the argument of `schedFootprintOfCores` (and of the staged confinement
theorem), and splitting the pair across two modules to satisfy a convention
neither half can follow buys nothing.  Each carries the tombstone of its move out
of the staged `InformationFlow/NonInterferenceCrossCore.lean`, where a production
footprint could not read it — the layering finding Cuts 7, 8a-ii and C3a each
paid once, arriving at the three arms nobody had asked it of.

## What is *not* here

A **parametric** footprint is not a resolved one and does not belong in this
module.  `setThreadCpuAffinityWithMigrationLockSet` — the SM5.H.4 form, which
takes two cores and no state — went to `Scheduler/Operations/PerCoreChooseThread.lean`
in this cut, beside `migrateSchedContextReplenishmentLockSet`, which WS-RR RR2.4
had relocated out of the same staged module for the same reason and twenty lines
short of its own siblings.  `schedLockSet_setThreadCpuAffinityOnCore_covers_parametric`
is the relation between the two, and it is what that relocation buys: a resolved
footprint whose counterpart is unreachable can state nothing about it.

## The exactness frames

Every empty replenish segment here is a **theorem**, not a reading of the body:
`observableSlotsConfinedToCores` covers six per-core slots and the replenish queue
is not one of them, so a write set says nothing about replenishments and a
footprint that declared one it does not write would be wider than its operation —
which costs the arm lock contention the operation does not have, an observable
channel (SM8.D's CC-5) and the reason WS-OD OD3.5 *narrowed* a footprint.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

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
            (enqueueRunnableOnCore (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
              (determineTargetCore st vtid.val) vtid.val) executingCore with
        | error e => rw [hR] at h; exact absurd h (by simp)
        | ok stR =>
          rw [hR] at h
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1,
            handleRescheduleSgiOnCore_replenishQueueOnCore _ executingCore stR c hR,
            enqueueRunnableOnCore_replenishQueueOnCore,
            PriorityInheritance.resumeReadyMidState_scheduler_eq]
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, enqueueRunnableOnCore_replenishQueueOnCore,
            PriorityInheritance.resumeReadyMidState_scheduler_eq]
  · exact absurd h (by simp)

/-- `v0.35.167`: and so does the enqueue-only form the gated wrapper takes while
the context-restore seam is dark — a strict subset of the above. -/
theorem resumeThreadEnqueueOnly_replenishQueueOnCore (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : Lifecycle.Suspend.resumeThreadEnqueueOnly st vtid executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold Lifecycle.Suspend.resumeThreadEnqueueOnly at h
  dsimp only at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h <;>
        (rw [Except.ok.injEq, Prod.mk.injEq] at h
         rw [← h.1, enqueueRunnableOnCore_replenishQueueOnCore,
            PriorityInheritance.resumeReadyMidState_scheduler_eq])
  · exact absurd h (by simp)

/-- `v0.35.167`: so the gated wrapper the live `.tcbResume` arm runs writes none
either, on both settings of the seam. -/
theorem resumeThreadOnCoreLive_replenishQueueOnCore (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : Lifecycle.Suspend.resumeThreadOnCoreLive st vtid executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold Lifecycle.Suspend.resumeThreadOnCoreLive at h
  split at h
  · exact resumeThreadOnCore_replenishQueueOnCore st st' vtid executingCore sgi c h
  · exact resumeThreadEnqueueOnly_replenishQueueOnCore st st' vtid executingCore sgi c h

/-- **`v0.35.167`: the live `.tcbResume` arm's scheduler-domain footprint.**

`schedFootprintOfCores` of the arm's own SM8.B write set, with an **empty**
replenish segment: a resume moves no scheduling context, which
`resumeThreadOnCoreLive_replenishQueueOnCore` is the statement of.

The fault retire the arm runs first (`retirePendingFaultForResume`, WS-RR RR4.11)
needs no member of its own: it writes one TCB's `pendingFault` and no scheduler
state at all (`retirePendingFaultForResume_scheduler_eq`). -/
def schedLockSet_resumeThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (resumeThreadOnCoreWriteSet st vtid executingCore) []

/-- `v0.35.167`: the footprint holds the resumed thread's home core's run-queue
write lock — the enqueue's own. -/
theorem schedLockSet_resumeThreadOnCore_contains_home_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    (SchedLockId.runQueue ⟨determineTargetCore st vtid.val⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_resumeThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [resumeThreadOnCoreWriteSet])

/-- `v0.35.167`: ...and the executing core's, which the local reschedule writes. -/
theorem schedLockSet_resumeThreadOnCore_contains_executing_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_resumeThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [resumeThreadOnCoreWriteSet])

/-- `v0.35.167`: and **no** replenish-queue lock, on any core — the declaration's
exact half, against `resumeThreadOnCoreLive_replenishQueueOnCore`'s. -/
theorem schedLockSet_resumeThreadOnCore_no_replenishQueue (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_resumeThreadOnCore st vtid executingCore := by
  intro hMem
  exact absurd ((mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem) (by simp)

-- ============================================================================
-- §2  The `.tcbSetPriority` and `.tcbSetMCPriority` arms
-- ============================================================================

open SeLe4n.Kernel.SchedContext.PriorityManagement in
/-- **The cores the live `.tcbSetPriority` / `.tcbSetMCPriority` may write** — the
target's home core, where its run-queue bucket migrates, and the executing core,
which runs the demotion's preemption point inline.  A remote preemption is posted
as an SGI, so the set over-approximates by one core there.

SM8.B.2's write set, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.167`. -/
def priorityControlWriteSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : List CoreId :=
  [determineTargetCore st tid, executingCore]

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

/-- `v0.35.167`: and the gated seam the live arms run, which is that or the
enqueue-only form — and the enqueue-only form returns its input outright. -/
theorem priorityRescheduleOnCoreLive_replenishQueueOnCore (st st' : SystemState)
    (running? : Option CoreId) (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCoreLive st running? executingCore
      shouldPreempt = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCoreLive at h
  split at h
  · exact priorityRescheduleOnCore_replenishQueueOnCore st st' running? executingCore
      shouldPreempt sgi c h
  · rw [SchedContext.PriorityManagement.priorityRescheduleEnqueueOnly_state st st' running?
      executingCore shouldPreempt sgi h]

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
  rw [priorityRescheduleOnCoreLive_replenishQueueOnCore _ st' _ executingCore shouldPreempt
      sgi c h,
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
    (executingCore : CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (priorityControlWriteSet st tid executingCore) []

/-- `v0.35.167`: the footprint holds the target's home core's run-queue write
lock — the bucket migration's own. -/
theorem schedLockSet_priorityControlOnCore_contains_home_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (SchedLockId.runQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_priorityControlOnCore st tid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [priorityControlWriteSet])

/-- `v0.35.167`: ...and the executing core's, which the demotion's local
preemption point writes. -/
theorem schedLockSet_priorityControlOnCore_contains_executing_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_priorityControlOnCore st tid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [priorityControlWriteSet])

/-- `v0.35.167`: and **no** replenish-queue lock, on any core. -/
theorem schedLockSet_priorityControlOnCore_no_replenishQueue (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_priorityControlOnCore st tid executingCore := by
  intro hMem
  exact absurd ((mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem) (by simp)

-- ============================================================================
-- §3  The `.tcbSetAffinity` arm
-- ============================================================================

/-- **Where a `.tcbSetAffinity` writes** — the old home core and the new one.

Unlike bind and configure, the second core needs no state at all:
`setThreadCpuAffinity` inserts the TCB with `cpuAffinity := affinity` and
`determineTargetCore` reads exactly that field, so the post-migration home is a
function of the *argument* (`setThreadCpuAffinity_determineTargetCore_eq`).

SM8.B.2's write set, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.167`. -/
def setThreadCpuAffinityWriteSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : List CoreId :=
  [determineTargetCore st tid, affinity.getD Concurrency.bootCoreId]

/-- **`v0.35.167`: the cores a `.tcbSetAffinity` moves a RESERVATION between.**

Unlike the two arms above, this one *does* move replenishments: changing a
thread's home core changes what `replenishQueueAffinityConsistentOnCore` demands
of every entry naming the context it runs on, so `setThreadCpuAffinityWithMigration`
migrates them with the thread (SM5.H.4).  The migration fires exactly when the
thread runs on a scheduling context at all — `tcb.schedContextBinding.scId?`,
which is `some` at `.bound` and at `.donated` and `none` at `.unbound` — and that
is the guard read here, off the **same** TCB the transition reads it off, on the
**same** state.  Not a proxy for it: the same expression.

Empty where the thread holds no reservation, which
`setThreadCpuAffinityWithMigration_replenishQueueOnCore_of_no_context` is the
exactness half of. -/
def setThreadCpuAffinityReplenishCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : List CoreId :=
  match (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) with
  | some _ => [determineTargetCore st tid, affinity.getD Concurrency.bootCoreId]
  | none => []

/-- `v0.35.167`: a thread on no reservation moves none — the segment is empty. -/
@[simp] theorem setThreadCpuAffinityReplenishCores_of_no_context (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = none) :
    setThreadCpuAffinityReplenishCores st tid affinity = [] := by
  unfold setThreadCpuAffinityReplenishCores; rw [h]

/-- **`v0.35.167`: and the live arm then writes no replenish queue at all** — the
declaration's exact half.  Its three effects are the affinity write (one typed
object rewrite), the (declined) replenishment migration and the run-queue
migration, and only the second can move an entry. -/
theorem setThreadCpuAffinityWithMigration_replenishQueueOnCore_of_no_context
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hNo : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = none)
    (h : setThreadCpuAffinityWithMigration st tid affinity executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold setThreadCpuAffinityWithMigration at h
  split at h
  · rename_i tcb hTcb
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · cases hSet : setThreadCpuAffinity st tid affinity with
        | error e => rw [hSet] at h; exact absurd h (by simp)
        | ok stSet =>
          rw [hSet] at h
          dsimp only at h
          have hBind : tcb.schedContextBinding.scId? = none := by
            rw [hTcb] at hNo; simpa using hNo
          rw [hBind] at h
          dsimp only at h
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1, migrateRunQueueOnAffinityChange_replenishQueueOnCore,
            setThreadCpuAffinity_scheduler_eq st stSet tid affinity hSet]
  · exact absurd h (by simp)

/-- **`v0.35.167`: the live `.tcbSetAffinity` arm's scheduler-domain footprint.** -/
def schedLockSet_setThreadCpuAffinityOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (setThreadCpuAffinityWriteSet st tid affinity)
    (setThreadCpuAffinityReplenishCores st tid affinity)

/-- `v0.35.167`: the footprint holds the old home core's run-queue write lock. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_old_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) :
    (SchedLockId.runQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [setThreadCpuAffinityWriteSet])

/-- `v0.35.167`: ...and the new one's. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_new_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) :
    (SchedLockId.runQueue ⟨affinity.getD Concurrency.bootCoreId⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [setThreadCpuAffinityWriteSet])

/-- **`v0.35.167`: and both replenish-queue write locks when — and only when —
the thread runs on a reservation.** -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_replenishQueue_writes
    (st : SystemState) (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (scId : SeLe4n.SchedContextId)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = some scId) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity ∧
    (SchedLockId.replenishQueue ⟨affinity.getD Concurrency.bootCoreId⟩,
      Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity := by
  constructor <;>
    exact (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
      (by unfold setThreadCpuAffinityReplenishCores; rw [h]; simp)

/-- **`v0.35.167`: ...and those two locks are the cores the migration actually
moves the reservation between.**

`setThreadCpuAffinityWithMigration` resolves its destination as
`determineTargetCore stSet tid`, at the *post*-affinity-write state, where the
footprint resolves it from the **argument**.  The two are one value
(`setThreadCpuAffinity_determineTargetCore_eq`) — which is why this write set,
unlike its two SchedContext siblings, needs no mid-state bridge — and stating it
here is what keeps the footprint and the transition from naming different cores:
a coverage claim read off `_contains_replenishQueue_writes` alone is about the
*argument*, not about the migration. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_covers_migration (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (scId : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = some scId) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity ∧
    (SchedLockId.replenishQueue ⟨determineTargetCore stSet tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity := by
  rw [setThreadCpuAffinity_determineTargetCore_eq st stSet tid affinity hInv hSet]
  exact schedLockSet_setThreadCpuAffinityOnCore_contains_replenishQueue_writes
    st tid affinity scId h

/-- **`v0.35.167`: and none where it runs on no reservation** — the narrowing the
parametric SM5.H.4 footprint cannot make.

`setThreadCpuAffinityWithMigrationLockSet` declares both replenish-queue locks
unconditionally, because it takes the two cores and nothing else; the resolved
form reads the binding and drops them on the `.unbound` path.  Over-declaring is
sound and not free — lock contention is an observable channel (SM8.D's CC-5) —
which is why WS-OD OD3.5 narrowed a footprint for the same reason. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_no_replenishQueue_of_no_context
    (st : SystemState) (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (c : CoreId)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = none) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_setThreadCpuAffinityOnCore st tid affinity := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem
  rw [setThreadCpuAffinityReplenishCores_of_no_context st tid affinity h] at this
  exact absurd this (by simp)

/-- **`v0.35.167`: the resolved footprint covers the parametric SM5.H.4 one** at
the two cores the migration actually moves the thread between, whenever the
thread runs on a reservation.

`setThreadCpuAffinityWithMigrationLockSet oldCore newCore` is the RR2.4-shaped
form: the object-store write lock and both queue kinds at both cores, ordered
lower-core-first.  Every member of it is a member here. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_covers_parametric (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (scId : SeLe4n.SchedContextId)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = some scId)
    (p : SchedLockId × Concurrency.AccessMode)
    (hp : p ∈ setThreadCpuAffinityWithMigrationLockSet (determineTargetCore st tid)
      (affinity.getD Concurrency.bootCoreId)) :
    p ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity := by
  have hRepl := schedLockSet_setThreadCpuAffinityOnCore_contains_replenishQueue_writes
    st tid affinity scId h
  simp only [setThreadCpuAffinityWithMigrationLockSet, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact schedFootprintOfCores_contains_objStore_write _ _
  · by_cases hc : (determineTargetCore st tid).val ≤ (affinity.getD Concurrency.bootCoreId).val
    · simp only [hc, if_true]
      exact schedLockSet_setThreadCpuAffinityOnCore_contains_old_runQueue_write _ _ _
    · simp only [hc, if_false]
      exact schedLockSet_setThreadCpuAffinityOnCore_contains_new_runQueue_write _ _ _
  · by_cases hc : (determineTargetCore st tid).val ≤ (affinity.getD Concurrency.bootCoreId).val
    · simp only [hc, if_true]
      exact schedLockSet_setThreadCpuAffinityOnCore_contains_new_runQueue_write _ _ _
    · simp only [hc, if_false]
      exact schedLockSet_setThreadCpuAffinityOnCore_contains_old_runQueue_write _ _ _
  · by_cases hc : (determineTargetCore st tid).val ≤ (affinity.getD Concurrency.bootCoreId).val
    · simp only [hc, if_true]; exact hRepl.1
    · simp only [hc, if_false]; exact hRepl.2
  · by_cases hc : (determineTargetCore st tid).val ≤ (affinity.getD Concurrency.bootCoreId).val
    · simp only [hc, if_true]; exact hRepl.2
    · simp only [hc, if_false]; exact hRepl.1

-- ============================================================================
-- §4  The `.schedContextConfigure` arm
-- ============================================================================

-- **The thread a SchedContext operation's scheduler effects act on** is
-- `SchedContextOps.schedContextBoundThread?`, whose own docstring has said since
-- SM8.B that it is "single-sourced here in production because two consumers need
-- it and a second copy would drift".  It was not: the staged
-- `InformationFlow/NonInterferenceCrossCore.lean` carried `schedContextSubject?`,
-- clause for clause the same function, and the write sets below read *that* one.
-- The copy is deleted at `v0.35.168` and every reader asks the owner -- by its
-- own name, not through an alias, because an alias is a second spelling and this
-- is the cut that retires one.

/-- **The cores `.schedContextUnbind` and `.schedContextConfigure` may write** —
the bound thread's home core alone.

Both have a single run-queue effect (clear-and-requeue, or re-bucket) and both
land on `determineTargetCore` of the SC's bound thread.  An SC with no bound
thread has no run-queue effect at all, hence the empty set.

**Not `.schedContextBind`**, which resolves its thread from an *argument*:
binding rejects an SC that already has one (`sc.boundThread.isSome → .error
.illegalState`), so on every success path this set is empty while bind does
write a run queue.  `schedContextBindWriteSet` is its write set.

SM8.B.2's write set, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.168` so the footprint
below can read it (see this module's header). -/
def schedContextWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId) : List CoreId :=
  match SchedContextOps.schedContextBoundThread? st scObjId with
  | some tid => [determineTargetCore st tid]
  | none => []

/-- **`v0.35.168`: the core a `.schedContextConfigure` moves a RESERVATION on.**

Unlike the three arms above, configure *does* write a replenish queue: it resets
the reservation to a single fresh replenishment and purges the stale entry first
(`purgeReplenishmentOnCore st (schedContextReplenishHome st sc) scIdTyped`), on
the SC's **home** core.  So the segment is that core whenever the capability's
target resolves to a SchedContext, and empty when it does not — where the
transition refuses with `.objectNotFound` and writes nothing.

It is deliberately **not** narrowed to the bound case.  An SC with no bound
thread has no home, `schedContextReplenishHome` answers `bootCoreId`, and the
purge still *runs* there: a stale entry left by an earlier binding is exactly
what it exists to drop, so a footprint omitting that lock would be false. -/
def schedContextConfigureReplenishCores (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc => [SchedContextOps.schedContextReplenishHome st sc]
  | none => []

/-- **`v0.35.168`: the live `.schedContextConfigure` arm's scheduler-domain
footprint.** -/
def schedLockSet_schedContextConfigureOnCore (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextWriteSet st scObjId)
    (schedContextConfigureReplenishCores st scObjId)

/-- `v0.35.168`: the footprint holds the bound thread's home core's run-queue
write lock — the bucket propagation's own. -/
theorem schedLockSet_schedContextConfigureOnCore_contains_home_runQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid) :
    (SchedLockId.runQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextConfigureOnCore st scObjId :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold schedContextWriteSet; rw [h]; simp)

/-- `v0.35.168`: ...and the SC's home core's replenish-queue write lock, which is
the purge's. -/
theorem schedLockSet_schedContextConfigureOnCore_contains_replenishQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (sc : SchedContext)
    (h : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc) :
    (SchedLockId.replenishQueue ⟨SchedContextOps.schedContextReplenishHome st sc⟩,
      Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextConfigureOnCore st scObjId :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold schedContextConfigureReplenishCores; rw [h]; simp)

/-- **`v0.35.168`: and the two are the SAME core whenever the SC is bound** — the
purge lands where the re-bucket does, which is what makes a one-core footprint
honest for an operation with two scheduling effects.  They part only for an
unbound SC, where the run segment is empty and the purge falls back to the boot
core, and `schedContextReplenishHome`'s own docstring is the reason. -/
theorem schedContextConfigureReplenishCores_eq_writeSet_of_bound (st : SystemState)
    (scObjId : SeLe4n.ObjId) (sc : SchedContext) (tid : SeLe4n.ThreadId)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hBound : sc.boundThread = some tid) :
    schedContextConfigureReplenishCores st scObjId = schedContextWriteSet st scObjId := by
  simp only [schedContextConfigureReplenishCores, schedContextWriteSet,
    SchedContextOps.schedContextBoundThread?, SchedContextOps.schedContextReplenishHome,
    hSc, hBound]

/-- **`v0.35.168`: and no replenish lock at all where the capability's target
resolves to no SchedContext** — the arm refuses `.objectNotFound` there and
writes nothing. -/
theorem schedLockSet_schedContextConfigureOnCore_no_replenishQueue_of_absent
    (st : SystemState) (scObjId : SeLe4n.ObjId) (c : CoreId)
    (h : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = none) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_schedContextConfigureOnCore st scObjId := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem
  unfold schedContextConfigureReplenishCores at this
  rw [h] at this
  exact absurd this (by simp)

-- ============================================================================
-- §5  The `.schedContextBind` arm
-- ============================================================================

/-- **The cores a `.schedContextBind` may write** — the bound thread's home core.

Deliberately **not** `schedContextWriteSet`: bind rejects an SC that already has
a bound thread, so on every success path `SchedContextOps.schedContextBoundThread?` is `none` and
that set is empty — while bind genuinely writes a run queue.  The thread is an
argument here, so this reads it directly.

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.168`. -/
def schedContextBindWriteSet (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  [determineTargetCore st tid]

/-- **`v0.35.168`: the live `.schedContextBind` arm's scheduler-domain
footprint**, with an **empty** replenish segment: a bind moves no replenishment.

seL4-MCS's `schedContext_bindTCB` ends in `SCHED_ENQUEUE`; this kernel's bind
re-buckets only an already-queued thread, which is the divergence
`docs/REGISTERED_DEBT.md`'s WS-CB row carries.  Closing it widens the run
segment, not this one — a placement is a run-queue write. -/
def schedLockSet_schedContextBindOnCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextBindWriteSet st tid) []

/-- `v0.35.168`: the footprint holds the bound thread's home core's run-queue
write lock. -/
theorem schedLockSet_schedContextBindOnCore_contains_home_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (SchedLockId.runQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextBindOnCore st tid :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [schedContextBindWriteSet])

/-- `v0.35.168`: and **no** replenish-queue lock, on any core — the declaration's
exact half, against `schedContextBind_replenishQueueOnCore`'s. -/
theorem schedLockSet_schedContextBindOnCore_no_replenishQueue (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_schedContextBindOnCore st tid := by
  intro hMem
  exact absurd ((mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem) (by simp)

-- ============================================================================
-- §6  The `.schedContextUnbind` arm
-- ============================================================================

/-- **The cores a `.schedContextUnbind` may write** — the subject's home core
*and* the core actually running it.

Deliberately **not** `schedContextWriteSet`.  The two differ, and the difference
is the defect this set exists to make visible: the run-queue re-bucket lands on
the subject's **home** core, while the preemption guard clears `current` on the
core actually **running** it.  Those coincide whenever affinity is set, and
diverge for an unbound-affinity thread running on a secondary core.

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.168`. -/
def schedContextUnbindWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match SchedContextOps.schedContextBoundThread? st scObjId with
  | some tid => determineTargetCore st tid :: (runningCoreOf? st tid).toList
  | none => []

/-- **The cores the live `.schedContextUnbind` may write** — the demoted
thread's home core, where the revocation re-buckets it, the core running it,
and the executing core, which runs the demotion's scheduling point inline.

When the running core is remote the seam only *posts* its SGI, so the declared
set over-approximates by one core on that path; over-approximating is the safe
direction, and it is the shape `resumeThreadOnCoreWriteSet` already uses.

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.168`. -/
def schedContextUnbindOnCoreWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  schedContextUnbindWriteSet st scObjId ++ [executingCore]

/-- **`v0.35.168`: the cores a `.schedContextUnbind` moves a RESERVATION on, and
the one place in this family where a segment is EVERY core.**

The unbind purges the SC's eligibility entry, and it has two arms.  When the
bound TCB resolves it purges on that thread's home core alone.  When it does
**not** — the arm reached after the TCB is already gone from the store — there
is no `cpuAffinity` left to read and no home core to name, so the transition
sweeps every core (`purgeReplenishmentFromAllCores`, whose own docstring gives
that reasoning) and the honest declaration is `allCores`.

Both arms are decided on the pre-state, so this is exact rather than a
conservative union: a footprint that named only the home core would be *false*
on the sweep arm, which is the direction that matters. -/
def schedContextUnbindReplenishCores (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match SchedContextOps.schedContextBoundThread? st scObjId with
  | some tid =>
      match st.getTcb? tid with
      | some _ => [determineTargetCore st tid]
      | none => Concurrency.allCores
  | none => []

/-- **`v0.35.168`: the live `.schedContextUnbind` arm's scheduler-domain
footprint.** -/
def schedLockSet_schedContextUnbindOnCore (st : SystemState) (scObjId : SeLe4n.ObjId)
    (executingCore : CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextUnbindOnCoreWriteSet st scObjId executingCore)
    (schedContextUnbindReplenishCores st scObjId)

/-- `v0.35.168`: the footprint holds the demoted thread's home core's run-queue
write lock — the re-bucket's own. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_home_runQueue_write (st : SystemState)
    (scObjId : SeLe4n.ObjId) (executingCore : CoreId) (tid : SeLe4n.ThreadId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid) :
    (SchedLockId.runQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold schedContextUnbindOnCoreWriteSet schedContextUnbindWriteSet; rw [h]; simp)

/-- `v0.35.168`: ...the core actually running it, whose `current` slot the
preemption guard clears... -/
theorem schedLockSet_schedContextUnbindOnCore_contains_running_runQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId)
    (tid : SeLe4n.ThreadId) (runCore : CoreId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid)
    (hRun : runningCoreOf? st tid = some runCore) :
    (SchedLockId.runQueue ⟨runCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by simp [schedContextUnbindOnCoreWriteSet, schedContextUnbindWriteSet, h, hRun])

/-- `v0.35.168`: ...and the executing core's, which the scheduling point writes. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_executing_runQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold schedContextUnbindOnCoreWriteSet; simp)

/-- `v0.35.168`: the footprint holds the demoted thread's home core's
replenish-queue write lock, which is the purge's, whenever the bound TCB
resolves. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_replenishQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid)
    (hTcb : st.getTcb? tid = some tcb) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by simp [schedContextUnbindReplenishCores, h, hTcb])

/-- **`v0.35.168`: and EVERY core's, on the sweep arm** — the honest declaration
of `purgeReplenishmentFromAllCores`, which is what the transition runs when the
bound TCB is already gone from the store. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_every_replenishQueue_write_of_sweep
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId)
    (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid)
    (hTcb : st.getTcb? tid = none) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by simp only [schedContextUnbindReplenishCores, h, hTcb]
        exact Concurrency.mem_allCores c)

/-- `v0.35.168`: and no replenish lock where the SC has no bound thread — the
arm refuses `.illegalState` there and writes nothing. -/
theorem schedLockSet_schedContextUnbindOnCore_no_replenishQueue_of_unbound
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId) (c : CoreId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = none) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_schedContextUnbindOnCore st scObjId executingCore := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem
  unfold schedContextUnbindReplenishCores at this
  rw [h] at this
  exact absurd this (by simp)

-- ============================================================================
-- §7  The exactness halves — what each SchedContext arm writes
-- ============================================================================
--
-- `observableSlotsConfinedToCores` covers six per-core slots and the replenish
-- queue is not one of them, so a write set says nothing about replenishments and
-- every segment above needs its own statement.  §5's is an absence, §4's and
-- §6's are frames: each arm writes the one replenish queue its own resolver
-- names, and no other.

/-- **`v0.35.168`: a `.schedContextBind` writes no replenish queue at all.**

Its four steps are the SchedContext rewrite, the TCB rewrite, an optional
run-queue re-bucket and a `scThreadIndex` update; none of them moves a
replenishment.  The exactness half of `schedLockSet_schedContextBindOnCore`'s
empty segment. -/
theorem schedContextBind_replenishQueueOnCore (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (vThreadId : SeLe4n.ValidThreadId) (c : CoreId)
    (h : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextBind at h
  split at h
  · rename_i sc hSc _
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i tcb hTcb
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · dsimp only at h
                rw [Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.2]
                split
                · simp only [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
                    SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                · simp only [SystemState.updateTcb_scheduler,
                    SystemState.rewriteObject_scheduler]
              · exact absurd h (by simp)
        · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`v0.35.168`: the configure's bound-thread propagation writes no replenish
queue.**

Its two halves are a priority rewrite with an optional run-queue re-bucket and a
domain rewrite; a `rewriteObject` frames the scheduler outright and a
`setRunQueueOnCore` frames every replenish queue.  What the arm *does* write is
the purge one step earlier, which is what
`schedContextConfigure_replenishQueueOnCore_ne` below is stated over. -/
theorem schedContextConfigureBoundPropagate_replenishQueueOnCore (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (c : CoreId) :
    (SchedContextOps.schedContextConfigureBoundPropagate stStored scId boundTid boundTcb
        hBound priority domain).scheduler.replenishQueueOnCore c
      = stStored.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only
  repeat' split
  all_goals
    simp [SystemState.rewriteObject_scheduler,
      SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

/-- **`v0.35.168`: a `.schedContextConfigure` writes exactly one replenish
queue** — the SC's own home core's, where its purge lands.

The exactness half of `schedLockSet_schedContextConfigureOnCore`'s one-core
segment: every other core's queue is untouched, so the footprint is neither
false nor wider than the operation. -/
theorem schedContextConfigure_replenishQueueOnCore_ne (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (budget period priority deadline domain : Nat)
    (sc : SchedContext) (c : CoreId)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc)
    (hne : c ≠ SchedContextOps.schedContextReplenishHome st sc)
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextConfigure at h
  split at h
  · exact absurd h (by simp)
  · rw [hSc] at h
    dsimp only at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · rename_i stStored hStore
        have hSched := SeLe4n.Model.storeObject_scheduler_eq _ _ _ _ hStore
        split at h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, hSched]
          exact SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _ hne.symm
        · split at h
          · rename_i boundTcb hBound _
            rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, schedContextConfigureBoundPropagate_replenishQueueOnCore, hSched]
            exact SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _ hne.symm
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, hSched]
            exact SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _ hne.symm
    · exact absurd h (by simp)

/-- **`v0.35.168`: a `.schedContextUnbind` whose bound TCB resolves writes
exactly one replenish queue** — that thread's home core's, where its purge
lands.

The exactness half of `schedLockSet_schedContextUnbindOnCore`'s one-core
segment.  The **other** arm needs no such statement and can have none: with the
bound TCB gone from the store the transition sweeps every core, which is exactly
what `schedContextUnbindReplenishCores` declares there. -/
theorem schedContextUnbind_replenishQueueOnCore_ne_of_tcb (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (sc : SchedContext) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (c : CoreId)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc)
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hne : c ≠ determineTargetCore st tid)
    (h : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextUnbind at h
  rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at h
  dsimp only at h
  simp only [hBound, hTcb] at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    dsimp only
    rw [SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _ hne.symm,
      SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
    dsimp only
    repeat' split
    all_goals
      simp [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
        SchedulerState.setCurrentOnCore_replenishQueueOnCore]

/-- **`v0.35.168`: ...and the live per-core arm writes the same one**, the
scheduling point it composes moving no replenishment
(`priorityRescheduleOnCore_replenishQueueOnCore`). -/
theorem schedContextUnbindOnCore_replenishQueueOnCore_ne_of_tcb (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (sc : SchedContext) (tid : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc)
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hne : c ≠ determineTargetCore st tid)
    (h : SchedContextOps.schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  dsimp only at h
  cases hU : SchedContextOps.schedContextUnbind vScId st with
  | error e => rw [hU] at h; exact absurd h (by simp)
  | ok r =>
      obtain ⟨u, stU⟩ := r
      rw [hU] at h
      dsimp only at h
      rw [priorityRescheduleOnCore_replenishQueueOnCore _ _ _ _ _ _ c h]
      exact schedContextUnbind_replenishQueueOnCore_ne_of_tcb st stU vScId sc tid tcb c
        hSc hBound hTcb hne (by cases u; exact hU)

end SeLe4n.Kernel
