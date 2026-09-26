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
import SeLe4n.Kernel.Lifecycle.Invariant.RetypeReservation
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
import SeLe4n.Kernel.Scheduler.Operations.SchedLockSet
import SeLe4n.Kernel.SyscallLockBracket
import SeLe4n.Kernel.SchedLockBracket

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

/-- **WS-RR RR8.12 Cut C6b: the `.tcbSetAffinity` arm's exactness frame.**

Keyed on the footprint's own replenish segment rather than on a resolution, which
is what a coverage proof consumes: `schedFootprintCoversWrites`'s replenish clause
asks "unchanged at every core the footprint does not name", and a
resolution-conditional frame answers a different question that the consumer then
has to case-split to reach.  The `none` arm is
`…_replenishQueueOnCore_of_no_context`'s claim with the segment empty; the `some`
arm is the migration's own `_other` frame, at the pair the segment declares —
`setThreadCpuAffinity_determineTargetCore_eq` is what makes the declared
destination the migration's destination rather than a second reading of it. -/
theorem setThreadCpuAffinityWithMigration_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId) (hInv : st.objects.invExt)
    (hne : c ∉ setThreadCpuAffinityReplenishCores st tid affinity)
    (h : setThreadCpuAffinityWithMigration st tid affinity executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold setThreadCpuAffinityReplenishCores at hne
  cases hBind : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) with
  | none =>
      exact setThreadCpuAffinityWithMigration_replenishQueueOnCore_of_no_context st st' tid
        affinity executingCore sgi c hBind h
  | some scId =>
      rw [hBind] at hne
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
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
              have hScId : tcb.schedContextBinding.scId? = some scId := by
                rw [hTcb] at hBind; simpa using hBind
              rw [hScId] at h
              dsimp only at h
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              have hNew := setThreadCpuAffinity_determineTargetCore_eq st stSet tid affinity
                hInv hSet
              rw [← h.1, migrateRunQueueOnAffinityChange_replenishQueueOnCore, hNew,
                migrateSchedContextReplenishment_replenishQueueOnCore_other stSet scId
                  (determineTargetCore st tid) (affinity.getD Concurrency.bootCoreId) c
                  (fun hEq => hne.1 hEq.symm) (fun hEq => hne.2 hEq.symm),
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

seL4-MCS's `schedContext_bindTCB` ends in `SCHED_ENQUEUE`, and since WS-RR
RR8.12 Cut B2 (`v0.35.182`) so does this kernel's bind: a parked runnable thread
is placed on its home core rather than left off every queue with a reservation
it cannot spend.  This docstring said that closing the divergence "widens the run
segment"; it did not, because the segment is the **home core** either way — the
placement inserts on exactly the core the re-bucket already wrote.  The
replenish segment stays empty on all three branches. -/
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
                -- Three arms since Cut B2 (`v0.35.182`): the re-bucket, the
                -- placement of a parked runnable thread, and the identity.  All
                -- three write a run queue or nothing, so none moves a replenish
                -- queue — which is what keeps this arm's segment EMPTY.
                split
                · simp only [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
                    SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                · split
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
`schedContextConfigure_replenishQueueOnCore_ne_of_sc` below is stated over. -/
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
theorem schedContextConfigure_replenishQueueOnCore_ne_of_sc (st st' : SystemState)
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

/-- **WS-RR RR8.12 Cut C6b: the `.schedContextConfigure` arm's exactness frame.**

Keyed on the footprint's own replenish segment, which is what a coverage proof
consumes; `…_ne_of_sc` above is the resolution-keyed form it is built from.  The
unresolved arm is not a gap but a refusal — the transition's own second branch
errors there — so the segment being empty costs the claim nothing. -/
theorem schedContextConfigure_replenishQueueOnCore_ne (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (budget period priority deadline domain : Nat) (c : CoreId)
    (hne : c ∉ schedContextConfigureReplenishCores st vScId.val)
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold schedContextConfigureReplenishCores at hne
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none =>
      exfalso
      unfold SchedContextOps.schedContextConfigure at h
      split at h
      · exact absurd h (by simp)
      · rw [hSc] at h
        exact absurd h (by simp)
  | some sc =>
      rw [hSc] at hne
      exact schedContextConfigure_replenishQueueOnCore_ne_of_sc st st' vScId budget period
        priority deadline domain sc c hSc (by simpa using hne) h

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

-- ============================================================================
-- §8  The `.lifecycleRetype` arm
-- ============================================================================
--
-- The destroy path's scheduler effects are the pre-retype cleanup's, and since
-- `v0.35.164`/`v0.35.165` there are two of them: a TCB target ends its
-- reservation the way a suspended thread's is (`cancelDonationArmOnCore`), and a
-- SchedContext target releases the binding it holds (`releaseSchedContextBinding`,
-- seL4's `schedContext_unbindAllTCBs` per core).  Both read the **pre-state** --
-- for a SchedContext target every earlier step of the cleanup is the identity,
-- and for a TCB target the arm IS the first step -- so this whole footprint is
-- pre-state computable with no mid-state bridge.

/-- **WS-RR RR8.12 Cut C6b: the `.schedContextUnbind` arm's exactness frame.**

Keyed on the footprint's own replenish segment; `…_ne_of_tcb` above is the
resolution-keyed form it is built from.  Three resolutions and only one of them
names a core: a SchedContext that resolves to no bound thread makes the
transition *fail*, and one bound to a thread the store no longer holds has no
`cpuAffinity` left to read, so the unbind sweeps every core and the segment is
`allCores` — where the claim is vacuous, correctly, because there is no core
outside it. -/
theorem schedContextUnbindOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hne : c ∉ schedContextUnbindReplenishCores st vScId.val)
    (h : SchedContextOps.schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold schedContextUnbindReplenishCores at hne
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none =>
      exfalso
      unfold SchedContextOps.schedContextUnbindOnCore at h
      dsimp only at h
      cases hU : SchedContextOps.schedContextUnbind vScId st with
      | error e => rw [hU] at h; exact absurd h (by simp)
      | ok r =>
          unfold SchedContextOps.schedContextUnbind at hU
          rw [SystemState.getSchedContextWitnessed?_eq_none hSc] at hU
          exact absurd hU (by simp)
  | some sc =>
      have hBT : SchedContextOps.schedContextBoundThread? st vScId.val = sc.boundThread := by
        unfold SchedContextOps.schedContextBoundThread?
        rw [hSc]
      rw [hBT] at hne
      cases hBound : sc.boundThread with
      | none =>
          exfalso
          unfold SchedContextOps.schedContextUnbindOnCore at h
          dsimp only at h
          cases hU : SchedContextOps.schedContextUnbind vScId st with
          | error e => rw [hU] at h; exact absurd h (by simp)
          | ok r =>
              unfold SchedContextOps.schedContextUnbind at hU
              rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at hU
              dsimp only at hU
              rw [hBound] at hU
              exact absurd hU (by simp)
      | some tid =>
          rw [hBound] at hne
          cases hTcb : st.getTcb? tid with
          | none =>
              simp only [hTcb] at hne
              exact absurd (Concurrency.mem_allCores c) hne
          | some tcb =>
              simp only [hTcb] at hne
              exact schedContextUnbindOnCore_replenishQueueOnCore_ne_of_tcb st st' vScId
                executingCore sgi sc tid tcb c hSc hBound hTcb (by simpa using hne) h

/-- **The cores a destroy sweep actually touches** — those the thread occupies in
the pre-state.

`removeRunnableFromAllCores` folds over *every* core, so the naive bound is
`allCores`, which is true and useless; the step is **guarded** by
`threadOccupiesCore` precisely so a sharper bound is available, and this is that
bound.

SM8.B.2's resolver, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.169` with the retype
write set that reads it. -/
def threadOccupiedCores (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  Concurrency.allCores.filter (threadOccupiesCore st tid)

/-- **Where a `.lifecycleRetype` writes a RUN QUEUE**, as a function of the object
being destroyed.

Only the TCB arm names any core, and it names the ones the doomed thread
occupies.  Every other kind — CNode, endpoint, notification, reply, VSpace root,
untyped, scheduling context — writes no run queue and no current slot, so its set
is empty.  **A SchedContext target is not an exception**: its release writes a
replenish queue, which is not one of the six slots
`observableSlotsConfinedToCores` covers, and which the replenish segment below
declares instead.

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.169`. -/
def lifecycleRetypeWriteSetOf (st : SystemState) (currentObj : KernelObject) :
    List CoreId :=
  match currentObj with
  | .tcb tcb => threadOccupiedCores st tcb.tid
  | _ => []

/-- The same set, resolved from the target's id through the pre-state store.
Retyping an absent object writes nothing (the pipeline errors out).

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.169`. -/
def lifecycleRetypeWriteSet (st : SystemState) (target : SeLe4n.ObjId) : List CoreId :=
  match st.getObject? target with
  | some obj => lifecycleRetypeWriteSetOf st obj
  | none => []

/-- **`v0.35.169`: the cores the destroy path's donation arm moves a RESERVATION
on**, keyed on the doomed thread's own binding — `cancelDonationArmOnCore`'s
three arms, read as cores.

`.unbound` moves nothing; `.bound` purges on the thread's home core; `.donated`
returns the context and migrates its replenishments from the holder's home to the
recorded owner's, the destination read at the **post-return** state exactly as
`cancelDonatedDonationOnCore` reads it.  A refused return migrates nothing, and
the empty list there is the transition's own behaviour rather than a narrowing. -/
def cancelDonationArmReplenishCoresAt (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (home : CoreId) : List CoreId :=
  match tcb.schedContextBinding with
  | .unbound => []
  | .bound _ => [home]
  | .donated _ owner =>
      match cleanupDonatedSchedContext st tid with
      | .error _ => []
      | .ok st' => [determineTargetCore st tid, determineTargetCore st' owner]

/-- The same, at the purge core `cancelDonationArmOnCore` itself computes — the
destroy path's instance.  The suspend pipeline's G3 passes the home it captured
**before** the teardown, which is why the general form exists at all. -/
def cancelDonationArmReplenishCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : List CoreId :=
  cancelDonationArmReplenishCoresAt st tid tcb (determineTargetCore st tid)

/-- **`v0.35.169`: the cores a binding release moves a RESERVATION on**, and the
second place in this module where a segment is EVERY core.

`releaseSchedContextBinding` purges on the bound thread's home core when that
thread resolves, and sweeps every core when it does not — with the TCB gone from
the store there is no `cpuAffinity` left to read and no home to name, which is
`schedContextUnbindReplenishCores`' reasoning on the same shape one operation
over.  A context bound to nothing has no binding to release, hence the empty
list. -/
def releaseSchedContextBindingReplenishCores (st : SystemState)
    (sc : SchedContext) : List CoreId :=
  match sc.boundThread with
  | none => []
  | some tid =>
      match st.getTcb? tid with
      | some _ => [determineTargetCore st tid]
      | none => Concurrency.allCores

/-- **`v0.35.169`: the cores a `.lifecycleRetype` moves a RESERVATION on**, as a
function of the object being destroyed — the TCB arm's donation cores, the
SchedContext arm's release cores, and nothing for any other kind. -/
def lifecycleRetypeReplenishCoresOf (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj : KernelObject) : List CoreId :=
  match currentObj with
  | .tcb tcb => cancelDonationArmReplenishCores st tcb.tid tcb
  | .schedContext sc => releaseSchedContextBindingReplenishCores st sc
  | _ => (fun _ => []) target

/-- The same set, resolved from the target's id through the pre-state store. -/
def lifecycleRetypeReplenishCores (st : SystemState) (target : SeLe4n.ObjId) :
    List CoreId :=
  match st.getObject? target with
  | some obj => lifecycleRetypeReplenishCoresOf st target obj
  | none => []

/-- **`v0.35.169`: the live `.lifecycleRetype` arm's scheduler-domain
footprint.** -/
def schedLockSet_lifecycleRetypeOnCore (st : SystemState) (target : SeLe4n.ObjId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (lifecycleRetypeWriteSet st target)
    (lifecycleRetypeReplenishCores st target)

/-- `v0.35.169`: the footprint holds the run-queue write lock of every core the
doomed thread occupies — the destroy sweep's own. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_occupied_runQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (c : CoreId)
    (h : st.getObject? target = some (.tcb tcb))
    (hOcc : threadOccupiesCore st tcb.tid c = true) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by simp only [lifecycleRetypeWriteSet, lifecycleRetypeWriteSetOf, h,
          threadOccupiedCores, List.mem_filter]
        exact ⟨Concurrency.mem_allCores c, hOcc⟩)

/-- `v0.35.169`: ...and the replenish-queue write lock of a `.bound` doomed
thread's home core, which is the unbind's purge core. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_bound_replenishQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (h : st.getObject? target = some (.tcb tcb))
    (hBind : tcb.schedContextBinding = .bound scId) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tcb.tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp [lifecycleRetypeReplenishCoresOf, cancelDonationArmReplenishCores,
          cancelDonationArmReplenishCoresAt, hBind])

/-- `v0.35.169`: ...and both of a `.donated` holder's, which are the return's
migration endpoints. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_donated_replenishQueue_writes
    (st st' : SystemState) (target : SeLe4n.ObjId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (h : st.getObject? target = some (.tcb tcb))
    (hBind : tcb.schedContextBinding = .donated scId owner)
    (hRet : cleanupDonatedSchedContext st tcb.tid = .ok st') :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tcb.tid⟩,
      Concurrency.AccessMode.write) ∈ schedLockSet_lifecycleRetypeOnCore st target ∧
    (SchedLockId.replenishQueue ⟨determineTargetCore st' owner⟩,
      Concurrency.AccessMode.write) ∈ schedLockSet_lifecycleRetypeOnCore st target := by
  constructor <;>
    exact (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
      (by unfold lifecycleRetypeReplenishCores
          rw [h]
          simp [lifecycleRetypeReplenishCoresOf, cancelDonationArmReplenishCores,
            cancelDonationArmReplenishCoresAt, hBind, hRet])

/-- `v0.35.169`: ...and the bound thread's home core's, on a SchedContext
target whose bound TCB resolves. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_release_replenishQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (sc : SchedContext)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : st.getObject? target = some (.schedContext sc))
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = some tcb) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st tid⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp [lifecycleRetypeReplenishCoresOf, releaseSchedContextBindingReplenishCores,
          hBound, hTcb])

/-- **`v0.35.169`: and EVERY core's, where that TCB is already gone** — the
honest declaration of `purgeReplenishmentFromAllCores`, which the release runs
when there is no `cpuAffinity` left to read. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_every_replenishQueue_write_of_sweep
    (st : SystemState) (target : SeLe4n.ObjId) (sc : SchedContext)
    (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : st.getObject? target = some (.schedContext sc))
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = none) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp only [lifecycleRetypeReplenishCoresOf, releaseSchedContextBindingReplenishCores,
          hBound, hTcb]
        exact Concurrency.mem_allCores c)

/-- **`v0.35.169`: and NO scheduler lock at all for every other kind of target.**

A CNode, endpoint, notification, reply, VSpace root or untyped target has no
scheduling effect: the cleanup's arms for them write the object store, the CDT
and the service registry, and nothing per-core.  Stated over both segments, so a
kind that acquires one has to move a definition rather than a proof. -/
theorem schedLockSet_lifecycleRetypeOnCore_empty_of_other (st : SystemState)
    (target : SeLe4n.ObjId) (obj : KernelObject)
    (h : st.getObject? target = some obj)
    (hTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hSc : ∀ sc, obj ≠ .schedContext sc) :
    schedLockSet_lifecycleRetypeOnCore st target
      = [(SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)] := by
  unfold schedLockSet_lifecycleRetypeOnCore lifecycleRetypeWriteSet
    lifecycleRetypeReplenishCores
  rw [h]
  cases obj with
  | tcb t => exact absurd rfl (hTcb t)
  | schedContext s => exact absurd rfl (hSc s)
  | _ =>
    simp [lifecycleRetypeWriteSetOf, lifecycleRetypeReplenishCoresOf,
      schedFootprintOfCores, schedCoreSegment, Concurrency.canonicalCores]

-- ============================================================================
-- §9  The exactness halves — what the destroy path writes
-- ============================================================================

/-- **`v0.35.169`: the `.bound` unbind writes exactly the core it is handed.** -/
theorem cancelBoundDonationOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore c : CoreId)
    (hne : rqCore ≠ c)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rw [Except.ok.injEq] at h
    rw [← h]
    simp only [SystemState.updateTcb_scheduler]
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hne,
      SystemState.updateSchedContext_scheduler]
  · exact absurd h (by simp)

/-- **`v0.35.169`: the `.donated` return writes exactly its migration's two
endpoints.** -/
theorem cancelDonatedDonationOnCore_replenishQueueOnCore_ne (st st' stRet : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) (c : CoreId)
    (hBind : tcb.schedContextBinding = .donated scId owner)
    (hRet : cleanupDonatedSchedContext st tid = .ok stRet)
    (hFrom : determineTargetCore st tid ≠ c)
    (hTo : determineTargetCore stRet owner ≠ c)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelDonatedDonationOnCore at h
  rw [hBind, hRet] at h
  dsimp only at h
  rw [Except.ok.injEq] at h
  rw [← h, migrateSchedContextReplenishment_replenishQueueOnCore_other _ _ _ _ _ hFrom hTo]
  exact cleanupDonatedSchedContext_scheduler_eq st stRet tid hRet ▸ rfl

/-- **`v0.35.170`: the donation arm writes exactly the cores its own resolver
names, at whatever purge core it is handed.**

Stated over the three-way match at an **explicit** `home` because that is the
question both askers ask, and they hand it different cores:
`cancelDonationArmOnCore` — the destroy path's arm — reads it off the state it
runs on, while `suspendThreadOnCore`'s G3 was handed it from the **pre**-G2
state, captured before the teardown for the reason that transition records.  A
frame stated at `determineTargetCore st tid` covers the first and not the
second, so it is the *parameter* that is general here and both consumers below
are instances of one proof. -/
theorem donationArmAt_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home c : CoreId)
    (hne : c ∉ cancelDonationArmReplenishCoresAt st tid tcb home)
    (h : (match tcb.schedContextBinding with
          | .unbound => (Except.ok st : Except KernelError SystemState)
          | .bound _ => cancelBoundDonationOnCore st tid tcb home
          | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelDonationArmReplenishCoresAt at hne
  cases hBind : tcb.schedContextBinding with
  | unbound =>
      rw [hBind] at h
      rw [Except.ok.injEq] at h; rw [← h]
  | bound scId =>
      rw [hBind] at h hne
      exact cancelBoundDonationOnCore_replenishQueueOnCore_ne st st' tid tcb _ c
        (by simp only [List.mem_singleton] at hne; exact fun hc => hne hc.symm) h
  | donated scId owner =>
      rw [hBind] at h hne
      cases hRet : cleanupDonatedSchedContext st tid with
      | error e =>
          rw [hRet] at hne
          unfold cancelDonatedDonationOnCore at h
          rw [hBind, hRet] at h
          exact absurd h (by simp)
      | ok stRet =>
          rw [hRet] at hne
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
          exact cancelDonatedDonationOnCore_replenishQueueOnCore_ne st st' stRet tid tcb
            scId owner c hBind hRet (fun hc => hne.1 hc.symm) (fun hc => hne.2 hc.symm) h

/-- **`v0.35.169`: the destroy path's donation arm writes exactly the cores its
own resolver names** — the exactness half of the retype footprint's `.tcb`
replenish segment, and the instance of the frame above at the purge core that
arm reads for itself. -/
theorem cancelDonationArmOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hne : c ∉ cancelDonationArmReplenishCores st tid tcb)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
  donationArmAt_replenishQueueOnCore_ne st st' tid tcb (determineTargetCore st tid) c hne h

/-- **`v0.35.169`: the binding release writes exactly the cores its own resolver
names** — the exactness half of the retype footprint's `.schedContext` replenish
segment.  The sweep arm names every core, so the hypothesis is unsatisfiable
there and the statement is about the bound arm. -/
theorem releaseSchedContextBinding_replenishQueueOnCore_ne (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (c : CoreId)
    (hne : c ∉ releaseSchedContextBindingReplenishCores st sc) :
    (releaseSchedContextBinding st scId sc).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold releaseSchedContextBinding
  unfold releaseSchedContextBindingReplenishCores at hne
  cases hBound : sc.boundThread with
  | none => rfl
  | some tid =>
      rw [hBound] at hne
      dsimp only at hne ⊢
      cases hTcb : st.getTcb? tid with
      | none => rw [hTcb] at hne; exact absurd (Concurrency.mem_allCores c) hne
      | some tcb =>
          rw [hTcb] at hne
          dsimp only
          simp only [List.mem_singleton] at hne
          rw [SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _
            (fun hc => hne hc.symm), SystemState.updateTcb_scheduler]

/-- **`v0.35.169`: and the whole pre-retype cleanup writes exactly the cores
`lifecycleRetypeReplenishCoresOf` names.**

The exactness half of `schedLockSet_lifecycleRetypeOnCore`'s replenish segment,
over all six object kinds: the TCB arm's donation step and the SchedContext
arm's release are the only two that move a replenishment, and every other step
of the pipeline — the reference sweep, the service-registry revoke, the CDT
detach, the reply and VSpace guards — frames the scheduler outright. -/
theorem lifecyclePreRetypeCleanup_replenishQueueOnCore_ne (st st' : SystemState)
    (target : SeLe4n.ObjId) (currentObj newObj : KernelObject) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCoresOf st target currentObj)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecyclePreRetypeCleanup at h
  unfold lifecycleRetypeReplenishCoresOf at hne
  cases hC : currentObj with
  | tcb tcb =>
      subst hC
      simp only at h hne
      split at h
      · exact absurd h (by simp)
      · rename_i stArm hRun
        have hArm : cancelDonationArmOnCore st tcb.tid tcb = .ok stArm := by
          split at hRun
          · exact absurd hRun (by simp)
          · exact hRun
        split at h
        · exact absurd h (by simp)
        · injection h with h
          subst h
          rw [cleanupTcbReferences_replenishQueueOnCore]
          exact cancelDonationArmOnCore_replenishQueueOnCore_ne st stArm tcb.tid tcb c hne hArm
  | schedContext sc =>
      subst hC
      simp only at h hne
      split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        exact releaseSchedContextBinding_replenishQueueOnCore_ne st _ sc c hne
  | endpoint ep =>
      subst hC
      simp only at h
      injection h with h
      subst h
      rw [cleanupEndpointServiceRegistrations_scheduler_eq]
  | cnode cn =>
      subst hC
      simp only at h
      split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        rw [detachCNodeSlots_scheduler_eq]
  | reply r =>
      subst hC
      simp only at h
      split at h
      · exact absurd h (by simp)
      · injection h with h; subst h; rfl
  | frame _ =>
      -- WS-BP BP7.1: a frame target is refused, so there is no `.ok` step.
      subst hC
      simp at h
  | _ =>
      subst hC
      simp only at h
      first
        | (injection h with h; subst h; rfl)
        | (split at h
           · exact absurd h (by simp)
           · injection h with h; subst h; rfl)

-- ============================================================================
-- §10  The `.tcbSuspend` arm — the step frames its segments rest on
-- ============================================================================
--
-- This arm is the one the previous cuts deferred, and its shape is why: the run
-- segment re-runs a seven-stage pipeline to the state each of its two walks
-- starts from, and the replenish segment is **two migrations read at
-- intermediate states** — the reclaim's, at the teardown's post-state, and G3's
-- donation arm's, at the post-revert state whose binding the reclaim may have
-- rewritten.  Neither is a proxy for a pre-state reading, so both are resolved
-- the way `replyRecvBodyWriteSet` resolves its own: by re-running the spine.

/-- **WS-RR RR8.12 Cut C6g (the exactness frame)**: the base retype-with-cleanup
writes no replenish queue outside `lifecycleRetypeReplenishCores` — the
FOOTPRINT's own segment.

Mirrors `lifecycleRetypeDirectWithCleanup_confinedToCores` clause for clause: the
well-formedness reject commits nothing, the absent-target arm is
`lifecycleRetypeDirect` (a store, so scheduler-silent), and the present arm is the
cleanup — the one step that moves a replenishment — then the scrub and the store,
both scheduler-silent. -/
theorem lifecycleRetypeDirectWithCleanup_replenishQueueOnCore_ne (authCap : Capability)
    (target : SeLe4n.ObjId) (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanup at h
  unfold lifecycleRetypeReplenishCores at hne
  split at h
  · exact absurd h (by simp)
  · cases hObj : SystemState.getObject? st target with
    | none =>
      rw [hObj] at h
      simp only [] at h
      rw [(lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj st st' h).1]
    | some currentObj =>
      rw [hObj] at h hne
      simp only [] at h
      cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
      | error e => rw [hClean] at h; simp only [] at h; exact absurd h (by simp)
      | ok stClean =>
        rw [hClean] at h
        simp only [] at h
        rw [(lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj
          (scrubObjectMemory stClean target currentObj.objectType) st' h).1,
          scrubObjectMemory_scheduler_eq stClean target currentObj.objectType]
        exact lifecyclePreRetypeCleanup_replenishQueueOnCore_ne st stClean target currentObj
          newObj c hne hClean

/-- **Cut C6g**: the ASID shootdown rounds move no replenishment — TLB maintenance
is not scheduling. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rw [hBase] at h; simp only [] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stBase⟩ := pair
    cases u
    rw [hBase] at h
    simp only [] at h
    rw [retypeShootdownAsids_eq] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    rw [retypeAsidRoundFold_scheduler]
    exact lifecycleRetypeDirectWithCleanup_replenishQueueOnCore_ne authCap target newObj st
      stBase c hne hBase

/-- **Cut C6g**: nor does the initiator's own per-core TLB view drain. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target newObj st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at h
  cases hRound : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
    with
  | error e => rw [hRound] at h; simp only [] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stRound⟩ := pair
    cases u
    rw [hRound] at h
    simp only [] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    rw [retypeInitiatorDrain_scheduler]
    exact lifecycleRetypeDirectWithCleanupShootdown_replenishQueueOnCore_ne executingCore authCap
      target newObj st stRound c hne hRound

/-- **Cut C6g (the live `.lifecycleRetype` arm's exactness frame)**: and neither
does the domain-wide instruction-cache broadcast, so the arm the syscall runs
writes no replenish queue outside the segment its footprint declares. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap target
      newObj st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at h
  cases hBase : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
      newObj st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff (retypeIcacheOperand target)
      (lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target newObj)
      st e).mpr hBase] at h
    exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stB⟩ := pair
    cases u
    rw [(Architecture.withIcacheBroadcast_frame hBase h).2.2.1]
    exact lifecycleRetypeDirectWithCleanupShootdownPerCore_replenishQueueOnCore_ne
      executingCore authCap target newObj st stB c hne hBase

/-- `v0.35.169`: the placement deschedule writes no replenish queue. -/
@[simp] theorem descheduleAt_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (placed : Option CoreId) (c : CoreId) :
    (descheduleAt st tid placed).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold descheduleAt
  cases placed with
  | none => rfl
  | some p => exact removeRunnableOnCore_replenishQueueOnCore st tid p c

/-- `v0.35.169`: G7's scheduling point writes no replenish queue — the only
state it can change is `handleRescheduleSgiOnCore`'s. -/
theorem suspendRescheduleOnCore_replenishQueueOnCore (st st' : SystemState)
    (runningCore executingCore : CoreId) (wasCurrent localDeboosted : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore executingCore
      wasCurrent localDeboosted = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals
    first
      | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1])
      | (exact absurd h (by simp))
  all_goals
    first
      | rfl
      | (rename_i hR; exact handleRescheduleSgiOnCore_replenishQueueOnCore _ executingCore _ c hR)

/-- `v0.35.169`: the reclaim's teardown writes exactly its migration's two
endpoints — the first half of the `.tcbSuspend` replenish segment. -/
theorem cancelIpcBlockingMigrated_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId) (c : CoreId)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder))
    (hFrom : determineTargetCore st holder ≠ c)
    (hTo : replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) scId
      (determineTargetCore st holder) ≠ c) :
    (cancelIpcBlockingMigrated victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold cancelIpcBlockingMigrated
  rw [hDon]
  dsimp only
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_other _ _ _ _ _ hFrom hTo,
    Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]

/-- `v0.35.169`: ...and with nothing donated it writes none at all. -/
theorem cancelIpcBlockingMigrated_replenishQueueOnCore_of_no_donation (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    (cancelIpcBlockingMigrated victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingMigrated_of_no_donation _ _ _ hDon,
    Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]

/-- `v0.35.169`: and the reclaim-complete teardown writes what the migration
writes — its holder deschedule is a run-queue step. -/
theorem cancelIpcBlockingReclaimed_replenishQueueOnCore (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId) :
    (cancelIpcBlockingReclaimed victim tcb st).scheduler.replenishQueueOnCore c
      = (cancelIpcBlockingMigrated victim tcb st).scheduler.replenishQueueOnCore c := by
  unfold cancelIpcBlockingReclaimed
  exact descheduleUnboundHolder_replenishQueueOnCore _ _ _ _ c

-- ============================================================================
-- §11  The `.tcbSuspend` arm's footprint
-- ============================================================================

/-- **The cores the live `.tcbSuspend` may write**, mirroring
`suspendThreadOnCore`'s own control flow. Four contributions, all read off the
**pre-state** exactly as the transition reads them:

* the reverted priority-inheritance chain's home cores, walked from the
  captured `blockingServer` at the post-teardown state;
* the core the pre-state **places** the victim on (`descheduleAtPlacementCores`,
  WS-RR RR8.6 — queued or current; its home and its running core until then,
  two proxies that between them missed a victim queued off its home), where it
  is dequeued;
* the **executing** core, where G7 may run a local preemption point.

Both donation arms, `clearPendingState` and the `.Inactive` store are per-core
silent and contribute nothing.  The teardown was too until **WS-RR RR8.12** gave
G2 the reclaim's scheduler step; since `v0.35.158` that step deschedules the
holder the reclaim unbound (WS-OD OD1.7's wake of it until then), so G2
contributes that holder's placed core, and no other
(`cancelIpcBlockingReclaimed_confinedToCores`). -/
def suspendThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match st.getTcb? vtid.val with
  | none => []
  | some tcb =>
    if tcb.threadState == .Inactive then []
    else
      -- One entry per pipeline step, in execution order; `[]` marks a step that
      -- writes no core at all, so this reads as the transition's own shape.
      --
      -- **WS-RR RR8.12**, re-keyed at `v0.35.158`: G2 is the teardown with its
      -- reclaim COMPLETED, so the first entry is no longer `[]`: the reclaim's
      -- holder deschedule removes the holder it unbound from the holder's **own**
      -- placement, which is neither the victim's placement nor the executing
      -- core (until `v0.35.158` the step was OD1.7's wake and the entry the
      -- holder's home core).  A write set that omits a written core is as false
      -- as a footprint that does, and until RR8.12 this one named none because
      -- the live pipeline performed no such step.
      (cancelUnboundHolderCore? st (cancelIpcBlockingMigrated vtid.val tcb st)
        vtid.val tcb).toList -- the reclaim's holder deschedule
      ++ (match PriorityInheritance.blockingServer st vtid.val with
       | some serverId =>
           pipChainWriteSet (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore
             (cancelIpcBlockingReclaimed vtid.val tcb st).objectIndex.length
       | none => []) -- the chain reversion, on the post-teardown state
      ++ [] -- donation cancellation
      ++ descheduleAtPlacementCores st vtid.val -- the placement dequeue
      ++ [] -- clearPendingState
      ++ [] -- the `.Inactive` store
      ++ [executingCore] -- the G7 scheduling point
/-- **`v0.35.170`: the cores the live `.tcbSuspend` moves a RESERVATION on.**

Two migrations, and neither is pre-state computable, which is why this arm is a
cut of its own.  G2's reclaim migrates the context it reclaims, and its
destination is read at the **torn** state.  G3's donation arm then runs on the
*post-revert* state, whose binding the reclaim may have rewritten — WS-OD OD5.3's
finding, that the pipeline pops twice at call depth ≥ 2 and the second pop's
destination is the outer caller's home, a core the pre-state cannot name because
at the pre-state the victim holds no binding at all.

So the segment re-runs the spine to each step's own state, exactly as
`replyRecvBodyWriteSet` does — and the one core that *is* read from the pre-state
is G3's purge core, because the pipeline itself reads it there (`home`, captured
before G2 for the reason `suspendThreadOnCore` records: the teardown never moves
it). -/
def suspendThreadReplenishCores (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match st.getTcb? vtid.val with
  | none => []
  | some tcb =>
    if tcb.threadState == .Inactive then []
    else
      cancelIpcBlockingReplenishCores st vtid.val tcb
      ++ (let stG2 := cancelIpcBlockingReclaimed vtid.val tcb st
          let stG2b := match PriorityInheritance.blockingServer st vtid.val with
            | some serverId =>
                (PriorityInheritance.propagatePipChainCrossCore stG2 serverId executingCore).1
            | none => stG2
          cancelDonationArmReplenishCoresAt stG2b vtid.val
            ((stG2b.getTcb? vtid.val).getD tcb) (determineTargetCore st vtid.val))

/-- **`v0.35.170`: the live `.tcbSuspend` arm's scheduler-domain footprint** —
the last of the declared arms, and the one that retires a six-parameter
parametric form.

`suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome placed
holderPlaced` takes five cores and an optional sixth from its caller; this reads
every one of them off the state the transition reads it from.  *A parameter is a
place for a caller to be wrong* (PR #895 round 10), and six of them is the
largest such surface in the tree. -/
def schedLockSet_suspendThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (suspendThreadOnCoreWriteSet st vtid executingCore)
    (suspendThreadReplenishCores st vtid executingCore)

/-- `v0.35.170`: an already-`.Inactive` victim is refused, so the footprint is
the object-store write lock and nothing else. -/
theorem schedLockSet_suspendThreadOnCore_of_inactive (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) :
    schedLockSet_suspendThreadOnCore st vtid executingCore
      = [(SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)] := by
  unfold schedLockSet_suspendThreadOnCore suspendThreadOnCoreWriteSet
    suspendThreadReplenishCores
  rw [hTcb]
  simp [hInactive, schedFootprintOfCores, schedCoreSegment, Concurrency.canonicalCores]

/-- `v0.35.170`: the footprint holds the executing core's run-queue write lock,
which G7's scheduling point writes. -/
theorem schedLockSet_suspendThreadOnCore_contains_executing_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold suspendThreadOnCoreWriteSet
        rw [hTcb]
        simp [beq_iff_eq, hActive])

/-- `v0.35.170`: ...and the victim's placed core's, which G4 dequeues it from. -/
theorem schedLockSet_suspendThreadOnCore_contains_placed_runQueue_write (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB) (placed : CoreId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive)
    (hPlaced : placedCoreOf? st vtid.val = some placed) :
    (SchedLockId.runQueue ⟨placed⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold suspendThreadOnCoreWriteSet
        rw [hTcb]
        simp [beq_iff_eq, hActive, descheduleAtPlacementCores, hPlaced])

/-- **`v0.35.170`: and both replenish-queue write locks the reclaim's migration
needs** — the endpoints it actually moves the reservation between. -/
theorem schedLockSet_suspendThreadOnCore_contains_reclaim_replenishQueue_writes
    (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st vtid.val tcb = some (scId, holder)) :
    (SchedLockId.replenishQueue ⟨determineTargetCore st holder⟩,
      Concurrency.AccessMode.write) ∈ schedLockSet_suspendThreadOnCore st vtid executingCore ∧
    (SchedLockId.replenishQueue
        ⟨replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st vtid.val tcb) scId
          (determineTargetCore st holder)⟩,
      Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore := by
  constructor <;>
    exact (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
      (by unfold suspendThreadReplenishCores
          rw [hTcb]
          simp [beq_iff_eq, hActive, cancelIpcBlockingReplenishCores, hDon])

/-- **`v0.35.170`: the resolved footprint covers the parametric one's RUN-QUEUE
segment**, at the two cores that form is handed by the operation.

Stated over the run-queue half alone, and that is the honest scope: the
parametric replenish segment is four free parameters — three cores and a list —
so a coverage claim over it would have to hypothesise that a caller passed what
the transition writes, which is the conclusion, and a theorem whose conclusion
is one of its own hypotheses pins nothing.  What the resolved form gives instead is the two
*exactness* statements this cut's §12 proves; the parametric form has neither,
which is how its replenish segment went four cuts without naming G2's
migration.

`placed` and `holderPlaced` are the only arguments the operation itself resolves
(`placedCoreOf?` on the pre-state, and `cancelUnboundHolderCore?` on the
reclaim's own state pair), so at those the containment is unconditional. -/
theorem schedLockSet_suspendThreadOnCore_covers_parametric_runQueue (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (home ownerHome outerHome : CoreId) (reclaimReplenish : List CoreId) (c : CoreId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive)
    (hp : (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome
          (placedCoreOf? st vtid.val)
          (cancelUnboundHolderCore? st (cancelIpcBlockingMigrated vtid.val tcb st)
            vtid.val tcb)
          reclaimReplenish) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore := by
  rw [suspendThreadOnCoreSchedLockSet, mem_schedFootprintOfCores_runQueue_iff] at hp
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ c).mpr ?_
  unfold suspendThreadOnCoreWriteSet
  rw [hTcb]
  simp only [beq_iff_eq, hActive, if_false, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.append_nil]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl) | hHolder
  · -- the victim's placed core, or the executing core where it is placed nowhere
    cases hPl : placedCoreOf? st vtid.val with
    | none => simp [descheduleAtPlacementCores, hPl]
    | some p => simp [descheduleAtPlacementCores, hPl]
  · simp
  · exact Or.inl (Or.inl (Or.inl hHolder))

-- ============================================================================
-- §12  The exactness halves — what the live `.tcbSuspend` writes
-- ============================================================================

/-- **`v0.35.170`: the reclaim-complete teardown writes exactly the cores its
own resolver names** — the first half of the `.tcbSuspend` replenish segment,
stated over `cancelIpcBlockingReplenishCores` so the footprint and the frame
read one answer. -/
theorem cancelIpcBlockingReclaimed_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hne : c ∉ cancelIpcBlockingReplenishCores st victim tcb) :
    (cancelIpcBlockingReclaimed victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingReclaimed_replenishQueueOnCore]
  unfold cancelIpcBlockingReplenishCores at hne
  cases hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb with
  | none => exact cancelIpcBlockingMigrated_replenishQueueOnCore_of_no_donation _ _ _ _ hDon
  | some p =>
      obtain ⟨scId, holder⟩ := p
      rw [hDon] at hne
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
      exact cancelIpcBlockingMigrated_replenishQueueOnCore_ne _ _ _ _ _ _ hDon
        (fun hc => hne.1 hc.symm) (fun hc => hne.2 hc.symm)

/-- **`v0.35.170`: ...and so does the cancellation composite**, whose own
footprint declares the same pair.

`cancelIpcBlockingOnCore` is the reclaim-complete teardown followed by the
victim's placement deschedule, and a deschedule is a run-queue step — so the
composite writes exactly what the reclaim's migration writes.  Stated because
`cancelIpcBlockingOnCoreSchedLockSet_covers_migration` is the *names what is
written* half and a footprint owes both: without this the composite could
acquire a replenish lock it never writes, or write one it never declares, and
nothing would say which. -/
theorem cancelIpcBlockingOnCore_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (c : CoreId)
    (hne : c ∉ cancelIpcBlockingReplenishCores st victim tcb) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingOnCore_eq_reclaimed_deschedule, descheduleThread,
    descheduleAtPlacement, descheduleAt_replenishQueueOnCore]
  exact cancelIpcBlockingReclaimed_replenishQueueOnCore_ne st victim tcb c hne

/-- **`v0.35.170`: and the whole live `.tcbSuspend` writes exactly the cores
`suspendThreadReplenishCores` names.**

The exactness half of the footprint's replenish segment, over the pipeline's
seven stages.  Two of them move a reservation — G2's reclaim moves the context
it reclaims, and G3's donation arm moves or purges the victim's own — and the
segment is their two resolvers concatenated, each read at the state its own step
runs on.  Every other stage frames every replenish queue outright: G2b's chain
revert re-buckets run queues (`propagatePipChainCrossCore_replenishQueueOnCore`),
G4's placement dequeue is a run-queue removal, G5 and G6 write TCBs, and G7's
scheduling point at most dispatches a successor.

Read with `schedLockSet_suspendThreadOnCore_contains_reclaim_replenishQueue_writes`
this is the pair a resolved scheduler footprint owes: the footprint names every
replenish queue the arm writes, and the arm writes no replenish queue the
footprint does not name. -/
theorem suspendThreadOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hne : c ∉ suspendThreadReplenishCores st vtid executingCore)
    (h : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold Lifecycle.Suspend.suspendThreadOnCore at h
  unfold suspendThreadReplenishCores at hne
  simp only at h hne
  cases hTcb : st.getTcb? vtid.val with
  | none => rw [hTcb] at h; exact absurd h (by simp)
  | some tcb =>
    rw [hTcb] at h hne
    simp only at h hne
    by_cases hInact : (tcb.threadState == .Inactive) = true
    · rw [if_pos hInact] at h; exact absurd h (by simp)
    · rw [if_neg hInact] at h hne
      simp only [List.mem_append, not_or] at hne
      -- G2: the reclaim-complete teardown, at the pre-state.
      have hG2 := cancelIpcBlockingReclaimed_replenishQueueOnCore_ne st vtid.val tcb c hne.1
      -- G2b: the chain revert frames every replenish queue.
      have hG2b : ∀ s : SystemState,
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId =>
               (PriorityInheritance.propagatePipChainCrossCore s serverId executingCore).1
           | none => s).scheduler.replenishQueueOnCore c
            = s.scheduler.replenishQueueOnCore c := by
        intro s
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => rfl
        | some serverId =>
            exact PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore
              s serverId executingCore _ c
      -- G3: the donation arm, at the post-revert state and the pre-state home.
      split at h
      · exact absurd h (by simp)
      · rename_i stArm hArm
        have hG3 := donationArmAt_replenishQueueOnCore_ne _ stArm vtid.val _
          (determineTargetCore st vtid.val) c hne.2 hArm
        -- G4..G7: every remaining stage frames every replenish queue.
        rw [suspendRescheduleOnCore_replenishQueueOnCore _ st' _ _ _ _ _ c h,
          SystemState.updateTcb_scheduler, Lifecycle.Suspend.clearPendingStateValid_eq,
          Lifecycle.Suspend.clearPendingState_scheduler_eq, descheduleAt_replenishQueueOnCore,
          hG3, hG2b, hG2]

-- ============================================================================
-- §13  The syscall-level resolver — one footprint per arm, from the operands
-- ============================================================================
--
-- WS-RR RR8.12 Cut C4.  `lockSetForSyscall` is the object domain's; this is the
-- scheduler domain's, and the two are deliberately the same shape: a `match`
-- over `SyscallId` dispatching to the arm's own resolved footprint, a boolean
-- inventory of which arms declare, and a negative over that inventory saying
-- every other arm declares nothing whatever the operands and whatever the state.
--
-- It is here rather than beside `lockSetForSyscall` for the reason this module
-- exists at all (see the header): `SchedLockId` is declared above every module
-- that holds a lifecycle, priority, affinity, SchedContext or retype
-- transition, so the arms' own footprints could not live beside them and this
-- resolver cannot live beside its object-domain twin.

open SeLe4n.Kernel.Concurrency (SyscallLockOperands)

/-- **WS-RR RR8.12 Cut C4: the scheduler-domain footprint the live syscall seam
declares**, at the decoded arm and the operands that arm's capability names.

Sixteen arms declare; the other nineteen answer `none`.  Each declared arm is
`SchedLockSet.ofList?` of its own resolved footprint, and that constructor's
`Nodup` obligation is `schedFootprintOfCores_keys_nodup` — so it provably never
refuses a footprint this kernel declares, which the per-arm `_isSome_iff`
characterisations below state.

**Every arm reads the operands the transition reads, and nothing else.**  Where
an operand is absent the arm answers `none`, which is the fail-closed direction
`SyscallLockOperands` has had since WS-RR RR7.10 and the one this file's object
domain twin already takes for a `.send` with no message: defaulting would
declare a footprint for a *different* transition.  `.call` needs the invoked
capability's rights and the receiver's slot base because its write set re-runs
the dispatch; `.reply` needs the `MessageInfo` and the register payload because
`decodeFaultReply` reads them to tell a restart from an abandon, and the abandon
is the one core the dispatch-level footprint never names; `.tcbSetAffinity`
needs the destination core, whose own `Option` is the unpin request and so must
not be collapsed with "not supplied".

**`.notificationSignal` routes to the BOUND arm**, which is the one the live
dispatch takes — Cut 7's own note, and the reason
`schedLockSet_notificationSignalBoundOnCore` exists beside the unbound one.

**`.reply` routes to the ARM's footprint, not the dispatch's**
(`schedLockSet_replyTransferOnCore`): `v0.35.163` proved the abandon's home-core
member is one the dispatch never writes, so a resolver that named the dispatch's
would be short by it.

**Reachable from the ABI seam since Cut C4b** (§14's
`declaredSchedLockSetForAbiEntry`), which is what makes the paragraph above a
statement about the live entry rather than about a resolver nobody calls.  Cut
C4 shipped this with `abiEntryLockOperands` (`SyscallLockBracket.lean`) building
its operands for the object domain alone: it supplied none of the five fields
named above, so `.call`, `.reply`, `.replyRecv` and `.tcbSetAffinity` would each
have answered `none` — an *undeclared* arm, which the bracket treats as "no
exclusion established" and which is therefore sound, and which would have
silently dropped four arms out of the very coverage this workstream is building.
C4b extended that one builder rather than adding a second: **the two domains
share `abiEntryPlan` and `abiEntryLockOperands`**
(`declaredSchedLockSetForAbiEntry_shares_decode`), so the syscall id, the caller
and the operands each domain's footprint is a function of are one decode.  A
second builder is the shape that lets one domain's footprint be acquired around
the other domain's transition. -/
def schedLockSetForSyscall (sid : SyscallId) (ops : SyscallLockOperands)
    (executingCore : CoreId) (st : SystemState) : Option SchedLockSet :=
  match sid with
  | .tcbSuspend =>
      ops.targetThread.bind fun victim =>
        victim.toValid?.bind fun vtid =>
          SchedLockSet.ofList? (schedLockSet_suspendThreadOnCore st vtid executingCore)
  | .tcbResume =>
      ops.targetThread.bind fun target =>
        target.toValid?.bind fun vtid =>
          SchedLockSet.ofList? (schedLockSet_resumeThreadOnCore st vtid executingCore)
  | .tcbSetPriority | .tcbSetMCPriority =>
      ops.targetThread.bind fun target =>
        SchedLockSet.ofList? (schedLockSet_priorityControlOnCore st target executingCore)
  | .tcbSetAffinity =>
      ops.targetThread.bind fun target =>
        ops.affinity.bind fun newCore =>
          SchedLockSet.ofList? (schedLockSet_setThreadCpuAffinityOnCore st target newCore)
  | .schedContextConfigure =>
      ops.targetObject.bind fun scObjId =>
        SchedLockSet.ofList? (schedLockSet_schedContextConfigureOnCore st scObjId)
  | .schedContextBind =>
      ops.targetThread.bind fun target =>
        SchedLockSet.ofList? (schedLockSet_schedContextBindOnCore st target)
  | .schedContextUnbind =>
      ops.targetObject.bind fun scObjId =>
        SchedLockSet.ofList? (schedLockSet_schedContextUnbindOnCore st scObjId executingCore)
  | .lifecycleRetype =>
      ops.targetObject.bind fun target =>
        SchedLockSet.ofList? (schedLockSet_lifecycleRetypeOnCore st target)
  | .notificationSignal =>
      ops.targetObject.bind fun nId =>
        SchedLockSet.ofList? (schedLockSet_notificationSignalBoundOnCore st nId)
  | .notificationWait =>
      SchedLockSet.ofList? (schedLockSet_notificationWaitOnCore executingCore)
  | .send =>
      ops.targetObject.bind fun epId =>
        SchedLockSet.ofList? (schedLockSet_endpointSendOnCore st epId executingCore)
  | .receive =>
      ops.targetObject.bind fun epId =>
        SchedLockSet.ofList? (schedLockSet_endpointReceiveOnCore st epId ops.caller executingCore)
  | .call =>
      ops.targetObject.bind fun epId =>
        ops.message.bind fun msg =>
          ops.endpointRights.bind fun rights =>
            ops.receiverSlotBase.bind fun slotBase =>
              SchedLockSet.ofList?
                (schedLockSet_endpointCallOnCore epId ops.caller msg rights slotBase
                  executingCore st)
  | .reply =>
      ops.targetReply.bind fun rid =>
        (replyAnsweredCaller? st rid).bind fun answered =>
          ops.message.bind fun msg =>
            ops.replyMessageInfo.bind fun mi =>
              ops.replyRegisters.bind fun regs =>
                SchedLockSet.ofList?
                  (schedLockSet_replyTransferOnCore ops.caller answered mi regs msg
                    executingCore st)
  | .replyRecv =>
      ops.targetObject.bind fun epId =>
        ops.targetReply.bind fun rid =>
          (replyAnsweredCaller? st rid).bind fun prevCaller =>
            (st.getTcb? ops.caller).bind fun receiver =>
              ops.message.bind fun msg =>
                ops.receiverSlotBase.bind fun slotBase =>
                  SchedLockSet.ofList?
                    (schedLockSet_endpointReplyRecvOnCore epId ops.caller rid prevCaller msg
                      receiver.cspaceRoot slotBase executingCore st)
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .untypedRetype
  | .mintReplyCap
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .tcbSetIPCBuffer | .tcbSetFaultHandler
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify | .declassifySignal
  | .auditRead | .auditDrain => none

/-- **Cut C4**: the arms `schedLockSetForSyscall` declares a footprint for.

A second enumeration beside that `match`, and here for the same reason
`declaredFootprintSyscall` is: the negative below has to name a set.  What
matters is which way it can drift, and both are closed.  Converting an arm to a
footprint without listing it here breaks
`schedLockSetForSyscall_undeclared_none` at elaboration; listing an arm that
still answers `none` is refused by that arm's own `_isSome_iff`, which states
the exact operands under which it declares.

There are `SyscallId.count = 37` arms; **sixteen** declare and twenty-one
answer `none`.  *Which* of those twenty-one write a scheduler slot at all is this
enumeration's own open question — the arms above are the ones WS-RR RR8.12's
sequence identified, and a twenty-second found to write one is a footprint to
declare rather than a row to move.  `.cspaceRevoke` (`v0.35.190`) is in the
`none` group for the same reason its `.cspaceDelete` sibling is: the revocation
family writes CNodes, the derivation tree and in-flight messages, and no
run-queue or replenish-queue slot on any core.  `.untypedRetype` (`v0.36.5`) is
there too: a carve writes an untyped, a fresh frame, one CNode slot, the CDT and
a page of machine memory — no scheduler field at all. -/
def declaredSchedFootprintSyscall : SyscallId → Bool
  | .tcbSuspend | .tcbResume
  | .tcbSetPriority | .tcbSetMCPriority | .tcbSetAffinity
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind
  | .lifecycleRetype
  | .notificationSignal | .notificationWait
  | .send | .receive | .call | .reply | .replyRecv => true
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .untypedRetype
  | .mintReplyCap
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .tcbSetIPCBuffer | .tcbSetFaultHandler
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify | .declassifySignal
  | .auditRead | .auditDrain => false

/-- **Cut C4**: every arm this module has not declared is undeclared, whatever
the operands and whatever the state.

The load-bearing direction, and the object domain's own reason: a caller reading
`some S` treats `S` as the complete set of **cores** the transition writes, so
an arm that returned a footprint before its coverage proof existed would hand
out exclusion the runtime never established.  Adding the next declared arm must
change `declaredSchedFootprintSyscall`, and forgetting to stops this
elaborating. -/
theorem schedLockSetForSyscall_undeclared_none (sid : SyscallId)
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : declaredSchedFootprintSyscall sid = false) :
    schedLockSetForSyscall sid ops executingCore st = none := by
  cases sid <;> first | rfl | exact absurd h (by simp [declaredSchedFootprintSyscall])

/-! ### The per-arm characterisations

Each says exactly which operands its arm needs, which is what closes the other
direction of `declaredSchedFootprintSyscall`'s drift: an arm listed there that
had quietly become unconditionally `none` could not satisfy its own `iff`.

Two things they establish besides.  **`SchedLockSet.ofList?` never refuses a
footprint this kernel declares** — every one of them is
`schedFootprintOfCores`, whose keys are `Nodup` by
`schedFootprintOfCores_keys_nodup` — so no arm's condition mentions the
constructor, and the fail-closed path exists for a footprint spelled some other
way.  And **the scheduler domain needs the caller's TCB on one arm only**,
`.replyRecv`, where the receiver's CSpace root enters the write set through the
capability transfer; the object domain needs it on all eight of its arms,
because there every footprint names the caller's CNode. -/

/-- `.notificationWait` declares unconditionally: its footprint is the executing
core's run-queue lock and nothing the state or the operands can withhold. -/
@[simp] theorem schedLockSetForSyscall_notificationWait_isSome
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .notificationWait ops executingCore st).isSome := by
  simp [schedLockSetForSyscall, SchedLockSet.ofList?, schedLockSet_notificationWaitOnCore,
    schedFootprintOfCores_keys_nodup]

/-- The four object-directed arms declare exactly when the operand naming the
object is supplied. -/
theorem schedLockSetForSyscall_objectDirected_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .schedContextConfigure ∨ sid = .schedContextUnbind ∨
         sid = .lifecycleRetype ∨ sid = .notificationSignal ∨ sid = .send) :
    (schedLockSetForSyscall sid ops executingCore st).isSome ↔ ops.targetObject.isSome := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases ops.targetObject <;>
       simp [SchedLockSet.ofList?, schedLockSet_schedContextConfigureOnCore,
         schedLockSet_schedContextUnbindOnCore, schedLockSet_lifecycleRetypeOnCore,
         schedLockSet_notificationSignalBoundOnCore, schedLockSet_endpointSendOnCore,
         schedFootprintOfCores_keys_nodup])

/-- `.receive` is object-directed too, and its footprint additionally reads the
receiving thread — which is the caller, so no operand beyond the endpoint. -/
theorem schedLockSetForSyscall_receive_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .receive ops executingCore st).isSome
      ↔ ops.targetObject.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject <;>
    simp [SchedLockSet.ofList?, schedLockSet_endpointReceiveOnCore,
      schedFootprintOfCores_keys_nodup]

/-- The two thread-directed priority arms declare on the target alone. -/
theorem schedLockSetForSyscall_priority_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .tcbSetPriority ∨ sid = .tcbSetMCPriority ∨ sid = .schedContextBind) :
    (schedLockSetForSyscall sid ops executingCore st).isSome ↔ ops.targetThread.isSome := by
  rcases h with rfl | rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases ops.targetThread <;>
       simp [SchedLockSet.ofList?, schedLockSet_priorityControlOnCore,
         schedLockSet_schedContextBindOnCore, schedFootprintOfCores_keys_nodup])

/-- `.tcbSetAffinity` needs the destination core as well, and its outer `Option`
is the one that says whether the caller supplied it at all. -/
theorem schedLockSetForSyscall_tcbSetAffinity_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .tcbSetAffinity ops executingCore st).isSome
      ↔ ops.targetThread.isSome ∧ ops.affinity.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetThread <;> cases ops.affinity <;>
    simp [SchedLockSet.ofList?, schedLockSet_setThreadCpuAffinityOnCore,
      schedFootprintOfCores_keys_nodup]

/-- The two thread-directed lifecycle arms need a target that is not the
reserved sentinel — the same promotion the transitions themselves perform, so
the footprint is declared exactly where the step can run. -/
theorem schedLockSetForSyscall_lifecycle_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .tcbSuspend ∨ sid = .tcbResume) :
    (schedLockSetForSyscall sid ops executingCore st).isSome
      ↔ ∃ t, ops.targetThread = some t ∧ t.toValid?.isSome := by
  rcases h with rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases hT : ops.targetThread with
     | none => simp
     | some t =>
        cases hV : t.toValid? <;>
          simp [hV, SchedLockSet.ofList?, schedLockSet_suspendThreadOnCore,
            schedLockSet_resumeThreadOnCore, schedFootprintOfCores_keys_nodup])

/-- `.call` needs the endpoint, the message, the invoked capability's rights and
the receiver's slot base — its write set re-runs the dispatch, which reads all
four. -/
theorem schedLockSetForSyscall_call_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .call ops executingCore st).isSome
      ↔ ops.targetObject.isSome ∧ ops.message.isSome ∧ ops.endpointRights.isSome ∧
        ops.receiverSlotBase.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject <;> cases ops.message <;> cases ops.endpointRights <;>
    cases ops.receiverSlotBase <;>
      simp [SchedLockSet.ofList?, schedLockSet_endpointCallOnCore,
        schedFootprintOfCores_keys_nodup]

/-- `.reply` needs the Reply object to resolve to an answered caller, and the
message, `MessageInfo` and register payload `decodeFaultReply` reads. -/
theorem schedLockSetForSyscall_reply_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .reply ops executingCore st).isSome
      ↔ (∃ rid, ops.targetReply = some rid ∧ (replyAnsweredCaller? st rid).isSome) ∧
        ops.message.isSome ∧ ops.replyMessageInfo.isSome ∧ ops.replyRegisters.isSome := by
  unfold schedLockSetForSyscall
  cases hR : ops.targetReply with
  | none => simp
  | some rid =>
      cases hA : replyAnsweredCaller? st rid <;>
        cases ops.message <;> cases ops.replyMessageInfo <;> cases ops.replyRegisters <;>
          simp [hA, SchedLockSet.ofList?, schedLockSet_replyTransferOnCore,
            schedFootprintOfCores_keys_nodup]

/-- `.replyRecv` needs both targets, the answered caller, the caller's own TCB
(its CSpace root is what the capability transfer writes through), the message
and the receiver's slot base. -/
theorem schedLockSetForSyscall_replyRecv_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .replyRecv ops executingCore st).isSome
      ↔ ops.targetObject.isSome ∧
        (∃ rid, ops.targetReply = some rid ∧ (replyAnsweredCaller? st rid).isSome) ∧
        (st.getTcb? ops.caller).isSome ∧ ops.message.isSome ∧ ops.receiverSlotBase.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject with
  | none => simp
  | some _ =>
      cases hR : ops.targetReply with
      | none => simp
      | some rid =>
          cases hA : replyAnsweredCaller? st rid <;>
            cases st.getTcb? ops.caller <;> cases ops.message <;>
              cases ops.receiverSlotBase <;>
                simp [hA, SchedLockSet.ofList?, schedLockSet_endpointReplyRecvOnCore,
                  schedFootprintOfCores_keys_nodup]

-- ============================================================================
-- §14  The ABI entry's scheduler-domain footprint
-- ============================================================================

open SeLe4n.Kernel.Concurrency (LockSet lockSetForSyscall)

/-- **WS-RR RR8.12 Cut C4b: the scheduler-domain footprint the live ABI seam
declares** — `declaredLockSetForAbiEntry`'s twin, clause for clause.

`schedLockSetForSyscall` at the **decoded** syscall id, the caller the executing
core is running, and the operands that caller's capability names, every input
derived from the entry's own resolution rather than supplied alongside it.  A
caller cannot bracket one syscall's scheduler footprint around another's.

**It shares `abiEntryPlan` and `abiEntryLockOperands` with the object domain**
rather than re-deriving either, which is what makes "the two domains bracket the
same syscall" a fact rather than a hope: a decode that resolves differently for
the two would put one domain's footprint around the other domain's transition.
Cut C4b is what made that sharing possible — the builder now supplies the five
operands the scheduler footprints read and the eight arms the object domain
declares nothing for, so the two resolvers see one decode and disagree only
about which *locks* it implies. -/
def declaredSchedLockSetForAbiEntry (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option SchedLockSet :=
  match abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st with
  | none => none
  | some (tid, decoded, stFilled) =>
    (abiEntryLockOperands decoded tid stFilled).bind
      (fun ops => schedLockSetForSyscall decoded.syscallId ops executingCore stFilled)

/-- **Cut C4b**: an entry whose plan does not resolve declares nothing — the
fail-closed direction the object domain's resolver takes for the same reason,
and the one a bracket reads as "no exclusion established". -/
@[simp] theorem declaredSchedLockSetForAbiEntry_of_no_plan (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (h : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st = none) :
    declaredSchedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredSchedLockSetForAbiEntry
  rw [h]

/-- **Cut C4b**: and an entry whose decoded arm is undeclared declares nothing,
whatever its operands resolve to.

The seam-level reading of `schedLockSetForSyscall_undeclared_none`, and the
statement a bracket needs: the nineteen arms this workstream has not given a
scheduler footprint fall back to the coarse serialisation rather than acquiring
a footprint nobody proved covers them. -/
theorem declaredSchedLockSetForAbiEntry_undeclared_none (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState)
    (hPlan : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (h : declaredSchedFootprintSyscall decoded.syscallId = false) :
    declaredSchedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredSchedLockSetForAbiEntry
  rw [hPlan]
  simp only
  cases hOps : abiEntryLockOperands decoded tid stFilled with
  | none => rfl
  | some ops =>
      simp only [Option.bind_some]
      exact schedLockSetForSyscall_undeclared_none decoded.syscallId ops executingCore stFilled h

/-- **Cut C4b**: the two domains resolve ONE decode.

Stated rather than left to be read off two definitions: both resolvers run
`abiEntryPlan` and then `abiEntryLockOperands` on its answer, so the syscall id,
the caller and the operands each domain's footprint is a function of are the same
three values.  A decode resolved twice is the shape that lets one domain's
footprint be acquired around the other domain's transition. -/
theorem declaredSchedLockSetForAbiEntry_shares_decode (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState) (ops : SyscallLockOperands)
    (hPlan : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (hOps : abiEntryLockOperands decoded tid stFilled = some ops) :
    declaredLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
        = lockSetForSyscall decoded.syscallId ops stFilled ∧
    declaredSchedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
        = schedLockSetForSyscall decoded.syscallId ops executingCore stFilled := by
  refine ⟨?_, ?_⟩
  · unfold declaredLockSetForAbiEntry
    rw [hPlan]
    simp only
    rw [hOps]
    rfl
  · unfold declaredSchedLockSetForAbiEntry
    rw [hPlan]
    simp only
    rw [hOps]
    rfl

/-- **Cut C4b**: the receiver CSpace root the `.replyRecv` footprint resolves IS
the root the live arm installs through.

The live arm hands `replyRecvBody` the **gate's** `cspaceRoot`; the scheduler
resolver has no gate to read, so it takes the caller's TCB at the same state.
`abiEntryLockOperands_caller` says that caller is the entry's own `tid`, and
`abiEntryGate_cspaceRoot` says the gate's root is that thread's — so the two are
one lookup rather than two readings of one question, which is the shape that
would let a footprint name a root the transition does not walk. -/
theorem abiEntrySchedReceiverCspaceRoot (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (ops : Concurrency.SyscallLockOperands)
    (tcb : TCB) (gate : SyscallGate)
    (hOps : abiEntryLockOperands decoded tid s = some ops)
    (hGate : abiEntryGate decoded tid s = some (tcb, gate)) :
    s.getTcb? ops.caller = some tcb ∧ gate.cspaceRoot = tcb.cspaceRoot := by
  obtain ⟨hLookup, hRoot, _⟩ := abiEntryGate_cspaceRoot decoded tid s tcb gate hGate
  rw [abiEntryLockOperands_caller decoded tid s ops hOps]
  exact ⟨hLookup, hRoot⟩

-- ============================================================================
-- §15  The UNIFIED syscall footprint — one ladder over both domains
-- ============================================================================

/-- **WS-RR RR8.12 Cut C6h**: an object-domain footprint's members lifted into
the unified domain, with the table lock canonicalised.

`canonicalSchedLockOfObject` is the per-lock half; this is the per-footprint one.
It is a plain `map`, so the object domain's declaration order is preserved and
`lockAcquireSequence` — which sorts — is what imposes the ladder, exactly as it
is for a scheduler footprint. -/
def liftObjectFootprint (S : Concurrency.LockSet) :
    List (SchedLockId × Concurrency.AccessMode) :=
  S.pairs.map (fun p => (canonicalSchedLockOfObject p.fst, p.snd))

/-- **Cut C6h**: the lift preserves membership, which is what a coverage or
conflict claim stated over the object footprint needs in order to reach the
unified one. -/
theorem mem_liftObjectFootprint (S : Concurrency.LockSet) (l : Concurrency.LockId)
    (m : Concurrency.AccessMode) (h : (l, m) ∈ S.pairs) :
    (canonicalSchedLockOfObject l, m) ∈ liftObjectFootprint S :=
  List.mem_map_of_mem h

/-- **Cut C6h**: the lifted members an already-named key would duplicate, dropped.

A syscall's two footprints both name the object-store table lock — the object
domain spells it `stateLevelLock` and the scheduler domain
`schedObjStoreLockId`, and they are one word (`schedAcquireLock_objStore_congr`).
Canonicalising makes them one **key**, so the union has to drop the second copy
or `SchedLockSet.ofList?` refuses the whole footprint for a duplicate key.

The drop is at `.write` only, which is the fail-closed direction: a scheduler
footprint always names the table lock at `.write`
(`schedFootprintOfCores_contains_objStore_write`), so a `.read` declaration on
the object side is subsumed and anything the predicate cannot see keeps its own
member and is refused by `ofList?` rather than silently merged at the weaker
mode. -/
def unifiedObjectResidue (O : Concurrency.LockSet) (S : SchedLockSet) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (liftObjectFootprint O).filter
    (fun p => !S.pairs.contains (p.fst, Concurrency.AccessMode.write))

/-- **WS-RR RR8.12 Cut C6h: the syscall seam's UNIFIED footprint.**

One `SchedLockSet` spanning both lock domains, which is what `SchedLockId` was
introduced for (SM5.A.2) and what the seam has never had.  The two domains are
not two lock *words*: `schedAcquireLock`'s `.object` arm calls SM3.C's own
`acquireLockOnObject`, so a `.object` member writes exactly the state a `LockSet`
member writes.  Bracketing them separately would therefore acquire the table lock
**twice** on the five arms whose object footprint names `stateLevelLock`, and —
worse — would walk the SM0.I ladder backwards: the inner bracket's level-0 table
lock would be taken after the outer bracket's levels 1..9.  `lockAcquireSequence`
sorts one list, so one footprint is one ladder.

Four arms, and the `none` arm is what keeps the pre-bracket seam reachable:

* **neither domain declares** — `none`, and the bracket falls back to the
  unbracketed step, exactly as it did before this row;
* **only the object domain** — the lifted object footprint;
* **only the scheduler domain** — that footprint unchanged;
* **both** — the scheduler footprint with the object domain's residue appended.

Acquiring a footprint is not claiming coverage: an arm declared in one domain and
not the other acquires what that domain declared, and the *other* domain's writes
stay outside a footprint until that domain declares one for it.  That is the same
posture `runUnderDeclaredLockSet` has taken since RR7.12 and is why landing this
ahead of the remaining object-domain declarations is safe. -/
def unifiedSchedLockSetForSyscall (sid : SyscallId) (ops : Concurrency.SyscallLockOperands)
    (executingCore : CoreId) (st : SystemState) : Option SchedLockSet :=
  match Concurrency.lockSetForSyscall sid ops st,
        schedLockSetForSyscall sid ops executingCore st with
  | none, none => none
  | some O, none => SchedLockSet.ofList? (liftObjectFootprint O)
  | none, some S => some S
  | some O, some S => SchedLockSet.ofList? (S.pairs ++ unifiedObjectResidue O S)

/-- **Cut C6h**: an arm neither domain declares yields no unified footprint.

The statement a bracket reads as "no exclusion established", and the one that
makes the fallback arm reachable rather than notional. -/
@[simp] theorem unifiedSchedLockSetForSyscall_undeclared (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (hObj : Concurrency.lockSetForSyscall sid ops st = none)
    (hSched : schedLockSetForSyscall sid ops executingCore st = none) :
    unifiedSchedLockSetForSyscall sid ops executingCore st = none := by
  unfold unifiedSchedLockSetForSyscall
  rw [hObj, hSched]

/-- **Cut C6h**: where only the scheduler domain declares, the unified footprint
IS the scheduler footprint — no widening, no reordering, definitionally. -/
@[simp] theorem unifiedSchedLockSetForSyscall_sched_only (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S : SchedLockSet)
    (hObj : Concurrency.lockSetForSyscall sid ops st = none)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S) :
    unifiedSchedLockSetForSyscall sid ops executingCore st = some S := by
  unfold unifiedSchedLockSetForSyscall
  rw [hObj, hSched]

/-- **Cut C6h**: every member the SCHEDULER domain declared is in the unified
footprint.

The direction the coverage family needs: `schedFootprintCoversWrites` is stated
of the scheduler footprint, and it is the unified one the bracket acquires, so a
claim about the first has to reach the second.  Membership is enough — the
predicate's three clauses are all of the form "a lock the footprint does **not**
name", so a superset of the declared members only ever makes them easier. -/
theorem mem_unifiedSchedLockSetForSyscall_of_sched (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S U : SchedLockSet) (p : SchedLockId × Concurrency.AccessMode)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S)
    (hU : unifiedSchedLockSetForSyscall sid ops executingCore st = some U)
    (hp : p ∈ S.pairs) : p ∈ U.pairs := by
  unfold unifiedSchedLockSetForSyscall at hU
  cases hObj : Concurrency.lockSetForSyscall sid ops st with
  | none =>
      rw [hObj, hSched] at hU
      exact (Option.some.inj hU) ▸ hp
  | some O =>
      rw [hObj, hSched] at hU
      rw [SchedLockSet.ofList?_pairs hU]
      exact List.mem_append_left _ hp

/-- **Cut C6h**: and every member the OBJECT domain declared is in it, at its own
mode or subsumed by the table lock's write.

The residue's filter is what makes the disjunction necessary: a member the
scheduler footprint already names at `.write` is dropped, and the only member it
can name is the canonical table lock. -/
theorem mem_unifiedSchedLockSetForSyscall_of_object (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (O : Concurrency.LockSet) (U : SchedLockSet) (l : Concurrency.LockId)
    (m : Concurrency.AccessMode)
    (hObj : Concurrency.lockSetForSyscall sid ops st = some O)
    (hU : unifiedSchedLockSetForSyscall sid ops executingCore st = some U)
    (hp : (l, m) ∈ O.pairs) :
    (canonicalSchedLockOfObject l, m) ∈ U.pairs ∨
      (canonicalSchedLockOfObject l, Concurrency.AccessMode.write) ∈ U.pairs := by
  unfold unifiedSchedLockSetForSyscall at hU
  cases hSched : schedLockSetForSyscall sid ops executingCore st with
  | none =>
      rw [hObj, hSched] at hU
      exact Or.inl ((SchedLockSet.ofList?_pairs hU) ▸ mem_liftObjectFootprint O l m hp)
  | some S =>
      rw [hObj, hSched] at hU
      rw [SchedLockSet.ofList?_pairs hU]
      by_cases hDrop : S.pairs.contains (canonicalSchedLockOfObject l,
          Concurrency.AccessMode.write)
      · exact Or.inr (List.mem_append_left _ (List.mem_of_elem_eq_true hDrop))
      · refine Or.inl (List.mem_append_right _ ?_)
        unfold unifiedObjectResidue
        refine List.mem_filter.mpr ⟨mem_liftObjectFootprint O l m hp, ?_⟩
        simp only [Bool.not_eq_true, Bool.not_eq_true'] at hDrop ⊢
        exact hDrop

/-- **WS-RR RR8.12 Cut C6h: the arm's coverage claim reaches what the seam
ACQUIRES.**

The bridge the deletion of `UncoveredLockDomain.syscallSeamSchedulerDomain`
rests on.  Every per-arm coverage theorem in `SyscallSchedContainment` is stated
over `schedLockSetForSyscall`'s answer; what the bracket acquires is
`unifiedSchedLockSetForSyscall`'s, which is that footprint with the object
domain's residue appended.  `mem_unifiedSchedLockSetForSyscall_of_sched` says the
first is a sub-multiset of the second, and coverage is monotone upward
(`schedFootprintCoversWrites_mono`), so the claim travels without being restated
— which is what keeps "what does this arm's footprint cover" a single question.

Stated once and generically rather than sixteen times at the arms: an instance
per arm would be sixteen copies of one application, and the next declared arm
would owe a seventeenth. -/
theorem unifiedSchedLockSetForSyscall_coversWrites (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S U : SchedLockSet) (st₀ st₁ : SystemState)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S)
    (hU : unifiedSchedLockSetForSyscall sid ops executingCore st = some U)
    (hCover : schedFootprintCoversWrites S st₀ st₁) :
    schedFootprintCoversWrites U st₀ st₁ :=
  schedFootprintCoversWrites_mono S U st₀ st₁
    (fun p hp => mem_unifiedSchedLockSetForSyscall_of_sched sid ops executingCore st S U p
      hSched hU hp)
    hCover

/-- **WS-RR RR8.12 Cut C6h: the unified footprint the live ABI seam declares.**

`declaredLockSetForAbiEntry`'s and `declaredSchedLockSetForAbiEntry`'s successor
at the seam, and their union by construction: it runs `abiEntryPlan` and
`abiEntryLockOperands` once — the same decode both single-domain resolvers read,
which `declaredSchedLockSetForAbiEntry_shares_decode` states — and hands the one
answer to `unifiedSchedLockSetForSyscall`.

The two single-domain resolvers are **kept**, not retired: each is what its own
domain's theorems are stated over, and the relation below is what ties them to
what the seam acquires. -/
def declaredUnifiedLockSetForAbiEntry (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option SchedLockSet :=
  match abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st with
  | none => none
  | some (tid, decoded, stFilled) =>
    (abiEntryLockOperands decoded tid stFilled).bind
      (fun ops => unifiedSchedLockSetForSyscall decoded.syscallId ops executingCore stFilled)

/-- **Cut C6h**: an entry whose plan does not resolve declares nothing — the
fail-closed direction both single-domain resolvers already take. -/
@[simp] theorem declaredUnifiedLockSetForAbiEntry_of_no_plan (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (h : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st = none) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredUnifiedLockSetForAbiEntry
  rw [h]

/-- **Cut C6h**: an entry undeclared in BOTH domains declares nothing.

The seam-level fallback condition, and the one that has to name both domains:
an arm the object domain declares nothing for is still bracketed when the
scheduler domain declares, and the converse. -/
theorem declaredUnifiedLockSetForAbiEntry_undeclared (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (hObj : declaredLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = none)
    (hSched : declaredSchedLockSetForAbiEntry ctx executingCore syscallId msgInfo
      x0 x1 x2 x3 x4 x5 st = none) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredUnifiedLockSetForAbiEntry
  unfold declaredLockSetForAbiEntry at hObj
  unfold declaredSchedLockSetForAbiEntry at hSched
  rcases hPlan : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st with
    _ | ⟨tid, decoded, stFilled⟩
  · rfl
  · rw [hPlan] at hObj hSched
    simp only at hObj hSched ⊢
    rcases hOps : abiEntryLockOperands decoded tid stFilled with _ | ops
    · rfl
    · rw [hOps] at hObj hSched
      simp only [Option.bind_some] at hObj hSched ⊢
      exact unifiedSchedLockSetForSyscall_undeclared decoded.syscallId ops executingCore
        stFilled hObj hSched

/-- **Cut C6h**: the seam's unified footprint is the union of what the two
single-domain resolvers declare, at the decode all three share.

The relation that lets a claim stated over either single-domain footprint reach
the set the bracket acquires — stated rather than left to be read off three
definitions, which is the shape that lets one domain's footprint be acquired
around the other domain's transition. -/
theorem declaredUnifiedLockSetForAbiEntry_shares_decode (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState) (ops : Concurrency.SyscallLockOperands)
    (hPlan : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (hOps : abiEntryLockOperands decoded tid stFilled = some ops) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
      = unifiedSchedLockSetForSyscall decoded.syscallId ops executingCore stFilled := by
  unfold declaredUnifiedLockSetForAbiEntry
  rw [hPlan]
  simp only
  rw [hOps]
  rfl

end SeLe4n.Kernel
