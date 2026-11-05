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

/-- WS-ZA ZA6.33: **the cores whose replenish queue the resume writes** — the
context's resume (`Lifecycle.Suspend.resumeContextCores`): the queue its own
release link names, which the purge edits, and the home core it is placed on.
Read at the entry state; the ready mark writes no binding and no context, so the
mid state the transition reads names the same cores
(`resumeThreadOnCoreReplenishCores_mid`). -/
def resumeThreadOnCoreReplenishCores (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    List CoreId :=
  Lifecycle.Suspend.resumeContextCores st vtid.val (determineTargetCore st vtid.val)

/-- The mid state the resume's context step reads names the entry state's cores. -/
theorem resumeThreadOnCoreReplenishCores_mid (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (hInv : st.objects.invExt) :
    Lifecycle.Suspend.resumeContextCores
        (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
        vtid.val (determineTargetCore st vtid.val) =
      resumeThreadOnCoreReplenishCores st vtid := by
  unfold resumeThreadOnCoreReplenishCores
  refine Lifecycle.Suspend.resumeContextCores_congr _ ?_ ?_
  · rw [markKeyChangeFrom_getTcb?]
    exact Lifecycle.Suspend.resumeReadyMidState_binding st vtid.val hInv vtid.val
  · intro s
    unfold SystemState.getSchedContext?
    rw [markKeyChangeFrom_objects]
    exact Lifecycle.Suspend.resumeReadyMidState_getSchedContext? st vtid.val hInv s

/-- `v0.35.167` (WS-ZA ZA6.33): the resume writes **no** replenish queue off
`resumeThreadOnCoreReplenishCores`.

Its legs are the ready-restore (one TCB, no scheduler state), the context's
resume (seL4's `refill_unblock_check` and `postpone`: the purge on the core its
link names and the placement on the home core), the home-core enqueue, and —
only when the home core is the executing one — the inline reschedule handler,
which moves no scheduling context.  The exactness half of the replenish segment
below. -/
theorem resumeThreadOnCore_replenishQueueOnCore (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId) (hInv : st.objects.invExt)
    (hc : c ∉ resumeThreadOnCoreReplenishCores st vtid)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  have hX : (Lifecycle.Suspend.resumeContext
      (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val) vtid.val
      (determineTargetCore st vtid.val)).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
    rw [Lifecycle.Suspend.resumeContext_replenishQueueOnCore _ _ _ _
      (by rw [markKeyChangeFrom_objects]
          exact PriorityInheritance.resumeReadyMidState_objects_invExt st vtid.val hInv)
      (by rw [resumeThreadOnCoreReplenishCores_mid st vtid hInv]; exact hc),
      markKeyChangeFrom_replenishQueueOnCore, PriorityInheritance.resumeReadyMidState_scheduler_eq]
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · split at h
        · split at h
          · rename_i stR hR
            rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1, handleRescheduleSgiOnCore_replenishQueueOnCore _ executingCore stR c hR,
              enqueueRunnableOnCore_replenishQueueOnCore, hX]
          · exact absurd h (by simp)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1, enqueueRunnableOnCore_replenishQueueOnCore, hX]
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, hX]
  · exact absurd h (by simp)

/-- **`v0.35.167`: the live `.tcbResume` arm's scheduler-domain footprint.**

`schedFootprintOfCores` of the arm's own SM8.B write set, with the context's
resume as its replenish segment (`resumeThreadOnCoreReplenishCores`, WS-ZA
ZA6.33), which `resumeThreadOnCore_replenishQueueOnCore` is the exactness
statement of.

The fault retire the arm runs first (`retirePendingFaultForResume`, WS-RR RR4.11)
needs no member of its own: it writes one TCB's `pendingFault` and no scheduler
state at all (`retirePendingFaultForResume_scheduler_eq`). -/
def schedLockSet_resumeThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (resumeThreadOnCoreWriteSet st vtid executingCore)
    (resumeThreadOnCoreReplenishCores st vtid)

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
      simp only []
      split
      · unfold discardPendingFault determineTargetCore
        rw [SystemState.updateTcb_getTcb?_self st t _ hInv, hT, Option.map_some]
      · unfold applyFaultRestart determineTargetCore
        rw [SystemState.updateTcb_getTcb?_self st t _ hInv, hT, Option.map_some]
        rfl

/-- WS-ZA ZA6.33: the fault retire rewrites one TCB's fault and frame, so it
keeps the thread's binding... -/
theorem retirePendingFaultForResume_binding (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    ((retirePendingFaultForResume st t).getTcb? t).map TCB.schedContextBinding =
      (st.getTcb? t).map TCB.schedContextBinding := by
  unfold retirePendingFaultForResume
  split
  · split
    · split
      · exact Lifecycle.Suspend.getTcb?_binding_updateTcb _ _ _ hInv (by intro _; rfl) t
      · exact Lifecycle.Suspend.getTcb?_binding_updateTcb _ _ _ hInv (by intro _; rfl) t
    · rfl
  · rfl

/-- ...and every context. -/
theorem retirePendingFaultForResume_getSchedContext? (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (s : SeLe4n.SchedContextId) :
    (retirePendingFaultForResume st t).getSchedContext? s = st.getSchedContext? s := by
  unfold retirePendingFaultForResume
  split
  · split
    · split
      · exact SystemState.updateTcb_getSchedContext? _ _ _ hInv s
      · exact SystemState.updateTcb_getSchedContext? _ _ _ hInv s
    · rfl
  · rfl

/-- **WS-LS LS2.3**: so the resume footprint resolved at the entry state is the
one the arm's transition runs under after the retire. -/
theorem schedLockSet_resumeThreadOnCore_retire (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (hInv : st.objects.invExt) :
    schedLockSet_resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore
      = schedLockSet_resumeThreadOnCore st vtid executingCore := by
  unfold schedLockSet_resumeThreadOnCore resumeThreadOnCoreWriteSet resumeThreadOnCoreReplenishCores
  rw [retirePendingFaultForResume_determineTargetCore st vtid.val hInv,
    Lifecycle.Suspend.resumeContextCores_congr _ (retirePendingFaultForResume_binding st vtid.val hInv)
      (retirePendingFaultForResume_getSchedContext? st vtid.val hInv)]

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

/-- WS-ZA ZA6.33: and a replenish-queue lock on exactly the cores the
context's resume writes — the declaration's exact half, against
`resumeThreadOnCore_replenishQueueOnCore`'s. -/
theorem schedLockSet_resumeThreadOnCore_replenishQueue_iff (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_resumeThreadOnCore st vtid executingCore ↔
      c ∈ resumeThreadOnCoreReplenishCores st vtid :=
  mem_schedFootprintOfCores_replenishQueue_iff _ _ _

end SeLe4n.Kernel
