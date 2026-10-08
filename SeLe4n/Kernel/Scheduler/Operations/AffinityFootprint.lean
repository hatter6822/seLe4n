-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.Scheduler.SchedFootprint

/-!
# The `.tcbSetAffinity` arm's scheduler footprint

`setThreadCpuAffinityWriteSet`, `setThreadCpuAffinityReplenishCores` and
`schedLockSet_setThreadCpuAffinityOnCore`, beside the transition they are about
(`setThreadCpuAffinityWithMigration`, `Scheduler/Operations/Core.lean`), with
the exactness frames, the per-member coverage theorems and the relation to the
parametric SM5.H.4 form (`schedLockSet_setThreadCpuAffinityOnCore_covers_parametric`).
Moved here from `SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

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
is what a coverage proof consumes: `footprintCoversWrites`'s replenish clause
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
    (affinity : Option CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (setThreadCpuAffinityWriteSet st tid affinity)
    (setThreadCpuAffinityReplenishCores st tid affinity)

/-- `v0.35.167`: the footprint holds the old home core's run-queue write lock. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_old_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [setThreadCpuAffinityWriteSet])

/-- `v0.35.167`: ...and the new one's. -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_new_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) :
    (LockKey.runQueue (affinity.getD Concurrency.bootCoreId), Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [setThreadCpuAffinityWriteSet])

/-- **`v0.35.167`: and both replenish-queue write locks when — and only when —
the thread runs on a reservation.** -/
theorem schedLockSet_setThreadCpuAffinityOnCore_contains_replenishQueue_writes
    (st : SystemState) (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (scId : SeLe4n.SchedContextId)
    (h : (st.getTcb? tid).bind (fun tcb => tcb.schedContextBinding.scId?) = some scId) :
    (LockKey.replenishQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity ∧
    (LockKey.replenishQueue (affinity.getD Concurrency.bootCoreId),
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
    (LockKey.replenishQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_setThreadCpuAffinityOnCore st tid affinity ∧
    (LockKey.replenishQueue (determineTargetCore stSet tid), Concurrency.AccessMode.write)
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
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
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
    (p : LockKey × Concurrency.AccessMode)
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

end SeLe4n.Kernel
