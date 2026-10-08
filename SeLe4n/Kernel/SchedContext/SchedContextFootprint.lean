-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Lifecycle.ResumeFootprint
import SeLe4n.Kernel.SchedContext.PriorityControlFootprint

/-!
# The SchedContext arms' scheduler footprints

The `.schedContextConfigure`, `.schedContextBind` and `.schedContextUnbind`
arms' write sets, replenish-core resolvers and resolved footprints, beside the
transitions they are about (`SchedContext/Operations.lean`,
`SchedContext/OperationsPerCore.lean`), with the exactness halves — what each
arm writes — and the per-member coverage theorems.  Moved here from
`SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged.

The exactness frames are theorems, not readings of the body:
`observableSlotsConfinedToCores` covers six per-core slots and the replenish
queue is not one of them, so a write set says nothing about replenishments and
a footprint that declared one it does not write would be wider than its
operation — lock contention the operation does not have, and an observable
channel (SM8.D's CC-5).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

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

/-- **The cores a `.schedContextConfigure` may write** — the bound thread's home
core, where the propagated priority re-buckets it (`schedContextWriteSet`), and,
when that thread is reply-blocked on a server, the home cores of the inheritance
chain the propagated priority re-walks (`waiterChainWriteSet`).

The chain segment is read from the **pre-state**, though the walk runs after the
SchedContext store and the propagation: neither moves a home core or a blocking
edge (`schedContextConfigureBoundPropagate_tcbChainFields`). -/
def schedContextConfigureWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  schedContextWriteSet st scObjId ++
    match SchedContextOps.schedContextBoundThread? st scObjId with
    | some tid => waiterChainWriteSet st tid (determineTargetCore st tid) st.objectIndex.length
    | none => []

/-- **`v0.35.168`: the live `.schedContextConfigure` arm's scheduler-domain
footprint.** -/
def schedLockSet_schedContextConfigureOnCore (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextConfigureWriteSet st scObjId)
    (schedContextConfigureReplenishCores st scObjId)

/-- `v0.35.168`: the footprint holds the bound thread's home core's run-queue
write lock — the bucket propagation's own. -/
theorem schedLockSet_schedContextConfigureOnCore_contains_home_runQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextConfigureOnCore st scObjId :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold schedContextConfigureWriteSet schedContextWriteSet; rw [h]; simp)

/-- `v0.35.168`: ...and the SC's home core's replenish-queue write lock, which is
the purge's. -/
theorem schedLockSet_schedContextConfigureOnCore_contains_replenishQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (sc : SchedContext)
    (h : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc) :
    (LockKey.replenishQueue (SchedContextOps.schedContextReplenishHome st sc),
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
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
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
    List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextBindWriteSet st tid) []

/-- `v0.35.168`: the footprint holds the bound thread's home core's run-queue
write lock. -/
theorem schedLockSet_schedContextBindOnCore_contains_home_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextBindOnCore st tid :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [schedContextBindWriteSet])

/-- `v0.35.168`: and **no** replenish-queue lock, on any core — the declaration's
exact half, against `schedContextBind_replenishQueueOnCore`'s. -/
theorem schedLockSet_schedContextBindOnCore_no_replenishQueue (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
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
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextUnbindOnCoreWriteSet st scObjId executingCore)
    (schedContextUnbindReplenishCores st scObjId)

/-- `v0.35.168`: the footprint holds the demoted thread's home core's run-queue
write lock — the re-bucket's own. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_home_runQueue_write (st : SystemState)
    (scObjId : SeLe4n.ObjId) (executingCore : CoreId) (tid : SeLe4n.ThreadId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
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
    (LockKey.runQueue runCore, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by simp [schedContextUnbindOnCoreWriteSet, schedContextUnbindWriteSet, h, hRun])

/-- `v0.35.168`: ...and the executing core's, which the scheduling point writes. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_executing_runQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId) :
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write)
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
    (LockKey.replenishQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
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
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by simp only [schedContextUnbindReplenishCores, h, hTcb]
        exact Concurrency.mem_allCores c)

/-- `v0.35.168`: and no replenish lock where the SC has no bound thread — the
arm refuses `.illegalState` there and writes nothing. -/
theorem schedLockSet_schedContextUnbindOnCore_no_replenishQueue_of_unbound
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId) (c : CoreId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = none) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
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
                rw [← h.2, markKeyChangeFor_replenishQueueOnCore]
                -- Three arms since Cut B2 (`v0.35.182`): the re-bucket, the
                -- placement of a parked runnable thread, and the identity.  All
                -- three write a run queue (and the placement a reschedule-pending
                -- flag) or nothing, so none moves a replenish queue — which is
                -- what keeps this arm's segment EMPTY.
                split
                · simp only [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
                    SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                · split
                  · simp only [SchedulerState.markReschedulePendingOnCore_replenishQueueOnCore,
                      SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
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
            rw [← h.2, PriorityInheritance.repropagateFromWaiter_replenishQueueOnCore,
              markKeyChangeFor_replenishQueueOnCore,
              schedContextConfigureBoundPropagate_replenishQueueOnCore, hSched]
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
    rw [← h.2, markKeyChangeFor_replenishQueueOnCore]
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

end SeLe4n.Kernel
