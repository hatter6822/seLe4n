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
(`purgeReplenishment st scIdTyped`), on the core the context's own release link
names (WS-ZA ZA6.3).  So the segment is that core whenever the capability's
target resolves to a SchedContext linked on a queue, and empty otherwise — an
unresolved target is refused with `.objectNotFound` and writes nothing, and an
unlinked context's purge writes no queue.

It is read from the link, not from the bound thread's home: a stale entry left
on another core by an earlier binding is exactly what the purge exists to drop,
so a footprint keyed on the home core would be false there.

**WS-ZA ZA6.4**: and the bound thread's home core, where the configure places
the context's fresh refill (seL4-MCS's `postpone` of a context whose refill is
not yet released), so the segment is the purge's core and the placement's. -/
def schedContextConfigureReplenishCores (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc => SchedContextOps.purgeReplenishCores st (SeLe4n.SchedContextId.ofObjId scObjId) ++
      match sc.boundThread with
      | some t => [determineTargetCore st t]
      | none => []
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
footprint**.  WS-ZA ZA6.4: its replenish segment is the bound thread's home core,
where the bind places a context whose head refill is not yet released
(seL4-MCS's `postpone`); before ZA6.4 it was empty.

seL4-MCS's `schedContext_bindTCB` ends in `SCHED_ENQUEUE`, and since WS-RR
RR8.12 Cut B2 (`v0.35.182`) so does this kernel's bind: a parked runnable thread
is placed on its home core rather than left off every queue with a reservation
it cannot spend.  This docstring said that closing the divergence "widens the run
segment"; it did not, because the segment is the **home core** either way — the
placement inserts on exactly the core the re-bucket already wrote. -/
def schedLockSet_schedContextBindOnCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedContextBindWriteSet st tid) (schedContextBindWriteSet st tid)

/-- `v0.35.168`: the footprint holds the bound thread's home core's run-queue
write lock. -/
theorem schedLockSet_schedContextBindOnCore_contains_home_runQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextBindOnCore st tid :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr (by simp [schedContextBindWriteSet])

/-- WS-ZA ZA6.4: and the home core's replenish-queue write lock — the release
placement's, against `schedContextBind_replenishQueueOnCore_ne`'s exact half. -/
theorem schedLockSet_schedContextBindOnCore_contains_home_replenishQueue_write (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (LockKey.replenishQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextBindOnCore st tid :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr (by simp [schedContextBindWriteSet])

-- ============================================================================
-- §6  The `.schedContextUnbind` arm
-- ============================================================================

/-- **The cores a `.schedContextUnbind` may write** — the subject's home core
*and* the core actually running it.

Deliberately **not** `schedContextWriteSet`.  The two differ, and the difference
is the defect this set exists to make visible: the run-queue re-bucket lands on
the subject's **home** core, while the preemption guard clears `current` on the
core actually **running** it.  Those coincide on every committed state under
the placement invariant (`currentHome`, WS-ZA ZA6.3); the set names both
because the operation reads both.

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

/-- **`v0.35.168`: the core a `.schedContextUnbind` moves a RESERVATION on.**

The unbind purges the SC's eligibility entry on both of its arms — the bound TCB
resolving or already gone from the store — and since WS-ZA ZA6.3 the purge reads
the core from the context's own release link, so neither arm needs a home core
and the segment is that one core (or none, for a context on no queue).  It was
every core on the gone-TCB arm while the purge had no core to read and swept
them all.  Read on the pre-state: the stages before the purge move no release
link (`schedContextUnbind_replenishQueueOnCore_ne_of_tcb`). -/
def schedContextUnbindReplenishCores (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match SchedContextOps.schedContextBoundThread? st scObjId with
  | some _ => SchedContextOps.purgeReplenishCores st (SeLe4n.SchedContextId.ofObjId scObjId)
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

/-- `v0.35.168`: the footprint holds the replenish-queue write lock of the core
the SC's release link names, which is the purge's, on either arm. -/
theorem schedLockSet_schedContextUnbindOnCore_contains_replenishQueue_write
    (st : SystemState) (scObjId : SeLe4n.ObjId) (executingCore : CoreId)
    (tid : SeLe4n.ThreadId) (d : CoreId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid)
    (hC : st.releaseCoreOf (SeLe4n.SchedContextId.ofObjId scObjId) = some d) :
    (LockKey.replenishQueue d, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedContextUnbindOnCore st scObjId executingCore :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by simp [schedContextUnbindReplenishCores, SchedContextOps.purgeReplenishCores, h, hC])

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

/-- **A `.schedContextBind` writes one replenish queue: its thread's home core's.**

Its steps are the SchedContext rewrite, the TCB rewrite, an optional run-queue
re-bucket, the reschedule-flag update and (WS-ZA ZA6.4) the release placement on
the thread's home core; only the last moves a replenishment, and on that core
alone.  The exactness half of `schedLockSet_schedContextBindOnCore`'s replenish
segment. -/
theorem schedContextBind_replenishQueueOnCore_ne (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (vThreadId : SeLe4n.ValidThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt) (hne : c ≠ determineTargetCore st vThreadId.val)
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
                rw [← h.2, SystemState.releasePlace_replenishQueueOnCore_ne _ _ _ c (by
                    rw [determineTargetCore_congr st _ vThreadId.val (by
                      rw [SystemState.updateTcb_getTcb?_self _ _ _
                          (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hObjInv),
                        SystemState.rewriteObject_schedContext_getTcb? st _ _ _ hObjInv, hTcb]
                      rfl)]
                    exact hne),
                  markKeyChangeFor_replenishQueueOnCore]
                -- Three arms since Cut B2 (`v0.35.182`): the re-bucket, the
                -- placement of a parked runnable thread, and the identity.  All
                -- three write a run queue (and the placement a reschedule-pending
                -- flag) or nothing, so none moves a replenish queue.
                split
                · simp only [SystemState.runRequeueOnCore_scheduler,
                    SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
                    SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore,
                    SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                · split
                  · simp only [SystemState.markReschedulePendingOnCore,
                      SchedulerState.markReschedulePendingOnCore_replenishQueueOnCore,
                      SystemState.runEnqueueOnCore_scheduler]
                    split <;> simp only [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
                      SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore,
                      SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                  · simp only [SystemState.updateTcb_scheduler,
                      SystemState.rewriteObject_scheduler]
              · exact absurd h (by simp)
        · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`v0.35.168`: the configure's bound-thread propagation writes no replenish
queue.**

Its two halves are a priority rewrite with an optional run-queue re-bucket and a
domain rewrite; a `rewriteObject` frames the scheduler outright and the re-bucket
(`runRequeueOnCore`) writes run-queue state only.  What the arm *does* write is
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
      SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
      SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore]

/-- **`v0.35.168`: a `.schedContextConfigure` writes exactly one replenish
queue** — the one the SC's own release link names, where its purge lands.

The exactness half of `schedLockSet_schedControlConfigure`'s one-core
segment: every other core's queue is untouched, so the footprint is neither
false nor wider than the operation. -/
theorem schedContextConfigure_replenishQueueOnCore_ne_of_sc (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (budget period priority deadline domain : Nat)
    (sc : SchedContext) (c : CoreId)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc)
    (hne : st.releaseCoreOf (SeLe4n.SchedContextId.ofObjId vScId.val) ≠ some c)
    (hHome : ∀ t, sc.boundThread = some t → c ≠ determineTargetCore st t)
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
          exact SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _ hne
        · split at h
          · rename_i boundTcb hBound _
            rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, SchedContextOps.configureResumeBound_replenishQueueOnCore,
              PriorityInheritance.repropagateFromWaiter_replenishQueueOnCore,
              markKeyChangeFor_replenishQueueOnCore, markCandidacyGainFor_replenishQueueOnCore,
              schedContextConfigureBoundPropagate_replenishQueueOnCore,
              SystemState.releasePlace_replenishQueueOnCore_ne _ _ _ c (hHome _ (by assumption)), hSched]
            exact SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _ hne
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, SystemState.releasePlace_replenishQueueOnCore_ne _ _ _ c (hHome _ (by assumption)),
              hSched]
            exact SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _ hne
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
        priority deadline domain sc c hSc (fun e => hne (by
          unfold SchedContextOps.purgeReplenishCores; rw [e]
          exact List.mem_append_left _ (List.mem_singleton_self c)))
        (fun t ht e => hne (by dsimp only; rw [ht, e]; exact List.mem_append_right _ (List.mem_singleton_self _))) h

/-- **`v0.35.168`: a `.schedContextUnbind` writes exactly one replenish queue**
— the one the SC's own release link names, where its purge lands, on both arms.

The exactness half of `schedLockSet_schedContextUnbindOnCore`'s segment.  The
stages before the purge (the current-slot clear, the two binding rewrites, the
run-queue stage) move no context's release link, so the purge reads the
pre-state's link (WS-ZA ZA6.3). -/
theorem schedContextUnbind_replenishQueueOnCore_ne_of_link (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (c : CoreId) (hObjInv : st.objects.invExt)
    (hne : st.releaseCoreOf (SeLe4n.SchedContextId.ofObjId vScId.val) ≠ some c)
    (h : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold SchedContextOps.schedContextUnbind at h
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => rw [SystemState.getSchedContextWitnessed?_eq_none hSc] at h; cases h
  | some sc =>
    rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at h
    dsimp only at h
    have hLink : ∀ (S0 : SystemState) (hO : S0.objects = st.objects) (sc' : SchedContext)
        (hf : sc'.releaseCoreCode = sc.releaseCoreCode) (hA : S0.rewriteAdmissible vScId.val
          (.schedContext sc')),
        (S0.rewriteObject vScId.val (.schedContext sc') hA).releaseCoreOf
          ⟨vScId.val.toNat⟩ ≠ some c := fun S0 hO sc' hf hA => by
      rw [SystemState.releaseCoreOf_rewrite_of_objects S0 st hO vScId.val ⟨vScId.val.toNat⟩ rfl
        sc sc' hSc hObjInv hf hA]
      exact hne
    have hLink2 : ∀ (S0 : SystemState) (hO : S0.objects = st.objects) (sc' : SchedContext)
        (hf : sc'.releaseCoreCode = sc.releaseCoreCode) (hA : S0.rewriteAdmissible vScId.val
          (.schedContext sc')) (t : SeLe4n.ThreadId) (f : TCB → TCB),
        ((S0.rewriteObject vScId.val (.schedContext sc') hA).updateTcb t f).releaseCoreOf
          ⟨vScId.val.toNat⟩ ≠ some c := fun S0 hO sc' hf hA t f => by
      rw [SystemState.releaseCoreOf_updateTcb _ _ _
        (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ (hO ▸ hObjInv))]
      exact hLink S0 hO sc' hf hA
    cases hBound : sc.boundThread with
    | none => simp only [hBound] at h; cases h
    | some tid =>
      simp only [hBound] at h
      cases hTcb : st.getTcb? tid with
      | some tcb =>
        simp only [hTcb] at h
        split at h
        · exact absurd h (by simp)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, markKeyChangeFor_replenishQueueOnCore, markCandidacyGainFor_replenishQueueOnCore,
            SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _ (by
              rw [SystemState.releaseCoreOf_of_runLinks
                  (SchedContextOps.schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _),
]
              exact hLink2 _ (by rfl) _ (by rfl) _ _ _),
            SchedContextOps.schedContextUnbindQueueStage_replenishQueueOnCore,
            SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
          dsimp only
          repeat' split
          all_goals
            simp [SchedulerState.setCurrentOnCore_replenishQueueOnCore]
      | none =>
        simp only [hTcb] at h
        rw [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _
          (hLink _ rfl { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
            rfl _), SystemState.rewriteObject_scheduler]

/-- **`v0.35.168`: ...and the live per-core arm writes the same one**, the
scheduling point it composes moving no replenishment
(`priorityRescheduleOnCore_replenishQueueOnCore`). -/
theorem schedContextUnbindOnCore_replenishQueueOnCore_ne_of_link (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId) (hObjInv : st.objects.invExt)
    (hne : st.releaseCoreOf (SeLe4n.SchedContextId.ofObjId vScId.val) ≠ some c)
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
      exact schedContextUnbind_replenishQueueOnCore_ne_of_link st stU vScId c hObjInv hne
        (by cases u; exact hU)

/-- **WS-RR RR8.12 Cut C6b: the `.schedContextUnbind` arm's exactness frame.**

Keyed on the footprint's own replenish segment; `…_ne_of_link` above is the
link-keyed form it is built from.  A SchedContext that resolves to no bound
thread makes the transition *fail*, so the segment being empty there costs the
claim nothing. -/
theorem schedContextUnbindOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId) (hObjInv : st.objects.invExt)
    (hne : c ∉ schedContextUnbindReplenishCores st vScId.val)
    (h : SchedContextOps.schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi)) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold schedContextUnbindReplenishCores at hne
  cases hBT : SchedContextOps.schedContextBoundThread? st vScId.val with
  | some _ =>
      rw [hBT] at hne
      exact schedContextUnbindOnCore_replenishQueueOnCore_ne_of_link st st' vScId executingCore
        sgi c hObjInv (fun e => hne (by
          unfold SchedContextOps.purgeReplenishCores; rw [e]; exact List.mem_singleton_self c)) h
  | none =>
      exfalso
      unfold SchedContextOps.schedContextUnbindOnCore at h
      dsimp only at h
      cases hU : SchedContextOps.schedContextUnbind vScId st with
      | error e => rw [hU] at h; exact absurd h (by simp)
      | ok r =>
          unfold SchedContextOps.schedContextUnbind at hU
          unfold SchedContextOps.schedContextBoundThread? at hBT
          cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
          | none => rw [SystemState.getSchedContextWitnessed?_eq_none hSc] at hU; cases hU
          | some sc =>
              rw [hSc] at hBT
              rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at hU
              dsimp only at hU
              simp only [hBT] at hU
              cases hU

end SeLe4n.Kernel
