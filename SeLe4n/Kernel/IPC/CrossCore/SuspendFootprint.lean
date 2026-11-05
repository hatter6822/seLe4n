-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Lifecycle.Operations.CleanupFootprint

/-!
# The `.tcbSuspend` arm's scheduler footprint

`suspendThreadOnCoreWriteSet`, `suspendThreadReplenishCores` and
`schedLockSet_suspendThreadOnCore`, beside the transition they are about
(`suspendThreadOnCore`, `IPC/CrossCore/Cancellation.lean`), with the step
frames its segments rest on, the exactness halves — what the live
`.tcbSuspend` writes — and the per-member coverage theorems.  Moved here from
`SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §10  The `.tcbSuspend` arm — the step frames its segments rest on
-- ============================================================================
--
-- The run segment re-runs the pipeline to the state its chain walk starts from,
-- and the replenish segment is the release removal's purge core read at the state
-- that removal runs on (WS-ZA ZA6.33: seL4's suspend neither unbinds nor returns
-- a loan, so the only replenish queue it writes is the one `tcbReleaseRemove`
-- edits).  Both are resolved the way `endpointReplyRecvWriteSet` resolves its own:
-- by re-running the spine.

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

/-- `v0.35.169`: the reclaim's teardown writes exactly its settle's cores
(WS-ZA ZA6.33) — the purge core the returned context's link names at the torn
state and the destination it is placed on. -/
theorem cancelIpcBlockingMigrated_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId) (c : CoreId)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder))
    (hFrom : c ∉ SchedContextOps.purgeReplenishCores
      (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) scId)
    (hTo : replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) scId
      (determineTargetCore st holder) ≠ c) :
    (cancelIpcBlockingMigrated victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold cancelIpcBlockingMigrated
  rw [hDon]
  dsimp only
  rw [SchedContextOps.settleReturnedContext_replenishQueueOnCore_ne _ _ _ _ hFrom (Ne.symm hTo),
    Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl

/-- `v0.35.169`: ...and with nothing donated it writes none at all. -/
theorem cancelIpcBlockingMigrated_replenishQueueOnCore_of_no_donation (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    (cancelIpcBlockingMigrated victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingMigrated_of_no_donation _ _ _ hDon,
    Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl

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
`suspendThreadOnCore`'s own control flow (WS-ZA ZA6.33, seL4's `suspend`):

* the reverted priority-inheritance chain's home cores, walked from the
  captured `blockingServer` at the post-cancel state;
* the core the pre-state **places** the victim on (`descheduleAtPlacementCores`,
  WS-RR RR8.6 — queued or current), where it is dequeued;
* the **executing** core, where G7 may run a local preemption point.

The IPC cancel (`cancelIpcKeepingContexts`: objects and the key hook's flags),
`clearPendingState`, the `.Inactive` store, the release removal (a replenish
queue, which no observable slot is) and the yield-link cancel are per-core
silent and contribute nothing. -/
def suspendThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match st.getTcb? vtid.val with
  | none => []
  | some tcb =>
    if tcb.threadState == .Inactive then []
    else
      -- One entry per pipeline step that writes a core, in execution order.
      (match PriorityInheritance.blockingServer st vtid.val with
       | some serverId =>
           pipChainWriteSet (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb)
             serverId executingCore
             (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb).objectIndex.length
       | none => []) -- the chain reversion, on the post-cancel state
      ++ descheduleAtPlacementCores st vtid.val -- the placement dequeue
      ++ [executingCore] -- the G7 scheduling point

/-- **The cores the live `.tcbSuspend` moves a reservation on** (WS-ZA ZA6.33):
the release removal's purge core (`releaseRemoveThreadCores`), read at the state
that removal runs on — the spine re-run to G6, exactly as the transition runs
it.  seL4's `suspend` neither unbinds the victim's context nor returns a loan,
so this is the only replenish queue it writes. -/
def suspendThreadReplenishCores (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match st.getTcb? vtid.val with
  | none => []
  | some tcb =>
    if tcb.threadState == .Inactive then []
    else
      let stG2 := Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb
      let stG2b := match PriorityInheritance.blockingServer st vtid.val with
        | some serverId =>
            (PriorityInheritance.propagatePipChainCrossCore stG2 serverId executingCore).1
        | none => stG2
      let stG6 := (Lifecycle.Suspend.clearPendingStateValid
          (descheduleAt stG2b vtid.val (placedCoreOf? st vtid.val)) vtid).updateTcb vtid.val
        fun t => { t with threadState := .Inactive }
      Lifecycle.Suspend.releaseRemoveThreadCores stG6 vtid.val

/-- **`v0.35.170`: the live `.tcbSuspend` arm's scheduler-domain footprint**,
every core read off the state the transition reads it from. -/
def schedLockSet_suspendThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (suspendThreadOnCoreWriteSet st vtid executingCore)
    (suspendThreadReplenishCores st vtid executingCore)

/-- `v0.35.170`: an already-`.Inactive` victim is refused, so the footprint is
the object-store write lock and nothing else. -/
theorem schedLockSet_suspendThreadOnCore_of_inactive (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) :
    schedLockSet_suspendThreadOnCore st vtid executingCore
      = [(LockKey.objStore, Concurrency.AccessMode.write)] := by
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
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write)
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
    (LockKey.runQueue placed, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by unfold suspendThreadOnCoreWriteSet
        rw [hTcb]
        simp [beq_iff_eq, hActive, descheduleAtPlacementCores, hPlaced])

/-- WS-ZA ZA6.33: **and the replenish-queue write lock the release removal
needs** — the queue its purge edits. -/
theorem schedLockSet_suspendThreadOnCore_contains_release_replenishQueue_writes
    (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (d : CoreId)
    (hd : d ∈ suspendThreadReplenishCores st vtid executingCore) :
    (LockKey.replenishQueue d, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr hd

/-- **`v0.35.170`: the resolved footprint covers the parametric one's RUN-QUEUE
segment**, at the core the operation itself resolves (`placedCoreOf?` on the
pre-state).  WS-ZA ZA6.33: the suspend deschedules no holder, so the parametric
form's holder member is `none`.  Stated over the run-queue half alone, which is
the honest scope: the parametric replenish segment is free parameters, and a
coverage claim over it would hypothesise its own conclusion. -/
theorem schedLockSet_suspendThreadOnCore_covers_parametric_runQueue (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (home ownerHome outerHome : CoreId) (reclaimReplenish : List CoreId) (c : CoreId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive)
    (hp : (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreLockSet home executingCore ownerHome outerHome
          (placedCoreOf? st vtid.val) none reclaimReplenish) :
    (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore := by
  rw [suspendThreadOnCoreLockSet, mem_schedFootprintOfCores_runQueue_iff] at hp
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ c).mpr ?_
  unfold suspendThreadOnCoreWriteSet
  rw [hTcb]
  simp only [beq_iff_eq, hActive, if_false, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.append_nil]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Option.toList_none, List.append_nil] at hp
  rcases hp with rfl | rfl
  · cases hPl : placedCoreOf? st vtid.val with
    | none => simp [descheduleAtPlacementCores, hPl]
    | some p => simp [descheduleAtPlacementCores, hPl]
  · simp

-- ============================================================================
-- §12  The exactness halves — what the live `.tcbSuspend` writes
-- ============================================================================

/-- **`v0.35.170`: the reclaim-complete teardown writes exactly the cores its
own resolver names**, stated over `cancelIpcBlockingReplenishCores` so the
footprint and the frame read one answer. -/
theorem cancelIpcBlockingReclaimed_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hne : c ∉ cancelIpcBlockingReplenishCores st victim tcb) :
    (cancelIpcBlockingReclaimed victim tcb st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingReclaimed_replenishQueueOnCore]
  cases hDon : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb with
  | none => exact cancelIpcBlockingMigrated_replenishQueueOnCore_of_no_donation _ _ _ _ hDon
  | some p =>
      obtain ⟨scId, holder⟩ := p
      rw [cancelIpcBlockingReplenishCores_of_donation _ _ _ _ _ hDon] at hne
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
      exact cancelIpcBlockingMigrated_replenishQueueOnCore_ne _ _ _ _ _ _ hDon
        hne.1 (fun hc => hne.2 hc.symm)

/-- **`v0.35.170`: ...and so does the cancellation composite**, whose own
footprint declares the same cores: it is the reclaim-complete teardown followed
by the victim's placement deschedule, a run-queue step.  The *names what is
written* half is `cancelIpcBlockingOnCoreLockSet_covers_settle`. -/
theorem cancelIpcBlockingOnCore_replenishQueueOnCore_ne (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (c : CoreId)
    (hne : c ∉ cancelIpcBlockingReplenishCores st victim tcb) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cancelIpcBlockingOnCore_eq_reclaimed_deschedule, descheduleThread,
    descheduleAtPlacement, descheduleAt_replenishQueueOnCore]
  exact cancelIpcBlockingReclaimed_replenishQueueOnCore_ne st victim tcb c hne

/-- **`v0.35.170`: and the whole live `.tcbSuspend` writes exactly the cores
`suspendThreadReplenishCores` names** (WS-ZA ZA6.33).  One stage moves a
reservation — G6a's release removal, whose purge edits the queue the victim's
context's link names — and every other frames every replenish queue: G2's IPC
cancel writes objects and the key hook's flags
(`cutCancelledCallerHead_replenishQueueOnCore`, `cancelIpcBlocking_scheduler_eq`),
G2b's chain revert re-buckets run queues, G4's placement dequeue is a run-queue
removal, G5 and G6 write TCBs, G6b's yield-link cancel writes a thread and a
context, and G7's scheduling point at most dispatches a successor. -/
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
      have hG2 : (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb).scheduler.replenishQueueOnCore c
          = st.scheduler.replenishQueueOnCore c := by
        unfold Lifecycle.Suspend.cancelIpcKeepingContexts
        rw [← Lifecycle.Suspend.cutCancelledCallerHead_replenishQueueOnCore st tcb c,
          Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl
      rw [suspendRescheduleOnCore_replenishQueueOnCore _ st' _ _ _ _ _ c h,
        SystemState.cancelYieldTo_scheduler]
      refine (Lifecycle.Suspend.releaseRemoveThread_replenishQueueOnCore_ne _ _ c hne).trans ?_
      rw [SystemState.updateTcb_scheduler, Lifecycle.Suspend.clearPendingStateValid_eq,
        Lifecycle.Suspend.clearPendingState_scheduler_eq, descheduleAt_replenishQueueOnCore,
        hG2b, hG2]

end SeLe4n.Kernel
