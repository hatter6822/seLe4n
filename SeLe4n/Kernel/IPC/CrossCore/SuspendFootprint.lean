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
import SeLe4n.Kernel.Lifecycle.Operations.RetypeFootprint

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
-- This arm is the one the previous cuts deferred, and its shape is why: the run
-- segment re-runs a seven-stage pipeline to the state each of its two walks
-- starts from, and the replenish segment is **two migrations read at
-- intermediate states** — the reclaim's, at the teardown's post-state, and G3's
-- donation arm's, at the post-revert state whose binding the reclaim may have
-- rewritten.  Neither is a proxy for a pre-state reading, so both are resolved
-- the way `endpointReplyRecvWriteSet` resolves its own: by re-running the spine.

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
`endpointReplyRecvWriteSet` does — and the one core that *is* read from the pre-state
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

`suspendThreadOnCoreLockSet home executingCore ownerHome outerHome placed
holderPlaced` takes five cores and an optional sixth from its caller; this reads
every one of them off the state the transition reads it from.  *A parameter is a
place for a caller to be wrong* (PR #895 round 10), and six of them is the
largest such surface in the tree. -/
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

/-- **`v0.35.170`: and both replenish-queue write locks the reclaim's migration
needs** — the endpoints it actually moves the reservation between. -/
theorem schedLockSet_suspendThreadOnCore_contains_reclaim_replenishQueue_writes
    (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hActive : tcb.threadState ≠ .Inactive)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st vtid.val tcb = some (scId, holder)) :
    (LockKey.replenishQueue (determineTargetCore st holder),
      Concurrency.AccessMode.write) ∈ schedLockSet_suspendThreadOnCore st vtid executingCore ∧
    (LockKey.replenishQueue
        (replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st vtid.val tcb) scId
          (determineTargetCore st holder)),
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
    (hp : (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreLockSet home executingCore ownerHome outerHome
          (placedCoreOf? st vtid.val)
          (cancelUnboundHolderCore? st (cancelIpcBlockingMigrated vtid.val tcb st)
            vtid.val tcb)
          reclaimReplenish) :
    (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_suspendThreadOnCore st vtid executingCore := by
  rw [suspendThreadOnCoreLockSet, mem_schedFootprintOfCores_runQueue_iff] at hp
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
`cancelIpcBlockingOnCoreLockSet_covers_migration` is the *names what is
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


end SeLe4n.Kernel
