-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.SchedContextArms

/-!
# Per-core slot confinement — the live priority-control arms

§5i: `.tcbSetPriority` and `.tcbSetMCPriority`, bounded by the target's
home core, the executing core and the priority-inheritance chain.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §5i The live priority-control arms
-- ============================================================================
--
-- PR #861 review round 12 rerouted `.tcbSetPriority` / `.tcbSetMCPriority` off
-- their doubly-boot-pinned operations, and round 15's inventory-completeness
-- check (`scripts/check_live_arm_per_core_routing.py`) observed that the reroute
-- was only half the obligation: a per-core operation can write a core it is not
-- executing on, and nothing here bounded what these two write. `.tcbSetAffinity`
-- was never rerouted — it has been per-core since SM5.H.4 — and had the same
-- gap for the same reason.

/-- SM8.B.2: rewriting a thread's priority source is per-core silent — it moves
objects and touches neither the scheduler nor a register bank.

**`v0.35.98`: one application of the frame stated at the write.**  Both halves
ran their own case analysis over the body, so the cut that made the `.bound` arm
a *pair* of writes broke both identically; the shared
`updatePrioritySource_only_modifies_objects` is what a further write on either
arm now costs nothing. -/
theorem updatePrioritySource_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (newPriority : SeLe4n.Priority) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.updatePrioritySource st tid tcb newPriority) [] := by
  obtain ⟨_, h⟩ := SchedContext.PriorityManagement.updatePrioritySource_only_modifies_objects
    st tid tcb newPriority
  exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq (by rw [h]) (by rw [h])

/-- SM8.B.2: the run-queue bucket migration writes exactly the core it is given.

The generalisation of `migrateRunQueueBucket`, which was pinned to `bootCoreId`
in both its membership test and its write — so a target queued anywhere else got
a silent no-op while its priority field moved (PR #861 review rounds 10 and 12,
the defect this whole layer exists to keep from recurring). -/
theorem migrateRunQueueBucketOnCore_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (newPriority : SeLe4n.Priority) (homeCore : CoreId) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st tid newPriority homeCore)
      [homeCore] := by
  unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    simp only [List.mem_singleton] at hc <;>
    (have hne : homeCore ≠ c := fun h => hc h.symm) <;>
    (repeat' split) <;>
    simp_all [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne,
      SchedulerState.setRunQueueOnCore_currentOnCore,
      SchedulerState.setRunQueueOnCore_activeDomainOnCore,
      SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
      SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- SM8.B.2: the priority ops' shared state effect — store the new value, then
re-bucket on the given core — writes exactly that core.

Factored out because both ops perform it and because composing it in one step
keeps the intermediate terms small: chaining the two leaves inline forces
`isDefEq` over a fully-expanded mid-state and times out. -/
theorem priorityUpdateAndMigrate_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority) (home : CoreId) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p home)
      [home] :=
  observableSlotsConfinedToCores_widen_cons
    (updatePrioritySource_confinedToCores st tid tcb p)
    (migrateRunQueueBucketOnCore_confinedToCores _ tid p home)

/-- The state a priority change re-walks the chain from agrees with the
pre-state on every home core and every blocking edge, so the
re-walk's write set is the one the pre-state names. -/
theorem priorityChangeMid_chainShape (base : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (p : SeLe4n.Priority) (home : CoreId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (ec : CoreId) (fuel : Nat)
    (hInv : base.objects.invExt) :
    waiterChainWriteSet (markKeyChangeFor
        (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
          (SchedContext.PriorityManagement.updatePrioritySource base tid tcb p) tid p home) tid k)
        tid ec fuel = waiterChainWriteSet base tid ec fuel := by
  generalize hMid : markKeyChangeFor
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource base tid tcb p) tid p home) tid k
    = mid
  have hObj : mid.objects =
      (SchedContext.PriorityManagement.updatePrioritySource base tid tcb p).objects := by
    rw [← hMid, markKeyChangeFor_objects]
    unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
    split <;> rfl
  have hMidInv : mid.objects.invExt := by
    rw [hObj]
    exact SchedContext.PriorityManagement.updatePrioritySource_preserves_objects_invExt
      base tid tcb p hInv
  obtain ⟨hHome, hEdge⟩ := PriorityInheritance.chainShape_of_tcbFields mid base (fun t => by
    rw [SystemState.getTcb?_congr_at (st := SchedContext.PriorityManagement.updatePrioritySource
      base tid tcb p) (st' := mid) (tid := t) (by rw [hObj])]
    exact updatePrioritySource_tcbChainFields base tid tcb p hInv t)
  exact PriorityInheritance.waiterChainWriteSet_congr mid base tid ec fuel hMidInv hInv hHome hEdge

/-- SM8.B.2: the priority ops' **whole** state effect writes the target's home
core, the executing core, and — when the target is reply-blocked — the cores of
the inheritance chain it re-walks, and nothing else.

Stated against the named effect `applyPriorityChangeOnCore` rather than its
composed steps, and over a base-state *variable*. Both matter: written
out inline, the composition's metavariables (base state, TCB, home core) have to
be recovered by unifying a `migrateRunQueueBucketOnCore (updatePrioritySource …)
…` pattern against a fully-expanded mid-state, which does not terminate at any
heartbeat budget — raising it to a million changed nothing, the same
"term shape, not budget" lesson v0.32.151 recorded. Named and generalised, the
caller instantiates it with one first-order match against its own `hStep`. -/
theorem applyPriorityChangeOnCore_confinedToCores (base st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : base.objects.invExt)
    (hStep : SchedContext.PriorityManagement.applyPriorityChangeOnCore base tid tcb p
      executingCore shouldPreempt = .ok (st', sgi)) :
    observableSlotsConfinedToCores base st'
      ([determineTargetCore base tid, executingCore] ++
        waiterChainWriteSet base tid executingCore base.objectIndex.length) := by
  have hA := observableSlotsConfinedToCores_then_flagOnly
    (priorityUpdateAndMigrate_confinedToCores base tid tcb p (determineTargetCore base tid))
    (markKeyChangeFor_confinedToCores _ tid (effectiveSchedParams base tcb))
  have hW := priorityChangeMid_chainShape base tid tcb p (determineTargetCore base tid)
    (effectiveSchedParams base tcb) executingCore base.objectIndex.length hObjInv
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at hStep
  generalize hMid : markKeyChangeFor
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource base tid tcb p) tid p
        (determineTargetCore base tid)) tid (effectiveSchedParams base tcb) = mid at hStep hA hW
  have hB := repropagateFromWaiter_confinedToCores mid tid executingCore base.objectIndex.length
  rw [hW] at hB
  have hC := priorityRescheduleOnCore_confinedToCores _ st' _ executingCore shouldPreempt sgi hStep
  refine observableSlotsConfinedToCores_mono ?_
    (observableSlotsConfinedToCores_trans (observableSlotsConfinedToCores_trans hA hB) hC)
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
  rcases hc with (hc | hc) | hc
  · exact Or.inl (Or.inl hc)
  · exact Or.inr hc
  · exact Or.inl (Or.inr hc)

-- WS-RR RR8.12 Cut C3b-i (`v0.35.167`): `priorityControlWriteSet` moved to the
-- production `SeLe4n/Kernel/SyscallSchedFootprint.lean`, beside
-- `schedLockSet_priorityControlOnCore`, for the reason the `.tcbResume`
-- tombstone above gives.  Same name, same namespace.

/-- SM8.B.2 (**the live `.tcbSetPriority` bound**): setting a priority writes no
core outside the target's home and the executing core.

Three legs — the priority-source store (silent), the bucket migration (the home
core), the preemption seam (the executing core) — and the home core is resolved
at the **pre-state**, exactly where `setPriorityOnCore` resolves it, so no
home-core bridge is needed. -/
theorem setPriorityOnCore_confinedToCores (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
      newPriority executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (priorityControlWriteSet st vTargetTid.val executingCore) := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore priorityControlWriteSet at *
  split at hStep
  · next callerTcb _ =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next targetTcb hTarget =>
        simp only [] at hStep
        exact applyPriorityChangeOnCore_confinedToCores st st' vTargetTid.val targetTcb
          newPriority executingCore _ sgi hObjInv hStep
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- SM8.B.2 (**the live `.tcbSetMCPriority` bound**): capping a thread's maximum
controlled priority writes no core outside the target's home and the executing
core, and the uncapped path writes no core at all.

One extra hop over `.tcbSetPriority`: the ceiling is stored *before* the home
core is resolved, so the transition reads `determineTargetCore` at a mid-state.
That store rewrites `maxControlledPriority`, never `cpuAffinity`, so it is not a
migration and the §1a bridge `determineTargetCore_insert_tcb` carries the
mid-state core back to the pre-state one the write set names. -/
theorem setMCPriorityOnCore_confinedToCores (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
      newMCP executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (priorityControlWriteSet st vTargetTid.val executingCore) := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore priorityControlWriteSet at *
  split at hStep
  · next callerTcb _ =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next targetTcb hTarget _ =>
        dsimp only [SystemState.rewriteObject] at hStep
        -- The ceiling store: an object write, so per-core silent, and not a
        -- migration — which is what lets the mid-state home core be the
        -- pre-state one. Both facts are stated over a *generic* post-state
        -- constrained by its fields, so neither has to restate the nested
        -- record-update literal the transition builds.
        have hSilent : ∀ r : SystemState, r.scheduler = st.scheduler →
            r.machine = st.machine → observableSlotsConfinedToCores st r [] :=
          fun _ h1 h2 => observableSlotsConfinedToCores_nil_of_scheduler_machine_eq h1 h2
        have hHome : ∀ (o : KernelObject) (t' : TCB), o = .tcb t' →
            t'.cpuAffinity = targetTcb.cpuAffinity →
            determineTargetCore { st with objects := st.objects.insert vTargetTid.val.toObjId o }
              vTargetTid.val = determineTargetCore st vTargetTid.val := by
          rintro o t' rfl hAff
          exact determineTargetCore_insert_tcb st _ vTargetTid.val targetTcb t' hObjInv
            (by rw [← RHTable_getElem?_eq_get?]
                exact (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget)
            hAff rfl _
        split at hStep
        · -- `hSilent`'s equations are left as goals rather than given as `rfl`
          -- here: supplied eagerly they would force Lean to solve
          -- `?r.scheduler =?= st.scheduler` for an unknown `?r`, and projecting a
          -- metavariable sends `whnf` into the fully-expanded 27-field mid-state
          -- record. Deferred, `?r` is fixed first by the second leg and both
          -- close by `rfl`.
          have hRaw : st.objects.get? vTargetTid.val.toObjId = some (.tcb targetTcb) := by
            rw [← RHTable_getElem?_eq_get?]
            exact (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget
          -- The ceiling store moves no home core and no blocking edge, so the
          -- chain the change re-walks names the pre-state's cores.
          have hChain : ∀ (o : KernelObject) (t' : TCB) (ec : CoreId) (fuel : Nat), o = .tcb t' →
              t'.cpuAffinity = targetTcb.cpuAffinity → t'.ipcState = targetTcb.ipcState →
              waiterChainWriteSet
                { st with objects := st.objects.insert vTargetTid.val.toObjId o }
                vTargetTid.val ec fuel =
              waiterChainWriteSet st vTargetTid.val ec fuel := by
            rintro o t' ec fuel rfl hAff hIpc
            have hInvR := SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt
              st.objects vTargetTid.val.toObjId (.tcb t') hObjInv
            obtain ⟨hH, hE⟩ := PriorityInheritance.chainShape_of_tcbFields _ st
              (insertTcb_tcbChainFields st
                { st with objects := st.objects.insert vTargetTid.val.toObjId (.tcb t') }
                vTargetTid.val targetTcb t' hObjInv hRaw hAff hIpc rfl)
            exact PriorityInheritance.waiterChainWriteSet_congr _ st vTargetTid.val ec fuel
              hInvR hObjInv hH hE
          refine observableSlotsConfinedToCores_mono ?_
            (observableSlotsConfinedToCores_trans (hSilent _ ?_ ?_)
              (applyPriorityChangeOnCore_confinedToCores _ st' vTargetTid.val _ newMCP
                executingCore true sgi
                (SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv) hStep))
          · intro c hc
            simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
              or_false] at hc ⊢
            rcases hc with (hc | hc) | hc
            · exact Or.inl (Or.inl (hc ▸ hHome _ _ rfl rfl))
            · exact Or.inl (Or.inr hc)
            · rw [hChain _ { targetTcb with maxControlledPriority := newMCP } _ _ rfl rfl rfl] at hc
              exact Or.inr hc
          · rfl
          · rfl
        · rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          exact observableSlotsConfinedToCores_widen_any (hSilent _ rfl rfl)
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

end SeLe4n.Kernel
