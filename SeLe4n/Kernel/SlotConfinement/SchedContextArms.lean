-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.IpcArms
import SeLe4n.Kernel.SchedContext.SchedContextFootprint
import SeLe4n.Kernel.Scheduler.Operations.AffinityFootprint

/-!
# Per-core slot confinement — the live SchedContext arms

§5h: `.schedContextBind`, `.schedContextConfigure`, `.schedContextUnbind`
and `.tcbSetAffinity`, each bounded by the write set its production
footprint declares (`SchedContext/SchedContextFootprint.lean`,
`Scheduler/Operations/AffinityFootprint.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §5h The live SchedContext arms
-- ============================================================================
--
-- PR #861 review round 14, and a direct consequence of this cut's own change:
-- `schedContextBind` / `schedContextConfigure` / `schedContextUnbind` used to
-- re-bucket and preempt against `bootCoreId`, so they wrote no remote core and
-- had no business in this inventory. Routing them through `determineTargetCore`
-- makes them genuine remote writers, and a remote writer without a write set is
-- exactly the gap this module exists to close.

-- WS-RR RR8.12 Cut C3b-ii (`v0.35.168`): `schedContextWriteSet` and
-- `schedContextUnbindWriteSet` moved to the production
-- `SeLe4n/Kernel/SchedContext/SchedContextFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), beside the footprints whose run
-- segments they are.  Same names, same namespace.
--
-- The resolver they read is **deleted** rather than moved: it was a second copy
-- of `SchedContextOps.schedContextBoundThread?`, clause for clause, under a
-- docstring on that one asserting it is "single-sourced here in production
-- because two consumers need it and a second copy would drift" -- the drift
-- hazard named at the owner while the second copy sat in this module.  Every
-- reader asks the owner now.

/-- SM8.B.2 (**the live `.schedContextUnbind` bound**): unbinding writes no core
outside `schedContextUnbindWriteSet`.

The transition's scheduler effects are a `setCurrentOnCore` at the subject's
**running** core and a `setRunQueueOnCore` at its **home** core, plus a
`setReplenishQueueOnCore` — which touches no confined slot, the replenish queue
being outside the six `observableSlotsConfinedToCores` fields. Everything else
it does is object-store and index writes.

The two cores are named separately because they genuinely differ (PR #861
review rounds 40/42): for an affinity-free thread running on a secondary core
the home is the boot core while `runningCoreOf?` is the secondary one, and the
transition must clear the slot that actually holds the thread while re-queueing
it where the next selection looks. That is why `schedContextUnbindWriteSet`
names both, and why it is a set of its own rather than `schedContextWriteSet` —
`.schedContextConfigure` only re-buckets, so declaring the running core there
would weaken its bound for nothing. -/
theorem schedContextUnbind_confinedToCores (vScId : SeLe4n.ValidObjId)
    (st st' : SystemState)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextUnbindWriteSet st vScId.val) := by
  unfold SchedContextOps.schedContextUnbind schedContextUnbindWriteSet
    SchedContextOps.schedContextBoundThread? at *
  split at hStep
  · next sc hSc _ =>
    simp only [hSc]
    split at hStep
    · exact absurd hStep (by simp)
    · next tid hBound =>
      simp only [hBound]
      split at hStep
      · next tcb hTcb =>
        -- `v0.35.4`: a donated holder is refused, so a successful unbind saw a
        -- binding that is not a donation.
        have hNotDon : tcb.schedContextBinding.isDonated = false := by
          cases hD : tcb.schedContextBinding.isDonated with
          | false => rfl
          | true => rw [hD] at hStep; simp at hStep
        simp only [hNotDon, Bool.false_eq_true, if_false] at hStep
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨-, hs⟩ := hStep
        subst hs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
          -- Two cores now: the re-bucket's home core and the guard's running
          -- core. `hc` rules out both; orient each disequality the way the
          -- `_ne` lemmas expect before simplifying.
          simp only [List.mem_cons, Option.mem_toList, not_or] at hc <;>
          (have hne : determineTargetCore st tid ≠ c := fun h => hc.1 h.symm) <;>
          (have hcRun : runningCoreOf? st tid ≠ some c := hc.2) <;>
          (repeat' split) <;>
          -- the replenish-queue setters are not in this transition's footprint;
          -- their five frames were carried here and never fired
          simp_all [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler,
            SystemState.updateTcb_machine, SystemState.rewriteObject_machine,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_ne,
            SchedulerState.setCurrentOnCore_currentOnCore_ne,
            SchedulerState.setRunQueueOnCore_currentOnCore,
            SchedulerState.setCurrentOnCore_activeDomainOnCore,
            SchedulerState.setRunQueueOnCore_activeDomainOnCore,
            SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
            SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
            SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
            SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
      · next hNoTcb =>
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨-, hs⟩ := hStep
        subst hs
        exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
               fun _ _ => rfl, fun _ _ => rfl⟩
  · exact absurd hStep (by simp)


-- WS-RR RR8.12 Cut C3b-ii (`v0.35.168`): `schedContextBindWriteSet` moved to the
-- production `SeLe4n/Kernel/SchedContext/SchedContextFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), beside
-- `schedLockSet_schedContextBindOnCore`.  Same name, same namespace.

/-- SM8.B.2 (**the live `.schedContextBind` bound**): binding writes no core
outside the bound thread's home core.

Bind has exactly one scheduling effect — the re-bucket this cut routed through
`determineTargetCore` — reached across two object writes, and the work is the
home-core bridge: the transition computes its target two inserts later than the
write set names it. Neither insert is a migration. The SchedContext insert
leaves every TCB lookup alone (`getTcb?_insert_schedContext_eq`); the TCB insert
rewrites `schedContextBinding` and `priority`, never `cpuAffinity`
(`determineTargetCore_insert_tcb`).

The bridge is **transported into the disequality** rather than rewritten into the
goal: the post-state is a structure literal far too large to restate, but
`hHome ▸ hne` gives the setter's own frame lemma exactly the hypothesis it
wants, and `exact` closes the rest up to definitional equality. -/
theorem schedContextBind_confinedToCores (vScId : SeLe4n.ValidObjId)
    (vThreadId : SeLe4n.ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextBindWriteSet st vThreadId.val) := by
  unfold SchedContextOps.schedContextBind at hStep
  split at hStep
  · next sc hSc _ =>
    split at hStep
    · exact absurd hStep (by simp)
    · -- `v0.35.4`: a context heading a reply stack is refused, so a successful
      -- bind saw none.
      have hNoHead : sc.scReply.isSome = false := by
        cases hH : sc.scReply.isSome with
        | false => rfl
        | true => rw [hH] at hStep; simp at hStep
      simp only [hNoHead, Bool.false_eq_true, if_false] at hStep
      split at hStep
      · next tcb hTcb =>
        -- `v0.35.4`: and a thread whose reply frame is on a live stack is refused.
        have hNoLive : replyFrameOnLiveStack st tcb = false := by
          cases hL : replyFrameOnLiveStack st tcb with
          | false => rfl
          | true => rw [hL] at hStep; split at hStep <;> simp at hStep
        simp only [hNoLive, Bool.false_eq_true, if_false] at hStep
        split at hStep
        · exact absurd hStep (by simp)
        · split at hStep
          · next hUnbound =>
            rw [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨-, hs⟩ := hStep
            subst hs
            -- `v0.35.71`: the two typed writes over `st`, reduced to the double
            -- insert under the pre-state's TCB witness.
            rw [SystemState.updateTcb_after_rewriteObject_schedContext st vScId.val _ _
              vThreadId.val tcb _ hObjInv hTcb]
            let sc1 : SchedContext := { sc with boundThread := some vThreadId.val,
                                                donationOrigin := none }
            let scObj : KernelObject := .schedContext sc1
            let st1 : SystemState := { st with objects := st.objects.insert vScId.val scObj }
            let tcb1 : TCB :=
              { tcb with schedContextBinding := SchedContextBinding.bound ⟨vScId.val.toNat⟩,
                         priority := sc.priority }
            let tcbObj : KernelObject := .tcb tcb1
            let st2 : SystemState :=
              { st1 with objects := st1.objects.insert vThreadId.val.toObjId tcbObj }
            have hScRaw : st.objects.get? vScId.val = some (.schedContext sc) := by
              simpa using (SystemState.getSchedContext?_eq_some_iff st
                (SeLe4n.SchedContextId.ofObjId vScId.val) sc).mp hSc
            have hT1 : ∀ x : SeLe4n.ThreadId, st1.getTcb? x = st.getTcb? x := fun x =>
              getTcb?_insert_schedContext_eq st st1
                (SeLe4n.SchedContextId.ofObjId vScId.val) sc sc1 hObjInv
                (by simpa using hScRaw) rfl x
            have hInv1 : st1.objects.invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv
            have hTcb1 : st1.objects.get? vThreadId.val.toObjId = some (.tcb tcb) := by
              have h := hT1 vThreadId.val
              rw [hTcb] at h
              simpa using (SystemState.getTcb?_eq_some_iff st1 vThreadId.val tcb).mp h
            have hHome : determineTargetCore st2 vThreadId.val
                = determineTargetCore st vThreadId.val := by
              refine Eq.trans (determineTargetCore_insert_tcb st1 st2 vThreadId.val tcb tcb1
                hInv1 hTcb1 rfl rfl vThreadId.val) ?_
              exact determineTargetCore_congr st st1 vThreadId.val (by rw [hT1 vThreadId.val])
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
              simp only [schedContextBindWriteSet, List.mem_singleton] at hc
            -- **WS-RR RR8.12 Cut B2 (`v0.35.182`)**: THREE arms since the bind
            -- places a parked runnable thread — the re-bucket, the placement and
            -- the identity.  The first two write `setRunQueueOnCore bindHome`,
            -- the same core the write set names, so each clause is the same
            -- lemma twice and then `rfl`; the write set does not move.
            · have hne : determineTargetCore st vThreadId.val ≠ c := fun h => hc h.symm
              -- KSC-1: the key-change flag wraps the bind's final state and the
              -- placement arm raises the home core's flag; neither moves a slot.
              refine (markKeyChangeFor_runQueueOnCore _ _ _ _).trans ?_
              split
              · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ (hHome ▸ hne)
              · split
                · exact (SchedulerState.markReschedulePendingOnCore_runQueueOnCore _ _ _).trans
                    (SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ (hHome ▸ hne))
                · rfl
            · refine (markKeyChangeFor_currentOnCore _ _ _ _).trans ?_
              split
              · exact SchedulerState.setRunQueueOnCore_currentOnCore _ _ c _
              · split
                · exact (SchedulerState.markReschedulePendingOnCore_currentOnCore _ _ _).trans
                    (SchedulerState.setRunQueueOnCore_currentOnCore _ _ c _)
                · rfl
            · refine (markKeyChangeFor_activeDomainOnCore _ _ _ _).trans ?_
              split
              · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore _ _ c _
              · split
                · exact (SchedulerState.markReschedulePendingOnCore_activeDomainOnCore _ _ _).trans
                    (SchedulerState.setRunQueueOnCore_activeDomainOnCore _ _ c _)
                · rfl
            · refine (markKeyChangeFor_domainTimeRemainingOnCore _ _ _ _).trans ?_
              split
              · exact SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore _ _ c _
              · split
                · exact (SchedulerState.markReschedulePendingOnCore_domainTimeRemainingOnCore _ _ _).trans
                    (SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore _ _ c _)
                · rfl
            · refine (markKeyChangeFor_domainScheduleIndexOnCore _ _ _ _).trans ?_
              split
              · exact SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore _ _ c _
              · split
                · exact (SchedulerState.markReschedulePendingOnCore_domainScheduleIndexOnCore _ _ _).trans
                    (SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore _ _ c _)
                · rfl
            · -- registers: untouched on all three arms, but the projection only
              -- reduces once the run-queue `if`s are resolved.
              refine (congrArg (fun m => m.regsOnCore c) (markKeyChangeFor_machine _ _ _)).trans ?_
              split
              · rfl
              · split <;> rfl
          · exact absurd hStep (by simp)
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

-- WS-RR RR8.12 Cut C3b-i (`v0.35.167`): `setThreadCpuAffinityWriteSet` moved to the
-- production `SeLe4n/Kernel/Scheduler/Operations/AffinityFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), beside
-- `schedLockSet_setThreadCpuAffinityOnCore`, for the reason the `.tcbResume`
-- tombstone above gives.  Same name, same namespace.

/-- SM8.B.2: the affinity write touches the object store only. -/
theorem setThreadCpuAffinity_scheduler_machine_eq (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet) :
    stSet.scheduler = st.scheduler ∧ stSet.machine = st.machine := by
  unfold setThreadCpuAffinity at hSet
  split at hSet
  · rw [Except.ok.injEq] at hSet; subst hSet; exact ⟨rfl, rfl⟩
  · exact absurd hSet (by simp)

-- `v0.35.167` (WS-RR RR8.12 Cut C3b-i): `setThreadCpuAffinity_determineTargetCore_eq`
-- moved to `Scheduler/Operations/Selection.lean`, beside the definition it is
-- about.  It was declared here, in a **staged** module, and the live
-- `.tcbSetAffinity` arm's production scheduler-domain footprint needs it to state
-- that the replenish pair it declares IS the migration's — the same layering
-- finding as `v0.35.166`'s five relocations and this cut's
-- `enqueueRunnableOnCore_replenishQueueOnCore`.

/-- SM8.B.2 (**the live `.tcbSetAffinity` bound**): a migration writes no core
outside the pair it moves the thread between.

Three effects, one of them confined-relevant. The `setThreadCpuAffinity` write
touches the object store only (`setThreadCpuAffinity_scheduler_machine_eq`); the
replenishment migration is per-core silent even on the cores it names
(`migrateSchedContextReplenishment_confinedToCores`, against the *empty* set,
because the replenish queue is outside the six observable slots); and the
run-queue migration is bounded by
`migrateRunQueueOnAffinityChange_confinedToCores`, new in this cut and the
reason `.tcbSetAffinity` could not carry a proof before it.

Read as a chain: `st` and the post-affinity state share every observable slot,
the replenishment stage preserves all of them, and the run-queue stage moves
only the two cores the write set names — the second of which is the *argument*,
via the bridge above. -/
theorem setThreadCpuAffinityWithMigration_confinedToCores
    (st st' : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (hInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (setThreadCpuAffinityWriteSet st targetTid affinity) := by
  unfold setThreadCpuAffinityWithMigration at hStep
  split at hStep
  · next tcb hTcb =>
    -- PR #889 review round 20: the declared-core refusal is a new leading
    -- branch, ahead of the running-on-a-forbidden-core guard below.
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · exact absurd hStep (by simp)
      · split at hStep
        · next stSet hSet =>
          rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          obtain ⟨hSched, hMach⟩ :=
            setThreadCpuAffinity_scheduler_machine_eq st stSet targetTid affinity hSet
          have hNew := setThreadCpuAffinity_determineTargetCore_eq st stSet targetTid affinity
            hInv hSet
          -- The mid-state after the (optional) replenishment migration. Written
          -- out rather than named: `set` cannot bind a `match` body here.
          have hRepl : observableSlotsConfinedToCores stSet
              (match tcb.schedContextBinding.scId? with
                | some scId => migrateSchedContextReplenishment stSet scId
                    (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
                | none => stSet) [] := by
            cases tcb.schedContextBinding.scId? with
            | none => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
                             fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
            | some scId => exact migrateSchedContextReplenishment_confinedToCores _ _ _ _
          have hRun := migrateRunQueueOnAffinityChange_confinedToCores
            (match tcb.schedContextBinding.scId? with
              | some scId => migrateSchedContextReplenishment stSet scId
                  (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
              | none => stSet) targetTid
            (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
          have key : ∀ c, c ∉ setThreadCpuAffinityWriteSet st targetTid affinity →
              c ∉ [determineTargetCore st targetTid, determineTargetCore stSet targetTid] := by
            intro c hc
            simp only [setThreadCpuAffinityWriteSet, List.mem_cons, List.not_mem_nil,
              or_false, not_or] at hc ⊢
            rw [hNew]
            exact hc
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals intro c hc
          all_goals have hcPair := key c hc
          · exact ((hRun.runQueue c hcPair).trans (hRepl.runQueue c (by simp))).trans
              (by rw [hSched])
          · exact ((hRun.current c hcPair).trans (hRepl.current c (by simp))).trans
              (by rw [hSched])
          · exact ((hRun.activeDomain c hcPair).trans (hRepl.activeDomain c (by simp))).trans
              (by rw [hSched])
          · exact ((hRun.domainTimeRemaining c hcPair).trans
              (hRepl.domainTimeRemaining c (by simp))).trans (by rw [hSched])
          · exact ((hRun.domainScheduleIndex c hcPair).trans
              (hRepl.domainScheduleIndex c (by simp))).trans (by rw [hSched])
          · exact ((hRun.regs c hcPair).trans (hRepl.regs c (by simp))).trans (by rw [hMach])
        · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- The waiter-side chain re-walk writes only the cores its write set names. -/
theorem repropagateFromWaiter_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (fuel : Nat) :
    observableSlotsConfinedToCores st
      (PriorityInheritance.repropagateFromWaiter st tid ec fuel)
      (waiterChainWriteSet st tid ec fuel) := by
  unfold PriorityInheritance.repropagateFromWaiter waiterChainWriteSet
  cases blockingServer st tid with
  | none => exact observableSlotsConfinedToCores_of_eq _ rfl
  | some server =>
    exact propagatePipChainCrossCore_confinedToCores _ _ st server

/-- A priority write keeps every thread's affinity and IPC state — the two
fields a home core and a blocking edge are read from. -/
theorem updatePrioritySource_tcbChainFields (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (p : SeLe4n.Priority) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    ((SchedContext.PriorityManagement.updatePrioritySource st tid tcb p).getTcb? t).map
        (fun x => (x.cpuAffinity, x.ipcState)) =
      (st.getTcb? t).map (fun x => (x.cpuAffinity, x.ipcState)) := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · rename_i scId _
    have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt st scId
      (fun sc => { sc with priority := p }) hInv
    by_cases h : tid.toObjId = t.toObjId
    · have ht : tid = t := ThreadId.toObjId_injective _ _ h
      subst ht
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv1,
        SystemState.updateSchedContext_getTcb? _ _ _ hInv]
      cases st.getTcb? tid <;> rfl
    · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv1 _ h,
        SystemState.updateSchedContext_getTcb? _ _ _ hInv]
  · by_cases h : tid.toObjId = t.toObjId
    · have ht : tid = t := ThreadId.toObjId_injective _ _ h
      subst ht
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv]
      cases st.getTcb? tid <;> rfl
    · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _ h]

/-- Re-storing a thread's TCB with the same affinity and IPC state keeps every
thread's pair of chain fields — the MCP ceiling write is one. -/
theorem insertTcb_tcbChainFields (st result : SystemState) (tid0 : SeLe4n.ThreadId)
    (t0 t' : TCB) (hInv : st.objects.invExt)
    (hOld : st.objects.get? tid0.toObjId = some (.tcb t0))
    (hAff : t'.cpuAffinity = t0.cpuAffinity) (hIpc : t'.ipcState = t0.ipcState)
    (hObj : result.objects = st.objects.insert tid0.toObjId (.tcb t')) (t : SeLe4n.ThreadId) :
    (result.getTcb? t).map (fun x => (x.cpuAffinity, x.ipcState)) =
      (st.getTcb? t).map (fun x => (x.cpuAffinity, x.ipcState)) := by
  unfold SystemState.getTcb?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects tid0.toObjId (.tcb t') hInv t.toObjId]
  by_cases hk : tid0.toObjId == t.toObjId
  · simp only [hk, if_pos]
    have hkey : st.objects.get? t.toObjId = some (.tcb t0) := by
      have : t.toObjId = tid0.toObjId := (eq_of_beq hk).symm
      rw [this]; exact hOld
    rw [hkey]
    simp [hAff, hIpc]
  · simp only [hk, if_neg, Bool.not_eq_true]

/-- The configure propagation tail keeps every thread's affinity and IPC state:
its two writes set the bound thread's priority and domain, and the re-bucket
touches the scheduler only. -/
theorem schedContextConfigureBoundPropagate_tcbChainFields (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (hInv : stStored.objects.invExt) (t : SeLe4n.ThreadId) :
    ((SchedContextOps.schedContextConfigureBoundPropagate stStored scId boundTid boundTcb hBound
        priority domain).getTcb? t).map (fun x => (x.cpuAffinity, x.ipcState)) =
      (stStored.getTcb? t).map (fun x => (x.cpuAffinity, x.ipcState)) := by
  have hRaw : ∀ (s : SystemState) (cur : TCB), s.getTcb? boundTid = some cur →
      s.objects.get? boundTid.toObjId = some (.tcb cur) := fun s cur h => by
    rw [← RHTable_getElem?_eq_get?]; exact (SystemState.getTcb?_eq_some_iff s boundTid cur).mp h
  have hW := insertTcb_tcbChainFields stStored
    { stStored with objects := (stStored.objects.insert boundTid.toObjId
        (.tcb { boundTcb with priority := ⟨priority⟩ })) }
    boundTid boundTcb { boundTcb with priority := ⟨priority⟩ } hInv (hRaw _ _ hBound) rfl rfl rfl
  have hInvW := RobinHood.RHTable.insert_preserves_invExt stStored.objects
    boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) hInv
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only [SystemState.rewriteObject]
  by_cases hPrioEq : boundTcb.priority.val = priority ∨
      ¬ SchedContextOps.schedContextConfigurePropagates boundTcb scId
  · rw [if_pos hPrioEq]
    try dsimp only []
    split
    · rename_i cur hCur _
      split
      · rfl
      · exact insertTcb_tcbChainFields stStored _ boundTid cur { cur with domain := ⟨domain⟩ }
          hInv (hRaw _ _ hCur) rfl rfl rfl t
    · rfl
  · rw [if_neg hPrioEq]
    try dsimp only []
    by_cases hMem : boundTid ∈ stStored.scheduler.runQueueOnCore
        (determineTargetCore { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) } boundTid)
    · rw [if_pos hMem]
      split
      · rename_i cur hCur _
        split
        · exact hW t
        · exact (insertTcb_tcbChainFields _ _ boundTid cur { cur with domain := ⟨domain⟩ }
            hInvW (hRaw _ _ hCur) rfl rfl rfl t).trans (hW t)
      · exact hW t
    · rw [if_neg hMem]
      split
      · rename_i cur hCur _
        split
        · exact hW t
        · exact (insertTcb_tcbChainFields _ _ boundTid cur { cur with domain := ⟨domain⟩ }
            hInvW (hRaw _ _ hCur) rfl rfl rfl t).trans (hW t)
      · exact hW t

/-- After a configure's SchedContext store and propagation, the bound thread's
chain names the pre-state's cores: neither write moves a home core or a blocking
edge, and the key-change flag is a scheduler write. -/
theorem waiterChainWriteSet_configurePropagate (st stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (ec : CoreId) (fuel : Nat)
    (hInvSt : st.objects.invExt) (hInvStored : stStored.objects.invExt)
    (hGet : ∀ t, stStored.getTcb? t = st.getTcb? t) :
    waiterChainWriteSet (markKeyChangeFor (SchedContextOps.schedContextConfigureBoundPropagate
        stStored scId boundTid boundTcb hBound priority domain) boundTid k) boundTid ec fuel =
      waiterChainWriteSet st boundTid ec fuel := by
  have hXInv : (markKeyChangeFor (SchedContextOps.schedContextConfigureBoundPropagate
      stStored scId boundTid boundTcb hBound priority domain) boundTid k).objects.invExt := by
    rw [markKeyChangeFor_objects]
    exact SchedContextOps.schedContextConfigureBoundPropagate_preserves_objects_invExt
      _ _ _ _ _ _ _ hInvStored
  obtain ⟨hH, hE⟩ := PriorityInheritance.chainShape_of_tcbFields _ st (fun t => by
    rw [SystemState.getTcb?_congr_at (st := SchedContextOps.schedContextConfigureBoundPropagate
        stStored scId boundTid boundTcb hBound priority domain)
        (st' := markKeyChangeFor (SchedContextOps.schedContextConfigureBoundPropagate
          stStored scId boundTid boundTcb hBound priority domain) boundTid k)
        (tid := t) (by rw [markKeyChangeFor_objects]), ← hGet t]
    exact schedContextConfigureBoundPropagate_tcbChainFields stStored scId boundTid boundTcb
      hBound priority domain hInvStored t)
  exact PriorityInheritance.waiterChainWriteSet_congr _ st boundTid ec fuel hXInv hInvSt hH hE

/-- A step that ends in the waiter-side chain re-walk writes its prefix's cores
and the chain's. -/
theorem observableSlotsConfinedToCores_repropagate {st X : SystemState}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {fuel : Nat} {cs W : List CoreId}
    (hX : observableSlotsConfinedToCores st X cs) (hW : waiterChainWriteSet X tid ec fuel = W) :
    observableSlotsConfinedToCores st (PriorityInheritance.repropagateFromWaiter X tid ec fuel)
      (cs ++ W) := by
  subst hW
  exact observableSlotsConfinedToCores_trans hX
    (repropagateFromWaiter_confinedToCores X tid ec fuel)

/-- SM8.B.2 (**the live `.schedContextConfigure` bound**): a configure writes no
core outside its subject's home core and, when that thread is reply-blocked, the
cores of the inheritance chain its propagated priority re-walks
(`schedContextConfigureWriteSet`).

Two scheduler writes, and only one of them is confined-relevant: the
replenish-queue purge is outside the six observable slots, so it is per-core
silent even on the core it names. The run-queue re-bucket needs the same
home-core bridge as bind, one hop longer — the target is computed after the
replenish write (scheduler-only, objects untouched), the `storeObject` of the
reconfigured SchedContext (`storeObject_schedContext_determineTargetCore_eq`) and
the TCB **priority** insert, which is not a migration.

The `boundThread = none` and `getTcb? = none` arms perform no scheduling work at
all, and the trailing domain propagation is an object write.  The chain re-walk
runs last; its write set is read from the pre-state because neither the store nor
the propagation moves a home core or a blocking edge
(`waiterChainWriteSet_configurePropagate`). -/
theorem schedContextConfigure_confinedToCores (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextConfigureWriteSet st vScId.val) := by
  unfold SchedContextOps.schedContextConfigure schedContextConfigureWriteSet schedContextWriteSet
    SchedContextOps.schedContextBoundThread? at *
  split at hStep
  · exact absurd hStep (by simp)
  · split at hStep
    · next sc hSc =>
      simp only [hSc]
      -- Zeta-reduce the `let updated := …` binder so the admission guard is a
      -- splittable `if` rather than a `have`-wrapped one.
      simp only [] at hStep
      split at hStep
      · -- admission granted
        split at hStep
        · exact absurd hStep (by simp)
        · next stStored hStore =>
          have hScRaw : st.objects.get? vScId.val = some (.schedContext sc) := by
            simpa using (SystemState.getSchedContext?_eq_some_iff st
              (SeLe4n.SchedContextId.ofObjId vScId.val) sc).mp hSc
          split at hStep
          · -- no bound thread: no scheduling effect at all
            next hNone =>
            simp only [hNone]
            rw [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨-, hs⟩ := hStep
            subst hs
            exact observableSlotsConfinedToCores_trans
              (purgeReplenishmentOnCore_confinedToCores st _ _)
              (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                (storeObject_scheduler_eq _ _ _ _ hStore)
                (storeObject_machine_eq _ _ _ _ hStore))
          · next boundTid hBound =>
            simp only [hBound]
            have hInvStored : stStored.objects.invExt :=
              -- Named again for the same reason: the store's pre-state is the
              -- post-replenish one, not `st`.
              -- `by exact` postpones these until `hStore` has fixed the
              -- pre-state; passed directly they pin it to `st` first.
              storeObject_preserves_objects_invExt (st' := stStored) (hStore := hStore)
                (hObjInv := by exact hObjInv)
            -- The SchedContext store is not a migration, and the replenish write
            -- leaves `objects` alone, so the home core is already the pre-state's.
            have hHomeStored : ∀ x : SeLe4n.ThreadId,
                determineTargetCore stStored x = determineTargetCore st x := fun x => by
              -- The lemma's own conclusion names the store's pre-state — the
              -- post-replenish one. Ascribing the statement up front would pin
              -- that to `st` and the store hypothesis would stop matching, so it
              -- is elaborated unascribed and closed by defeq: the replenish
              -- write leaves `objects`, and `determineTargetCore` reads nothing
              -- else.
              have h := storeObject_schedContext_determineTargetCore_eq (x := x) (sc := sc)
                (hStore := hStore) (hPre := by exact hScRaw) (hObjInv := by exact hObjInv)
              exact h
            split at hStep
            · next boundTcb hTcbStored _ =>
              have hTcbStoredRaw :
                  stStored.objects.get? boundTid.toObjId = some (.tcb boundTcb) := by
                simpa using (SystemState.getTcb?_eq_some_iff stStored boundTid boundTcb).mp
                  hTcbStored
              let boundTcb2 : TCB := { boundTcb with priority := ⟨priority⟩ }
              let boundObj : KernelObject := .tcb boundTcb2
              let stWithTcb : SystemState :=
                { stStored with objects := stStored.objects.insert boundTid.toObjId boundObj }
              have hHomeWith : determineTargetCore stWithTcb boundTid
                  = determineTargetCore st boundTid :=
                Eq.trans
                  (determineTargetCore_insert_tcb stStored stWithTcb boundTid boundTcb boundTcb2
                    hInvStored hTcbStoredRaw rfl rfl boundTid)
                  (hHomeStored boundTid)
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              -- The chain re-walk last: its cores are the pre-state chain's,
              -- because the store and the propagation move no home core and no
              -- blocking edge.
              have hGetSt : ∀ t, stStored.getTcb? t = st.getTcb? t := fun t =>
                storeObject_schedContextAt_getTcb?_eq
                  (SchedContextOps.purgeReplenishmentOnCore st
                    (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩)
                  stStored (SeLe4n.SchedContextId.ofObjId vScId.val) sc _ (by exact hSc)
                  (by exact hObjInv) (by exact hStore) t
              refine observableSlotsConfinedToCores_repropagate ?_
                (waiterChainWriteSet_configurePropagate st stStored _ boundTid boundTcb _ priority
                  domain _ _ _ hObjInv hInvStored hGetSt)
              unfold SchedContextOps.schedContextConfigureBoundPropagate
              -- The prefix common to every arm: replenish purge then the SC
              -- store, neither of which is confined-relevant.
              have hStoredConf : observableSlotsConfinedToCores st stStored [] :=
                observableSlotsConfinedToCores_trans
                  (purgeReplenishmentOnCore_confinedToCores st _ _)
                  (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                    (storeObject_scheduler_eq _ _ _ _ hStore)
                    (storeObject_machine_eq _ _ _ _ hStore))
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
                simp only [List.mem_singleton] at hc <;>
                (have hne : determineTargetCore stWithTcb boundTid ≠ c := by
                  rw [hHomeWith]; exact fun h => hc h.symm) <;>
                -- Hoisted: a nested `by simp` inside a `first` alternative throws
                -- rather than backtracking, so the alternatives below carry no
                -- tactic blocks of their own.
                (have hNil : c ∉ ([] : List CoreId) := by simp) <;>
                ((try dsimp only [SystemState.rewriteObject]); repeat' split) <;>
                first
                  -- KSC-1: every propagate arm is wrapped by the key-change
                  -- flag write, which moves no slot; strip it first.
                  | (rw [markKeyChangeFor_runQueueOnCore]
                     first
                       | exact hStoredConf.runQueue c hNil
                       | (rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ hne]
                          exact hStoredConf.runQueue c hNil))
                  | (rw [markKeyChangeFor_currentOnCore]
                     first
                       | exact hStoredConf.current c hNil
                       | (rw [SchedulerState.setRunQueueOnCore_currentOnCore]
                          exact hStoredConf.current c hNil))
                  | (rw [markKeyChangeFor_activeDomainOnCore]
                     first
                       | exact hStoredConf.activeDomain c hNil
                       | (rw [SchedulerState.setRunQueueOnCore_activeDomainOnCore]
                          exact hStoredConf.activeDomain c hNil))
                  | (rw [markKeyChangeFor_domainTimeRemainingOnCore]
                     first
                       | exact hStoredConf.domainTimeRemaining c hNil
                       | (rw [SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]
                          exact hStoredConf.domainTimeRemaining c hNil))
                  | (rw [markKeyChangeFor_domainScheduleIndexOnCore]
                     first
                       | exact hStoredConf.domainScheduleIndex c hNil
                       | (rw [SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
                          exact hStoredConf.domainScheduleIndex c hNil))
                  | (rw [markKeyChangeFor_machine]; exact hStoredConf.regs c hNil)
                  -- arms that stop at `stStored` / `stWithTcb` (object writes only)
                  | exact hStoredConf.runQueue c hNil
                  | exact hStoredConf.current c hNil
                  | exact hStoredConf.activeDomain c hNil
                  | exact hStoredConf.domainTimeRemaining c hNil
                  | exact hStoredConf.domainScheduleIndex c hNil
                  | exact hStoredConf.regs c hNil
                  -- arms that additionally take the run-queue re-bucket
                  | (rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ hne]
                     exact hStoredConf.runQueue c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_currentOnCore]
                     exact hStoredConf.current c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_activeDomainOnCore]
                     exact hStoredConf.activeDomain c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]
                     exact hStoredConf.domainTimeRemaining c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
                     exact hStoredConf.domainScheduleIndex c hNil)
                  | rfl
            · -- the bound TCB vanished behind the store: no scheduling effect
              next hNoTcb =>
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              refine observableSlotsConfinedToCores_widen_any ?_
              exact observableSlotsConfinedToCores_trans
                (purgeReplenishmentOnCore_confinedToCores st _ _)
                (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                  (storeObject_scheduler_eq _ _ _ _ hStore)
                  (storeObject_machine_eq _ _ _ _ hStore))
      · exact absurd hStep (by simp)
    · exact absurd hStep (by simp)

-- WS-RR RR8.12 Cut C3b-ii (`v0.35.168`): `schedContextUnbindOnCoreWriteSet` moved to
-- the production `SeLe4n/Kernel/SchedContext/SchedContextFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), beside
-- `schedLockSet_schedContextUnbindOnCore`, whose run segment IS it.  Same name,
-- same namespace; the confinement theorem below stays here.

/-- SM8.B.2 (**the live `.schedContextUnbind` bound**): the per-core unbind
writes no core outside the demoted thread's home and the executing core.

Two legs, composed by `observableSlotsConfinedToCores_trans` — which is why the
write set is literally the concatenation the transition performs: the revocation
(bounded by `schedContextUnbind_confinedToCores`) and the preemption seam
(bounded by `priorityRescheduleOnCore_confinedToCores`). A rejected unbind never
reaches the seam. -/
theorem schedContextUnbindOnCore_confinedToCores (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId executingCore st
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (schedContextUnbindOnCoreWriteSet st vScId.val executingCore) := by
  unfold SchedContextOps.schedContextUnbindOnCore schedContextUnbindOnCoreWriteSet at *
  simp only [] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next stMid hUnbind =>
    exact observableSlotsConfinedToCores_trans
      (schedContextUnbind_confinedToCores vScId st stMid hUnbind)
      (priorityRescheduleOnCore_confinedToCores stMid st' _ executingCore true sgi hStep)

end SeLe4n.Kernel
