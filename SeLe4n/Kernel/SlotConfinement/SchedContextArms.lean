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
import SeLe4n.Kernel.SchedContext.SchedControlFootprint

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
            SchedContextOps.schedContextUnbindQueueStage_runQueueOnCore_ne,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_currentOnCore_ne,
            SchedulerState.setCurrentOnCore_activeDomainOnCore,
            SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
            SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore]
      · next hNoTcb =>
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨-, hs⟩ := hStep
        subst hs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _ <;>
          simp [SystemState.rewriteObject_scheduler, SystemState.rewriteObject_machine]
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
            let sc1 : SchedContext :=
              { sc.releaseReadyHead st.machine.timer with
                boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val)
                donationOrigin := none }
            let scObj : KernelObject := .schedContext sc1
            let st1 : SystemState := { st with objects := st.objects.insert vScId.val scObj }
            let tcb1 : TCB :=
              { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0,
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
              -- WS-ZA ZA4.5: both queue arms write through the thread's TCB
              -- run-queue links, on the home core only.
              refine (SystemState.releaseOnlyWrite.runQueueOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              refine (markKeyChangeFor_runQueueOnCore _ _ _ _).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_runQueueOnCore_ne _ _ c _ _ (hHome ▸ hne)]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_runQueueOnCore,
                    SystemState.runEnqueueOnCore_runQueueOnCore_ne _ _ c _ _ (hHome ▸ hne)]
                · rfl
            · refine (SystemState.releaseOnlyWrite.currentOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              refine (markKeyChangeFor_currentOnCore _ _ _ _).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_currentOnCore]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_currentOnCore,
                    SystemState.runEnqueueOnCore_currentOnCore]
                · rfl
            · refine (SystemState.releaseOnlyWrite.activeDomainOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              refine (markKeyChangeFor_activeDomainOnCore _ _ _ _).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_activeDomainOnCore]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_activeDomainOnCore,
                    SystemState.runEnqueueOnCore_activeDomainOnCore]
                · rfl
            · refine (SystemState.releaseOnlyWrite.domainTimeRemainingOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              refine (markKeyChangeFor_domainTimeRemainingOnCore _ _ _ _).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_domainTimeRemainingOnCore]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_domainTimeRemainingOnCore,
                    SystemState.runEnqueueOnCore_domainTimeRemainingOnCore]
                · rfl
            · refine (SystemState.releaseOnlyWrite.domainScheduleIndexOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              refine (markKeyChangeFor_domainScheduleIndexOnCore _ _ _ _).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_domainScheduleIndexOnCore]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_domainScheduleIndexOnCore,
                    SystemState.runEnqueueOnCore_domainScheduleIndexOnCore]
                · rfl
            · -- registers: untouched on all three arms.
              refine (congrArg (fun m => m.regsOnCore c)
                (SystemState.releaseOnlyWrite.machine (SystemState.releasePlace_releaseOnlyWrite _ _ _))).trans ?_
              refine (congrArg (fun m => m.regsOnCore c) (markKeyChangeFor_machine _ _ _)).trans ?_
              split
              · rw [SystemState.runRequeueOnCore_machine]
              · split
                · rw [SystemState.markReschedulePendingOnCore, SystemState.runEnqueueOnCore_machine]
                · rfl
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

/-- WS-ZA ZA6.3: the vacate writes the old home's `current` slot alone. -/
theorem vacateForAffinityChange_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : CoreId) :
    observableSlotsConfinedToCores st (vacateForAffinityChange st tid oldCore newCore)
      [oldCore] := by
  refine ⟨fun c _ => vacateForAffinityChange_runQueueOnCore _ _ _ _ c, fun c hc => ?_,
    fun c _ => ?_, fun c _ => ?_, fun c _ => ?_, fun c _ => by rw [vacateForAffinityChange_machine]⟩
  · have hne : c ≠ oldCore := fun h => hc (by simp [h])
    rw [vacateForAffinityChange_currentOnCore, if_neg (fun h => hne h.1)]
  all_goals (unfold vacateForAffinityChange; split <;> simp)

/-- WS-ZA ZA6.3: the requeue writes the new home's run queue alone. -/
theorem requeueVacatedOnNewHome_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (newCore : CoreId) (vacated : Bool) :
    observableSlotsConfinedToCores st (requeueVacatedOnNewHome st tid newCore vacated)
      [newCore] := by
  refine ⟨fun c hc => ?_, fun c _ => requeueVacatedOnNewHome_currentOnCore _ _ _ _ c,
    fun c _ => ?_, fun c _ => ?_, fun c _ => ?_, fun c _ => by rw [requeueVacatedOnNewHome_machine]⟩
  · have hne : newCore ≠ c := fun h => hc (by simp [h])
    unfold requeueVacatedOnNewHome
    split
    · split
      · simp only [SchedulerState.markReschedulePendingOnCore_runQueueOnCore,
          SystemState.runEnqueueOnCore_scheduler]
        split
        · simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne]
        · rfl
      · rfl
    · rfl
  all_goals (unfold requeueVacatedOnNewHome; split; (split <;> simp); rfl)

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
  obtain ⟨tcb, stSet, -, -, -, -, hSet, rfl, -⟩ :=
    setThreadCpuAffinityWithMigration_ok_shape hStep
  obtain ⟨hSched, hMach⟩ := setThreadCpuAffinity_scheduler_machine_eq _ stSet targetTid affinity hSet
  have hSetC : observableSlotsConfinedToCores (vacateForAffinityChange st targetTid
      (determineTargetCore st targetTid) (affinity.getD Concurrency.bootCoreId)) stSet [] :=
    ⟨fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hSched],
     fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hMach]⟩
  -- The mid-state after the (optional) replenishment migration. Written
  -- out rather than named: `set` cannot bind a `match` body here.
  have hRepl : observableSlotsConfinedToCores stSet
      (match tcb.schedContextBinding.scId? with
        | some scId => migrateSchedContextReplenishment stSet scId
            (determineTargetCore st targetTid) (affinity.getD Concurrency.bootCoreId)
        | none => stSet) [] := by
    cases tcb.schedContextBinding.scId? with
    | none => exact observableSlotsConfinedToCores_refl _ _
    | some scId => exact migrateSchedContextReplenishment_confinedToCores _ _ _ _
  refine ((((vacateForAffinityChange_confinedToCores _ _ _ _).append hSetC).append hRepl).append
    ((migrateRunQueueOnAffinityChange_confinedToCores _ _ _ _).append
      (requeueVacatedOnNewHome_confinedToCores _ _ _ _))).mono ?_
  intro c hc
  simp only [setThreadCpuAffinityWriteSet, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc ⊢
  by_cases h1 : c = determineTargetCore st targetTid
  · exact .inl h1
  · right; simp only [h1, false_or, or_false, or_self] at hc; exact hc

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
    by_cases hMem : ({ stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) } : SystemState).queuedOn
        (determineTargetCore { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) } boundTid) boundTid = true
    · rw [if_pos hMem]
      -- The re-key moves only the thread's TCB run-queue links (WS-ZA ZA4.5),
      -- which neither field reads.
      have hQ := (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks
        { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) }
        (determineTargetCore { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) } boundTid) boundTid
        { boundTcb with priority := ⟨priority⟩ }.boostedPriority)
      have hQt := (TCB.map_proj_eq_of_map_withoutRunLinks_eq (fun x => (x.cpuAffinity, x.ipcState))
        (hQ.getTcb? t)).trans (hW t)
      have hInvQ := SystemState.runRequeueOnCore_objects_invExt
        { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) }
        (determineTargetCore { stStored with objects := (stStored.objects.insert boundTid.toObjId
          (.tcb { boundTcb with priority := ⟨priority⟩ })) } boundTid) boundTid
        { boundTcb with priority := ⟨priority⟩ }.boostedPriority hInvW
      split
      · rename_i cur hCur _
        split
        · exact hQt
        · exact (insertTcb_tcbChainFields _ _ boundTid cur { cur with domain := ⟨domain⟩ }
            hInvQ (hRaw _ _ hCur) rfl rfl rfl t).trans hQt
      · exact hQt
    · rw [if_neg hMem]
      split
      · rename_i cur hCur _
        split
        · exact hW t
        · exact (insertTcb_tcbChainFields _ _ boundTid cur { cur with domain := ⟨domain⟩ }
            hInvW (hRaw _ _ hCur) rfl rfl rfl t).trans (hW t)
      · exact hW t

/-- After a configure's SchedContext store and propagation, the state keeps the
store invariant, every home core and every blocking edge of the pre-state:
neither write moves a home core or a blocking edge, and the key-change flag is
a scheduler write. -/
theorem configurePropagate_chainShape (st stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (b : Bool)
    (hInvStored : stStored.objects.invExt)
    (hGet : ∀ t, stStored.getTcb? t = st.getTcb? t) :
    (markKeyChangeFor (markCandidacyGainFor
        (SchedContextOps.schedContextConfigureBoundPropagate
          stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k).objects.invExt ∧
    (∀ t, determineTargetCore (markKeyChangeFor (markCandidacyGainFor
        (SchedContextOps.schedContextConfigureBoundPropagate
          stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k) t =
        determineTargetCore st t) ∧
    (∀ t, blockingServer (markKeyChangeFor (markCandidacyGainFor
        (SchedContextOps.schedContextConfigureBoundPropagate
          stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k) t =
        blockingServer st t) := by
  have hXInv : (markKeyChangeFor (markCandidacyGainFor
      (SchedContextOps.schedContextConfigureBoundPropagate
        stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k).objects.invExt := by
    rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]
    exact SchedContextOps.schedContextConfigureBoundPropagate_preserves_objects_invExt
      _ _ _ _ _ _ _ hInvStored
  obtain ⟨hH, hE⟩ := PriorityInheritance.chainShape_of_tcbFields _ st (fun t => by
    rw [SystemState.getTcb?_congr_at (st := SchedContextOps.schedContextConfigureBoundPropagate
        stStored scId boundTid boundTcb hBound priority domain)
        (st' := markKeyChangeFor (markCandidacyGainFor
          (SchedContextOps.schedContextConfigureBoundPropagate
            stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k)
        (tid := t) (by rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]), ← hGet t]
    exact schedContextConfigureBoundPropagate_tcbChainFields stStored scId boundTid boundTcb
      hBound priority domain hInvStored t)
  exact ⟨hXInv, hH, hE⟩

/-- After a configure's SchedContext store and propagation, the bound thread's
chain names the pre-state's cores (`configurePropagate_chainShape`). -/
theorem waiterChainWriteSet_configurePropagate (st stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (b : Bool) (ec : CoreId) (fuel : Nat)
    (hInvSt : st.objects.invExt) (hInvStored : stStored.objects.invExt)
    (hGet : ∀ t, stStored.getTcb? t = st.getTcb? t) :
    waiterChainWriteSet (markKeyChangeFor (markCandidacyGainFor
        (SchedContextOps.schedContextConfigureBoundPropagate
          stStored scId boundTid boundTcb hBound priority domain) boundTid b) boundTid k)
        boundTid ec fuel =
      waiterChainWriteSet st boundTid ec fuel :=
  have h := configurePropagate_chainShape st stStored scId boundTid boundTcb hBound priority
    domain k b hInvStored hGet
  PriorityInheritance.waiterChainWriteSet_congr _ st boundTid ec fuel h.1 hInvSt h.2.1 h.2.2

/-- WS-ZA ZA6.4: the configure's resume tail writes the bound thread's home core
alone: a removal or a placement there, and a reschedule flag, which is no
observable slot. -/
theorem configureResumeBound_confinedToCores (st : SystemState) (t : SeLe4n.ThreadId)
    (sc : SchedContext) :
    observableSlotsConfinedToCores st (SchedContextOps.configureResumeBound st t sc)
      [determineTargetCore st t] := by
  refine ⟨fun c hc => ?_, fun c _ => ?_, fun c _ => ?_, fun c _ => ?_, fun c _ => ?_,
    fun c _ => ?_⟩
  · have hne : determineTargetCore st t ≠ c := fun h => hc (by simp [h])
    unfold SchedContextOps.configureResumeBound
    dsimp only
    repeat' split
    all_goals simp only [SystemState.runEnqueueOnCore_scheduler,
      SystemState.runRemoveOnCore_scheduler, SystemState.markReschedulePendingOnCore_scheduler,
      SchedulerState.markReschedulePendingOnCore_runQueueOnCore]
    all_goals (try split) <;>
      simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne]
  all_goals
    unfold SchedContextOps.configureResumeBound
    dsimp only
    repeat' split
    all_goals try simp only [SystemState.runEnqueueOnCore_scheduler,
      SystemState.runRemoveOnCore_scheduler, SystemState.markReschedulePendingOnCore_scheduler]
    all_goals (try split) <;> simp

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

/-- WS-ZA ZA6.4: the release placement writes the release queues alone, so it
moves no observable slot on any core. -/
theorem releasePlace_confinedToCores (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st (st.releasePlace c s) [] :=
  have h := SystemState.releasePlace_releaseOnlyWrite st c s
  ⟨fun d _ => h.runQueueOnCore d, fun d _ => h.currentOnCore d,
    fun d _ => h.activeDomainOnCore d, fun d _ => h.domainTimeRemainingOnCore d,
    fun d _ => h.domainScheduleIndexOnCore d, fun d _ => by rw [h.machine]⟩

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
          obtain ⟨scP, hScP, -⟩ := (SchedContextOps.purgeReplenishment_agree st
            ⟨vScId.val.toNat⟩).getSchedContext?_some hSc
          have hScPRaw := (SystemState.getSchedContext?_eq_some_iff _
            (SeLe4n.SchedContextId.ofObjId vScId.val) scP).mp hScP
          have hInvP := SchedContextOps.purgeReplenishment_objects_invExt st ⟨vScId.val.toNat⟩ hObjInv
          split at hStep
          · -- no bound thread: no scheduling effect at all
            next hNone =>
            simp only [hNone]
            rw [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨-, hs⟩ := hStep
            subst hs
            exact observableSlotsConfinedToCores_trans
              (purgeReplenishment_confinedToCores st _)
              (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                (storeObject_scheduler_eq _ _ _ _ hStore)
                (storeObject_machine_eq _ _ _ _ hStore))
          · next boundTid hBound =>
            simp only [hBound]
            have hInvStored0 : stStored.objects.invExt :=
              -- Named again for the same reason: the store's pre-state is the
              -- post-replenish one, not `st`.
              -- `by exact` postpones these until `hStore` has fixed the
              -- pre-state; passed directly they pin it to `st` first.
              storeObject_preserves_objects_invExt (st' := stStored) (hStore := hStore)
                (hObjInv := by exact hInvP)
            -- The SchedContext store is not a migration, and the replenish write
            -- leaves `objects` alone, so the home core is already the pre-state's.
            have hHomeStored0 : ∀ x : SeLe4n.ThreadId,
                determineTargetCore stStored x = determineTargetCore st x := fun x => by
              -- The lemma's own conclusion names the store's pre-state — the
              -- post-replenish one. Ascribing the statement up front would pin
              -- that to `st` and the store hypothesis would stop matching, so it
              -- is elaborated unascribed and closed by defeq: the replenish
              -- write leaves `objects`, and `determineTargetCore` reads nothing
              -- else.
              have h := storeObject_schedContext_determineTargetCore_eq (x := x) (sc := scP)
                (hStore := hStore) (hPre := by exact hScPRaw) (hObjInv := by exact hInvP)
              exact h.trans (determineTargetCore_congr _ _ x
                (by rw [SchedContextOps.purgeReplenishment_getTcb?]))
            have hGetSt0 : ∀ t, stStored.getTcb? t = st.getTcb? t := fun t =>
              (storeObject_schedContextAt_getTcb?_eq
                (SchedContextOps.purgeReplenishment st ⟨vScId.val.toNat⟩)
                stStored (SeLe4n.SchedContextId.ofObjId vScId.val) scP _ (by exact hScP)
                (by exact hInvP) (by exact hStore) t).trans
                (SchedContextOps.purgeReplenishment_getTcb? st _ t)
            have hStoredConf0 : observableSlotsConfinedToCores st stStored [] :=
              observableSlotsConfinedToCores_trans
                (purgeReplenishment_confinedToCores st _)
                (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                  (storeObject_scheduler_eq _ _ _ _ hStore)
                  (storeObject_machine_eq _ _ _ _ hStore))
            -- WS-ZA ZA6.4: the release placement on the home core writes the
            -- release queue alone: no object a reading below sees, no slot.
            have hAgP := SystemState.releasePlace_agree stStored (determineTargetCore st boundTid)
              ⟨vScId.val.toNat⟩
            have hInvStored := SystemState.releasePlace_objects_invExt stStored
              (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩ hInvStored0
            have hGetSt : ∀ t, (stStored.releasePlace (determineTargetCore st boundTid)
                ⟨vScId.val.toNat⟩).getTcb? t = st.getTcb? t := fun t =>
              (hAgP.getTcb? t).trans (hGetSt0 t)
            have hHomeStored : ∀ x : SeLe4n.ThreadId,
                determineTargetCore (stStored.releasePlace (determineTargetCore st boundTid)
                  ⟨vScId.val.toNat⟩) x = determineTargetCore st x := fun x =>
              (determineTargetCore_congr _ _ x (by rw [hAgP.getTcb? x])).trans (hHomeStored0 x)
            have hStoredConf : observableSlotsConfinedToCores st
                (stStored.releasePlace (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩) [] :=
              observableSlotsConfinedToCores_trans hStoredConf0
                (releasePlace_confinedToCores _ _ _)
            clear hGetSt0 hHomeStored0 hStoredConf0 hInvStored0 hAgP
            generalize stStored.releasePlace (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩ =
              stPlaced at hStep hInvStored hGetSt hHomeStored hStoredConf
            split at hStep
            · next boundTcb hTcbStored _ =>
              have hTcbStoredRaw :
                  stPlaced.objects.get? boundTid.toObjId = some (.tcb boundTcb) := by
                simpa using (SystemState.getTcb?_eq_some_iff stPlaced boundTid boundTcb).mp
                  hTcbStored
              let boundTcb2 : TCB := { boundTcb with priority := ⟨priority⟩ }
              let boundObj : KernelObject := .tcb boundTcb2
              let stWithTcb : SystemState :=
                { stPlaced with objects := stPlaced.objects.insert boundTid.toObjId boundObj }
              have hHomeWith : determineTargetCore stWithTcb boundTid
                  = determineTargetCore st boundTid :=
                Eq.trans
                  (determineTargetCore_insert_tcb stPlaced stWithTcb boundTid boundTcb boundTcb2
                    hInvStored hTcbStoredRaw rfl rfl boundTid)
                  (hHomeStored boundTid)
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              -- The chain re-walk last: its cores are the pre-state chain's,
              -- because the store and the propagation move no home core and no
              -- blocking edge.
              -- WS-ZA ZA6.4: the resume tail runs after the re-walk, on the
              -- bound thread's home, which neither the propagation nor the
              -- re-walk moves.
              obtain ⟨hXInv, hHX, -⟩ := configurePropagate_chainShape st stPlaced _ boundTid
                boundTcb _ priority domain (effectiveSchedParams st boundTcb)
                (hasSufficientBudget st boundTcb) hInvStored hGetSt
              refine observableSlotsConfinedToCores_mono (fun c hc => by
                  rcases List.mem_append.mp hc with h | h
                  · exact h
                  · rw [List.mem_singleton] at h
                    rw [h, PriorityInheritance.repropagateFromWaiter_determineTargetCore _ _ _ _
                      hXInv, hHX]
                    simp)
                (observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_repropagate ?_
                    (waiterChainWriteSet_configurePropagate st stPlaced _ boundTid boundTcb _
                      priority domain _ _ _ _ hObjInv hInvStored hGetSt))
                  (configureResumeBound_confinedToCores _ boundTid _))
              unfold SchedContextOps.schedContextConfigureBoundPropagate
              -- The prefix common to every arm: replenish purge, the SC store
              -- and the release placement, none of which is confined-relevant.
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
                  -- flag write, which moves no slot; strip it first.  The
                  -- re-bucket alternative goes first in each group: a plain
                  -- `exact` against a link-write state unfolds it and runs out
                  -- of heartbeats instead of failing.
                  | (rw [markKeyChangeFor_runQueueOnCore, markCandidacyGainFor_runQueueOnCore]
                     first
                       | (rw [SystemState.runRequeueOnCore_runQueueOnCore_ne _ _ c _ _ hne]
                          exact hStoredConf.runQueue c hNil)
                       | exact hStoredConf.runQueue c hNil)
                  | (rw [markKeyChangeFor_currentOnCore, markCandidacyGainFor_currentOnCore]
                     first
                       | (rw [SystemState.runRequeueOnCore_currentOnCore]
                          exact hStoredConf.current c hNil)
                       | exact hStoredConf.current c hNil)
                  | (rw [markKeyChangeFor_activeDomainOnCore, markCandidacyGainFor_activeDomainOnCore]
                     first
                       | (rw [SystemState.runRequeueOnCore_activeDomainOnCore]
                          exact hStoredConf.activeDomain c hNil)
                       | exact hStoredConf.activeDomain c hNil)
                  | (rw [markKeyChangeFor_domainTimeRemainingOnCore, markCandidacyGainFor_domainTimeRemainingOnCore]
                     first
                       | (rw [SystemState.runRequeueOnCore_domainTimeRemainingOnCore]
                          exact hStoredConf.domainTimeRemaining c hNil)
                       | exact hStoredConf.domainTimeRemaining c hNil)
                  | (rw [markKeyChangeFor_domainScheduleIndexOnCore, markCandidacyGainFor_domainScheduleIndexOnCore]
                     first
                       | (rw [SystemState.runRequeueOnCore_domainScheduleIndexOnCore]
                          exact hStoredConf.domainScheduleIndex c hNil)
                       | exact hStoredConf.domainScheduleIndex c hNil)
                  | (rw [markKeyChangeFor_machine, markCandidacyGainFor_machine]
                     first
                       | (rw [SystemState.runRequeueOnCore_machine]; exact hStoredConf.regs c hNil)
                       | exact hStoredConf.regs c hNil)
                  -- arms that take the run-queue re-bucket but no flag
                  | (rw [SystemState.runRequeueOnCore_runQueueOnCore_ne _ _ c _ _ hne]
                     exact hStoredConf.runQueue c hNil)
                  | (rw [SystemState.runRequeueOnCore_currentOnCore]
                     exact hStoredConf.current c hNil)
                  | (rw [SystemState.runRequeueOnCore_activeDomainOnCore]
                     exact hStoredConf.activeDomain c hNil)
                  | (rw [SystemState.runRequeueOnCore_domainTimeRemainingOnCore]
                     exact hStoredConf.domainTimeRemaining c hNil)
                  | (rw [SystemState.runRequeueOnCore_domainScheduleIndexOnCore]
                     exact hStoredConf.domainScheduleIndex c hNil)
                  | (rw [SystemState.runRequeueOnCore_machine]; exact hStoredConf.regs c hNil)
                  -- arms that stop at `stPlaced` / `stWithTcb` (object writes only)
                  | exact hStoredConf.runQueue c hNil
                  | exact hStoredConf.current c hNil
                  | exact hStoredConf.activeDomain c hNil
                  | exact hStoredConf.domainTimeRemaining c hNil
                  | exact hStoredConf.domainScheduleIndex c hNil
                  | exact hStoredConf.regs c hNil
                  | rfl
            · -- the bound TCB vanished behind the store: no scheduling effect
              next hNoTcb =>
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              refine observableSlotsConfinedToCores_widen_any ?_
              exact hStoredConf
      · exact absurd hStep (by simp)
    · exact absurd hStep (by simp)

/-- WS-ZA ZA6.4 (**the live `.schedContextConfigure` bound**): a configure
through core `core`'s control writes no core outside the configure's write set
and, on a move, the affinity change's pair and the control's core
(`schedControlConfigureWriteSet`).  The move is bounded by
`setThreadCpuAffinityWithMigration_confinedToCores`, and the configure on the
moved state by `schedContextConfigure_confinedToCores`, whose write set read off
the moved state is the pre-state's or the control's core
(`schedContextConfigureWriteSet_of_move`). -/
theorem schedControlConfigure_confinedToCores (core : CoreId) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedControlConfigure core vScId budget period priority deadline
      domain st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedControlConfigureWriteSet st core vScId.val) := by
  rcases SchedContextOps.schedControlConfigure_ok_cases hStep with
    h | ⟨sc, t, stM, sgi, hSc, hB, hNe, hM, h⟩
  · exact observableSlotsConfinedToCores_mono
      (schedContextConfigureWriteSet_subset_schedControl st core vScId.val)
      (schedContextConfigure_confinedToCores vScId _ _ _ _ _ st st' hObjInv h)
  · rw [(schedControlConfigureWriteSet_of_move hSc hB hNe).1]
    have hInvM := setThreadCpuAffinityWithMigration_preserves_objects_invExt _ _ _ _ hObjInv _ hM
    refine observableSlotsConfinedToCores_mono (fun d hd => ?_)
      (observableSlotsConfinedToCores_trans
        (setThreadCpuAffinityWithMigration_confinedToCores st stM t (some core) core sgi hObjInv hM)
        (schedContextConfigure_confinedToCores vScId _ _ _ _ _ stM st' hInvM h))
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append.mpr (.inl hd)
    · rcases schedContextConfigureWriteSet_of_move hObjInv hSc hB hM d hd with e | e
      · exact List.mem_append.mpr (.inr (e ▸ List.mem_cons_self ..))
      · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ e))

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

/-- WS-ZA ZA6.9 (**the live `.schedContextConsumed` bound**): the Consumed
invocation writes no core's observable slot — `setConsumed` writes a context's
count and its caller's saved registers, both in the object store. -/
theorem schedContextConsumedOnCore_confinedToCores (s : SeLe4n.SchedContextId)
    (executingCore : CoreId) (st st' : SystemState)
    (hStep : schedContextConsumedOnCore s executingCore st = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok hStep
  rw [SystemState.setConsumed_eq_objects]
  exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq rfl rfl

end SeLe4n.Kernel
