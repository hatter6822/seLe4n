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
          | true => rw [hL] at hStep; simp at hStep
        simp only [hNoLive, Bool.false_eq_true, if_false] at hStep
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
              { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0 }
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
            -- **WS-RR RR8.12 Cut B2 (`v0.35.182`)**: two arms since WS-SX SX6.4
            -- — the placement of a parked runnable thread and the identity.  The
            -- placement writes `setRunQueueOnCore bindHome`, the same core the
            -- write set names, so each clause is one lemma and then `rfl`.
            · have hne : determineTargetCore st vThreadId.val ≠ c := fun h => hc h.symm
              -- KSC-1: the placement arm raises the home core's flag, which moves
              -- no slot.  WS-ZA ZA4.5: it writes through the thread's TCB
              -- run-queue links, on the home core only.
              refine (SystemState.releaseOnlyWrite.runQueueOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              split
              · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_runQueueOnCore,
                  SystemState.runEnqueueOnCore_runQueueOnCore_ne _ _ c _ _ (hHome ▸ hne)]
              · rfl
            · refine (SystemState.releaseOnlyWrite.currentOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              split
              · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_currentOnCore,
                  SystemState.runEnqueueOnCore_currentOnCore]
              · rfl
            · refine (SystemState.releaseOnlyWrite.activeDomainOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              split
              · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_activeDomainOnCore,
                  SystemState.runEnqueueOnCore_activeDomainOnCore]
              · rfl
            · refine (SystemState.releaseOnlyWrite.domainTimeRemainingOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              split
              · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_domainTimeRemainingOnCore,
                  SystemState.runEnqueueOnCore_domainTimeRemainingOnCore]
              · rfl
            · refine (SystemState.releaseOnlyWrite.domainScheduleIndexOnCore (SystemState.releasePlace_releaseOnlyWrite _ _ _) c).trans ?_
              split
              · rw [SystemState.markReschedulePendingOnCore, SchedulerState.markReschedulePendingOnCore_domainScheduleIndexOnCore,
                  SystemState.runEnqueueOnCore_domainScheduleIndexOnCore]
              · rfl
            · -- registers: untouched on both arms.
              refine (congrArg (fun m => m.regsOnCore c)
                (SystemState.releaseOnlyWrite.machine (SystemState.releasePlace_releaseOnlyWrite _ _ _))).trans ?_
              split
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
  by_cases h : tid.toObjId = t.toObjId
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

/-- WS-ZA ZA6.4: the release placement writes the release queues alone, so it
moves no observable slot on any core. -/
theorem releasePlace_confinedToCores (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st (st.releasePlace c s) [] :=
  have h := SystemState.releasePlace_releaseOnlyWrite st c s
  ⟨fun d _ => h.runQueueOnCore d, fun d _ => h.currentOnCore d,
    fun d _ => h.activeDomainOnCore d, fun d _ => h.domainTimeRemainingOnCore d,
    fun d _ => h.domainScheduleIndexOnCore d, fun d _ => by rw [h.machine]⟩

/-- SM8.B.2 (**the live `.schedContextConfigure` bound**): a configure writes no
core outside its subject's home core (`schedContextConfigureWriteSet`).

The replenish-queue purge and the release placement are outside the six
observable slots, so they are per-core silent even on the core they name; the
`storeObject` of the reconfigured SchedContext is an object write
(`storeObject_schedContext_determineTargetCore_eq` keeps every home core).  The
`boundThread = none` and `getTcb? = none` arms perform no scheduling work at all.
On the bound arm the candidacy mark is a reschedule flag, and the resume tail
(`configureResumeBound_confinedToCores`) writes the bound thread's home core
alone.  WS-SX SX6.4: the configure propagates nothing to the thread, so it
re-walks no inheritance chain. -/
theorem schedContextConfigure_confinedToCores (vScId : SeLe4n.ValidObjId)
    (budget period : Nat) (extraRefills badge flags : UInt64) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period extraRefills badge flags st
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
            · next boundTcb hTcbStored =>
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              -- The candidacy mark is a reschedule flag, no observable slot; the
              -- resume tail writes the bound thread's home core alone, which
              -- neither the store nor the release placement moves.
              have hMark : observableSlotsConfinedToCores st
                  (markCandidacyGainFor stPlaced boundTid (hasSufficientBudget st boundTcb)) [] :=
                ⟨fun c hc => (markCandidacyGainFor_runQueueOnCore _ _ _ _).trans
                    (hStoredConf.runQueue c hc),
                  fun c hc => (markCandidacyGainFor_currentOnCore _ _ _ _).trans
                    (hStoredConf.current c hc),
                  fun c hc => (markCandidacyGainFor_activeDomainOnCore _ _ _ _).trans
                    (hStoredConf.activeDomain c hc),
                  fun c hc => (markCandidacyGainFor_domainTimeRemainingOnCore _ _ _ _).trans
                    (hStoredConf.domainTimeRemaining c hc),
                  fun c hc => (markCandidacyGainFor_domainScheduleIndexOnCore _ _ _ _).trans
                    (hStoredConf.domainScheduleIndex c hc),
                  fun c hc => by rw [markCandidacyGainFor_machine]; exact hStoredConf.regs c hc⟩
              refine observableSlotsConfinedToCores_mono (fun c hc => ?_)
                (observableSlotsConfinedToCores_trans hMark
                  (configureResumeBound_confinedToCores _ boundTid _))
              simp only [List.nil_append, List.mem_singleton] at hc
              rw [hc, determineTargetCore_congr_getTcb?
                (markCandidacyGainFor stPlaced boundTid (hasSufficientBudget st boundTcb))
                stPlaced boundTid (SystemState.getTcb?_congr_at (st := stPlaced)
                  (by rw [markCandidacyGainFor_objects])),
                hHomeStored]
              simp
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
    (budget period : Nat) (extraRefills badge flags : UInt64) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedControlConfigure core vScId budget period extraRefills badge flags
       st = .ok ((), st')) :
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

/-- **The live `.schedContextUnbind` bound**: seL4-MCS's `SchedContext_Unbind`
writes the thread unbind's cores, and the notification unbind writes no
scheduler slot or machine state. -/
theorem schedContextUnbindAllOnCore_confinedToCores (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindAllOnCore vScId executingCore st
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (schedContextUnbindOnCoreWriteSet st vScId.val executingCore) := by
  have hN : ∀ X : SystemState, observableSlotsConfinedToCores X
      (unbindSchedContextNotification X (SeLe4n.SchedContextId.ofObjId vScId.val)) [] :=
    fun X => observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (unbindSchedContextNotification_scheduler _ _) (unbindSchedContextNotification_machine _ _)
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok hStep
  · obtain ⟨rfl, -⟩ := hU
    exact observableSlotsConfinedToCores_mono (fun _ h => by simp at h) (hN _)
  · exact observableSlotsConfinedToCores_mono (fun _ h => by simpa using h)
      (observableSlotsConfinedToCores_trans
        (schedContextUnbindOnCore_confinedToCores vScId executingCore st stU sgi hU) (hN stU))

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

/-! ### The yieldTo invocation (WS-ZA ZA6.29) -/

theorem runRemoveOnCore_confinedToCores (S : SystemState) (h : CoreId) (x : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores S (S.runRemoveOnCore h x) [h] :=
  ⟨fun c hc => SystemState.runRemoveOnCore_runQueueOnCore_ne S h c x (fun e => hc (by simp [e])),
   fun c _ => by simp, fun c _ => by simp, fun c _ => by simp, fun c _ => by simp,
   fun c _ => by simp⟩

theorem runDescheduleOnCore_confinedToCores (S : SystemState) (h : CoreId) (x : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores S (S.runDescheduleOnCore h x) [h] := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c _ => by simp, fun c _ => by simp,
    fun c _ => by simp, fun c _ => ?_⟩
  · have hne : h ≠ c := fun e => hc (by simp [e])
    simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne]
  · rw [SystemState.runDescheduleOnCore_currentOnCore, if_neg (fun e => hc (by simp [e.1]))]
  · unfold SystemState.runDescheduleOnCore
    simp only [SystemState.runRemoveOnCore_machine]

theorem runEnqueueHeadOnCore_confinedToCores (S : SystemState) (h : CoreId) (x : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    observableSlotsConfinedToCores S (S.runEnqueueHeadOnCore h x p) [h] := by
  refine ⟨fun c hc => SystemState.runEnqueueHeadOnCore_runQueueOnCore_ne S h c x p
      (fun e => hc (by simp [e])),
    fun c _ => SystemState.runEnqueueHeadOnCore_currentOnCore _ _ _ _ _, ?_, ?_, ?_,
    fun c _ => by simp⟩
  all_goals intro c _; rw [SystemState.runEnqueueHeadOnCore_scheduler]; split <;> simp

/-- **The unlinked branch's requeue** writes the target's home core alone. -/
theorem yieldToRequeue_confinedToCores (S : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    observableSlotsConfinedToCores S (SchedContextOps.yieldToRequeue S home t p) [home] := by
  unfold SchedContextOps.yieldToRequeue
  split
  · exact observableSlotsConfinedToCores_refl S _
  · have h := observableSlotsConfinedToCores_trans (runRemoveOnCore_confinedToCores S home t)
      (runEnqueueHeadOnCore_confinedToCores _ home t p)
    refine observableSlotsConfinedToCores_mono (fun c hc => by simpa using hc)
      (observableSlotsConfinedToCores_then_flagOnly h ?_)
    exact ⟨fun _ _ => by simp, fun _ _ => by simp, fun _ _ => by simp, fun _ _ => by simp,
      fun _ _ => by simp, fun _ _ => by simp⟩

/-- **The linked branch** writes the executing core alone: the link is an
object write, and the dequeues, the head enqueues and the scheduling point are
core `c`'s. -/
theorem yieldToLink_confinedToCores (S : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (caller t : SeLe4n.ThreadId) (pC pT : SeLe4n.Priority) :
    observableSlotsConfinedToCores S (SchedContextOps.yieldToLink S c s caller t pC pT) [c] := by
  have h0 : observableSlotsConfinedToCores S (setYieldLink S s caller) [] :=
    observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (SystemState.setYieldLink_scheduler S s caller) (SystemState.setYieldLink_machine S s caller)
  have h1 := observableSlotsConfinedToCores_trans
    (observableSlotsConfinedToCores_trans
      (observableSlotsConfinedToCores_trans
        (observableSlotsConfinedToCores_trans
          (runRemoveOnCore_confinedToCores (setYieldLink S s caller) c t)
          (runDescheduleOnCore_confinedToCores _ c caller))
        (runEnqueueHeadOnCore_confinedToCores _ c caller pC))
      (runEnqueueHeadOnCore_confinedToCores _ c t pT))
    (handleRescheduleSgiOnCore_confinedToCores _ _ c
      (SchedContextOps.yieldToLink_sgi S c s caller t pC pT))
  exact observableSlotsConfinedToCores_mono (fun d hd => by simpa using hd)
    (observableSlotsConfinedToCores_widen_cons h0
      (observableSlotsConfinedToCores_mono (fun d hd => by simpa using hd) h1))

/-- The yieldTo resolves its thread's home core on the completion's state,
which is the pre-state's: the completion writes yield links, a consumed count
and return registers, never an affinity. -/
theorem determineTargetCore_completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    determineTargetCore (completeYieldFrom st s) t = determineTargetCore st t :=
  determineTargetCore_congr _ _ t
    ((SystemState.completeYieldFrom_objectsAgreeOffYield st s hInv).getTcb?_map (·.cpuAffinity)
      (fun _ => rfl) t)

/-- A yieldTo that succeeds names its context's bound thread. -/
theorem schedContextYieldToOnCore_boundThread {scObjId : SeLe4n.ObjId} {e : CoreId}
    {st st' : SystemState}
    (hStep : SchedContextOps.schedContextYieldToOnCore (SeLe4n.SchedContextId.ofObjId scObjId) e st
      = .ok st') :
    ∃ caller t, SchedContextOps.schedContextBoundThread? st scObjId = some t ∧
      st' = SchedContextOps.yieldToBound st e (SeLe4n.SchedContextId.ofObjId scObjId) caller t := by
  obtain ⟨caller, sc, t, -, -, -, hS, hk, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok hStep
  refine ⟨caller, t, ?_, rfl⟩
  unfold SchedContextOps.schedContextBoundThread?
  rw [hS]
  simp [SchedContext.boundThread, hk, SeLe4n.ThreadId.ofOptCode]

/-- WS-ZA ZA6.29 (**the live `.schedContextYieldTo` bound**): a yieldTo writes
no core outside the executing core and its context's thread's home core
(`schedContextYieldToWriteSet`).  The completion, the resume and `setConsumed`
write no observable slot; the requeue writes the home core; the link writes
the executing core. -/
theorem schedContextYieldToOnCore_confinedToCores (scObjId : SeLe4n.ObjId) (e : CoreId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextYieldToOnCore (SeLe4n.SchedContextId.ofObjId scObjId) e st
      = .ok st') :
    observableSlotsConfinedToCores st st' (schedContextYieldToWriteSet st scObjId e) := by
  obtain ⟨caller, t, hB, rfl⟩ := schedContextYieldToOnCore_boundThread hStep
  unfold schedContextYieldToWriteSet
  rw [hB]
  dsimp only
  rw [← determineTargetCore_completeYieldFrom st (SeLe4n.SchedContextId.ofObjId scObjId) t hInv]
  generalize SeLe4n.SchedContextId.ofObjId scObjId = s
  unfold SchedContextOps.yieldToBound
  dsimp only
  have hPrefix : observableSlotsConfinedToCores st
      ((completeYieldFrom st s).releasePlace (determineTargetCore (completeYieldFrom st s) t) s) [] :=
    List.nil_append [] ▸ observableSlotsConfinedToCores_trans
      (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (SystemState.completeYieldFrom_scheduler st s) (by rw [SystemState.completeYieldFrom_eq_objects]))
      (releasePlace_confinedToCores _ _ s)
  generalize determineTargetCore (completeYieldFrom st s) t = home at hPrefix ⊢
  generalize (completeYieldFrom st s).releasePlace home s = st2 at hPrefix ⊢
  have hSet : ∀ X : SystemState, observableSlotsConfinedToCores st2 X [e, home] →
      observableSlotsConfinedToCores st (setConsumed X s caller true) [e, home] := fun X hX =>
    observableSlotsConfinedToCores_then_flagOnly
      (observableSlotsConfinedToCores_mono (fun d hd => by simpa using hd)
        (observableSlotsConfinedToCores_trans hPrefix hX))
      (by rw [SystemState.setConsumed_eq_objects]
          exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq rfl rfl)
  have hNone := hSet st2 (observableSlotsConfinedToCores_refl st2 _)
  have hLink : ∀ pC pT, observableSlotsConfinedToCores st
      (SchedContextOps.yieldToLink st2 e s caller t pC pT) [e, home] := fun pC pT =>
    observableSlotsConfinedToCores_mono
      (fun d hd => by simp only [List.nil_append, List.mem_singleton] at hd; simp [hd])
      (observableSlotsConfinedToCores_trans hPrefix (yieldToLink_confinedToCores st2 e s caller t pC pT))
  split
  · exact hNone
  · split
    · exact hNone
    · split
      · exact hNone
      · split
        · split
          · exact hSet _ (observableSlotsConfinedToCores_mono (fun d hd => by simp [List.mem_singleton.mp hd])
              (yieldToRequeue_confinedToCores st2 home t _))
          · exact hLink _ _
        · exact hNone

end SeLe4n.Kernel
