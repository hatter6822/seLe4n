-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbsInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
import SeLe4n.Kernel.ReschedulePendingArms.Tick
import SeLe4n.Kernel.SchedContext.BindingAffinity
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.SyscallSchedFootprint
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks
-- PR #889 review round 20: the declared-core scenario reads the RPi5 and
-- single-core simulation bindings, so the platform contracts come in here.
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.Sim.Contract

/-!
# WS-SM SM5.H — Per-core CBS test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.H
"Per-core CBS" deliverable (WS-SM SM5 §3.8, §5).

* **§1 Surface anchors** — every public SM5.H symbol resolves at elaboration time
  (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (validity / pipeline
  / affinity preservation by `replenishOnCore`, the migration's structural + validity
  facts, the headline restoration `schedContextMigration_consistent`, the per-core CBS
  invariant bundle, and the CBS budget bounds) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cbs_suite` exercises the actual
  `replenishOnCore` / `migrateSchedContextReplenishment` /
  `setThreadCpuAffinityWithMigration` computations on concrete CBS fixtures (the
  SM5.H.8 scenarios): per-core replenishment scheduling, the cross-core SchedContext
  migration (entries genuinely move), the affinity-change-with-migration composite,
  size-consistency preservation, the CBS budget bounds, and the inventory partition
  counts.
* **§4 Binding lifecycle** (WS-RR bind/unbind affinity closure) — the
  `SchedContext/BindingAffinity.lean` surface: the orphan-freedom invariant and
  the `schedContextBind` / `schedContextUnbind{,OnCore}` preservation theorems
  anchor and apply at elaboration time, and the runtime scenarios drive a full
  bind → replenish → unbind cycle, the unbind's home-core purge, the wrapper's
  no-running-core arm, and the dead-TCB arm's purge of the core its context is
  linked on, on concrete
  fixtures.
-/

namespace SeLe4n.Testing.SmpCbs

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.H public symbol resolves
-- ============================================================================

-- SM5.H.1 / .5 the affinity-consistency invariant:
-- WS-RR RR7.30: the unpinned half of the declared-core bound.
#check @determineTargetCore_lt_declaredCoreCount
#check @replenishQueueAffinityConsistentOnCore
#check @replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistent_smp_at
#check @default_replenishQueueAffinityConsistentOnCore
#check @default_replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistentOnCore_frame

-- SM5.H.2 the replenishOnCore primitive + frames:
#check @replenishOnCore
#check @replenishOnCore_machine
#check @replenishOnCore_getTcb?
#check @replenishOnCore_determineTargetCore
#check @replenishOnCore_replenishQueueOnCore_self
#check @replenishOnCore_replenishQueueOnCore_ne
#check @replenishOnCore_runQueueOnCore
#check @replenishOnCore_currentOnCore
#check @replenishOnCore_activeDomainOnCore
#check @replenishOnCore_mem

-- SM5.H.3 / .6 / .5 replenishOnCore preservation:
#check @replenishOnCore_preserves_replenishQueueValidOnCore
#check @replenishOnCore_preserves_replenishQueueValidOnCore_ne
#check @replenishOnCore_preserves_replenishQueueValid_smp
#check @replenishOnCore_preserves_replenishmentPipelineOrderOnCore
#check @replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne
#check @replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore

-- SM5.H.4 the migration operation + frames + structural:
#check @migrateSchedContextReplenishment
#check @migrateSchedContextReplenishment_noop
#check @migrateSchedContextReplenishment_agree
#check @migrateSchedContextReplenishment_machine
#check @migrateSchedContextReplenishment_getSchedContext?
#check @migrateSchedContextReplenishment_determineTargetCore
#check @migrateSchedContextReplenishment_replenishQueueOnCore_to
#check @migrateSchedContextReplenishment_replenishQueueOnCore_from
#check @migrateSchedContextReplenishment_replenishQueueOnCore_other
#check @migrateSchedContextReplenishment_fromCore_excludes_scId
#check @migrateSchedContextReplenishment_mem_toCore
#check @migrateSchedContextReplenishment_preserves_replenishQueueValid_smp
#check @migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp

-- SM5.H.4 affinity-write helpers:
#check @determineTargetCore_congr_getTcb?
#check @setThreadCpuAffinity_determineTargetCore_ne
#check @setThreadCpuAffinity_getSchedContext?

-- SM5.H.4 / .5 migration affinity behaviour + composite + headline:
#check @migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
#check @migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
#check @migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
#check @setThreadCpuAffinityWithMigration
#check @setThreadCpuAffinityWithMigration_error_of_no_tcb
#check @setThreadCpuAffinityWithMigration_bound_state_eq
#check @setThreadCpuAffinityWithMigration_unbound_state_eq
#check @schedContextMigration_consistent

-- SM5.H.7 per-core CBS invariant + budget accounting:
#check @perCoreCbsInvariant
#check @default_perCoreCbsInvariant
#check @replenishOnCore_preserves_perCoreCbsInvariant
#check @SchedContext.chargeBudget_refillTotal
#check @SchedContext.releaseReadyHead_refillTotal
#check @SchedContext.chargeBudget_refillsFit

-- SM5.H.4 (§6c/§11) the full-thread-migration run-queue move + scheduler preservation:
#check @migrateRunQueueOnAffinityChange
#check @migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed
#check @migrateSchedContextReplenishment_runQueueOnCore
#check @setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed
#check @migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore

-- SM5.H.4 (§9) object-store invariant preservation:
#check @replenishOnCore_preserves_objects_invExt
#check @setThreadCpuAffinityWithMigration_preserves_objects_invExt

-- SM5.H.4 (§12 B7) the binding-uniqueness grounding + grounded headline:
#check @schedContextBindingConsistent_boundThread_unique
#check @schedContextMigration_consistent_of_bindingConsistent

-- SM5.H.4 (§13 A5) the composite per-core CBS invariant preservation:
#check @setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp
#check @setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp
#check @setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp

-- SM5.H.4 (§10) the cross-domain lock-set footprints:
#check @replenishOnCoreLockSet
#check @migrateSchedContextReplenishmentLockSet
#check @migrateRunQueueOnAffinityChangeLockSet
#check @setThreadCpuAffinityWithMigrationLockSet
#check @setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le
-- #5 (Codex P2): the migration footprint's keys are ascending UNCONDITIONALLY (the
-- per-core queue locks are sorted lower-core-first), so a reverse-direction migration
-- (e.g. core 1 → boot core 0) acquires in canonical order — no deadlock.
#check @setThreadCpuAffinityWithMigrationLockSet_pairwise_le
example (oldCore newCore : SeLe4n.Kernel.Concurrency.CoreId) :
    ((setThreadCpuAffinityWithMigrationLockSet oldCore newCore).map (·.1)).Pairwise (· ≤ ·) :=
  setThreadCpuAffinityWithMigrationLockSet_pairwise_le oldCore newCore
-- #2 (Codex P1): rebinding a thread RUNNING on a core its new affinity forbids is
-- rejected fail-closed (`.threadOnDifferentCore`).
#check @setThreadCpuAffinityWithMigration_rejects_running_off_home
-- PR #889 review round 20: an affinity naming a PE the platform does not
-- declare is refused fail-closed (`.invalidArgument`), and unpinning is not.
#check @setThreadCpuAffinityWithMigration_rejects_undeclared_core
#check @setThreadCpuAffinityWithMigration_none_passes_declared_check

-- SM5.H.4 (D15 composite, §17) the full affinity composite preserves SM4.C
-- run-queue↔budget consistency on every core:
#check @setThreadCpuAffinity_getTcb?_self
#check @setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore
#check @migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore
#check @setThreadCpuAffinityWithMigration_preserves_schedContextRunQueueConsistent_perCore
-- SM5.H.4 (B8/SGI + C10, §18) the composite's cross-core SGI characterisation:
#check @setThreadCpuAffinityWithMigration_sgi_eq
#check @setThreadCpuAffinityWithMigration_no_sgi_if_local
#check @setThreadCpuAffinityWithMigration_emits_reschedule_of_remote_runnable
#check @setThreadCpuAffinityWithMigration_sgi_happensBefore

-- SM5.H.2 (A2/A4, §14) the live-tick CBS bridge:
#check @timeoutBlockedThreads_replenishQueueOnCore
#check @timerTickBudgetOnCore_bound_exhausted_replenish_eq
#check @timerTickBudgetOnCore_preserves_replenishQueueValidOnCore

-- SM5.H.4 (C10, §15) the migration's cross-core memory-model HB:
#check @affinityMigrationOrdering_synchronizesWith
#check @affinityMigrationOrdering_happensBefore

-- SM5.H.4 the `tcbSetAffinity` syscall wiring (production-reached):
#check @setThreadCpuAffinityOp
#check @decodeAffinity
#check @lockSet_tcbSetAffinity
#check @lockSet_consistent_tcbSetAffinity

-- SM5.H inventory:
#check @perCoreCbsTheorems
#check @perCoreCbsTheorems_count
#check @perCoreCbsTheorems_partition_sum
#check @perCoreCbsTheorems_identifiers_nodup
#check @perCoreCbsTheorems_lockSet_count
#check @perCoreCbsTheorems_liveTick_count
#check @perCoreCbsTheorems_memoryModel_count

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- SM5.H.3: scheduling a replenishment preserves replenish-queue validity.
example (st : SystemState) (c : CoreId) (scId : SchedContextId)
    (hValid : replenishQueueValidOnCore st c) :
    replenishQueueValidOnCore (replenishOnCore st c scId) c :=
  replenishOnCore_preserves_replenishQueueValidOnCore st c scId hValid

-- SM5.H.6: scheduling a future replenishment preserves pipeline order.
example (st : SystemState) (c : CoreId) (scId : SchedContextId)
    (hPipeline : replenishmentPipelineOrderOnCore st c)
    (hFuture : ∀ t, st.releaseKeyOf scId = some t → t > st.machine.timer) :
    replenishmentPipelineOrderOnCore (replenishOnCore st c scId) c :=
  replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c scId hPipeline hFuture

-- SM5.H.5: scheduling a home-core replenishment preserves affinity consistency.
example (st : SystemState) (c : CoreId) (scId : SchedContextId)
    (hCons : replenishQueueAffinityConsistentOnCore st c)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    replenishQueueAffinityConsistentOnCore (replenishOnCore st c scId) c :=
  replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore st c scId hCons hTarget

-- SM5.H.4: the migration preserves replenish-queue validity on every core.
example (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId)
    (hValid : ∀ c, replenishQueueValidOnCore st c) (c : CoreId) :
    replenishQueueValidOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c :=
  migrateSchedContextReplenishment_preserves_replenishQueueValid_smp st scId fromCore toCore hValid c

-- SM5.H.4: after a migration, no scId entry remains on the source core.
example (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId)
    (h : fromCore ≠ toCore) (t : Nat) :
    (scId, t) ∉ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore).entries :=
  migrateSchedContextReplenishment_fromCore_excludes_scId st scId fromCore toCore h t

-- SM5.H.4 headline: the affinity-change + migration composite RESTORES affinity
-- consistency on every core (given the 1:1 binding + pre-state consistency).
example (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) (hBound : sc.boundThread = some targetTid)
    (hUnique : ∀ scId'' sc'', st.getSchedContext? scId'' = some sc'' →
      sc''.boundThread = some targetTid → scId'' = scId)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    replenishQueueAffinityConsistent_smp st'.1 :=
  schedContextMigration_consistent st targetTid affinity executingCore tcb scId sc st'
    hTcb hInv hBind hSc hBound hUnique hCons hStep

-- SM5.H.4 (§12 B7) grounded headline: hUnique is DISCHARGED from the live
-- `schedContextBindingConsistent` invariant.
example (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) (hBound : sc.boundThread = some targetTid)
    (hBindCons : schedContextBindingConsistent st)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    replenishQueueAffinityConsistent_smp st'.1 :=
  schedContextMigration_consistent_of_bindingConsistent st targetTid affinity executingCore
    tcb scId sc st' hTcb hInv hBind hSc hBound hBindCons hCons hStep

-- SM5.H.4 (§13 A5): the composite preserves the FULL per-core CBS invariant on every core.
example (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) (hBound : sc.boundThread = some targetTid)
    (hBindCons : schedContextBindingConsistent st)
    (hCbs : ∀ c, perCoreCbsInvariant st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    ∀ c, perCoreCbsInvariant st'.1 c :=
  setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp st targetTid affinity
    executingCore tcb scId sc st' hTcb hInv hBind hSc hBound hBindCons hCbs hStep

-- SM5.H.4 (§11): the run-queue migration preserves run-queue well-formedness on every core.
example (st : SystemState) (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId)
    (h : runQueueOnCoreWellFormed st.scheduler c') :
    runQueueOnCoreWellFormed (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler c' :=
  migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed st tid fromCore toCore c' h

-- SM5.H.4 (§16 D15): the run-queue migration preserves SM4.C run-queue↔budget consistency.
example (st : SystemState) (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId)
    (hAll : ∀ c, schedContextRunQueueConsistent_perCore st c) (hR : st.runQueueRefined) :
    schedContextRunQueueConsistent_perCore
      (migrateRunQueueOnAffinityChange st tid fromCore toCore) c' :=
  migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore
    st tid fromCore toCore c' hAll hR

-- SM5.H.2 (A4): the live per-core budget tick preserves replenish-queue validity.
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (b : Bool) (c' : CoreId)
    (hValid : ∀ c'', replenishQueueValidOnCore st c'')
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) :
    replenishQueueValidOnCore st' c' :=
  timerTickBudgetOnCore_preserves_replenishQueueValidOnCore st c tid tcb st' b c' hValid hStep

-- SM5.H.7: scheduling maintains the aggregate per-core CBS invariant.
example (st : SystemState) (c : CoreId) (scId : SchedContextId)
    (hInv : perCoreCbsInvariant st c)
    (hFuture : ∀ t, st.releaseKeyOf scId = some t → t > st.machine.timer)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    perCoreCbsInvariant (replenishOnCore st c scId) c :=
  replenishOnCore_preserves_perCoreCbsInvariant st c scId hInv hFuture hTarget

-- SM5.H.7, WS-ZA ZA6.4: a charge keeps the refill total (unconditional).
example (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).refillTotal = sc.refillTotal :=
  sc.chargeBudget_refillTotal start usage now

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.H.8 cross-core CBS scenarios
-- ============================================================================

private def core1 : CoreId := ⟨1, by decide⟩
private def scId0 : SchedContextId := SchedContextId.ofNat 200
private def tid0 : SeLe4n.ThreadId := ThreadId.ofNat 100

/-- A CBS SchedContext bound to thread `tid0`, budget 100, period 1000, remaining 50. -/
private def sc0 : SchedContext :=
  { scId := scId0, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨5⟩, deadline := ⟨0⟩,
    domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThreadCode := SeLe4n.ThreadId.optCode (some tid0), isActive := true,
    refillTailCount := 0 }

/-- `tid0`'s TCB, bound to `sc0` and pinned (`cpuAffinity`) to core 1. -/
private def tcb0 : TCB :=
  { tid := tid0, priority := ⟨5⟩, domain := ⟨0⟩, spaceCells := SeLe4n.Model.TCB.spaceCellsOf (ObjId.ofNat 0) (ObjId.ofNat 0), ipcBuffer := SeLe4n.VAddr.ofNat 0,
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId0), scBindingOwnerCode := 0, cpuAffinity := some core1 }

/-- `sc0` + `tcb0` with `sc0`'s head holding budget: tid0 is runnable, so its
context is on no release queue (seL4-MCS queues only a context whose head is used
up). -/
private def stCbsRunnable : SystemState :=
  ((BootstrapBuilder.empty.withObject scId0.toObjId (.schedContext sc0)).withObject
    tid0.toObjId (.tcb tcb0)).build

/-- A CBS state: `sc0` + `tcb0` in the object store; core 1's replenish queue holds
`scId0`'s pending replenishment, its head used up (eligible at tick 5000); machine timer = 0.  This is
affinity-consistent (`scId0` is homed on core 1 — `tcb0.cpuAffinity = some core1`). -/
private def stCbs : SystemState :=
  withReleaseEntryOnCore stCbsRunnable core1 scId0 5000

/-- Core `c`'s release queue is count-consistent (Bool form for runtime
assertions): the walk along the contexts' release links from the core's head
reads as many entries as the core's count records. -/
private def sizeConsistentB (st : SystemState) (c : CoreId) : Bool :=
  (st.releaseEntriesOn c).length == st.scheduler.releaseCountOnCore c

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1 SM5.H.2: `replenishOnCore` places a context on the target core only, at
its earliest pending refill (WS-ZA ZA6.3: one entry per context, keyed by the
refill, as seL4-MCS's release queue is). -/
private def runReplenishScenarios : IO Unit := do
  IO.println "--- §3.1 SM5.H.2 replenishOnCore scheduling ---"
  let base := ((BootstrapBuilder.empty.withObject scId0.toObjId (.schedContext
      { sc0 with budgetRemaining := ⟨0⟩, refillHeadPresent := true,
                 refillHeadAmount := 50, refillHeadEligibleAt := 6000 })).withObject tid0.toObjId (.tcb tcb0)).build
  let st' := replenishOnCore base core1 scId0
  assertBool "replenishOnCore queues scId0 on core 1 at its refill's release time (6000)"
    (st'.releaseEntriesOn core1 == [(scId0, 6000)])
  assertBool "placing it again keeps one entry: a context is on its queue once"
    ((replenishOnCore st' core1 scId0).releaseEntriesOn core1 == [(scId0, 6000)])
  assertBool "a context already queued on core 1 is not placed on another core's queue"
    ((replenishOnCore st' bootCoreId scId0).releaseEntriesOn bootCoreId == [] &&
      (replenishOnCore st' bootCoreId scId0).releaseEntriesOn core1 == [(scId0, 6000)])
  assertBool "replenishOnCore leaves the boot core's replenish queue empty"
    ((st'.releaseEntriesOn bootCoreId).isEmpty)
  assertBool "replenishOnCore keeps the context in the store (sc0 still resolves)"
    ((st'.getSchedContext? scId0).isSome)
  assertBool "replenishOnCore never advances the machine timer (still 0)"
    (st'.machine.timer == base.machine.timer)
  assertBool "replenishOnCore keeps core 1's replenish queue count-consistent"
    (sizeConsistentB st' core1)
  assertBool "a context with no pending refill is not queued"
    ((replenishOnCore ((BootstrapBuilder.empty.withObject scId0.toObjId (.schedContext sc0)).withObject
        tid0.toObjId (.tcb tcb0)).build core1 scId0).releaseEntriesOn core1 == [])

/-- §3.2 SM5.H.4: the migration genuinely *moves* `scId0`'s entries between cores. -/
private def runMigrationScenarios : IO Unit := do
  IO.println "--- §3.2 SM5.H.4 SchedContext replenishment migration ---"
  -- Migrate scId0's replenishments from core 1 to the boot core (core 0).
  let stM := migrateSchedContextReplenishment stCbs scId0 core1 bootCoreId
  assertBool "after migration, core 1's queue no longer holds (scId0, 5000)"
    (!(stM.releaseEntriesOn core1).contains (scId0, 5000))
  assertBool "after migration, the boot core's queue now holds (scId0, 5000)"
    ((stM.releaseEntriesOn bootCoreId).contains (scId0, 5000))
  assertBool "after migration, the boot core's queue is size-consistent"
    (sizeConsistentB stM bootCoreId)
  assertBool "after migration, core 1's queue is size-consistent"
    (sizeConsistentB stM core1)
  assertBool "migration never touches the object store (sc0 still resolves)"
    ((stM.getSchedContext? scId0).isSome)
  -- A self-migration is the identity.
  assertBool "self-migration (core 1 → core 1) leaves core 1's queue unchanged"
    ((migrateSchedContextReplenishment stCbs scId0 core1 core1).releaseEntriesOn core1
      == (stCbs.releaseEntriesOn core1))
  -- A core untouched by the migration is unchanged.
  assertBool "migration (core 1 → boot core) frames a third core's queue (core 1 ≠ this)"
    ((migrateSchedContextReplenishment stCbs scId0 core1 bootCoreId).releaseEntriesOn ⟨2, by decide⟩).isEmpty

/-- §3.3 SM5.H.4: the affinity-change-with-migration composite drags the SchedContext's
replenishments to the new home core AND (for a remote new home) emits the cross-core
`.reschedule` SGI. -/
private def runCompositeScenarios : IO Unit := do
  IO.println "--- §3.3 SM5.H.4 setThreadCpuAffinityWithMigration composite ---"
  -- determineTargetCore reads tcb0's affinity (= core 1).
  assertBool "tid0's home core (determineTargetCore) is core 1 (its cpuAffinity)"
    (determineTargetCore stCbs tid0 == core1)
  -- Rebind tid0 to the boot core, executing on core 1: the composite migrates
  -- scId0's replenishments from core 1 to the boot core.  The new home (boot core)
  -- is remote from the executing core (core 1).
  match setThreadCpuAffinityWithMigration stCbs tid0 (some bootCoreId) core1 with
  | .ok (st', sgi) =>
      assertBool "after the composite, tid0's cpuAffinity is committed to the boot core"
        (match st'.getTcb? tid0 with | some t => t.cpuAffinity == some bootCoreId | none => false)
      assertBool "after the composite, the boot core's queue holds (scId0, 5000)"
        ((st'.releaseEntriesOn bootCoreId).contains (scId0, 5000))
      assertBool "after the composite, core 1's queue no longer holds (scId0, 5000)"
        (!(st'.releaseEntriesOn core1).contains (scId0, 5000))
      assertBool "after the composite, tid0's new home core is the boot core"
        (determineTargetCore st' tid0 == bootCoreId)
      -- tid0 was not runnable (not in any run queue), so no cross-core SGI fires
      -- (the SGI is gated on the thread being runnable on its new home core).
      assertBool "blocked tid0's remote re-home emits no spurious cross-core SGI"
        (sgi == none)
  | .error _ =>
      assertBool "composite (bind tid0 → boot core) succeeds" false
  -- A LOCAL re-home (executing core == new home) never emits a cross-core SGI.
  match setThreadCpuAffinityWithMigration stCbs tid0 (some core1) core1 with
  | .ok (_, sgi) =>
      assertBool "local re-home (exec core == new home) emits no SGI"
        (sgi == none)
  | .error _ => assertBool "local re-home succeeds" false
  -- The composite is fail-closed on a non-TCB target.
  assertBool "composite on a non-TCB target is .error .invalidArgument"
    (match setThreadCpuAffinityWithMigration stCbs (ThreadId.ofNat 999) (some bootCoreId) core1 with
     | .error .invalidArgument => true
     | _ => false)
  -- An unbound thread (no SchedContext) has no replenishments to migrate; the
  -- composite is just the affinity write + run-queue migration.
  let stUnbound : SystemState :=
    let base := (BootstrapBuilder.empty.withObject (ThreadId.ofNat 300).toObjId
      (.tcb { tcb0 with tid := ThreadId.ofNat 300, scBindingScCode := 0, scBindingOwnerCode := 0 })).build
    base
  assertBool "composite on an unbound thread succeeds (affinity + run-queue write only)"
    (match setThreadCpuAffinityWithMigration stUnbound (ThreadId.ofNat 300) (some bootCoreId) core1 with
     | .ok _ => true | .error _ => false)
  -- The syscall op (`setThreadCpuAffinityOp`, production-reached) commits the state.
  match ThreadId.toValid? tid0 with
  | some vtid0 =>
      assertBool "setThreadCpuAffinityOp (bind tid0 → boot core) succeeds + migrates"
        (match setThreadCpuAffinityOp stCbs vtid0 (some bootCoreId) with
         | .ok st' => (st'.releaseEntriesOn bootCoreId).contains (scId0, 5000)
         | .error _ => false)
  | none => assertBool "tid0 validates as a non-sentinel ThreadId" false
  -- `decodeAffinity` decodes the raw affinity word: 0..numCores-1 bind, the marker unbinds.
  assertBool "decodeAffinity 1 = .ok (some core 1)"
    (match decodeAffinity 1 with | .ok (some c) => c.val == 1 | _ => false)
  assertBool "decodeAffinity (unbind marker = numCores) = .ok none"
    (match decodeAffinity affinityUnbindMarker with | .ok none => true | _ => false)
  assertBool "decodeAffinity (out of range) = .error .invalidArgument"
    (match decodeAffinity (numCores + 5) with | .error .invalidArgument => true | _ => false)

/-- §3.4 SM5.H.7, WS-ZA ZA6.4: the refill accounting — a charge keeps the
refill total (the budget is conserved), takes what ran off the head, and keeps
the refills within `maxReplenishments`. -/
private def runBudgetScenarios : IO Unit := do
  IO.println "--- §3.4 SM5.H.7 CBS refill accounting ---"
  let charged := sc0.chargeBudget 0 1 1
  assertBool "a one-tick charge keeps the refill total (50 → 50)"
    (charged.refillTotal == sc0.refillTotal)
  assertBool "a one-tick charge takes one unit off the head (50 → 49)"
    (charged.budgetRemaining.val == 49)
  assertBool "a one-tick charge keeps the refills within maxReplenishments"
    (charged.refillSize ≤ maxReplenishments)
  let spent := sc0.chargeBudget 0 50 50
  assertBool "a whole-head charge leaves the head used up and the total kept"
    (spent.budgetRemaining.val == 0 && spent.refillTotal == sc0.refillTotal)

/-- §3.5 SM5.H.5: the affinity-consistency invariant's *decidable* witnesses on the
default (boot) and the CBS fixture states. -/
private def runAffinityScenarios : IO Unit := do
  IO.println "--- §3.5 SM5.H.5 affinity consistency witnesses ---"
  -- On the boot state the replenish queues are empty (vacuously consistent).
  assertBool "boot: every core's replenish queue is empty (vacuous consistency)"
    ((allCores).all (fun c => ((default : SystemState).releaseEntriesOn c).isEmpty))
  -- On stCbs, core 1's single entry's SchedContext is homed on core 1 (the
  -- decidable content of affinity-consistency for that entry).
  assertBool "stCbs: scId0's bound thread (tid0) is homed on core 1 (matches its queue)"
    (determineTargetCore stCbs tid0 == core1)
  assertBool "stCbs: core 1's replenish queue holds exactly scId0's entry"
    ((stCbs.releaseEntriesOn core1) == [(scId0, 5000)])

/-- §3.5b **PR #889 review round 20**: the live affinity path refuses a PE the
    platform does not have.

    `stCbs`'s machine carries the default `declaredCoreCount = numCores`, so
    core 1 is a legal home there; `stSingleCore` is the same state on a machine
    that declares one PE, which is what
    `bootAndInitialisePlatform SimSingleCorePlatform` installs (its binding's
    `machineConfig` is `simSingleCoreMachineConfig`, and
    `declaredCoreCountAgrees` holds it equal to `coreCount = 1`).  The pair is
    the point: the same request is accepted on one machine and refused on the
    other, so this is a *bound* and not a blanket refusal. -/
private def stSingleCore : SystemState :=
  { stCbs with machine := { stCbs.machine with declaredCoreCount := 1 } }

private def runDeclaredCoreScenarios : IO Unit := do
  IO.println "--- §3.5b PR #889 round 20: declared-core bound on .tcbSetAffinity ---"
  -- The four bindings agree with their own machine configuration, so the number
  -- the boot enforces is the number the live transition reads.
  assertBool "RPi5 binding: machineConfig.declaredCoreCount = coreCount (4)"
    (SeLe4n.Platform.RPi5.rpi5MachineConfig.declaredCoreCount ==
      SeLe4n.Platform.PlatformBinding.coreCount
        (platform := SeLe4n.Platform.RPi5.RPi5Platform))
  assertBool "single-core sim binding: machineConfig.declaredCoreCount = coreCount (1)"
    (SeLe4n.Platform.Sim.simSingleCoreMachineConfig.declaredCoreCount ==
      SeLe4n.Platform.PlatformBinding.coreCount
        (platform := SeLe4n.Platform.Sim.SimSingleCorePlatform))
  assertBool "single-core sim binding declares exactly one PE"
    (SeLe4n.Platform.Sim.simSingleCoreMachineConfig.declaredCoreCount == 1)
  -- The refusal, on a one-PE machine.
  assertBool "one-PE machine: .tcbSetAffinity to core 1 is refused (.invalidArgument)"
    (match setThreadCpuAffinityWithMigration stSingleCore tid0 (some core1) bootCoreId with
     | .error .invalidArgument => true
     | _ => false)
  -- ...and it commits nothing: the pinned affinity is unchanged.
  assertBool "one-PE machine: a refused affinity write leaves the TCB pinned as it was"
    (match stSingleCore.getTcb? tid0 with
     | some tcb => tcb.cpuAffinity == some core1
     | none => false)
  -- The bound is narrow: core 0 is a PE this machine has.
  assertBool "one-PE machine: .tcbSetAffinity to core 0 is accepted"
    (setThreadCpuAffinityWithMigration stSingleCore tid0 (some bootCoreId) bootCoreId).isOk
  -- ...and unpinning names no core at all, so it is never refused by this check.
  assertBool "one-PE machine: unpinning (.tcbSetAffinity none) is accepted"
    (setThreadCpuAffinityWithMigration stSingleCore tid0 none bootCoreId).isOk
  -- The same request on the full-width machine is accepted — the refusal is the
  -- platform's declared width, not a new blanket rule.
  assertBool "four-PE machine: the same core-1 request is accepted"
    (setThreadCpuAffinityWithMigration stCbs tid0 (some core1) bootCoreId).isOk
  -- **WS-RR RR7.30**: the unpinned half of the same bound, executed.  The two
  -- refusals above cover every *pinned* thread; a thread with no affinity, and a
  -- `tid` that resolves to no TCB at all, both route to `bootCoreId` — core `0`,
  -- which every binding declares (`coreCountPos`).  So no thread of any kind is
  -- enqueued on a PE the machine does not have, which is what
  -- `determineTargetCore_lt_declaredCoreCount` states.
  let stUnpinned : SystemState :=
    match setThreadCpuAffinityWithMigration stSingleCore tid0 none bootCoreId with
    | .ok (st, _) => st
    | .error _ => stSingleCore
  assertBool "one-PE machine: an unpinned thread routes to core 0"
    (determineTargetCore stUnpinned tid0 == bootCoreId)
  assertBool "one-PE machine: an unpinned thread's home is a declared PE"
    (decide ((determineTargetCore stUnpinned tid0).val <
      stUnpinned.machine.declaredCoreCount))
  assertBool "one-PE machine: a tid with no TCB routes to core 0 as well"
    (determineTargetCore stSingleCore (ThreadId.ofNat 4242) == bootCoreId)
  -- The bound is the machine's, so the same routing on the four-PE machine is
  -- still inside its (wider) declared set — the theorem is a bound, not a pin.
  assertBool "four-PE machine: the unpinned home is still a declared PE"
    (decide ((determineTargetCore stCbs (ThreadId.ofNat 4242)).val <
      stCbs.machine.declaredCoreCount))

/-- §3.6: SM5.H.4 full-thread-migration — the run-queue entry moves cores. -/
private def runRunQueueMigrationScenarios : IO Unit := do
  IO.println "--- §3.6 SM5.H.4 run-queue migration (full thread migration) ---"
  -- Put tid0 in core 1's run queue, then migrate it to the boot core.
  let stRq : SystemState := stCbs.runEnqueueOnCore core1 tid0 ⟨5⟩
  let stMoved := migrateRunQueueOnAffinityChange stRq tid0 core1 bootCoreId
  assertBool "before: tid0 is in core 1's run queue"
    ((stRq.queuedOn core1 tid0))
  assertBool "after run-queue migration: tid0 left core 1's run queue"
    (!(stMoved.queuedOn core1 tid0))
  assertBool "after run-queue migration: tid0 entered the boot core's run queue"
    ((stMoved.queuedOn bootCoreId tid0))
  assertBool "run-queue migration frames the replenish queue (still holds scId0)"
    ((stMoved.releaseEntriesOn core1).contains (scId0, 5000))
  -- A self-migration is the identity.
  assertBool "self run-queue migration (core 1 → core 1) is the identity"
    ((migrateRunQueueOnAffinityChange stRq tid0 core1 core1).queuedOn core1 tid0)
  -- A runnable thread re-homed to a REMOTE core emits the cross-core SGI.
  match setThreadCpuAffinityWithMigration stRq tid0 (some bootCoreId) core1 with
  | .ok (st', sgi) =>
      assertBool "runnable tid0's remote re-home emits a cross-core .reschedule SGI to the boot core"
        (sgi == some (bootCoreId, SgiKind.reschedule))
      assertBool "runnable tid0's remote re-home: tid0 is now in the boot core's run queue"
        ((st'.queuedOn bootCoreId tid0))
  | .error _ => assertBool "runnable tid0 remote re-home succeeds" false
  -- D15 witness: after migrating tid0 (in core 1's run queue, SC budget 50 > 0) to the
  -- boot core, the SM4.C run-queue↔budget consistency content holds for tid0 on the new
  -- core — it is in the boot core's run queue AND its SchedContext has positive budget.
  -- The thread is runnable, so its context is off every release queue: the
  -- witness starts from `stCbsRunnable`.
  let stMovedPos := migrateRunQueueOnAffinityChange (stCbsRunnable.runEnqueueOnCore core1 tid0 ⟨5⟩)
    tid0 core1 bootCoreId
  assertBool "D15: a migrated runnable thread carries its positive SC budget to the new core"
    (((stMovedPos.queuedOn bootCoreId tid0)) &&
     (match stMovedPos.getSchedContext? scId0 with | some sc => sc.budgetRemaining.val > 0 | none => false))
  -- #2: rebinding a thread RUNNING on its home to another core takes it off that
  -- core in the same transition (WS-ZA ZA6.3, seL4's `remoteTCBStall`), where the
  -- retired reading refused it (`.threadOnDifferentCore`, Codex P1) — and refused
  -- nothing when unpinning, leaving the thread running off its home.  Put tid0 as
  -- `currentOnCore core1` (running ⇒ dequeue-on-dispatch, in no run queue), then
  -- rebind it to the boot core.
  let stRunning : SystemState :=
    { stCbs with scheduler := stCbs.scheduler.setCurrentOnCore core1 (some tid0) }
  match setThreadCpuAffinityWithMigration stRunning tid0 (some bootCoreId) bootCoreId with
  | .ok (stV, _) =>
      assertBool "#2: the rebind vacates core 1 and queues tid0 on its new home, the boot core"
        (stV.scheduler.currentOnCore core1 == none && stV.queuedOn bootCoreId tid0 &&
          !stV.queuedOn core1 tid0)
      assertBool "#2: ...and flags core 1 to choose again"
        (stV.scheduler.reschedulePendingOnCore core1)
      assertBool "#2: ...and its reservation's refill follows it to the boot core"
        ((stV.releaseEntriesOn bootCoreId) == [(scId0, 5000)] &&
          (stV.releaseEntriesOn core1).isEmpty)
  | .error _ => assertBool "#2: rebinding a running thread to another core succeeds" false
  -- rebinding the SAME running thread to its current (admitted) core 1 still succeeds.
  match setThreadCpuAffinityWithMigration stRunning tid0 (some core1) bootCoreId with
  | .ok _ => assertBool "#2: rebinding a running thread to its own (admitted) core 1 succeeds" true
  | .error _ => assertBool "#2: rebind a running thread to its own core succeeds" false

/-- §3.7 (A2/A4): the live per-core budget tick's bound-exhausted replenish write IS
the abstract `replenishOnCore` primitive's (A2), and the tick preserves replenish-queue
validity (A4) — driven on a genuine budget-exhausted SchedContext. -/
private def runLiveTickScenarios : IO Unit := do
  IO.println "--- §3.7 SM5.H.2 (A2/A4) live-tick CBS bridge ---"
  -- A budget-EXHAUSTED SchedContext (budgetRemaining = 1 ≤ 1) bound to tid0, on core 1.
  -- Its head holds budget, so it is on no release queue (seL4-MCS queues only a
  -- context whose head is used up); the tick's charge queues it.
  let scExhausted : SchedContext := { sc0 with budgetRemaining := ⟨1⟩ }
  let stExhausted : SystemState :=
    ((BootstrapBuilder.empty.withObject scId0.toObjId
      (.schedContext scExhausted)).withObject tid0.toObjId (.tcb tcb0)).build
  -- Cut B2: the tick charges the thread the store holds, resolved through the
  -- witnessed lookup that supplies the proof its in-place rewrite consumes.
  match stExhausted.getTcbWitnessed? tid0 with
  | none => assertBool "the CBS fixture stores tid0 (the exhausted charge runs)" false
  | some ⟨tcbX, hX⟩ =>
      match timerTickBudgetOnCore stExhausted core1 tid0 tcbX hX with
      | (st', preempted) =>
          assertBool "bound-exhausted budget tick preempts (returns true)"
            (preempted == true)
          -- A2: the LIVE tick's replenish-queue write on core 1 is exactly the
          -- abstract `replenishOnCore` primitive's: the context sits where its
          -- refills place it, so placing it again changes nothing.
          assertBool "A2: live bound-exhausted tick's core-1 replenish queue == replenishOnCore's"
            ((st'.releaseEntriesOn core1) ==
              ((replenishOnCore st' core1 scId0).releaseEntriesOn core1))
          -- A2 (concretely): the used tick is scheduled one period on (0 + period =
          -- 1000, seL4-MCS's `schedule_used`), and the context's one entry is there.
          assertBool "A2: the tick keyed scId0 at its earliest refill (now + period = 1000)"
            ((st'.releaseEntriesOn core1) == [(scId0, 1000)])
          -- A4: the post-tick core-1 replenish queue is still valid (size-consistent).
          assertBool "A4: live bound-exhausted tick keeps core 1's replenish queue size-consistent"
            (sizeConsistentB st' core1)
          -- A non-exhausted / unbound tick leaves the replenish queue untouched (A4 other
          -- branches) — on a state that STORES the unbound thread, since the tick charges
          -- what the store holds.
          let stUnboundThread : SystemState :=
            { stCbs with
                objects := stCbs.objects.insert tid0.toObjId
                  (.tcb { tcb0 with scBindingScCode := 0, scBindingOwnerCode := 0, timeSlice := 3 }) }
          assertBool "A4: an UNBOUND time-slice tick leaves core 1's replenish queue untouched"
            (match stUnboundThread.getTcbWitnessed? tid0 with
             | some ⟨tcbU, hU⟩ =>
               match timerTickBudgetOnCore stUnboundThread core1 tid0 tcbU hU with
               | (stU, _) => (stU.releaseEntriesOn core1) == [(scId0, 5000)]
             | none => false)

/-- §3.8: the SM5.H theorem-inventory partition counts (compiled-`decide` guards). -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.7 SM5.H inventory partition counts ---"
  assertBool "inventory has 116 entries"
    (decide (perCoreCbsTheorems.length = 116))
  assertBool "predicate category has 6 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .predicate)).length = 6))
  assertBool "replenish category has 14 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .replenish)).length = 14))
  assertBool "preservation category has 8 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .preservation)).length = 8))
  assertBool "migration category has 25 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .migration)).length = 25))
  assertBool "affinityWrite category has 4 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .affinityWrite)).length = 4))
  assertBool "consistency category has 22 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .consistency)).length = 22))
  assertBool "budget category has 6 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .budget)).length = 6))
  assertBool "lockSet category has 20 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .lockSet)).length = 20))
  assertBool "liveTick category has 8 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .liveTick)).length = 8))
  assertBool "memoryModel category has 3 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .memoryModel)).length = 3))

/-- §3.8 (SM5.H.4 §17/§18): the D15 composite + the cross-core SGI characterisation
on real states.  Exercises the new completion theorems' content non-vacuously: the
remote-runnable composite emits exactly the `.reschedule` SGI to the new home (and a
local re-home emits none), and the migrated thread satisfies the SM4.C
run-queue↔budget consistency on its new core. -/
private def runSm5hCompletionScenarios : IO Unit := do
  IO.println "--- §3.8 SM5.H.4 D15 composite + SGI characterisation ---"
  -- tid0 runnable on core 1, re-homed to the (remote, from core 1) boot core.
  let stRq : SystemState := stCbsRunnable.runEnqueueOnCore core1 tid0 ⟨5⟩
  match setThreadCpuAffinityWithMigration stRq tid0 (some bootCoreId) core1 with
  | .ok (st', sgi) =>
      -- §18 `_emits_reschedule_of_remote_runnable`: remote (boot ≠ core1) + runnable
      -- (tid0 landed in the boot core's run queue) ⇒ exactly one `.reschedule` SGI.
      assertBool "§18: remote+runnable composite emits the .reschedule SGI to the new home"
        (sgi == some (bootCoreId, SgiKind.reschedule))
      -- §17 D15 (composite): the migrated thread satisfies run-queue↔budget consistency
      -- on its new core — present in the boot core's run queue AND positive SC budget.
      assertBool "§17 D15 composite: migrated thread is in the new core's run queue with positive SC budget"
        (((st'.queuedOn bootCoreId tid0)) &&
         (match st'.getSchedContext? scId0 with | some sc => sc.budgetRemaining.val > 0 | none => false))
  | .error _ => assertBool "remote-runnable composite succeeds" false
  -- §18 `_no_sgi_if_local`: a local re-home (new home == executing core) emits no SGI.
  match setThreadCpuAffinityWithMigration stRq tid0 (some core1) core1 with
  | .ok (_, sgi) =>
      assertBool "§18: a local re-home (new home = executing core) emits no cross-core SGI"
        (sgi == none)
  | .error _ => assertBool "local re-home composite succeeds" false

-- §3.9b (SM5.I affinity discharge): surface anchors for the affinity-consistency
-- discharge.  The carried-entries affinity is DERIVED via the proven prepared /
-- budget / schedule per-phase frames; the strengthened aggregate replaces the
-- v0.31.57 whole-state assume-conclusion `hAffinity` with `currentBoundHomedOnCore`
-- on the prepared state, which the placement invariant and the binding pair give
-- (WS-ZA ZA6.3).  Hypothesis-carrying theorems, so surface-anchored (not
-- runtime-decidable).
section Sm5iAffinityAnchors
open SeLe4n.Kernel
#check @affinityConsistent_transfer
#check @determineTargetCore_insert_tcb
#check @getSchedContext?_boundThread_insert_schedContext
#check @processReplenishmentsDueOnCore_determineTargetCore
#check @processReplenishmentsDueOnCore_boundThread
#check @timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore
#check @scheduleEffectiveOnCore_preserves_replenishQueueAffinityConsistentOnCore
#check @timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore
#check @timerTickOnCore_preserves_perCoreCbsInvariant_discharged
#check @timerTickBudgetOnCore_preserves_replenishQueueAffinityConsistentOnCore
#check @budgetExhaustOnCore_preserves_replenishQueueAffinityConsistentOnCore
#check @timeoutBlockedThreads_homeBindFrame
#check @releaseFreeFor_of_boundHome
#check @spendBudget_requeue_releaseFreeFor
#check @currentBoundHomedOnCore_of_placement
#check @yieldCharge_requeue_releaseFreeFor
-- non-vacuity: the freshly-booted system is affinity-consistent on every core, so the
-- pre-state `hCons` hypothesis of the headline is satisfiable.
example (c : SeLe4n.Kernel.Concurrency.CoreId) :
    replenishQueueAffinityConsistentOnCore (default : SystemState) c :=
  default_replenishQueueAffinityConsistentOnCore c
end Sm5iAffinityAnchors

/-- §3.9 (SM5.I): the live per-core timer tick preserves the per-core CBS invariant's
**validity** + **pipeline-order** conjuncts — verified on a concrete tick result
(both conjuncts are decidable on a closed state).  This exercises the SM5.I
preservation theorems' content non-vacuously: on an idle core the tick succeeds and
its replenish queue is sorted, size-consistent, and future-ordered. -/
private def runSm5iTickCbsChecks : IO Unit := do
  IO.println "--- §3.9 SM5.I live-tick preserves perCoreCbsInvariant (validity + pipeline) ---"
  let st := BootstrapBuilder.empty.build
  let st1 := timerTickOnCore st bootCoreId
  assertBool "SM5.I: live-tick result replenish queue is count-consistent (validity)"
    (sizeConsistentB st1 bootCoreId)
  assertBool "SM5.I: live-tick result replenish queue is future-ordered (pipeline)"
    ((st1.releaseEntriesOn bootCoreId).all (fun pair => decide (pair.2 > st1.machine.timer)))
  assertBool "SM5.I: live-tick reads but does not advance the global timer"
    (st1.machine.timer == st.machine.timer)

-- ============================================================================
-- §4  The binding lifecycle (WS-RR bind/unbind affinity closure)
-- ============================================================================

-- §4.1 surface anchors: the `SchedContext/BindingAffinity.lean` public surface
-- plus its two composition seams (the preemption seam's state decomposition and
-- the reschedule receiver's read frames).
#check @replenishQueueEntriesBoundOnCore
#check @replenishQueueEntriesBound_smp
#check @default_replenishQueueEntriesBound_smp
#check @replenishQueueEntriesBoundOnCore_transfer
#check @replenishQueueAffinityConsistentOnCore_transfer
#check @replenishOnCore_preserves_replenishQueueEntriesBoundOnCore
#check @migrateSchedContextReplenishment_preserves_replenishQueueEntriesBound_smp
#check @schedContextBind_preserves_replenishQueueAffinityConsistent_smp
#check @schedContextBind_preserves_replenishQueueEntriesBound_smp
#check @schedContextBind_preserves_objects_invExt
#check @schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp
#check @schedContextUnbind_preserves_replenishQueueEntriesBound_smp
#check @schedContextUnbind_preserves_objects_invExt
#check @schedContextUnbindOnCore_preserves_replenishQueueAffinityConsistent_smp
#check @schedContextUnbindOnCore_preserves_replenishQueueEntriesBound_smp
#check @SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases
#check @handleRescheduleSgiOnCore_determineTargetCore
#check @handleRescheduleSgiOnCore_boundThread

-- §4.2 elaboration-time applications: each headline theorem consumes exactly its
-- stated hypothesis set (the affinity ↔ orphan-freedom mutual dependence is the
-- point: bind's affinity needs orphan-freedom, unbind's orphan-freedom needs
-- affinity, unbind's affinity needs neither).
example (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    replenishQueueAffinityConsistent_smp st' :=
  schedContextBind_preserves_replenishQueueAffinityConsistent_smp vScId vThreadId st st'
    hObjInv hCons hOrphan h

example (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    replenishQueueEntriesBound_smp st' :=
  schedContextBind_preserves_replenishQueueEntriesBound_smp vScId vThreadId st st'
    hObjInv hOrphan h

example (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueAffinityConsistent_smp st' :=
  schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp vScId st st' hObjInv hCons h

example (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hRef : st.releaseQueueRefined)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueEntriesBound_smp st' :=
  schedContextUnbind_preserves_replenishQueueEntriesBound_smp vScId st st'
    hObjInv hRef hOrphan h

example (vScId : ValidObjId) (ec : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    replenishQueueAffinityConsistent_smp st' :=
  schedContextUnbindOnCore_preserves_replenishQueueAffinityConsistent_smp vScId ec st st'
    sgi? hObjInv hCons h

example (vScId : ValidObjId) (ec : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hRef : st.releaseQueueRefined)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    replenishQueueEntriesBound_smp st' :=
  schedContextUnbindOnCore_preserves_replenishQueueEntriesBound_smp vScId ec st st'
    sgi? hObjInv hRef hOrphan h

-- non-vacuity: the freshly-booted system satisfies the orphan-freedom
-- hypothesis, so the bind theorems' `hOrphan` is satisfiable from boot.
example : replenishQueueEntriesBound_smp (default : SystemState) :=
  default_replenishQueueEntriesBound_smp

-- §4.3 runtime fixtures: an *unbound* SchedContext + unbound same-domain TCB
-- pair alongside the §3 bound pair, so bind's queue frame is observed on a
-- populated queue and the lifecycle's purge leaves the other SchedContext's
-- entry standing.

private def scIdLifecycle : SchedContextId := SchedContextId.ofNat 210
private def tidLifecycle : SeLe4n.ThreadId := ThreadId.ofNat 110

/-- An **unbound, inactive** SchedContext — the shape `schedContextBind`'s guard
admits. -/
private def scLifecycle : SchedContext :=
  { scId := scIdLifecycle, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨7⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThreadCode := 0,
    isActive := false, refillTailCount := 0 }

/-- `tidLifecycle`'s TCB: unbound, same domain as `scLifecycle`, pinned to core 1. -/
private def tcbLifecycle : TCB :=
  { tid := tidLifecycle, priority := ⟨3⟩, domain := ⟨0⟩, spaceCells := SeLe4n.Model.TCB.spaceCellsOf (ObjId.ofNat 0) (ObjId.ofNat 0), ipcBuffer := SeLe4n.VAddr.ofNat 0,
    scBindingScCode := 0, scBindingOwnerCode := 0, cpuAffinity := some core1 }

/-- The §3 CBS fixture plus the unbound pair: core 1's queue holds the *bound*
SchedContext's entry `(scId0, 5000)`; `scIdLifecycle` holds none (orphan-free). -/
private def stLifecycle : SystemState :=
  let base := ((((BootstrapBuilder.empty.withObject scId0.toObjId
    (.schedContext sc0)).withObject tid0.toObjId (.tcb tcb0)).withObject
    scIdLifecycle.toObjId (.schedContext scLifecycle)).withObject
    tidLifecycle.toObjId (.tcb tcbLifecycle)).build
  withReleaseEntryOnCore base core1 scId0 5000

private def scIdLifecycleValid : SeLe4n.ValidObjId := ⟨scIdLifecycle.toObjId, by decide⟩
private def tidLifecycleValid : SeLe4n.ValidThreadId := ⟨tidLifecycle, by decide⟩
private def scId0Valid : SeLe4n.ValidObjId := ⟨scId0.toObjId, by decide⟩

private def core2 : CoreId := ⟨2, by decide⟩

/-- A SchedContext bound to a thread with **no TCB** — the unbind's dead-TCB
arm's input shape.  Its entry sits on core 2: with the bound TCB gone,
`determineTargetCore` has nothing to read, so a home-core purge would compute
the boot core — which is exactly why the purge reads the core the context is
linked on (`releaseCoreOf`, WS-ZA ZA6.3) rather than trusting the home
computation.  (The mis-homed entry also shows the state is outside the affinity
invariant; the purge is the fail-closed cleanup that re-establishes
orphan-freedom regardless.) -/
private def tidDangling : SeLe4n.ThreadId := ThreadId.ofNat 120
private def scIdDangling : SchedContextId := SchedContextId.ofNat 220
private def scDangling : SchedContext :=
  { scId := scIdDangling, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨6⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThreadCode := SeLe4n.ThreadId.optCode (some tidDangling), isActive := true, refillTailCount := 0 }
private def stDangling : SystemState :=
  let base := (BootstrapBuilder.empty.withObject scIdDangling.toObjId
    (.schedContext scDangling)).build
  withReleaseEntryOnCore base core2 scIdDangling 7000
private def scIdDanglingValid : SeLe4n.ValidObjId := ⟨scIdDangling.toObjId, by decide⟩

/-- §4.4: the binding lifecycle drives the replenish-queue invariants live —
bind commits both binding sides and frames every queue; replenish populates the
home core; unbind clears both binding sides and purges exactly the home core's
entries for its SchedContext (the other SchedContext's entry survives); the
per-core wrapper agrees and surfaces no SGI for a thread running nowhere; the
dead-TCB arm purges the core its context is linked on. -/
private def runBindingLifecycleScenarios : IO Unit := do
  IO.println "--- §4.4 binding lifecycle: bind → replenish → unbind ---"
  -- ── bind ──
  match SchedContextOps.schedContextBind scIdLifecycleValid tidLifecycleValid stLifecycle with
  | .error _ =>
      assertBool "bind succeeds on an unbound SchedContext + unbound same-domain TCB" false
  | .ok ((), stB) =>
      assertBool "bind commits the SchedContext side (boundThread = the thread)"
        (match stB.getSchedContext? scIdLifecycle with
         | some sc => sc.boundThread == some tidLifecycle
         | none => false)
      assertBool "bind commits the TCB side (schedContextBinding = bound)"
        (match stB.getTcb? tidLifecycle with
         | some t => t.schedContextBinding == .bound scIdLifecycle
         | none => false)
      assertBool "bind leaves core 1's replenish queue exactly as it was"
        ((stB.releaseEntriesOn core1)
          == (stLifecycle.releaseEntriesOn core1))
      assertBool "bind leaves the boot core's replenish queue empty"
        ((stB.releaseEntriesOn bootCoreId).isEmpty)
      -- ── replenish on the new binding's home core ──
      let stR := withReleaseEntryOnCore stB core1 scIdLifecycle 9000
      assertBool "replenish after bind lands (scIdLifecycle, 9000) on core 1"
        ((stR.releaseEntriesOn core1).contains (scIdLifecycle, 9000))
      -- ── unbind (main arm: the bound TCB exists) ──
      match SchedContextOps.schedContextUnbind scIdLifecycleValid stR with
      | .error _ =>
          assertBool "unbind succeeds on the freshly-bound SchedContext" false
      | .ok ((), stU) =>
          assertBool "unbind clears the SchedContext side (boundThread = none)"
            (match stU.getSchedContext? scIdLifecycle with
             | some sc => sc.boundThread == (none : Option SeLe4n.ThreadId) && !sc.isActive
             | none => false)
          assertBool "unbind clears the TCB side (schedContextBinding = unbound)"
            (match stU.getTcb? tidLifecycle with
             | some t => t.schedContextBinding == .unbound
             | none => false)
          assertBool "unbind purges its SchedContext's entries from the home core"
            ((stU.releaseEntriesOn core1).all
              (fun e => e.1 != scIdLifecycle))
          assertBool "unbind leaves the other SchedContext's entry standing"
            ((stU.releaseEntriesOn core1).contains (scId0, 5000))
  -- ── the live wrapper: no running core → unbind's state, no SGI ──
  match SchedContextOps.schedContextUnbindOnCore scId0Valid core1 stCbs with
  | .error _ =>
      assertBool "wrapper unbind succeeds on the §3 bound fixture" false
  | .ok (stW, sgi?) =>
      assertBool "wrapper surfaces no SGI for a bound thread running nowhere"
        sgi?.isNone
      assertBool "wrapper purges the home core's entry (scId0, 5000)"
        ((stW.releaseEntriesOn core1).all
          (fun e => e.1 != scId0))
      assertBool "wrapper clears the SchedContext side too"
        (match stW.getSchedContext? scId0 with
         | some sc => sc.boundThread == (none : Option SeLe4n.ThreadId)
         | none => false)
  -- ── the dead-TCB arm: the core the context is linked on purged ──
  match SchedContextOps.schedContextUnbind scIdDanglingValid stDangling with
  | .error _ =>
      assertBool "the unbind succeeds on a dead-TCB binding" false
  | .ok ((), stS) =>
      assertBool "setup: the dead-TCB SchedContext is queued on core 2, off any home"
        ((stDangling.releaseEntriesOn core2) == [(scIdDangling, 7000)])
      assertBool "the unbind purges the entry from the core it is linked on (core 2)"
        ((stS.releaseEntriesOn core2).isEmpty)
      assertBool "and every other core's queue stays empty"
        ((stS.releaseEntriesOn core1).isEmpty && (stS.releaseEntriesOn bootCoreId).isEmpty)
      assertBool "the unbind clears the SchedContext side (orphan-freedom restored)"
        (match stS.getSchedContext? scIdDangling with
         | some sc => sc.boundThread == (none : Option SeLe4n.ThreadId) && !sc.isActive
         | none => false)

/-- §4.5 (WS-RR RR8.12 Cut C3b-i) an **unbound** thread, pinned to core 1, in the
same store as `tcb0`.  It is what makes the affinity arm's replenish-segment
narrowing measurable: `tcb0` runs on a reservation and `tcbUnbound` does not, so
the two resolve the same footprint's replenish segment to opposite answers on one
state.  A fixture holding only `tcb0` can exhibit the `some` arm and never the
`none` one. -/
private def tidUnbound : SeLe4n.ThreadId := ThreadId.ofNat 130

private def tcbUnbound : TCB :=
  { tid := tidUnbound, priority := ⟨5⟩, domain := ⟨0⟩, spaceCells := SeLe4n.Model.TCB.spaceCellsOf (ObjId.ofNat 0) (ObjId.ofNat 0), ipcBuffer := SeLe4n.VAddr.ofNat 0,
    scBindingScCode := 0, scBindingOwnerCode := 0, cpuAffinity := some core1 }

private def stAffinityFp : SystemState :=
  let base := (((BootstrapBuilder.empty.withObject scId0.toObjId (.schedContext sc0)).withObject
    tid0.toObjId (.tcb tcb0)).withObject tidUnbound.toObjId (.tcb tcbUnbound)).build
  withReleaseEntryOnCore base core1 scId0 5000

/-- Does a scheduler-domain footprint name this core's replenish-queue write lock? -/
private def hasReplenishWriteLock (fp : List (LockKey × Concurrency.AccessMode))
    (c : CoreId) : Bool :=
  decide ((LockKey.replenishQueue c, Concurrency.AccessMode.write) ∈ fp)

/-- ...and this core's run-queue write lock? -/
private def hasRunQueueWriteLock (fp : List (LockKey × Concurrency.AccessMode))
    (c : CoreId) : Bool :=
  decide ((LockKey.runQueue c, Concurrency.AccessMode.write) ∈ fp)

/-- §4.5 **WS-RR RR8.12 Cut C3b-i — the live `.tcbSetAffinity` arm's resolved
scheduler-domain footprint.**

Three things this measures that no theorem in the tree states of a *state*.

1. The resolved footprint's replenish segment follows the **binding**, not the
   arm: the same migration, core 1 → core 2, declares both cores' replenish write
   locks for a thread on a reservation and none at all for a thread on none.
2. The `setThreadCpuAffinityWithMigrationLockSet` the SM5.H.4 form declares is
   computed **beside** the resolved one on the unbound shape, so the narrowing is
   known to discriminate rather than merely to pass — the parametric footprint
   names both replenish locks there, because it takes two cores and no state.
3. The narrowing is exact in the other direction too: the live transition writes
   no replenish queue on the unbound shape, and does move the reservation on the
   bound one. -/
private def runAffinityFootprintScenarios : IO Unit := do
  IO.println "--- §4.5 Cut C3b-i: the .tcbSetAffinity arm's resolved scheduler footprint ---"
  let fpBound := schedLockSet_setThreadCpuAffinityOnCore stAffinityFp tid0 (some core2)
  let fpUnbound := schedLockSet_setThreadCpuAffinityOnCore stAffinityFp tidUnbound (some core2)
  let fpParametric := setThreadCpuAffinityWithMigrationLockSet core1 core2
  -- pre: the fixture really does hold the two shapes the claim distinguishes.
  assertBool "pre: tid0 runs on scId0 and is homed on core 1"
    (determineTargetCore stAffinityFp tid0 == core1 &&
      (match stAffinityFp.getTcb? tid0 with
       | some t => t.schedContextBinding.scId? == some scId0
       | none => false))
  assertBool "pre: tidUnbound is homed on core 1 too and runs on no reservation"
    (determineTargetCore stAffinityFp tidUnbound == core1 &&
      (match stAffinityFp.getTcb? tidUnbound with
       | some t => t.schedContextBinding.scId? == (none : Option SchedContextId)
       | none => false))
  -- (1) the run-queue segment is the arm's, and it is the same on both shapes:
  -- the narrowing is about the replenish segment alone.
  assertBool "C3b-i: both shapes declare the old home core's run-queue write lock"
    (hasRunQueueWriteLock fpBound core1 && hasRunQueueWriteLock fpUnbound core1)
  assertBool "C3b-i: ...and the new one's"
    (hasRunQueueWriteLock fpBound core2 && hasRunQueueWriteLock fpUnbound core2)
  -- (2) the replenish segment follows the binding.
  assertBool "C3b-i: a thread on a reservation declares BOTH cores' replenish write locks"
    (hasReplenishWriteLock fpBound core1 && hasReplenishWriteLock fpBound core2)
  assertBool "C3b-i: a thread on NO reservation declares no replenish lock on any core"
    (allCores.all (fun c => !hasReplenishWriteLock fpUnbound c))
  -- (3) the parametric SM5.H.4 footprint, computed beside the resolved one, is
  -- what makes (2) a narrowing rather than a restatement.
  assertBool "C3b-i: the parametric footprint declares both replenish locks on the SAME migration"
    (hasReplenishWriteLock fpParametric core1 && hasReplenishWriteLock fpParametric core2)
  assertBool "C3b-i: so on the unbound shape the two footprints DISAGREE — the narrowing is live"
    (hasReplenishWriteLock fpParametric core1 && !hasReplenishWriteLock fpUnbound core1)
  assertBool "C3b-i: and on the bound shape every parametric member is a resolved member (coverage)"
    (fpParametric.all (fun p => decide (p ∈ fpBound)))
  -- (4) the live transition agrees with each declaration.
  match setThreadCpuAffinityWithMigration stAffinityFp tidUnbound (some core2) bootCoreId with
  | .error e =>
      assertBool s!"the unbound affinity change must succeed (got {repr e})" false
  | .ok (stU, _) =>
      assertBool "C3b-i: ...and the live arm writes no replenish queue on any core there"
        (allCores.all (fun c =>
          (stU.releaseEntriesOn c)
            == (stAffinityFp.releaseEntriesOn c)))
  match setThreadCpuAffinityWithMigration stAffinityFp tid0 (some core2) bootCoreId with
  | .error e =>
      assertBool s!"the bound affinity change must succeed (got {repr e})" false
  | .ok (stB, _) =>
      assertBool "C3b-i: the bound shape's live arm DOES move the reservation, to the new home"
        ((stB.releaseEntriesOn core2).contains (scId0, 5000) &&
          !(stB.releaseEntriesOn core1).contains (scId0, 5000))

/-- §4.6 (WS-RR RR8.12 Cut C3b-ii) the reading this cut had to reject: a
one-core replenish segment for the unbind, keyed on the bound thread's home.

It is right on the arm where the bound TCB resolves and **false** on the arm
where it does not — with the TCB gone from the store there is no `cpuAffinity`
left to read, `determineTargetCore` falls back to the boot core, while the
transition purges the core the context's own release link names
(`purgeReplenishCores`, WS-ZA ZA6.3).  Spelled here and nowhere else, so §4.6's
assertions are known to discriminate. -/
private def homeOnlyUnbindReplenishCores (st : SystemState) (scObjId : ObjId) :
    List CoreId :=
  match SchedContextOps.schedContextBoundThread? st scObjId with
  | some tid => [determineTargetCore st tid]
  | none => []

/-- §4.6 **WS-RR RR8.12 Cut C3b-ii — the three SchedContext arms' resolved
scheduler-domain footprints.**

Four things this measures that no theorem states of a *state*.

1. The unbind's replenish segment is the core the context is linked on, on the
   **dead-TCB** arm as on the bound arm, and the live transition agrees with
   each: on the dead-TCB fixture it purges core 2, which the home-only reading
   above does not declare.
2. The configure's replenish segment is the SC's **home** core, which is the same
   core its run segment names whenever the SC is bound — one core for an
   operation with two scheduling effects.
3. The bind declares no replenish lock at all, and writes none.
4. Each footprint is `schedFootprintOfCores` of its arm's own write set, so the
   run segments are the SM8.B ones rather than a second resolution. -/
private def runSchedContextFootprintScenarios : IO Unit := do
  IO.println "--- §4.6 Cut C3b-ii: the three SchedContext arms' scheduler footprints ---"
  -- ── (1) the unbind, on both arms ──
  let fpUnbindBound := schedLockSet_schedContextUnbindOnCore stCbs scId0.toObjId bootCoreId
  let fpUnbindDeadTcb := schedLockSet_schedContextUnbindOnCore stDangling scIdDangling.toObjId
    bootCoreId
  assertBool "pre: scId0's bound thread resolves and is homed on core 1"
    ((SchedContextOps.schedContextBoundThread? stCbs scId0.toObjId == some tid0)
      && determineTargetCore stCbs tid0 == core1
      && (stCbs.getTcb? tid0).isSome)
  assertBool "pre: scIdDangling names a thread with NO TCB — the dead-TCB arm's shape"
    ((SchedContextOps.schedContextBoundThread? stDangling scIdDangling.toObjId
        == some tidDangling)
      && (stDangling.getTcb? tidDangling).isNone)
  assertBool "C3b-ii: the bound arm declares exactly the home core's replenish write lock"
    (hasReplenishWriteLock fpUnbindBound core1
      && allCores.all (fun c => c == core1 || !hasReplenishWriteLock fpUnbindBound c))
  assertBool "C3b-ii: the dead-TCB arm declares the core the context is linked on (core 2) alone"
    (hasReplenishWriteLock fpUnbindDeadTcb core2
      && allCores.all (fun c => c == core2 || !hasReplenishWriteLock fpUnbindDeadTcb c))
  assertBool "C3b-ii: the retired home-only reading declares ONE core on the bound arm..."
    ((homeOnlyUnbindReplenishCores stCbs scId0.toObjId).length == 1)
  assertBool "C3b-ii: ...and the boot core on the dead-TCB arm, where the live one names core 2"
    (homeOnlyUnbindReplenishCores stDangling scIdDangling.toObjId == [bootCoreId]
      && schedContextUnbindReplenishCores stDangling scIdDangling.toObjId == [core2])
  -- ...and the live transition writes the core the segment names.
  match SchedContextOps.schedContextUnbindOnCore scIdDanglingValid bootCoreId stDangling with
  | .error e =>
      assertBool s!"C3b-ii: the dead-TCB unbind must succeed (got {repr e})" false
  | .ok (stS, _) =>
      assertBool "C3b-ii: the live dead-TCB unbind leaves core 1's queue empty"
        ((stS.releaseEntriesOn core1).isEmpty)
      assertBool "C3b-ii: ...and purges core 2's entry, which the home-only reading never declared"
        ((stS.releaseEntriesOn core2).isEmpty
          && !(homeOnlyUnbindReplenishCores stDangling scIdDangling.toObjId).contains core2)
  match SchedContextOps.schedContextUnbindOnCore scId0Valid bootCoreId stCbs with
  | .error e =>
      assertBool s!"C3b-ii: the bound-arm unbind must succeed (got {repr e})" false
  | .ok (stB, _) =>
      assertBool "C3b-ii: the bound arm purges the home core and leaves every other alone"
        ((stB.releaseEntriesOn core1).all (fun e => e.1 != scId0)
          && allCores.all (fun c => c == core1 ||
              (stB.releaseEntriesOn c)
                == (stCbs.releaseEntriesOn c)))
  -- ── (2) the configure ──
  let fpConfigure := schedLockSet_schedContextConfigureOnCore stCbs scId0.toObjId
  assertBool "C3b-ii: the configure declares the SC's home core's replenish write lock — the purge's"
    (hasReplenishWriteLock fpConfigure core1)
  assertBool "C3b-ii: ...and its run segment names the SAME core, so one lock covers both effects"
    (hasRunQueueWriteLock fpConfigure core1
      && (schedContextConfigureReplenishCores stCbs scId0.toObjId).all
          (fun c => (schedContextWriteSet stCbs scId0.toObjId).contains c))
  match SchedContextOps.schedContextConfigure scId0Valid 100 1000 5 0 0 stCbs with
  | .error e =>
      assertBool s!"C3b-ii: the configure must succeed (got {repr e})" false
  | .ok ((), stC) =>
      assertBool "C3b-ii: the live configure writes no replenish queue outside the declared core"
        (allCores.all (fun c => c == core1 ||
          (stC.releaseEntriesOn c)
            == (stCbs.releaseEntriesOn c)))
  -- ── (3) the bind ──
  let fpBind := schedLockSet_schedContextBindOnCore stLifecycle tidLifecycle
  assertBool "C3b-ii: the bind declares the bound thread's home core's run-queue write lock"
    (hasRunQueueWriteLock fpBind (determineTargetCore stLifecycle tidLifecycle))
  let bindHome := determineTargetCore stLifecycle tidLifecycle
  assertBool "C3b-ii: ...and the replenish lock of that home core alone (WS-ZA ZA6.4 postpone)"
    (hasReplenishWriteLock fpBind bindHome
      && allCores.all (fun c => c == bindHome || !hasReplenishWriteLock fpBind c))
  match SchedContextOps.schedContextBind scIdLifecycleValid tidLifecycleValid stLifecycle with
  | .error e =>
      assertBool s!"C3b-ii: the bind must succeed (got {repr e})" false
  | .ok ((), stBd) =>
      assertBool "C3b-ii: ...and the live bind writes no replenish queue outside the home core"
        (allCores.all (fun c => c == bindHome ||
          (stBd.releaseEntriesOn c)
            == (stLifecycle.releaseEntriesOn c)))

/-- §4.7 **WS-RR RR8.12 Cut C4 — the syscall-level scheduler resolver.**

`schedLockSetForSyscall` is the scheduler domain's `lockSetForSyscall`, and this
group measures the two things no theorem in the tree states of a *state*: that a
declared arm's answer IS that arm's own footprint (not a set the test supplied,
and not a neighbouring arm's), and that the operand each arm needs is the one it
refuses without.

The negative half — every undeclared arm answers `none` whatever the operands —
is `schedLockSetForSyscall_undeclared_none`, quantified over all nineteen, so
what is exercised here is the **declared** side and the per-arm operand
conditions the theorem cannot reach.

The control matters as much as the cases: `.tcbSetAffinity` is asserted to
refuse when only its *thread* operand is supplied, which is the one arm whose
missing operand is itself an `Option` — collapsing the two layers would make an
unsupplied operand read as an unpin request. -/
private def runSyscallSchedResolverScenarios : IO Unit := do
  IO.println "--- §4.7 Cut C4: the syscall-level scheduler footprint resolver ---"
  let st := stAffinityFp
  let opsThread : Concurrency.SyscallLockOperands :=
    { caller := tid0, targetThread := some tid0 }
  let opsObject : Concurrency.SyscallLockOperands :=
    { caller := tid0, targetObject := some scId0.toObjId }
  -- (i) A declared arm's answer IS its own resolved footprint, at the operands
  -- the caller supplied — the relation, not a presence check.
  assertBool "the .tcbSetPriority arm answers the priority-control footprint"
    (match schedLockSetForSyscall .tcbSetPriority opsThread bootCoreId st with
     | some fp => decide (fp.pairs = schedLockSet_priorityControlOnCore st tid0 bootCoreId)
     | none => false)
  assertBool "...and .schedContextUnbind answers the unbind's, at its own operand"
    (match schedLockSetForSyscall .schedContextUnbind opsObject bootCoreId st with
     | some fp =>
         decide (fp.pairs
           = schedLockSet_schedContextUnbindOnCore st scId0.toObjId bootCoreId)
     | none => false)
  assertBool "...and .notificationWait answers the executing core's alone"
    (match schedLockSetForSyscall .notificationWait opsThread bootCoreId st with
     | some fp => decide (fp.pairs = schedLockSet_notificationWaitOnCore bootCoreId)
     | none => false)
  -- (ii) Two arms do not answer the same set: a resolver that dispatched to one
  -- footprint for every arm would pass (i) three times over.
  assertBool "NEGATIVE: the priority arm and the unbind arm declare DIFFERENT sets"
    (match schedLockSetForSyscall .tcbSetPriority opsThread bootCoreId st,
           schedLockSetForSyscall .schedContextUnbind opsObject bootCoreId st with
     | some a, some b => decide (a.pairs ≠ b.pairs)
     | _, _ => false)
  -- (iii) The operand each arm needs is the one it refuses without.
  assertBool "NEGATIVE: a thread-directed arm with no thread operand declares nothing"
    (decide (schedLockSetForSyscall .tcbSetPriority { caller := tid0 } bootCoreId st = none))
  assertBool "NEGATIVE: an object-directed arm with no object operand declares nothing"
    (decide (schedLockSetForSyscall .schedContextUnbind { caller := tid0 } bootCoreId st
      = none))
  -- The destination core is a second operand, and its own `none` is an unpin
  -- request — so an unsupplied operand must not read as one.
  assertBool "CONTROL: .tcbSetAffinity refuses on the thread operand ALONE"
    (decide (schedLockSetForSyscall .tcbSetAffinity opsThread bootCoreId st = none) &&
     (schedLockSetForSyscall .tcbSetAffinity
        { caller := tid0, targetThread := some tid0, affinity := some (some core2) }
        bootCoreId st).isSome &&
     (schedLockSetForSyscall .tcbSetAffinity
        { caller := tid0, targetThread := some tid0, affinity := some none }
        bootCoreId st).isSome)
  -- (iv) The undeclared arms, on a state and operands that would satisfy a
  -- declared one — so the `none` is the inventory's answer rather than a
  -- missing operand's.
  assertBool "NEGATIVE: eighteen arms declare nothing on fully-supplied operands"
    ([SyscallId.cspaceMint, .cspaceCopy, .cspaceMove, .mintReplyCap,
      .vspaceMap, .vspaceUnmap, .vspaceUnifyInstruction,
      .serviceRegister, .serviceRevoke, .serviceQuery,
      .tcbSetIPCBuffer, .tcbSetFaultHandler,
      .tcbBindNotification, .tcbUnbindNotification,
      .declassify, .declassifySignal, .auditRead, .auditDrain].all fun sid =>
        decide (declaredSchedFootprintSyscall sid = false) &&
        decide (schedLockSetForSyscall sid
          { caller := tid0, targetThread := some tid0, targetObject := some scId0.toObjId,
            affinity := some (some core2) } bootCoreId st = none))
  -- (v) ...and the fifteen the inventory names here are exactly the ones the `match`
  -- can answer: a declared arm listed here that had become unconditionally
  -- `none` is what the per-arm `_isSome_iff` family refuses, and this is the
  -- runtime reading of the same fact for the arms this fixture can supply.
  assertBool "the inventory names fifteen of these arms"
    (decide (([SyscallId.tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority,
      .tcbSetAffinity, .schedContextConfigure, .schedContextBind, .schedContextUnbind,
      .notificationSignal, .notificationWait,
      .send, .receive, .call, .reply, .replyRecv].filter
        (fun sid => declaredSchedFootprintSyscall sid)).length = 15))
  -- (vi) WS-ZA ZA5.4 part 23: the finalising delete and the revocation declare
  -- whatever the operands — every core's run queue, since a destroyed
  -- endpoint's or notification's cancelled waiters wake on their own cores.
  -- Part 26: and the space change, whose old CSpace root may be deleted by the
  -- zombie loop.
  assertBool "the capability destroys and the space change declare unconditionally"
    ([SyscallId.cspaceDelete, .cspaceRevoke, .tcbSetSpace].all fun sid =>
      declaredSchedFootprintSyscall sid &&
        (schedLockSetForSyscall sid { caller := tid0 } bootCoreId st).isSome)

/-- WS-ZA ZA6.4: **the no-stranded-refill check bites**.  The check reads the
links: a bound context with its head used up must be on a core's chain at its
head's release time.  The witnesses keep the context and its pending refill
and break the relation — the context off every queue, then queued at a time
its head no longer holds — and the check refuses both. -/
private def runRefillStrandedWitness : IO Unit := do
  IO.println "--- §3.27 a bound context's pending refill is never stranded ---"
  let strandedOk (st : SystemState) : Bool :=
    (releaseNoRefillStrandedChecks st.objectIndex st).all (·.2)
  assertBool "a runnable bound context holds no pending refill: nothing to check"
    (strandedOk stCbsRunnable)
  assertBool "a used-up head queued at its release time passes" (strandedOk stCbs)
  let stOff := stCbsRunnable.updateSchedContext scId0 fun sc =>
    { sc with budgetRemaining := ⟨0⟩, refillHeadPresent := true,
              refillHeadAmount := sc.budget.val, refillHeadEligibleAt := 5000 }
  assertBool "a used-up head on no release queue is refused" (!strandedOk stOff)
  let stMoved := stCbs.updateSchedContext scId0 fun sc =>
    { sc with refillHeadEligibleAt := 6000 }
  assertBool "a context queued at a time its head no longer holds is refused"
    (!strandedOk stMoved)
  assertBool "placing it again restores the relation"
    (strandedOk (stMoved.releasePlace core1 scId0))

def main : IO Unit := do
  IO.println "=== WS-SM SM5.H — Per-core CBS suite ==="
  runReplenishScenarios
  runMigrationScenarios
  runCompositeScenarios
  runBudgetScenarios
  runAffinityScenarios
  runDeclaredCoreScenarios
  runRunQueueMigrationScenarios
  runLiveTickScenarios
  runSm5hCompletionScenarios
  runSm5iTickCbsChecks
  runInventoryChecks
  runBindingLifecycleScenarios
  runAffinityFootprintScenarios
  runSchedContextFootprintScenarios
  runSyscallSchedResolverScenarios
  runRefillStrandedWitness
  IO.println "=== SM5.H suite: all assertions passed ==="

end SeLe4n.Testing.SmpCbs

def main : IO Unit := SeLe4n.Testing.SmpCbs.main
