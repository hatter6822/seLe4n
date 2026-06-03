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
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.H — Per-core CBS test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.H
"Per-core CBS" deliverable (`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.8, §5).

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
#check @replenishQueueAffinityConsistentOnCore
#check @replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistent_smp_at
#check @default_replenishQueueAffinityConsistentOnCore
#check @default_replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistentOnCore_frame

-- SM5.H.2 the replenishOnCore primitive + frames:
#check @replenishOnCore
#check @replenishOnCore_objects
#check @replenishOnCore_machine
#check @replenishOnCore_getTcb?
#check @replenishOnCore_getSchedContext?
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
#check @migrateSchedContextReplenishment_objects
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
#check @setThreadCpuAffinityWithMigration_bound_eq
#check @setThreadCpuAffinityWithMigration_unbound_eq
#check @schedContextMigration_consistent

-- SM5.H.7 per-core CBS invariant + budget accounting:
#check @perCoreCbsInvariant
#check @default_perCoreCbsInvariant
#check @replenishOnCore_preserves_perCoreCbsInvariant
#check @consumeBudget_preserves_le_budget
#check @applyRefill_preserves_le_budget
#check @scheduleReplenishment_replenishments_bounded

-- SM5.H inventory:
#check @perCoreCbsTheorems
#check @perCoreCbsTheorems_count
#check @perCoreCbsTheorems_partition_sum
#check @perCoreCbsTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- SM5.H.3: scheduling a replenishment preserves replenish-queue validity.
example (st : SystemState) (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hValid : replenishQueueValidOnCore st c) :
    replenishQueueValidOnCore (replenishOnCore st c scId eligibleAt) c :=
  replenishOnCore_preserves_replenishQueueValidOnCore st c scId eligibleAt hValid

-- SM5.H.6: scheduling a future replenishment preserves pipeline order.
example (st : SystemState) (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hPipeline : replenishmentPipelineOrderOnCore st c) (hFuture : eligibleAt > st.machine.timer) :
    replenishmentPipelineOrderOnCore (replenishOnCore st c scId eligibleAt) c :=
  replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c scId eligibleAt hPipeline hFuture

-- SM5.H.5: scheduling a home-core replenishment preserves affinity consistency.
example (st : SystemState) (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hCons : replenishQueueAffinityConsistentOnCore st c)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    replenishQueueAffinityConsistentOnCore (replenishOnCore st c scId eligibleAt) c :=
  replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore st c scId eligibleAt hCons hTarget

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
example (st : SystemState) (targetTid : SeLe4n.ThreadId) (newCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext) (st' : SystemState)
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) (hBound : sc.boundThread = some targetTid)
    (hUnique : ∀ scId'' sc'', st.getSchedContext? scId'' = some sc'' →
      sc''.boundThread = some targetTid → scId'' = scId)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid (some newCore) = .ok st') :
    replenishQueueAffinityConsistent_smp st' :=
  schedContextMigration_consistent st targetTid newCore tcb scId sc st'
    hTcb hInv hBind hSc hBound hUnique hCons hStep

-- SM5.H.7: scheduling maintains the aggregate per-core CBS invariant.
example (st : SystemState) (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hInv : perCoreCbsInvariant st c) (hFuture : eligibleAt > st.machine.timer)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    perCoreCbsInvariant (replenishOnCore st c scId eligibleAt) c :=
  replenishOnCore_preserves_perCoreCbsInvariant st c scId eligibleAt hInv hFuture hTarget

-- SM5.H.7: the CBS budget bound is maintained by replenishment (unconditional).
example (sc : SchedContext) (refillAmount : Nat) :
    (applyRefill sc refillAmount).budgetRemaining.val ≤ (applyRefill sc refillAmount).budget.val :=
  applyRefill_preserves_le_budget sc refillAmount

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.H.8 cross-core CBS scenarios
-- ============================================================================

private def core1 : CoreId := ⟨1, by decide⟩
private def scId0 : SchedContextId := SchedContextId.ofNat 200
private def tid0 : SeLe4n.ThreadId := ThreadId.ofNat 100

/-- A CBS SchedContext bound to thread `tid0`, budget 100, period 1000, remaining 50. -/
private def sc0 : SchedContext :=
  { scId := scId0, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨5⟩, deadline := ⟨0⟩,
    domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThread := some tid0, isActive := true,
    replenishments := [] }

/-- `tid0`'s TCB, bound to `sc0` and pinned (`cpuAffinity`) to core 1. -/
private def tcb0 : TCB :=
  { tid := tid0, priority := ⟨5⟩, domain := ⟨0⟩, cspaceRoot := ObjId.ofNat 0,
    vspaceRoot := ObjId.ofNat 0, ipcBuffer := SeLe4n.VAddr.ofNat 0,
    schedContextBinding := .bound scId0, cpuAffinity := some core1 }

/-- A CBS state: `sc0` + `tcb0` in the object store; core 1's replenish queue holds
`scId0`'s pending replenishment (eligible at tick 5000); machine timer = 0.  This is
affinity-consistent (`scId0` is homed on core 1 — `tcb0.cpuAffinity = some core1`). -/
private def stCbs : SystemState :=
  let base := ((BootstrapBuilder.empty.withObject scId0.toObjId (.schedContext sc0)).withObject
    tid0.toObjId (.tcb tcb0)).build
  let q := ReplenishQueue.empty.insert scId0 5000
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core1 q }

/-- A `ReplenishQueue` is size-consistent (Bool form for runtime assertions). -/
private def sizeConsistentB (rq : ReplenishQueue) : Bool := rq.size == rq.entries.length

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1 SM5.H.2: `replenishOnCore` schedules an entry on the target core only. -/
private def runReplenishScenarios : IO Unit := do
  IO.println "--- §3.1 SM5.H.2 replenishOnCore scheduling ---"
  let st' := replenishOnCore stCbs core1 scId0 6000
  assertBool "replenishOnCore adds (scId0, 6000) to core 1's replenish queue"
    ((st'.scheduler.replenishQueueOnCore core1).entries.contains (scId0, 6000))
  assertBool "replenishOnCore keeps core 1's existing (scId0, 5000) entry"
    ((st'.scheduler.replenishQueueOnCore core1).entries.contains (scId0, 5000))
  assertBool "replenishOnCore leaves the boot core's replenish queue empty"
    ((st'.scheduler.replenishQueueOnCore bootCoreId).entries.isEmpty)
  assertBool "replenishOnCore never touches the object store (sc0 still resolves)"
    ((st'.getSchedContext? scId0).isSome)
  assertBool "replenishOnCore never advances the machine timer (still 0)"
    (st'.machine.timer == stCbs.machine.timer)
  assertBool "replenishOnCore keeps core 1's replenish queue size-consistent"
    (sizeConsistentB (st'.scheduler.replenishQueueOnCore core1))

/-- §3.2 SM5.H.4: the migration genuinely *moves* `scId0`'s entries between cores. -/
private def runMigrationScenarios : IO Unit := do
  IO.println "--- §3.2 SM5.H.4 SchedContext replenishment migration ---"
  -- Migrate scId0's replenishments from core 1 to the boot core (core 0).
  let stM := migrateSchedContextReplenishment stCbs scId0 core1 bootCoreId
  assertBool "after migration, core 1's queue no longer holds (scId0, 5000)"
    (!(stM.scheduler.replenishQueueOnCore core1).entries.contains (scId0, 5000))
  assertBool "after migration, the boot core's queue now holds (scId0, 5000)"
    ((stM.scheduler.replenishQueueOnCore bootCoreId).entries.contains (scId0, 5000))
  assertBool "after migration, the boot core's queue is size-consistent"
    (sizeConsistentB (stM.scheduler.replenishQueueOnCore bootCoreId))
  assertBool "after migration, core 1's queue is size-consistent"
    (sizeConsistentB (stM.scheduler.replenishQueueOnCore core1))
  assertBool "migration never touches the object store (sc0 still resolves)"
    ((stM.getSchedContext? scId0).isSome)
  -- A self-migration is the identity.
  assertBool "self-migration (core 1 → core 1) leaves core 1's queue unchanged"
    (((migrateSchedContextReplenishment stCbs scId0 core1 core1).scheduler.replenishQueueOnCore core1).entries
      == (stCbs.scheduler.replenishQueueOnCore core1).entries)
  -- A core untouched by the migration is unchanged.
  assertBool "migration (core 1 → boot core) frames a third core's queue (core 1 ≠ this)"
    ((migrateSchedContextReplenishment stCbs scId0 core1 bootCoreId).scheduler.replenishQueueOnCore ⟨2, by decide⟩).entries.isEmpty

/-- §3.3 SM5.H.4: the affinity-change-with-migration composite drags the SchedContext's
replenishments to the new home core. -/
private def runCompositeScenarios : IO Unit := do
  IO.println "--- §3.3 SM5.H.4 setThreadCpuAffinityWithMigration composite ---"
  -- determineTargetCore reads tcb0's affinity (= core 1).
  assertBool "tid0's home core (determineTargetCore) is core 1 (its cpuAffinity)"
    (determineTargetCore stCbs tid0 == core1)
  -- Rebind tid0 to the boot core: the composite migrates scId0's replenishments
  -- from core 1 to the boot core.
  match setThreadCpuAffinityWithMigration stCbs tid0 (some bootCoreId) with
  | .ok st' =>
      assertBool "composite (bind tid0 → boot core) succeeds"
        true
      assertBool "after the composite, the boot core's queue holds (scId0, 5000)"
        ((st'.scheduler.replenishQueueOnCore bootCoreId).entries.contains (scId0, 5000))
      assertBool "after the composite, core 1's queue no longer holds (scId0, 5000)"
        (!(st'.scheduler.replenishQueueOnCore core1).entries.contains (scId0, 5000))
      assertBool "after the composite, tid0's new home core is the boot core"
        (determineTargetCore st' tid0 == bootCoreId)
  | .error _ =>
      assertBool "composite (bind tid0 → boot core) succeeds" false
  -- The composite is fail-closed on a non-TCB target.
  assertBool "composite on a non-TCB target is .error .invalidArgument"
    (match setThreadCpuAffinityWithMigration stCbs (ThreadId.ofNat 999) (some bootCoreId) with
     | .error .invalidArgument => true
     | _ => false)
  -- An unbound thread (no SchedContext) has no replenishments to migrate; the
  -- composite is just the affinity write.
  let stUnbound : SystemState :=
    let base := (BootstrapBuilder.empty.withObject (ThreadId.ofNat 300).toObjId
      (.tcb { tcb0 with tid := ThreadId.ofNat 300, schedContextBinding := .unbound })).build
    base
  assertBool "composite on an unbound thread succeeds (affinity write only)"
    (match setThreadCpuAffinityWithMigration stUnbound (ThreadId.ofNat 300) (some bootCoreId) with
     | .ok _ => true | .error _ => false)

/-- §3.4 SM5.H.7: the CBS budget bounds (`budgetRemaining ≤ budget`) hold under
charge / refill, and the replenishment schedule stays bounded. -/
private def runBudgetScenarios : IO Unit := do
  IO.println "--- §3.4 SM5.H.7 CBS budget accounting ---"
  -- consumeBudget never exceeds the budget ceiling.
  assertBool "consumeBudget keeps budgetRemaining ≤ budget (50 → 49 ≤ 100)"
    ((consumeBudget sc0 1).budgetRemaining.val ≤ (consumeBudget sc0 1).budget.val)
  assertBool "consumeBudget decrements budgetRemaining (50 → 49)"
    ((consumeBudget sc0 1).budgetRemaining.val == 49)
  -- applyRefill caps at the budget ceiling.
  assertBool "applyRefill caps budgetRemaining at budget (50 + 1000 capped to 100)"
    ((applyRefill sc0 1000).budgetRemaining.val == 100)
  assertBool "applyRefill keeps budgetRemaining ≤ budget"
    ((applyRefill sc0 1000).budgetRemaining.val ≤ (applyRefill sc0 1000).budget.val)
  -- scheduleReplenishment keeps the schedule within maxReplenishments.
  assertBool "scheduleReplenishment keeps ≤ maxReplenishments entries"
    ((scheduleReplenishment sc0 0 ⟨10⟩).replenishments.length ≤ maxReplenishments)

/-- §3.5 SM5.H.5: the affinity-consistency invariant's *decidable* witnesses on the
default (boot) and the CBS fixture states. -/
private def runAffinityScenarios : IO Unit := do
  IO.println "--- §3.5 SM5.H.5 affinity consistency witnesses ---"
  -- On the boot state the replenish queues are empty (vacuously consistent).
  assertBool "boot: every core's replenish queue is empty (vacuous consistency)"
    ((allCores).all (fun c => ((default : SystemState).scheduler.replenishQueueOnCore c).entries.isEmpty))
  -- On stCbs, core 1's single entry's SchedContext is homed on core 1 (the
  -- decidable content of affinity-consistency for that entry).
  assertBool "stCbs: scId0's bound thread (tid0) is homed on core 1 (matches its queue)"
    (determineTargetCore stCbs tid0 == core1)
  assertBool "stCbs: core 1's replenish queue holds exactly scId0's entry"
    ((stCbs.scheduler.replenishQueueOnCore core1).entries == [(scId0, 5000)])

/-- §3.6: the SM5.H theorem-inventory partition counts (compiled-`decide` guards). -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.6 SM5.H inventory partition counts ---"
  assertBool "inventory has 54 entries"
    (decide (perCoreCbsTheorems.length = 54))
  assertBool "predicate category has 6 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .predicate)).length = 6))
  assertBool "replenish category has 12 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .replenish)).length = 12))
  assertBool "preservation category has 6 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .preservation)).length = 6))
  assertBool "migration category has 13 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .migration)).length = 13))
  assertBool "affinityWrite category has 3 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .affinityWrite)).length = 3))
  assertBool "consistency category has 8 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .consistency)).length = 8))
  assertBool "budget category has 6 entries"
    (decide ((perCoreCbsTheorems.filter (fun t => t.category == .budget)).length = 6))

def main : IO Unit := do
  IO.println "=== WS-SM SM5.H — Per-core CBS suite ==="
  runReplenishScenarios
  runMigrationScenarios
  runCompositeScenarios
  runBudgetScenarios
  runAffinityScenarios
  runInventoryChecks
  IO.println "=== SM5.H suite: all assertions passed ==="

end SeLe4n.Testing.SmpCbs

def main : IO Unit := SeLe4n.Testing.SmpCbs.main
