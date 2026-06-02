-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCoreInventory
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.F — Per-core PIP test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.F
"Per-core priority inheritance protocol" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.6, §5).

* **§1 Surface anchors** — every public SM5.F symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem
  (`computeMaxWaiterPriorityOnCore_le_global`, `pipBoost_perCore_consistent`,
  `pipBoostWithWake_*`, `blockingAcyclic_perCore`, `priorityInheritance_perCore_witness`,
  `restoreToReadyWithWake_*`) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_pip_suite` exercises the actual
  `computeMaxWaiterPriorityOnCore` / `pipBoostWithWake` / `determineTargetCore` /
  `blockingServerOnCore` / `restoreToReadyWithWake` computations on a concrete
  cross-core blocking scenario: a server bound to a remote core with a
  high-priority waiter on the boot core.
-/

namespace SeLe4n.Testing.SmpPip

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.PriorityInheritance
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReady restoreToReadyOnCore restoreToReadyWithWake)

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.F public symbol resolves
-- ============================================================================

-- SM5.F.1 computeMaxWaiterPriorityOnCore + decomposition + frame:
#check @computeMaxWaiterPriorityOnCore
#check @optPriorityVal
#check @computeMaxWaiterPriorityOnCore_no_waiters
#check @computeMaxWaiterPriorityOnCore_le_global
#check @computeMaxWaiterPriorityOnCore_frame

-- SM5.F.2 updatePipBoostOnCore + bridge / frame / preservation:
#check @updatePipBoostOnCore
#check @updatePipBoost_eq_updatePipBoostOnCore_bootCore
#check @updatePipBoostOnCore_preserves_objects_invExt
#check @updatePipBoostOnCore_objects_ne
#check @updatePipBoostOnCore_preserves_objectIndex
#check @updatePipBoostOnCore_preserves_blockingServer
#check @updatePipBoostOnCore_preserves_blockingAcyclic
#check @updatePipBoostOnCore_runQueueOnCore_ne
#check @updatePipBoostOnCore_currentOnCore
#check @updatePipBoostOnCore_getTcb?_pipBoost

-- SM5.F.3 pipBoost_perCore_consistent:
#check @optPriorityVal_pipBoost_le_effectiveSchedParams
#check @pipBoost_perCore_consistent

-- SM5.F.2 pipBoostWithWake (cross-core PIP wake):
#check @pipBoostWithWake
#check @pipBoostWithWake_state
#check @pipBoostWithWake_no_sgi_if_local
#check @pipBoostWithWake_emits_sgi_if_remote
#check @pipBoostWithWake_no_sgi_if_noop
#check @pipBoostWithWake_sgi_is_reschedule
#check @pipBoostWithWake_emits_at_most_one_sgi
#check @pipBoostWithWake_preserves_objects_invExt
#check @pipBoostWithWake_preserves_blockingAcyclic
#check @pipBoostWithWake_bootCore_unbound

-- SM5.F.4 propagatePipChainCrossCore (donation chain across cores):
#check @propagatePipChainCrossCore
#check @propagatePipChainCrossCore_zero
#check @propagatePipChainCrossCore_step
#check @propagatePipChainCrossCoreState
#check @propagatePipChainCrossCoreState_step
#check @propagatePipChainCrossCore_preserves_objects_invExt
#check @propagatePipChainCrossCore_preserves_blockingAcyclic
#check @propagatePipChainCrossCore_zero_sgis
#check @propagatePipChainCrossCore_no_sgis_head_terminal
#check @propagatePipChainCrossCore_head_sgi_remote

-- SM5.F.5 / SM5.F.6 restoreToReadyOnCore / restoreToReadyWithWake:
#check @restoreToReadyOnCore
#check @restoreToReadyWithWake
#check @restoreToReady_objects_invExt
#check @restoreToReadyOnCore_preserves_objects_invExt
#check @restoreToReadyOnCore_currentOnCore
#check @restoreToReadyOnCore_runQueueOnCore_ne
#check @restoreToReadyOnCore_pipBoost_recomputed
#check @restoreToReadyWithWake_state
#check @restoreToReadyWithWake_no_sgi_if_local
#check @restoreToReadyWithWake_emits_sgi_if_remote
#check @restoreToReadyWithWake_sgi_is_reschedule
#check @restoreToReadyWithWake_preserves_objects_invExt

-- SM5.F.7 / SM5.F.8 per-core blocking graph:
#check @blockingServerOnCore
#check @blockingServerOnCore_eq_global_of_onCore
#check @blockingServerOnCore_none_of_offCore
#check @blockingServerOnCore_implies_global
#check @blockingServerOnCore_subgraph
#check @blockingGraphOnCore_consistent
#check @blockingChainOnCore
#check @blockingChainOnCore_subset
#check @blockingAcyclicOnCore
#check @blockingAcyclic_perCore

-- SM5.F.9 aggregate witness + inventory:
#check @priorityInheritance_perCore_witness
#check @perCorePipTheorems
#check @perCorePipTheorems_count
#check @perCorePipTheorems_partition_sum
#check @perCorePipTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): apply each headline theorem
-- ============================================================================

-- SM5.F.1: the per-core waiter slice never exceeds the global boost.
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    optPriorityVal (computeMaxWaiterPriorityOnCore st c tid)
      ≤ optPriorityVal (computeMaxWaiterPriority st tid) :=
  computeMaxWaiterPriorityOnCore_le_global st c tid

-- SM5.F.2: the single-core boost is the per-core boost at the boot core (bridge).
example (st : SystemState) (tid : SeLe4n.ThreadId) :
    updatePipBoost st tid = updatePipBoostOnCore st bootCoreId tid :=
  updatePipBoost_eq_updatePipBoostOnCore_bootCore st tid

-- SM5.F.3: a PIP-consistent holder's per-core slice is bounded by its effective priority.
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hConsistent : tcb.pipBoost = computeMaxWaiterPriority st tid) :
    optPriorityVal (computeMaxWaiterPriorityOnCore st c tid) ≤ (effectiveSchedParams st tcb).1.val :=
  pipBoost_perCore_consistent st c tid tcb hTcb hConsistent

-- SM5.F.2: a local PIP boost emits no SGI.
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hLocal : determineTargetCore st tid = ec) :
    (pipBoostWithWake st tid ec).2 = none :=
  pipBoostWithWake_no_sgi_if_local st tid ec hLocal

-- SM5.F.2: a remote material PIP boost emits a reschedule SGI to the home core.
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (t t' : TCB)
    (hRemote : determineTargetCore st tid ≠ ec)
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : t.pipBoost ≠ t'.pipBoost) :
    (pipBoostWithWake st tid ec).2 = some (determineTargetCore st tid, SgiKind.reschedule) :=
  pipBoostWithWake_emits_sgi_if_remote st tid ec t t' hRemote hPre hPost hMaterial

-- SM5.F.4: the cross-core donation chain walk preserves blocking acyclicity.
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat)
    (hInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (propagatePipChainCrossCore st tid ec fuel).1 :=
  propagatePipChainCrossCore_preserves_blockingAcyclic st tid ec fuel hInv hAcyclic

-- SM5.F.6: the per-core resume recomputes pipBoost from the GLOBAL blocking graph.
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (t1 : TCB)
    (hTcb1 : (restoreToReady st tid).getTcb? tid = some t1)
    (hInv : (restoreToReady st tid).objects.invExt) :
    ∃ t', (restoreToReadyOnCore st c tid).getTcb? tid = some t' ∧
      t'.pipBoost = computeMaxWaiterPriority (restoreToReady st tid) tid :=
  restoreToReadyOnCore_pipBoost_recomputed st c tid t1 hTcb1 hInv

-- SM5.F.7: the global blocking graph is the union of the per-core slices.
example (st : SystemState) (tid s : SeLe4n.ThreadId) :
    (∃ c, blockingServerOnCore st c tid = some s) ↔ blockingServer st tid = some s :=
  blockingGraphOnCore_consistent st tid s

-- SM5.F.8: the per-core blocking slice is acyclic.
example (st : SystemState) (c : CoreId) (hAcyclic : blockingAcyclic st) :
    blockingAcyclicOnCore st c :=
  blockingAcyclic_perCore st c hAcyclic

-- SM5.F.9: aggregate per-core PIP soundness witness.
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (pipBoostWithWake st tid ec).1 ∧
    (∀ c, blockingAcyclicOnCore st c) ∧
    (∀ c t, blockingServerOnCore st c t = none ∨ blockingServerOnCore st c t = blockingServer st t) :=
  priorityInheritance_perCore_witness st tid ec hInv hAcyclic

-- ============================================================================
-- §3  Runtime assertions (Tier-2): concrete cross-core blocking scenario
-- ============================================================================

/-- Core 1 — a non-boot core (the server's home). -/
private def core1 : CoreId := ⟨1, by decide⟩
private def core0 : CoreId := bootCoreId

private def srv : SeLe4n.ThreadId := ThreadId.ofNat 200
private def cli : SeLe4n.ThreadId := ThreadId.ofNat 201

/-- A server TCB bound to `aff`, priority `prio`, IPC-ready, no PIP boost. -/
private def mkServerTcb (tidN : Nat) (prio : Nat) (aff : CoreId) : TCB :=
  { tid := ThreadId.ofNat tidN, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0, ipcState := .ready, cpuAffinity := some aff }

/-- A waiter TCB (unbound, so it homes to the boot core) blocked on reply to
`server`, priority `prio`. -/
private def mkWaiterTcb (tidN : Nat) (prio : Nat) (server : Nat) : TCB :=
  { tid := ThreadId.ofNat tidN, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0,
    ipcState := .blockedOnReply (ObjId.ofNat 50) (some (ThreadId.ofNat server)) }

/-- The cross-core blocking scenario: a server `srv` bound to the **remote** core
1, with a high-priority (10) waiter `cli` blocked on reply to it.  `cli` is
unbound, so it homes to the boot core 0. -/
private def st : SystemState :=
  ((BootstrapBuilder.empty.withObject srv.toObjId (.tcb (mkServerTcb 200 5 core1))).withObject
    cli.toObjId (.tcb (mkWaiterTcb 201 10 200))).build

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1: SM5.F.1 — per-core waiter-priority slice + the per-core ≤ global decomposition. -/
private def runComputeChecks : IO Unit := do
  IO.println "--- §3.1 SM5.F.1 computeMaxWaiterPriorityOnCore ---"
  assertBool "global computeMaxWaiterPriority of the server is the waiter's priority (10)"
    (decide (computeMaxWaiterPriority st srv = some ⟨10⟩))
  assertBool "core 0's slice carries the (boot-core-homed) waiter's priority (10)"
    (decide (computeMaxWaiterPriorityOnCore st core0 srv = some ⟨10⟩))
  assertBool "core 1's slice is empty (the waiter does not home to core 1)"
    (decide (computeMaxWaiterPriorityOnCore st core1 srv = none))
  assertBool "per-core slice (core 0) ≤ global boost (decomposition, SM5.F.1)"
    (decide (optPriorityVal (computeMaxWaiterPriorityOnCore st core0 srv)
              ≤ optPriorityVal (computeMaxWaiterPriority st srv)))
  assertBool "per-core slice (core 1, empty) ≤ global boost (decomposition)"
    (decide (optPriorityVal (computeMaxWaiterPriorityOnCore st core1 srv)
              ≤ optPriorityVal (computeMaxWaiterPriority st srv)))

/-- §3.2: SM5.F.2 — `determineTargetCore` + the cross-core PIP wake SGI emission. -/
private def runWakeChecks : IO Unit := do
  IO.println "--- §3.2 SM5.F.2 determineTargetCore + pipBoostWithWake ---"
  assertBool "the server's home core is the remote core 1 (bound affinity)"
    (decide (determineTargetCore st srv = core1))
  assertBool "the (unbound) waiter homes to the boot core 0"
    (decide (determineTargetCore st cli = core0))
  -- Executing on core 0, the remote material boost pokes core 1 with a reschedule SGI.
  assertBool "remote material PIP boost emits (core1, .reschedule) SGI"
    (decide ((pipBoostWithWake st srv core0).2 = some (core1, SgiKind.reschedule)))
  -- Executing on core 1 (the home core), no SGI is needed.
  assertBool "local PIP boost (executing on the home core) emits NO SGI"
    (decide ((pipBoostWithWake st srv core1).2 = none))
  -- The boost VALUE applied is the GLOBAL max (10), regardless of which core executes.
  assertBool "the boost sets the server's pipBoost to the GLOBAL max (some 10)"
    (decide (((pipBoostWithWake st srv core0).1.getTcb? srv).bind (·.pipBoost) = some ⟨10⟩))

/-- §3.3: SM5.F.7 — the per-core blocking-graph slice + consistency with the global graph. -/
private def runBlockingGraphChecks : IO Unit := do
  IO.println "--- §3.3 SM5.F.7 blockingServerOnCore + consistency ---"
  assertBool "the global blocking edge: cli → srv"
    (decide (blockingServer st cli = some srv))
  assertBool "core 0's slice carries cli's edge (cli homes to core 0)"
    (decide (blockingServerOnCore st core0 cli = some srv))
  assertBool "core 1's slice does NOT carry cli's edge (cli homes to core 0)"
    (decide (blockingServerOnCore st core1 cli = none))
  -- The union over cores recovers the global edge (consistency).
  assertBool "the global edge is recovered by SOME core's slice (consistency)"
    (decide (blockingServerOnCore st (determineTargetCore st cli) cli = some srv))

/-- §3.4: SM5.F.6 — the cross-core resume wake SGI emission. -/
private def runResumeChecks : IO Unit := do
  IO.println "--- §3.4 SM5.F.6 restoreToReadyWithWake ---"
  -- Resuming the server (bound to core 1) while executing on core 0 pokes core 1.
  assertBool "remote resume emits (core1, .reschedule) SGI"
    (decide ((restoreToReadyWithWake st srv core0).2 = some (core1, SgiKind.reschedule)))
  -- Resuming while executing on the home core 1 needs no SGI.
  assertBool "local resume (executing on the home core) emits NO SGI"
    (decide ((restoreToReadyWithWake st srv core1).2 = none))

/-- §3.5: SM5.F inventory partition counts. -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.5 SM5.F theorem inventory ---"
  assertBool "inventory has 61 entries"
    (decide (perCorePipTheorems.length = 61))
  assertBool "compute category has 5 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .compute)).length = 5))
  assertBool "updateBoost category has 10 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .updateBoost)).length = 10))
  assertBool "wake category has 10 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .wake)).length = 10))
  assertBool "chain category has 11 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .chain)).length = 11))
  assertBool "resume category has 12 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .resume)).length = 12))
  assertBool "blockingGraph category has 10 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .blockingGraph)).length = 10))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCorePipTheorems.map (·.identifier)).Nodup)

def runSmpPipChecks : IO Unit := do
  IO.println "WS-SM SM5.F — Per-core PIP suite"
  IO.println "===================================="
  runComputeChecks
  runWakeChecks
  runBlockingGraphChecks
  runResumeChecks
  runInventoryChecks
  IO.println "===================================="
  IO.println "All SM5.F per-core PIP checks PASS."

end SeLe4n.Testing.SmpPip

def main : IO Unit :=
  SeLe4n.Testing.SmpPip.runSmpPipChecks

