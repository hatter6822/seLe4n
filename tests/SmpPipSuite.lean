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
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReady restoreToReadyOnCore restoreToReadyWithWake
  resumeThreadOnCore)

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

-- SM5.F completion pass (B5/B6/B7/B8/C9/D11/F13/dispatch):
-- SM5.F.1 full decomposition:
#check @computeMaxWaiterPriority_eq_sup_perCore
#check @computeMaxWaiterPriority_value
#check @computeMaxWaiterPriorityOnCore_value
-- SM5.F.2/3 home-core stability + post-boost dominance:
#check @updatePipBoostOnCore_getTcb?_cpuAffinity
#check @updatePipBoostOnCore_eq_self_of_getTcb?_none
#check @updatePipBoostOnCore_preserves_determineTargetCore
#check @updatePipBoostOnCore_establishes_perCore_dominance
-- SM5.F.4 C9 runnability gate:
#check @pipBoostWithWake_no_sgi_if_not_runnable
-- SM5.F.4 chain SGI completeness:
#check @propagatePipChainCrossCore_head_emission_mem
#check @propagatePipChainCrossCore_tail_sgis_mem
#check @propagatePipChainCrossCore_sgis_all_reschedule
#check @propagatePipChainCrossCore_sgi_length_le_fuel
#check @propagatePipChainCrossCore_second_link_sgi_remote
#check @propagatePipChainCrossCore_singleCore_no_sgis
#check @propagatePipChainCrossCoreState_singleCore_eq_propagate
-- SM5.F.4 memory-model happens-before:
#check @pipBoostOrdering_synchronizesWith
#check @pipBoostOrdering_happensBefore
-- SM5.F.6 complete per-core resume:
#check @resumeReadyMidState_getTcb?_ready
#check @resumeReadyMidState_objects_invExt
#check @resumeThreadOnCore_sets_threadState
#check @resumeThreadOnCore_preserves_objects_invExt
#check @resumeThreadOnCore_rejects_non_inactive
#check @resumeThreadOnCore_rejects_non_tcb
#check @resumeThreadOnCore_local_no_sgi
#check @resumeThreadOnCore_remote_sgi
-- SM5.F.9 full witness:
#check @priorityInheritance_perCore_witness_full
-- SM5.F.4 cross-core wake dispatch:
#check @computeCrossCoreSgis
#check @computeCrossCoreSgis_all_reschedule
#check @computeCrossCoreSgis_nil_single_core
-- SM6.B wake-SGI fix: the body fires on a cross-core wake (not only a PIP boost):
#check @crossCoreSgiBody_remote_wake
#check @crossCoreWakeDispatch
#check @crossCoreWakeDispatch_singleCore
#check @pipChainWakeDispatch
#check @pipChainWakeDispatch_singleCore
#check @perCorePipTheorems_memoryModel_count
#check @perCorePipTheorems_dispatch_count

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

-- SM5.F.2 (PR #811 P2-2): a remote, runnable-on-home, material PIP boost emits a
-- reschedule SGI to the home core.  "Material" is now the *effective* priority
-- (run-queue bucket key) changing, exactly the `updatePipBoostOnCore` bucket-migration
-- condition (the WS-SM SM5.F.4 C9 runnability gate is part of the hypotheses).
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (t t' : TCB)
    (hRemote : determineTargetCore st tid ≠ ec)
    (hRunnable : tid ∈ st.scheduler.runQueueOnCore (determineTargetCore st tid))
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : (resolveEffectivePrioDeadline st t).1
      ≠ (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1) :
    (pipBoostWithWake st tid ec).2 = some (determineTargetCore st tid, SgiKind.reschedule) :=
  pipBoostWithWake_emits_sgi_if_remote st tid ec t t' hRemote hRunnable hPre hPost hMaterial

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

-- SM5.F.1 (B5): the global boost is exactly the sup over every core's slice.
example (st : SystemState) (tid : SeLe4n.ThreadId) :
    optPriorityVal (computeMaxWaiterPriority st tid)
      = allCores.foldl
          (fun n c => Nat.max n (optPriorityVal (computeMaxWaiterPriorityOnCore st c tid))) 0 :=
  computeMaxWaiterPriority_eq_sup_perCore st tid

-- SM5.F.4 (C9): a boost of a non-runnable holder fires no SGI.
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hNotRun : tid ∉ st.scheduler.runQueueOnCore (determineTargetCore st tid)) :
    (pipBoostWithWake st tid ec).2 = none :=
  pipBoostWithWake_no_sgi_if_not_runnable st tid ec hNotRun

-- SM5.F.4: home-core stability — a boost never changes any thread's home core.
example (st : SystemState) (c : CoreId) (tid t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    determineTargetCore (updatePipBoostOnCore st c tid) t = determineTargetCore st t :=
  updatePipBoostOnCore_preserves_determineTargetCore st c tid t hInv

-- SM5.F.6 (F13): every successful complete per-core resume leaves the resumed thread
-- `.Ready` — including the PR #811 P2-5 inline local reschedule (which frames out the
-- resumed thread, never the executing core's current).
example (st : SystemState) (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (tcb : TCB)
    (st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore ec ≠ some vtid.val)
    (h : resumeThreadOnCore st vtid ec = .ok (st', sgi)) :
    ∃ t', st'.getTcb? vtid.val = some t' ∧ t'.threadState = .Ready :=
  resumeThreadOnCore_sets_threadState st vtid ec tcb st' sgi hGet hInactive hInv hNotCur h

-- SM5.F.4: the diff-based dispatch is inert on single-core.
example (pre post : SystemState)
    (hAllBoot : ∀ t, determineTargetCore post t = bootCoreId) :
    crossCoreWakeDispatch pre post bootCoreId = pure () :=
  crossCoreWakeDispatch_singleCore pre post hAllBoot

-- SM5.F.4: memory-model — the boost publication happens-before the home core observes it.
example (boostCore homeCore : CoreId) (loc : AtomicLocation) (v : Nat) :
    happensBefore (wakeOrderingTrace boostCore homeCore loc v)
      (wakeReleaseEvent boostCore loc v) (wakeAcquireEvent homeCore loc v) :=
  pipBoostOrdering_happensBefore boostCore homeCore loc v

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
unbound, so it homes to the boot core 0.  The server is **runnable on its home
core 1** (in core 1's run queue at its base priority 5), so a cross-core boost of
it genuinely warrants poking core 1 (the WS-SM SM5.F.4 C9 runnability gate). -/
private def st : SystemState :=
  let base := ((BootstrapBuilder.empty.withObject srv.toObjId (.tcb (mkServerTcb 200 5 core1))).withObject
    cli.toObjId (.tcb (mkWaiterTcb 201 10 200))).build
  { base with scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(srv, ⟨5⟩)]) }

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
  -- PR #811 P2-3: the resume wake sets the resumed thread .Ready (not left .Inactive),
  -- so the poked core never dispatches a still-inactive run-queue entry.
  assertBool "P2-3 restoreToReadyWithWake leaves the resumed thread threadState = .Ready"
    (((restoreToReadyWithWake st srv core0).1.getTcb? srv).map (·.threadState)
      == some ThreadState.Ready)

/-- §3.5: SM5.F inventory partition counts. -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.5 SM5.F theorem inventory ---"
  assertBool "inventory has 99 entries"
    (decide (perCorePipTheorems.length = 99))
  assertBool "compute category has 8 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .compute)).length = 8))
  assertBool "updateBoost category has 14 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .updateBoost)).length = 14))
  assertBool "wake category has 11 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .wake)).length = 11))
  assertBool "chain category has 18 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .chain)).length = 18))
  assertBool "resume category has 24 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .resume)).length = 24))
  assertBool "blockingGraph category has 10 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .blockingGraph)).length = 10))
  assertBool "memoryModel category has 2 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .memoryModel)).length = 2))
  assertBool "dispatch category has 8 entries"
    (decide ((perCorePipTheorems.filter (fun t => t.category == .dispatch)).length = 8))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCorePipTheorems.map (·.identifier)).Nodup)

/-- The same scenario but with the server NOT runnable on its home core (no run
queue) — the WS-SM SM5.F.4 C9 negative case. -/
private def stNoRq : SystemState :=
  ((BootstrapBuilder.empty.withObject srv.toObjId (.tcb (mkServerTcb 200 5 core1))).withObject
    cli.toObjId (.tcb (mkWaiterTcb 201 10 200))).build

/-- An all-unbound variant (server NOT bound to a remote core) — the single-core
deployment in which every thread homes to the boot core.  Exercises the single-core
bridges (`propagatePipChainCrossCore_singleCore_no_sgis`). -/
private def stUnbound : SystemState :=
  ((BootstrapBuilder.empty.withObject srv.toObjId
      (.tcb { mkServerTcb 200 5 core1 with cpuAffinity := none })).withObject
    cli.toObjId (.tcb (mkWaiterTcb 201 10 200))).build

/-- A high-base server bound to the remote core 1. -/
private def srvHi : SeLe4n.ThreadId := ThreadId.ofNat 202
/-- A low-priority waiter blocked on `srvHi`. -/
private def cliLo : SeLe4n.ThreadId := ThreadId.ofNat 203

/-- The PR #811 P2-2 fixture: a server `srvHi` whose BASE priority (10) already
*dominates* its waiter `cliLo`'s priority (5).  Boosting `srvHi` sets its `pipBoost`
to `some 5`, but its *effective* priority stays `max(10, 5) = 10` — so no run-queue
bucket migrates and there is no scheduling consequence on the home core.  `srvHi` is
runnable on its home core 1, so the C9 runnability gate is SATISFIED — only the new
effective-priority materiality gate suppresses the (otherwise spurious) cross-core
IPI that the old raw-`pipBoost` gate would have fired. -/
private def stImmaterial : SystemState :=
  let base := ((BootstrapBuilder.empty.withObject srvHi.toObjId
      (.tcb (mkServerTcb 202 10 core1))).withObject
    cliLo.toObjId (.tcb (mkWaiterTcb 203 5 202))).build
  { base with scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(srvHi, ⟨10⟩)]) }

/-- §3.6: WS-SM SM5.F.4 C9 — the runnability gate on the cross-core boost SGI. -/
private def runC9Checks : IO Unit := do
  IO.println "--- §3.6 SM5.F.4 C9 runnability gate ---"
  -- Server runnable on its home core 1 ⇒ a remote material boost fires the SGI.
  assertBool "runnable remote holder: boost fires (core1, .reschedule) SGI"
    (decide ((pipBoostWithWake st srv core0).2 = some (core1, SgiKind.reschedule)))
  -- Server NOT runnable on core 1 (no run queue) ⇒ no spurious cross-core IPI.
  assertBool "non-runnable remote holder: boost fires NO SGI (C9 — no spurious IPI)"
    (decide ((pipBoostWithWake stNoRq srv core0).2 = none))
  -- The boost VALUE is still set in both cases (only the SGI is gated).
  assertBool "non-runnable boost still sets the GLOBAL pipBoost (some 10)"
    (decide (((pipBoostWithWake stNoRq srv core0).1.getTcb? srv).bind (·.pipBoost) = some ⟨10⟩))

/-- §3.7: WS-SM SM5.F.1 — the exact per-core decomposition (global = sup over cores). -/
private def runDecompositionChecks : IO Unit := do
  IO.println "--- §3.7 SM5.F.1 exact per-core decomposition ---"
  assertBool "global boost = sup over allCores of the per-core slices (SM5.F.1 completeness)"
    (decide (optPriorityVal (computeMaxWaiterPriority st srv)
      = allCores.foldl (fun n c => Nat.max n (optPriorityVal (computeMaxWaiterPriorityOnCore st c srv))) 0))
  assertBool "the decomposition value is the waiter's priority (10)"
    (decide (allCores.foldl
      (fun n c => Nat.max n (optPriorityVal (computeMaxWaiterPriorityOnCore st c srv))) 0 = 10))

/-- §3.8: WS-SM SM5.F.4 — cross-core donation chain SGI completeness. -/
private def runChainChecks : IO Unit := do
  IO.println "--- §3.8 SM5.F.4 cross-core chain SGI completeness ---"
  -- Walk the chain from the waiter `cli`: cli (local, no-op) → srv (remote, runnable,
  -- material) — so the chain collects srv's reschedule SGI to core 1.
  assertBool "chain from cli collects srv's (core1, .reschedule) SGI (head + tail completeness)"
    (decide ((propagatePipChainCrossCore st cli core0 3).2 = [(core1, SgiKind.reschedule)]))
  assertBool "every chain SGI is a .reschedule (well-formed)"
    (decide ((propagatePipChainCrossCore st cli core0 3).2.all (fun p => p.2 == SgiKind.reschedule)))
  assertBool "the chain SGI list is bounded by fuel (≤ 3, no storm)"
    (decide ((propagatePipChainCrossCore st cli core0 3).2.length ≤ 3))

/-- §3.9: WS-SM SM5.F.4 — the cross-core wake dispatch (computeCrossCoreSgis). -/
private def runDispatchChecks : IO Unit := do
  IO.println "--- §3.9 SM5.F.4 cross-core wake dispatch ---"
  -- A cross-core boost: pre = st (srv pipBoost none), post = the boosted state.
  -- The diff-based dispatch detects srv's remote pipBoost change and fires (core1).
  let post := (pipBoostWithWake st srv core0).1
  assertBool "diff dispatch FIRES for a cross-core boost: [(core1, .reschedule)]"
    (decide (computeCrossCoreSgis st post core0 = [(core1, SgiKind.reschedule)]))
  -- Executing on core 1 (the home core), the same boost diff pokes no remote core.
  assertBool "diff dispatch is empty when executing on the boosted thread's home core"
    (decide (computeCrossCoreSgis st post core1 = []))
  -- No change ⇒ no dispatch (the identity diff).
  assertBool "diff dispatch of an unchanged state is empty (no spurious poke)"
    (decide (computeCrossCoreSgis st st core0 = []))
  -- Every dispatched SGI is a reschedule.
  assertBool "every dispatched SGI is a .reschedule"
    (decide ((computeCrossCoreSgis st post core0).all (fun p => p.2 == SgiKind.reschedule)))
  -- PR #811 P2-1: a boost of a NON-runnable remote holder (stNoRq: srv bound to core1
  -- but not in its run queue) emits no diff SGI — the C9 runnability gate, consistent
  -- with pipBoostWithWake_no_sgi_if_not_runnable (no spurious cross-core IPI).
  let postNoRq := (pipBoostWithWake stNoRq srv core0).1
  assertBool "P2-1 diff dispatch is empty for a boost of a NON-runnable holder (C9 consistency)"
    (decide (computeCrossCoreSgis stNoRq postNoRq core0 = []))
  -- WS-SM SM6.B (the wake-SGI fix): a cross-core WAKE — srv non-runnable in stNoRq,
  -- woken onto its remote home core1 — now fires the diff-recovered reschedule SGI.
  -- The earlier priority-only gate dropped this (a wake leaves the effective priority
  -- unchanged), so a live cross-core notification / endpoint-call wake reached the
  -- remote core only at its next local timer tick.  The diff dispatch must now match
  -- the wake operation's own surfaced SGI (`crossCoreSgiBody_remote_wake`).
  let postWake := (wakeThread stNoRq srv core0).1
  assertBool "SM6.B wake: the wake op itself surfaces (core1, .reschedule)"
    (decide ((wakeThread stNoRq srv core0).2 = some (core1, SgiKind.reschedule)))
  assertBool "SM6.B wake: diff dispatch now FIRES for the cross-core wake: [(core1, .reschedule)]"
    (decide (computeCrossCoreSgis stNoRq postWake core0 = [(core1, SgiKind.reschedule)]))
  assertBool "SM6.B wake: executing on the woken thread's home core pokes nothing (inert)"
    (decide (computeCrossCoreSgis stNoRq postWake core1 = []))

/-- §3.10: completion-pass non-vacuity — B6 dominance, B7 home-core stability,
F13 complete resume, and the single-core bridge, exercised on concrete states. -/
private def runCompletionNonVacuityChecks : IO Unit := do
  IO.println "--- §3.10 completion-pass non-vacuity (B6/B7/F13/single-core) ---"
  -- B7: a boost never changes any thread's home core (cpuAffinity untouched).
  assertBool "B7 home-core stability: the boost leaves srv's home core unchanged"
    (decide (determineTargetCore (pipBoostWithWake st srv core0).1 srv = determineTargetCore st srv))
  assertBool "B7 home-core stability: the boost leaves cli's home core unchanged"
    (decide (determineTargetCore (pipBoostWithWake st srv core0).1 cli = determineTargetCore st cli))
  -- B6: post-boost the holder's effective priority is the waiter's (10) — it
  -- dominates core 0's pre-state waiter slice (10).
  assertBool "B6 dominance: the boosted holder's effective priority is 10 (dominates the slice)"
    (decide ((((pipBoostWithWake st srv core0).1.getTcb? srv).map
      (fun t => (effectiveSchedParams (pipBoostWithWake st srv core0).1 t).1.val)).getD 0 = 10))
  -- F13: the complete per-core resume of an Inactive thread (stNoRq, srv Inactive +
  -- not enqueued) sets threadState := .Ready AND returns the remote .reschedule SGI.
  -- (The match returns a Bool directly — SystemState has no DecidableEq, so we do not
  -- `decide` over the Except result; we project the observable Bool facts.)
  assertBool "F13 resumeThreadOnCore: Inactive→Ready + remote (core1, .reschedule) SGI"
    (match resumeThreadOnCore stNoRq ((ThreadId.ofNat 200).toValid (by decide)) core0 with
     | .ok (st', sgi) =>
       (sgi == some (core1, SgiKind.reschedule)) &&
       ((st'.getTcb? srv).map (·.threadState) == some ThreadState.Ready)
     | .error _ => false)
  -- F13: resume of a non-existent (non-TCB) target → invalidArgument (rejection path).
  assertBool "F13 resumeThreadOnCore: a non-TCB target → invalidArgument"
    (match resumeThreadOnCore stNoRq ((ThreadId.ofNat 999).toValid (by decide)) core0 with
     | .error .invalidArgument => true
     | _ => false)
  -- Single-core bridge: on the all-unbound state the chain walk fires NO cross-core SGI.
  assertBool "single-core (all-unbound) chain walk fires no cross-core SGI"
    (decide ((propagatePipChainCrossCore stUnbound cli bootCoreId 3).2 = []))

/-- §3.11: WS-SM SM5.F.2 (PR #811 P2-2) — the effective-priority materiality gate.
A boost that raises `pipBoost` but NOT the *effective* priority (the holder's base
already dominates the boost) migrates no run-queue bucket and so fires NO cross-core
SGI — closing the spurious IPI the old raw-`pipBoost` gate would have emitted.  The
holder is runnable on its home core, so the C9 runnability gate is satisfied: only the
new effective-priority gate suppresses the poke. -/
private def runP2MaterialityChecks : IO Unit := do
  IO.println "--- §3.11 SM5.F.2 P2-2 effective-priority materiality gate ---"
  -- The boost VALUE is still applied: srvHi.pipBoost := some 5 (the waiter's prio).
  assertBool "P2-2 the immaterial boost still sets pipBoost := some 5 (value applied)"
    (decide (((pipBoostWithWake stImmaterial srvHi core0).1.getTcb? srvHi).bind (·.pipBoost)
              = some ⟨5⟩))
  -- srvHi IS runnable on its home core 1 — the C9 gate is satisfied, not the suppressor.
  assertBool "P2-2 the holder IS runnable on its home core (C9 gate satisfied, not suppressing)"
    (decide (srvHi ∈ stImmaterial.scheduler.runQueueOnCore core1))
  -- The effective priority of the POST-BOOST holder is unchanged (base 10 dominates the
  -- applied boost 5) — read from the genuinely boosted state, so this exercises the exact
  -- `max(base, pipBoost) = max(10, 5) = 10` the materiality gate compares.
  assertBool "P2-2 post-boost effective priority is STILL 10 (base 10 dominates the applied boost 5)"
    (match (pipBoostWithWake stImmaterial srvHi core0).1.getTcb? srvHi with
     | some t => decide ((resolveEffectivePrioDeadline (pipBoostWithWake stImmaterial srvHi core0).1 t).1
                          = ⟨10⟩)
     | none => false)
  -- THE FIX: no SGI fires for the immaterial boost (no spurious cross-core IPI).
  assertBool "P2-2 immaterial boost fires NO SGI (effective bucket unchanged)"
    (decide ((pipBoostWithWake stImmaterial srvHi core0).2 = none))
  -- The diff-based dispatch agrees: no dispatch for the immaterial diff.
  let postImm := (pipBoostWithWake stImmaterial srvHi core0).1
  assertBool "P2-2 diff dispatch is empty for the immaterial boost (matches direct path)"
    (decide (computeCrossCoreSgis stImmaterial postImm core0 = []))
  -- Contrast: the original fixture (srv base 5, waiter 10) IS material (5 → 10), fires.
  assertBool "P2-2 contrast: a MATERIAL boost (srv 5→10) still fires (core1, .reschedule)"
    (decide ((pipBoostWithWake st srv core0).2 = some (core1, SgiKind.reschedule)))

/-- §3.12: WS-SM SM5.F.6 (PR #811 P2-5) — the inline LOCAL reschedule.  A resume whose
home core IS the executing core processes the reschedule **inline** (the exact handler
the remote core would otherwise run on the `.reschedule` SGI): the resumed thread is
dispatched to current on that core, keeps `threadState = .Ready`, and NO cross-core SGI
is emitted.  A resume from a *remote* executing core returns the SGI instead. -/
private def runP5LocalRescheduleChecks : IO Unit := do
  IO.println "--- §3.12 SM5.F.6 P2-5 inline local reschedule ---"
  -- LOCAL: resume srv (bound to core 1) while EXECUTING on core 1 (its home).
  match resumeThreadOnCore stNoRq ((ThreadId.ofNat 200).toValid (by decide)) core1 with
  | .ok (st4, sgi) =>
    assertBool "P2-5 local resume succeeds with NO cross-core SGI (reschedule done inline)"
      (sgi == none)
    assertBool "P2-5 local resume leaves the resumed thread threadState = .Ready"
      ((st4.getTcb? srv).map (·.threadState) == some ThreadState.Ready)
    assertBool "P2-5 local resume dispatches the resumed thread to current on its core"
      (st4.scheduler.currentOnCore core1 == some srv)
  | .error _ =>
    assertBool "P2-5 local resume must succeed on the well-formed fixture" false
  -- REMOTE contrast: resuming from a different executing core returns the SGI instead.
  match resumeThreadOnCore stNoRq ((ThreadId.ofNat 200).toValid (by decide)) core0 with
  | .ok (_, sgi) =>
    assertBool "P2-5 contrast: a REMOTE resume returns the (core1, .reschedule) SGI"
      (sgi == some (core1, SgiKind.reschedule))
  | .error _ =>
    assertBool "P2-5 remote resume must succeed" false

/-- §3.13: WS-SM SM5.F.4 — cross-core SGI coalescing (`dedupCrossCoreSgis`).  The pure
dispatch layer `fireCrossCoreSgis` fires: one `.reschedule` per target core (no redundant
cross-core IPI — a boost chain naming the same remote home core twice pokes it once), and
no SGI the boost did not request.  Exercises the coalescing logic at runtime (the BaseIO
`fireCrossCoreSgis` itself is FFI and unrunnable host-side; its pure decision core is here). -/
private def runDedupChecks : IO Unit := do
  IO.println "--- §3.13 SM5.F.4 cross-core SGI coalescing (dedup) ---"
  let r := SgiKind.reschedule
  assertBool "dedup of [] is [] (no SGIs to fire)"
    (decide (dedupCrossCoreSgis [] = []))
  assertBool "dedup of a single SGI is itself"
    (decide (dedupCrossCoreSgis [(core1, r)] = [(core1, r)]))
  -- THE COALESCING: two links naming the SAME home core fire ONE IPI (no storm).
  assertBool "dedup coalesces a duplicate target core to ONE SGI (no IPI storm)"
    (decide (dedupCrossCoreSgis [(core1, r), (core1, r)] = [(core1, r)]))
  -- DISTINCT cores preserved (first occurrence wins), the repeated one dropped.
  assertBool "dedup keeps DISTINCT target cores, drops the repeat (first-wins)"
    (decide (dedupCrossCoreSgis [(core1, r), (core0, r), (core1, r)] = [(core1, r), (core0, r)]))
  -- `dedupCrossCoreSgis_nodup_cores` witness: deduped target cores are pairwise distinct.
  assertBool "deduped target cores are pairwise distinct (nodup_cores)"
    (decide ((dedupCrossCoreSgis [(core1, r), (core0, r), (core1, r), (core0, r)]).map (·.1)).Nodup)
  -- `dedupCrossCoreSgis_subset` witness: every deduped SGI was in the input.
  assertBool "dedup introduces no SGI the input did not contain (subset)"
    (decide ((dedupCrossCoreSgis [(core1, r), (core0, r)]).all
              (fun s => [(core1, r), (core0, r)].contains s)))

def runSmpPipChecks : IO Unit := do
  IO.println "WS-SM SM5.F — Per-core PIP suite"
  IO.println "===================================="
  runComputeChecks
  runWakeChecks
  runBlockingGraphChecks
  runResumeChecks
  runC9Checks
  runDecompositionChecks
  runChainChecks
  runDispatchChecks
  runCompletionNonVacuityChecks
  runP2MaterialityChecks
  runP5LocalRescheduleChecks
  runDedupChecks
  runInventoryChecks
  IO.println "===================================="
  IO.println "All SM5.F per-core PIP checks PASS."

end SeLe4n.Testing.SmpPip

def main : IO Unit :=
  SeLe4n.Testing.SmpPip.runSmpPipChecks

