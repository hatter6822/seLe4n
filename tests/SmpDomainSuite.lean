-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomainInventory
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.G — Per-core domain scheduling test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.G
"Per-core domain scheduling" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.7, §5).

* **§1 Surface anchors** — every public SM5.G symbol resolves at elaboration time
  (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (cyclic,
  establishes-in-domain, respects-active-domain, cross-core independence, the
  production bridge, the §3.7 Theorem 3.7.1 membership) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_domain_suite` exercises the actual
  `advanceDomainOnCore` / `chooseThreadOnCore` computations on concrete
  domain-schedule fixtures (the SM5.G.6 scenarios): single-domain no-op, multi-
  domain rotation (domain + index + time), cyclic return-to-start, post-rotation
  in-domain membership, selection respects the active-domain barrier, and cross-core
  domain independence, plus the SM5.G.5 lock-set witnesses and the inventory
  partition counts.
-/

namespace SeLe4n.Testing.SmpDomain

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.G public symbol resolves
-- ============================================================================

-- SM5.G.2 rotation primitive + frames + single-step:
#check @advanceDomainOnCore
#check @advanceDomainOnCore_empty
#check @advanceDomainOnCore_objects
#check @advanceDomainOnCore_getTcb?
#check @advanceDomainOnCore_domainSchedule
#check @advanceDomainOnCore_runQueueOnCore
#check @advanceDomainOnCore_currentOnCore
#check @advanceDomainOnCore_activeDomainOnCore_ne
#check @advanceDomainOnCore_domainTimeRemainingOnCore_ne
#check @advanceDomainOnCore_domainScheduleIndexOnCore_ne
#check @advanceDomainOnCore_rotates
#check @advanceDomainOnCore_domainTimeRemainingOnCore_self
#check @advanceDomainOnCore_domainScheduleIndexOnCore_self
#check @advanceDomainOnCore_index_lt

-- SM5.G.2 cyclic theorem:
#check @advanceDomainOnCoreN
#check @advanceDomainOnCoreN_zero
#check @advanceDomainOnCoreN_succ
#check @advanceDomainOnCoreN_domainSchedule
#check @advanceDomainOnCoreN_index
#check @advanceDomainOnCore_cyclic

-- SM5.G.2 bridge to production:
#check @switchDomainOnCore_activeDomain_eq_advanceDomainOnCore

-- SM5.G.3 isInDomainSchedule:
#check @advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule
#check @advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne
#check @advanceDomainOnCore_preserves_isInDomainSchedule_smp
#check @activeDomainOnCore_isInDomainSchedule_mem
#check @activeDomainOnCore_isInDomainSchedule_mem_of_smp
#check @advanceDomainOnCore_activeDomain_mem

-- SM5.G.4 respects_activeDomain:
#check @chooseBestRunnableBy_result_eligible
#check @chooseBestInBucket_result_eligible
#check @chooseThreadOnCore_respects_activeDomain
#check @chooseThreadEffectiveOnCore_respects_activeDomain

-- SM5.G.5 cross-core independence + footprint:
#check @advanceDomainOnCore_independent_of_other_core
#check @advanceDomainOnCore_perCore_independence
#check @advanceDomainOnCoreLockSet
#check @advanceDomainOnCoreLockSet_length
#check @advanceDomainOnCoreLockSet_write_only
#check @advanceDomainOnCoreLockSet_contains_runQueue_write
#check @advanceDomainOnCoreLockSet_keys_nodup
#check @advanceDomainOnCoreLockSet_disjoint_of_ne

-- SM5.G inventory:
#check @perCoreDomainTheorems
#check @perCoreDomainTheorems_count
#check @perCoreDomainTheorems_partition_sum
#check @perCoreDomainTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- SM5.G.2 cyclic: rotating `length` times returns the index to its start.
example (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hidx : st.scheduler.domainScheduleIndexOnCore c < st.scheduler.domainSchedule.length) :
    (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  advanceDomainOnCore_cyclic st c hSched hidx

-- SM5.G.3: a rotation always lands on a domain that is in the schedule.
example (st : SystemState) (c : CoreId) :
    activeDomainOnCore_isInDomainSchedule (advanceDomainOnCore st c) c :=
  advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule st c

-- SM5.G.3: the plan §3.7 Theorem 3.7.1 membership form.
example (st : SystemState) (c : CoreId)
    (hPred : activeDomainOnCore_isInDomainSchedule st c)
    (hNe : st.scheduler.domainSchedule ≠ []) :
    st.scheduler.activeDomainOnCore c ∈ st.scheduler.domainSchedule.map (·.domain) :=
  activeDomainOnCore_isInDomainSchedule_mem st c hPred hNe

-- SM5.G.4: a selected thread is in core c's active domain (the domain barrier).
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hSel : chooseThreadOnCore st c = .ok (some tid))
    (hTcb : st.getTcb? tid = some tcb) :
    tcb.domain = st.scheduler.activeDomainOnCore c :=
  chooseThreadOnCore_respects_activeDomain st c tid tcb hSel hTcb

-- SM5.G.5: a sibling core's selection is unaffected by core c's domain rotation.
example (st : SystemState) (c c' : CoreId) (h : c ≠ c') :
    chooseThreadOnCore (advanceDomainOnCore st c) c' = chooseThreadOnCore st c' :=
  advanceDomainOnCore_independent_of_other_core st c c' h

-- SM5.G.2 bridge: the production switch's domain effect IS the pure rotation.
example (st : SystemState) (c : CoreId) (st' : SystemState)
    (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = (advanceDomainOnCore st c).scheduler.activeDomainOnCore c :=
  switchDomainOnCore_activeDomain_eq_advanceDomainOnCore st c st' hStep

-- SM5.G.5: disjoint cores' rotation footprints are disjoint.
example (c c' : CoreId) (h : c ≠ c') :
    SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) ∉ (advanceDomainOnCoreLockSet c').map (·.1) :=
  advanceDomainOnCoreLockSet_disjoint_of_ne c c' h

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.G.6 domain-rotation scenarios
-- ============================================================================

/-- Minimal test TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def tidA : SeLe4n.ThreadId := ThreadId.ofNat 100
private def tidB : SeLe4n.ThreadId := ThreadId.ofNat 101

/-- A two-entry domain schedule: domain 0 for 5 ticks, then domain 1 for 3 ticks. -/
private def twoDomainSchedule : List DomainScheduleEntry :=
  [ { domain := ⟨0⟩, length := 5 }, { domain := ⟨1⟩, length := 3 } ]

/-- Core 1 (a non-boot core), used by the cross-core-independence scenario. -/
private def core1 : CoreId := ⟨1, by decide⟩

/-- An empty-schedule (single-domain) state: `advanceDomainOnCore` must be a no-op. -/
private def stSingleDomain : SystemState := BootstrapBuilder.empty.build

/-- A two-domain state at index 0 (active domain 0, time 5).  The per-core defaults
(`activeDomain = ⟨0⟩`, `domainScheduleIndex = 0`, `domainTimeRemaining = 5`) already
match the first schedule entry, so only `domainSchedule` is overridden.  Core 1's run
queue is seeded with a thread so the cross-core run-queue frame test is non-vacuous. -/
private def stTwoDomain : SystemState :=
  let base := BootstrapBuilder.empty.build
  { base with scheduler :=
      { (base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(tidA, ⟨10⟩)])) with
        domainSchedule := twoDomainSchedule } }

/-- A two-domain state whose boot-core run queue holds an in-(active-)domain thread
`tidA` (domain 0) and an out-of-domain thread `tidB` (domain 1).  `chooseThreadOnCore`
(active domain 0) must select `tidA` and skip `tidB`. -/
private def stDomainSelect : SystemState :=
  let base := (((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withObject
    tidB.toObjId (.tcb (mkTcb 101 20 1))).withRunnable [tidA, tidB]).build
  { base with scheduler := { base.scheduler with domainSchedule := twoDomainSchedule } }

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1–§3.6: the SM5.G.6 domain-rotation scenarios on concrete fixtures. -/
private def runDomainScenarios : IO Unit := do
  IO.println "--- §3 SM5.G.6 per-core domain-rotation scenarios ---"
  -- Scenario 1: single-domain mode (empty schedule) ⇒ rotation is a no-op.
  assertBool "scenario 1: empty schedule ⇒ advanceDomainOnCore is a no-op (active domain unchanged)"
    ((advanceDomainOnCore stSingleDomain bootCoreId).scheduler.activeDomainOnCore bootCoreId
      == stSingleDomain.scheduler.activeDomainOnCore bootCoreId)
  assertBool "scenario 1: empty schedule ⇒ schedule index unchanged (0)"
    ((advanceDomainOnCore stSingleDomain bootCoreId).scheduler.domainScheduleIndexOnCore bootCoreId == 0)
  -- Scenario 2: multi-domain rotation ⇒ active domain advances 0 → 1.
  assertBool "scenario 2: rotation advances active domain 0 ⇒ 1"
    ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.activeDomainOnCore bootCoreId == ⟨1⟩)
  assertBool "scenario 2: rotation advances the schedule index 0 ⇒ 1"
    ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.domainScheduleIndexOnCore bootCoreId == 1)
  assertBool "scenario 2: rotation resets the domain quantum to entry 1's length (3)"
    ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.domainTimeRemainingOnCore bootCoreId == 3)
  assertBool "scenario 2: a second rotation cycles the active domain back 1 ⇒ 0"
    ((advanceDomainOnCoreN stTwoDomain bootCoreId 2).scheduler.activeDomainOnCore bootCoreId == ⟨0⟩)
  -- Scenario 3: cyclic — advancing `length` (= 2) times returns the index to start (0).
  assertBool "scenario 3: cyclic — advancing length (=2) times returns the schedule index to 0"
    ((advanceDomainOnCoreN stTwoDomain bootCoreId stTwoDomain.scheduler.domainSchedule.length).scheduler.domainScheduleIndexOnCore bootCoreId == 0)
  assertBool "scenario 3: the schedule length is invariant across rotations (still 2)"
    ((advanceDomainOnCoreN stTwoDomain bootCoreId 5).scheduler.domainSchedule.length == 2)
  -- Scenario 4: after a rotation the active domain is a member of the schedule.
  assertBool "scenario 4: post-rotation active domain (1) is in the schedule's domain list"
    ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.activeDomainOnCore bootCoreId
      ∈ ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.domainSchedule.map (·.domain)))
  assertBool "scenario 4: the starting active domain (0) is in the schedule's domain list"
    (stTwoDomain.scheduler.activeDomainOnCore bootCoreId ∈ (stTwoDomain.scheduler.domainSchedule.map (·.domain)))
  -- Scenario 5: selection respects the active-domain barrier (active domain 0).
  assertBool "scenario 5: chooseThreadOnCore selects the in-domain thread A (domain 0)"
    (decide (chooseThreadOnCoreSelects stDomainSelect bootCoreId tidA))
  assertBool "scenario 5: chooseThreadOnCore does NOT select the out-of-domain thread B (domain 1)"
    (!decide (chooseThreadOnCoreSelects stDomainSelect bootCoreId tidB))
  assertBool "scenario 5: the selected thread A's domain (0) equals the active domain (0)"
    (((stDomainSelect.getTcb? tidA).map (·.domain)) == some (stDomainSelect.scheduler.activeDomainOnCore bootCoreId))
  -- Scenario 6: cross-core independence — rotating the boot core's domain leaves
  -- core 1's active domain (and selection) unchanged.
  assertBool "scenario 6: rotating the boot core's domain frames core 1's active domain"
    ((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.activeDomainOnCore core1
      == stTwoDomain.scheduler.activeDomainOnCore core1)
  assertBool "scenario 6: rotating the boot core's domain frames core 1's run queue"
    (((advanceDomainOnCore stTwoDomain bootCoreId).scheduler.runQueueOnCore core1).toList
      == (stTwoDomain.scheduler.runQueueOnCore core1).toList)
  assertBool "scenario 6: rotating the boot core's domain never touches the object store"
    ((advanceDomainOnCore stTwoDomain bootCoreId).objects.toList.length == stTwoDomain.objects.toList.length)

/-- §3.7: the SM5.G.5 lock-set structural witnesses (decidable). -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.7 SM5.G.5 rotation lock-set witnesses ---"
  assertBool "advanceDomainOnCoreLockSet bootCoreId is the single per-core lock (length 1)"
    (decide ((advanceDomainOnCoreLockSet bootCoreId).length = 1))
  assertBool "advanceDomainOnCoreLockSet bootCoreId is write-only"
    (decide ((advanceDomainOnCoreLockSet bootCoreId).all (fun p => p.2 == AccessMode.write)))
  assertBool "footprint contains the boot core's run-queue write lock"
    (decide ((SchedLockId.runQueue ⟨bootCoreId⟩, AccessMode.write)
              ∈ advanceDomainOnCoreLockSet bootCoreId))
  assertBool "boot core's run-queue lock is NOT in core 1's rotation footprint (disjoint)"
    (decide (SchedLockId.runQueue (⟨bootCoreId⟩ : RunQueueLockId)
              ∉ (advanceDomainOnCoreLockSet core1).map (·.1)))

/-- §3.8: the SM5.G theorem-inventory partition counts (compiled-`decide` guards). -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.8 SM5.G inventory partition counts ---"
  assertBool "inventory has 39 entries"
    (decide (perCoreDomainTheorems.length = 39))
  assertBool "rotation category has 14 entries"
    (decide ((perCoreDomainTheorems.filter (fun t => t.category == .rotation)).length = 14))
  assertBool "cyclic category has 6 entries"
    (decide ((perCoreDomainTheorems.filter (fun t => t.category == .cyclic)).length = 6))
  assertBool "domainSchedule category has 6 entries"
    (decide ((perCoreDomainTheorems.filter (fun t => t.category == .domainSchedule)).length = 6))
  assertBool "respects category has 4 entries"
    (decide ((perCoreDomainTheorems.filter (fun t => t.category == .respects)).length = 4))
  assertBool "independence category has 8 entries"
    (decide ((perCoreDomainTheorems.filter (fun t => t.category == .independence)).length = 8))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCoreDomainTheorems.map (·.identifier)).Nodup)

def main : IO Unit := do
  IO.println "=== WS-SM SM5.G — Per-core domain scheduling suite ==="
  runDomainScenarios
  runLockSetChecks
  runInventoryChecks
  IO.println "=== SM5.G suite: all assertions passed ==="

end SeLe4n.Testing.SmpDomain

def main : IO Unit := SeLe4n.Testing.SmpDomain.main
