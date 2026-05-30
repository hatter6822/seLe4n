-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.A — Per-core `chooseThread` test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM5.A "Per-core chooseThread" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.1, §5).

* **§1 Surface anchors** — every public SM5.A symbol resolves at
  elaboration time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem
  (frame, per-core independence, idle-fallback completeness, selection
  soundness, the `schedulerInvariant_perCore` corollaries) to verified
  inputs.
* **§3 Runtime assertions** — `lake exe smp_scheduler_selection_suite`
  exercises the actual `chooseThreadOnCore` computation on six concrete
  fixtures (SM5.A.8): empty queue → idle fallback; single in-domain
  thread selected; highest-priority wins; out-of-domain thread skipped;
  per-core independence; selection soundness (chosen ∈ run queue), plus
  the SM5.A.2 lock-set witnesses.
-/

namespace SeLe4n.Testing.SmpSchedulerSelection

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.A public symbol resolves
-- ============================================================================

-- SM5.A.1 (production) + SM5.A.5 migration bridge:
#check @chooseThreadOnCore
#check @chooseThread_eq_chooseThreadOnCore_bootCore

-- SM5.A.2 lock-set:
#check @RunQueueLockId
#check @chooseThreadOnCoreLockSet
#check @chooseThreadOnCoreLockSet_length
#check @chooseThreadOnCoreLockSet_read_only
#check @chooseThreadOnCoreLockSet_core
#check @chooseThreadOnCoreLockSet_keys_nodup

-- SM5.A.3 per-core independence:
#check @chooseThreadOnCore_frame
#check @chooseThreadOnCore_perCore_independence
#check @chooseThreadOnCore_independent_of_setRunQueueOnCore
#check @chooseThreadOnCore_independent_of_setActiveDomainOnCore
#check @chooseThreadOnCore_independent_of_setCurrentOnCore
#check @chooseThreadOnCore_independent_of_write_off_lockSet

-- SM5.A.4 idle-fallback completeness:
#check @chooseThreadOnCore_ok_of_runnableTCBs
#check @chooseThreadOnCore_none_no_eligible
#check @chooseThreadOnCore_some_of_eligible
#check @chooseThreadOnCore_ok_of_schedulerInvariant

-- SM5.A.6 selection soundness:
#check @chooseThreadOnCore_some_mem_runQueueOnCore
#check @chooseThread_preserves_runQueueOnCore_wellFormed
#check @chooseThreadOnCore_some_mem_of_schedulerInvariant

-- SM5.A.7 decidability:
#check @chooseThreadOnCoreSelects
#check @chooseThreadOnCoreIdleFallback

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- SM5.A.3: the frame theorem applies to any two states agreeing on core c's
-- reads.
example (s₁ s₂ : SystemState) (c : CoreId)
    (hObj : s₁.objects = s₂.objects)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c) :
    chooseThreadOnCore s₁ c = chooseThreadOnCore s₂ c :=
  chooseThreadOnCore_frame s₁ s₂ c hObj hRQ hAD

-- SM5.A.3: per-core independence under a sibling-core run-queue write.
example (s : SystemState) (c c' : CoreId) (rq : RunQueue) (h : c ≠ c') :
    chooseThreadOnCore { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c :=
  chooseThreadOnCore_independent_of_setRunQueueOnCore s c c' rq h

-- SM5.A.3: the plan §3.1.2 named per-core-independence form.
example (s : SystemState) (c₁ c₂ : CoreId) (h : c₁ ≠ c₂) (rq : RunQueue) :
    chooseThreadOnCore { s with scheduler := s.scheduler.setRunQueueOnCore c₂ rq } c₁
      = chooseThreadOnCore s c₁ :=
  chooseThreadOnCore_perCore_independence s c₁ c₂ h rq

-- SM5.A.4: never errors on a well-formed all-TCB run queue.
example (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hr : runnableThreadsAreTCBsOnCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r :=
  chooseThreadOnCore_ok_of_runnableTCBs st c hwf hr

-- SM5.A.4: completeness — `.ok none` implies no in-domain runnable thread.
example (st : SystemState) (c : CoreId) (h : chooseThreadOnCore st c = .ok none)
    (tid : SeLe4n.ThreadId) (htid : tid ∈ (st.scheduler.runQueueOnCore c).toList)
    (tcb : TCB) (htcb : st.getTcb? tid = some tcb) :
    tcb.domain ≠ st.scheduler.activeDomainOnCore c :=
  chooseThreadOnCore_none_no_eligible st c h tid htid tcb htcb

-- SM5.A.4: an eligible in-domain thread guarantees a `some` selection.
example (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hr : runnableThreadsAreTCBsOnCore st c)
    (tid₀ : SeLe4n.ThreadId) (tcb₀ : TCB)
    (hMem : tid₀ ∈ (st.scheduler.runQueueOnCore c).toList)
    (hTcb : st.getTcb? tid₀ = some tcb₀)
    (hDom : tcb₀.domain = st.scheduler.activeDomainOnCore c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  chooseThreadOnCore_some_of_eligible st c hwf hr tid₀ tcb₀ hMem hTcb hDom

-- SM5.A.6: selection soundness — a chosen thread is a run-queue member.
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  chooseThreadOnCore_some_mem_runQueueOnCore st c tid hwf h

-- SM5.A.4 / SM5.A.6: the `schedulerInvariant_perCore` corollaries.
example (st : SystemState) (c : CoreId) (h : schedulerInvariant_perCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r :=
  chooseThreadOnCore_ok_of_schedulerInvariant st c h

example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariant_perCore st c)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  chooseThreadOnCore_some_mem_of_schedulerInvariant st c tid hInv h

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the six SM5.A.8 scenarios + lock-set
-- ============================================================================

/-- Minimal test TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def tidA : SeLe4n.ThreadId := ThreadId.ofNat 100
private def tidB : SeLe4n.ThreadId := ThreadId.ofNat 101
private def tidC : SeLe4n.ThreadId := ThreadId.ofNat 102

/-- Scenario fixtures.  Each populates the boot core's run queue (the
`BootstrapBuilder` only writes `bootCoreId`); `chooseThreadOnCore` is
evaluated at `bootCoreId`, whose default active domain is `⟨0⟩`. -/
private def stEmpty : SystemState := BootstrapBuilder.empty.build

private def stSingle : SystemState :=
  ((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withRunnable
    [tidA]).build

private def stTwo : SystemState :=
  (((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withObject
    tidB.toObjId (.tcb (mkTcb 101 20 0))).withRunnable [tidA, tidB]).build

private def stOutOfDomain : SystemState :=
  ((BootstrapBuilder.empty.withObject tidC.toObjId (.tcb (mkTcb 102 30 1))).withRunnable
    [tidC]).build

/-- Core 1 (a non-boot core), used by the per-core-independence scenario. -/
private def core1 : CoreId := ⟨1, by decide⟩

/-- `stSingle` with core 1's run queue overwritten with an unrelated thread.
Per SM5.A.3, this must not affect the selection on the boot core. -/
private def stSingleWithCore1Busy : SystemState :=
  { stSingle with scheduler :=
      stSingle.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(tidB, ⟨99⟩)]) }

/-- A state whose **boot core** run queue is empty but whose **core 1** run
queue holds the in-(active-)domain runnable thread `tidA` (a genuine TCB in
the global object store).  Exercises `chooseThreadOnCore` at a *non-boot*
core `c ≠ bootCoreId` — the whole point of the `(c : CoreId)` parameter. -/
private def stCore1Runnable : SystemState :=
  let base := (BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).build
  { base with scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(tidA, ⟨10⟩)]) }

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1–§3.6: the six SM5.A.8 selection scenarios, each evaluating the real
`chooseThreadOnCore` computation via the decidable selection predicates. -/
private def runSelectionScenarios : IO Unit := do
  IO.println "--- §3 SM5.A.8 per-core chooseThread scenarios ---"
  -- Scenario 1: empty run queue → idle-fallback signal `.ok none`.
  assertBool "scenario 1: empty run queue ⇒ idle fallback (.ok none)"
    (decide (chooseThreadOnCoreIdleFallback stEmpty bootCoreId))
  assertBool "scenario 1: empty run queue selects no concrete thread"
    (!decide (chooseThreadOnCoreSelects stEmpty bootCoreId tidA))
  -- Scenario 2: a single in-domain runnable thread is selected.
  assertBool "scenario 2: single in-domain thread ⇒ selected"
    (decide (chooseThreadOnCoreSelects stSingle bootCoreId tidA))
  assertBool "scenario 2: single in-domain thread ⇒ not idle fallback"
    (!decide (chooseThreadOnCoreIdleFallback stSingle bootCoreId))
  -- Scenario 3: the highest-priority in-domain thread wins.
  assertBool "scenario 3: highest-priority thread (B, prio 20) selected over A (prio 10)"
    (decide (chooseThreadOnCoreSelects stTwo bootCoreId tidB))
  assertBool "scenario 3: lower-priority thread A is NOT selected"
    (!decide (chooseThreadOnCoreSelects stTwo bootCoreId tidA))
  -- Scenario 4: an out-of-(active-)domain thread is skipped → idle fallback.
  assertBool "scenario 4: out-of-domain thread (domain 1, active 0) ⇒ idle fallback"
    (decide (chooseThreadOnCoreIdleFallback stOutOfDomain bootCoreId))
  assertBool "scenario 4: out-of-domain thread C is NOT selected"
    (!decide (chooseThreadOnCoreSelects stOutOfDomain bootCoreId tidC))
  -- Scenario 5: per-core independence — a busy core 1 does not change the
  -- boot core's selection (computational witness of SM5.A.3).
  assertBool "scenario 5: boot-core selection unaffected by core 1's run queue"
    (decide (chooseThreadOnCoreSelects stSingleWithCore1Busy bootCoreId tidA))
  assertBool "scenario 5: boot core does NOT pick up core 1's thread B"
    (!decide (chooseThreadOnCoreSelects stSingleWithCore1Busy bootCoreId tidB))
  -- Scenario 6: selection soundness — the chosen thread is in the run queue.
  assertBool "scenario 6: selected thread A is a member of the boot-core run queue"
    (decide (tidA ∈ (stSingle.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "scenario 6: selected thread B is a member of the two-thread run queue"
    (decide (tidB ∈ (stTwo.scheduler.runQueueOnCore bootCoreId).toList))
  -- Scenario 7: genuine per-core selection on a NON-boot core (c ≠ bootCoreId).
  -- Core 1 has the in-domain runnable thread A; the boot core is empty.
  assertBool "scenario 7: core 1 selects its own in-domain runnable thread A"
    (decide (chooseThreadOnCoreSelects stCore1Runnable core1 tidA))
  assertBool "scenario 7: the boot core (empty) falls back to idle"
    (decide (chooseThreadOnCoreIdleFallback stCore1Runnable bootCoreId))
  assertBool "scenario 7: core 1's thread A is NOT visible to the boot core's selection"
    (!decide (chooseThreadOnCoreSelects stCore1Runnable bootCoreId tidA))

/-- §3.7: SM5.A.2 lock-set structural witnesses (decidable). -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.7 SM5.A.2 lock-set witnesses ---"
  assertBool "chooseThreadOnCoreLockSet bootCoreId is a singleton"
    (decide ((chooseThreadOnCoreLockSet bootCoreId).length = 1))
  assertBool "chooseThreadOnCoreLockSet bootCoreId is read-only"
    (decide ((chooseThreadOnCoreLockSet bootCoreId).all (fun p => p.2 == AccessMode.read)))
  assertBool "chooseThreadOnCoreLockSet bootCoreId guards exactly the boot core"
    (decide ((chooseThreadOnCoreLockSet bootCoreId).all (fun p => p.1.core == bootCoreId)))
  assertBool "every core's chooseThread lock-set is a singleton"
    (allCores.all (fun c => decide ((chooseThreadOnCoreLockSet c).length = 1)))

def runSmpSchedulerSelectionChecks : IO Unit := do
  IO.println "WS-SM SM5.A — Per-core chooseThread suite"
  IO.println "===================================="
  runSelectionScenarios
  runLockSetChecks
  IO.println "===================================="
  IO.println "All SM5.A per-core chooseThread checks PASS."

end SeLe4n.Testing.SmpSchedulerSelection

def main : IO Unit :=
  SeLe4n.Testing.SmpSchedulerSelection.runSmpSchedulerSelectionChecks
