-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuite
import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuiteInventory
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.I — Per-core invariant suite test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.I
"Per-core invariant suite" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §5 SM5.I, §6.1).

* **§1 Surface anchors** — every public SM5.I symbol resolves at elaboration
  time (rename/removal fails the build): the structural invariant + engine, the
  ten transition preservation theorems, the helper lemmas, the suite index, and
  the inventory.
* **§2 Elaboration-time examples** — apply each headline preservation theorem
  (the SM5.I.8 "preservation by every transition" surface) to inputs, plus
  concrete non-vacuity witnesses on the freshly-booted system (the pure-framing
  transitions genuinely *preserve* the structural SMP invariant there).
* **§3 Runtime assertions** — `lake exe smp_invariant_suite` exercises the
  actual transition computation on concrete fixtures: the structural-invariant
  conjuncts on the default state and after `advanceDomainOnCore` /
  `enqueueRunnableOnCore` (the woken thread enters the run queue and resolves to
  a TCB; sibling-core slots are framed), and the inventory partition counts.
-/

namespace SeLe4n.Testing.SmpInvariant

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.I public symbol resolves
-- ============================================================================

-- §1 structural invariant + engine:
#check @schedulerInvariantStructural_perCore
#check @schedulerInvariantStructural_smp
#check @schedulerInvariantStructural_perCore_to_queueCurrentConsistent
#check @schedulerInvariantStructural_perCore_to_currentThreadValid
#check @schedulerInvariantStructural_perCore_to_runnableThreadsAreTCBs
#check @schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed
#check @schedulerInvariantStructural_perCore_aggregateForall
#check @schedulerInvariantStructural_smp_at
#check @schedulerInvariant_perCore_to_structural
#check @schedulerInvariant_smp_to_structural
#check @default_schedulerInvariantStructural_perCore
#check @default_schedulerInvariantStructural_smp
#check @schedulerInvariantStructural_perCore_frame
#check @schedulerInvariantStructural_smp_of_establish_and_frame

-- §3 preservation by every transition (SM5.I.8):
#check @advanceDomainOnCore_preserves_schedulerInvariantStructural_smp
#check @enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp
#check @wakeThread_preserves_schedulerInvariantStructural_smp
#check @idleFallbackOnCore_currentOnCore_ne
#check @idleFallbackOnCore_runQueueOnCore_ne
#check @scheduleEffectiveOnCore_independent_of_other_core
#check @scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp
#check @scheduleOrIdleOnCore_preserves_schedulerInvariantStructural_smp
#check @preemptCurrentOnCore_getTcb?_isSome
#check @preemptCurrentOnCore_runQueue_resolves
#check @switchToThreadOnCore_getTcb?_isSome
#check @switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @switchToThreadOnCore_preserves_schedulerInvariantStructural_smp
#check @handleRescheduleSgiOnCore_preserves_schedulerInvariantStructural_smp
#check @enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp
#check @replenishOnCore_preserves_schedulerInvariantStructural_smp
#check @decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp

-- §4 suite index (SM5.I.1–I.7/I.9):
#check @currentOnCore_validThreadIfSome
#check @runQueueOnCore_wellFormed_of_structural
#check @schedContextRunQueueConsistent_perCore_of_crossSubsystem
#check @priorityInheritance_perCore_iff_blockingAcyclic
#check @schedulerInvariant_smp_dominates_structural
#check @schedulerInvariantStructural_perCore_pairwise
#check @crossSubsystemInvariant_smp_dominates_structural

-- inventory:
#check @perCoreInvariantSuiteTheorems
#check @perCoreInvariantSuiteTheorems_count
#check @perCoreInvariantSuiteTheorems_partition_sum
#check @perCoreInvariantSuiteTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): apply each headline theorem
-- ============================================================================

/-- The freshly-booted system satisfies the structural SMP invariant. -/
example : schedulerInvariantStructural_smp (default : SystemState) :=
  default_schedulerInvariantStructural_smp

/-- Non-vacuity: the pure-framing domain rotation genuinely preserves the
structural SMP invariant on the default state. -/
example (c : CoreId) :
    schedulerInvariantStructural_smp (advanceDomainOnCore (default : SystemState) c) :=
  advanceDomainOnCore_preserves_schedulerInvariantStructural_smp default c
    default_schedulerInvariantStructural_smp

/-- Non-vacuity: the CBS replenishment preserves the structural SMP invariant on
the default state. -/
example (c : CoreId) (scId : SchedContextId) (t : Nat) :
    schedulerInvariantStructural_smp (replenishOnCore (default : SystemState) c scId t) :=
  replenishOnCore_preserves_schedulerInvariantStructural_smp default c scId t
    default_schedulerInvariantStructural_smp

/-- Non-vacuity: the non-boundary domain decrement preserves the structural SMP
invariant on the default state. -/
example (c : CoreId) :
    schedulerInvariantStructural_smp (decrementDomainTimeOnCore (default : SystemState) c) :=
  decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp default c
    default_schedulerInvariantStructural_smp

/-- The SM5.I.8 engine applies to an arbitrary per-core transition. -/
example (st st' : SystemState) (c₀ : CoreId)
    (hPre : schedulerInvariantStructural_smp st)
    (hC0 : schedulerInvariantStructural_perCore st' c₀)
    (hFC : ∀ c', c₀ ≠ c' → st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c')
    (hFR : ∀ c', c₀ ≠ c' → st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c')
    (hT : ∀ tid, (st.getTcb? tid).isSome → (st'.getTcb? tid).isSome) :
    schedulerInvariantStructural_smp st' :=
  schedulerInvariantStructural_smp_of_establish_and_frame hPre hC0 hFC hFR hT

/-- The switch preservation is applicable (SM5.I.8). -/
example (st st' : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hPre : schedulerInvariantStructural_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') : schedulerInvariantStructural_smp st' :=
  switchToThreadOnCore_preserves_schedulerInvariantStructural_smp st c₀ tid st' hInv hPre h

/-- The dispatcher preservation is applicable (SM5.I.8 keystone). -/
example (st st' : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt) (hPre : schedulerInvariantStructural_smp st)
    (h : scheduleEffectiveOnCore st c₀ = .ok st') : schedulerInvariantStructural_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp st c₀ st' hInv hPre h

/-- The full SM4.C aggregate dominates the structural suite (SM5.I.5/I.7 bridge). -/
example (st : SystemState) (h : schedulerInvariant_smp st) :
    schedulerInvariantStructural_smp st := schedulerInvariant_smp_dominates_structural h

/-- SM5.I.6 structural cross-core independence is applicable. -/
example (st : SystemState) (c₁ c₂ : CoreId) (hne : c₁ ≠ c₂)
    (vc : Option SeLe4n.ThreadId) (vrq : RunQueue)
    (h : schedulerInvariantStructural_perCore st c₁) :
    schedulerInvariantStructural_perCore
      { st with scheduler := (st.scheduler.setCurrentOnCore c₂ vc).setRunQueueOnCore c₂ vrq } c₁ :=
  schedulerInvariantStructural_perCore_pairwise hne vc vrq h

-- ============================================================================
-- §3  Runtime assertions (Tier-2): `lake exe smp_invariant_suite`
-- ============================================================================

/-- A non-boot core for the sibling-frame scenarios. -/
private def core1 : CoreId := ⟨1, by decide⟩
private def tidA : SeLe4n.ThreadId := ThreadId.ofNat 100

private def mkTcb (tid prio : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- Empty boot state. -/
private def stEmpty : SystemState := BootstrapBuilder.empty.build

/-- A boot state whose boot-core run queue holds a priority-10 thread `tidA`. -/
private def stRun : SystemState :=
  ((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10))).withRunnable
    [tidA]).build

/-- `stRun` with the domain rotated on the boot core (a pure-framing transition). -/
private def stRunRotated : SystemState := advanceDomainOnCore stRun bootCoreId

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1: the structural-invariant *safety facts* hold on the freshly-booted
(empty) system — no current thread, empty run queue, so the conjuncts hold
trivially. -/
private def runDefaultChecks : IO Unit := do
  IO.println "--- §3.1 structural safety facts on the empty boot state ---"
  assertBool "boot core has no current thread (queueCurrentConsistent / currentThreadValid vacuous)"
    (decide ((stEmpty.scheduler.currentOnCore bootCoreId) = none))
  assertBool "boot core's run queue is empty (runnableThreadsAreTCBs vacuous)"
    (decide ((stEmpty.scheduler.runQueueOnCore bootCoreId).toList = []))
  assertBool "core 1 has no current thread"
    (decide ((stEmpty.scheduler.currentOnCore core1) = none))

/-- §3.2: `advanceDomainOnCore` frames the run queue, current, and TCB
resolution on the operated core (the structural conjuncts are preserved
because the rotation touches only the domain triple). -/
private def runFramingChecks : IO Unit := do
  IO.println "--- §3.2 advanceDomainOnCore frames the structural reads ---"
  assertBool "tidA still in the boot-core run queue after rotation (runnableThreadsAreTCBs frame)"
    (decide (tidA ∈ (stRunRotated.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "tidA still resolves to a TCB after rotation (currentThreadValid / runnable frame)"
    (decide (stRunRotated.getTcb? tidA).isSome)
  assertBool "boot-core current unchanged by rotation (= none)"
    (decide ((stRunRotated.scheduler.currentOnCore bootCoreId) = none))
  assertBool "sibling core 1's run queue unaffected by a boot-core rotation (cross-core frame)"
    (decide ((stRunRotated.scheduler.runQueueOnCore core1).toList = []))

/-- §3.3: `enqueueRunnableOnCore` (the wake) genuinely enqueues a blocked TCB and
keeps it a TCB — the substantive content of `runnableThreadsAreTCBs` preservation
on the operated core. -/
private def runWakeChecks : IO Unit := do
  IO.println "--- §3.3 enqueueRunnableOnCore (wake) maintains runnable-are-TCBs ---"
  -- `tidB` is a TCB present in the store but NOT yet runnable.
  let tidB : SeLe4n.ThreadId := ThreadId.ofNat 200
  let stBlocked : SystemState :=
    (BootstrapBuilder.empty.withObject tidB.toObjId (.tcb (mkTcb 200 5))).build
  let stWoken : SystemState := enqueueRunnableOnCore stBlocked bootCoreId tidB
  assertBool "the woken thread is now in the boot-core run queue"
    (decide (tidB ∈ (stWoken.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "the woken thread still resolves to a TCB (runnable-are-TCBs holds)"
    (decide (stWoken.getTcb? tidB).isSome)
  assertBool "the wake leaves sibling core 1's run queue empty (cross-core frame)"
    (decide ((stWoken.scheduler.runQueueOnCore core1).toList = []))

/-- §3.4: the SM5.I inventory partition counts. -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.4 SM5.I inventory partition counts ---"
  assertBool "inventory has 39 entries"
    (decide (perCoreInvariantSuiteTheorems.length = 39))
  assertBool "structural category has 14 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .structural)).length = 14))
  assertBool "preservation category has 18 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .preservation)).length = 18))
  assertBool "suite category has 7 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .suite)).length = 7))

/-- Run all SM5.I runtime checks. -/
def runAllChecks : IO Unit := do
  IO.println "=== WS-SM SM5.I — Per-core invariant suite runtime checks ==="
  runDefaultChecks
  runFramingChecks
  runWakeChecks
  runInventoryChecks
  IO.println "=== all SM5.I suite checks passed ==="

end SeLe4n.Testing.SmpInvariant

def main : IO Unit := SeLe4n.Testing.SmpInvariant.runAllChecks
