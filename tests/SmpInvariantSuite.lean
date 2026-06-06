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
#check @schedulerInvariantStructural_perCore_pairwise_iff
#check @crossSubsystemInvariant_smp_dominates_structural

-- inventory:
#check @perCoreInvariantSuiteTheorems
#check @perCoreInvariantSuiteTheorems_count
#check @perCoreInvariantSuiteTheorems_partition_sum
#check @perCoreInvariantSuiteTheorems_identifiers_nodup

-- §5 SM4.B register-bank payoff: the `…Reg` invariant + contextMatches establishment +
-- the 10 Reg-extended preservations + the PER lemmas:
#check @SeLe4n.RegisterFile.beq_symm
#check @SeLe4n.RegisterFile.beq_trans
#check @contextMatchesCurrentOnCore_frame_at
#check @contextMatchesCurrentOnCore_of_machine_eq_and_regContext
#check @scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore
#check @switchToThreadOnCore_establishes_contextMatchesCurrentOnCore
#check @schedulerInvariantStructuralReg_perCore
#check @schedulerInvariantStructuralReg_smp
#check @schedulerInvariantStructuralReg_smp_of_base_and_ctx
#check @default_schedulerInvariantStructuralReg_smp
#check @scheduleEffectiveOnCore_preserves_contextMatchesCurrentOnCore_sibling
#check @switchToThreadOnCore_preserves_contextMatchesCurrentOnCore_sibling
#check @advanceDomainOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @wakeThread_preserves_schedulerInvariantStructuralReg_smp
#check @scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @replenishOnCore_preserves_schedulerInvariantStructuralReg_smp
#check @decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralReg_smp

-- §6 Nodup-extended invariant + the 10 RegNodup-extended preservations:
#check @SeLe4n.Kernel.RunQueue.insert_preserves_toList_nodup
#check @SeLe4n.Kernel.RunQueue.remove_preserves_toList_nodup
#check @schedulerInvariantStructuralRegNodup_perCore
#check @schedulerInvariantStructuralRegNodup_smp
#check @runQueueUniqueOnCore_smp_of_operated_and_frame
#check @default_schedulerInvariantStructuralRegNodup_smp
#check @advanceDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @enqueueRunnableOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp
#check @scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @switchToThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @replenishOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralRegNodup_smp
#check @perCoreInvariantSuiteTheorems_registerBank_count

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

/-- SM4.B register-bank payoff: the full SM4.C aggregate dominates the
register-bank-extended invariant (so every full witness yields it). -/
example (st : SystemState) (h : schedulerInvariant_smp st) :
    schedulerInvariantStructuralReg_smp st := schedulerInvariant_smp_to_structuralReg h

/-- SM4.B register-bank payoff: the freshly-booted system satisfies the
register-bank-extended SMP invariant (the contextMatches conjunct holds on every
core — vacuously, since no core has a current thread at boot). -/
example : schedulerInvariantStructuralReg_smp (default : SystemState) :=
  default_schedulerInvariantStructuralReg_smp

/-- SM4.B register-bank payoff: the live per-core dispatch preserves the
register-bank-extended invariant (the keystone — the dispatch *establishes*
`contextMatchesCurrentOnCore` on the operated core). -/
example (st st' : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt) (hPre : schedulerInvariantStructuralReg_smp st)
    (h : scheduleEffectiveOnCore st c₀ = .ok st') : schedulerInvariantStructuralReg_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ st' hInv hPre h

/-- SM4.B register-bank payoff: the per-core preemptive switch preserves the
register-bank-extended invariant. -/
example (st st' : SystemState) (c₀ : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hPre : schedulerInvariantStructuralReg_smp st)
    (h : switchToThreadOnCore st c₀ tid = .ok st') : schedulerInvariantStructuralReg_smp st' :=
  switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp st c₀ tid st' hInv hPre h

/-- The Nodup-extended invariant (6th conjunct) is preserved by the live dispatch. -/
example (st st' : SystemState) (c₀ : CoreId)
    (hInv : st.objects.invExt) (hPre : schedulerInvariantStructuralRegNodup_smp st)
    (h : scheduleEffectiveOnCore st c₀ = .ok st') : schedulerInvariantStructuralRegNodup_smp st' :=
  scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp st c₀ st' hInv hPre h

/-- The Nodup-extended invariant is preserved by the cross-core wake. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid)
    (hPre : schedulerInvariantStructuralRegNodup_smp st) :
    schedulerInvariantStructuralRegNodup_smp (wakeThread st tid ec).1 :=
  wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp st tid ec hInv hNotCur hPre

/-- The `RegisterFile` structural `BEq` is a partial equivalence (symm + trans),
the algebra the dispatch sibling-frame idempotency argument rests on. -/
example (a b c : RegisterFile) (hab : (a == b) = true) (hbc : (b == c) = true) :
    (c == a) = true := SeLe4n.RegisterFile.beq_symm (SeLe4n.RegisterFile.beq_trans hab hbc)

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

private def tidB1 : SeLe4n.ThreadId := ThreadId.ofNat 101

/-- A genuinely **multi-core** state: core 0 (boot) runs `tidA`, core 1 runs
`tidB1`, each TCB carrying the default `registerContext` and each core's register
bank holding the default `RegisterFile` — so `contextMatchesCurrentOnCore` holds
on *both* cores simultaneously, which a single shared register file could never
do.  This is the SM4.B per-core-register-bank payoff, exercised at runtime. -/
private def stMultiCore : SystemState :=
  let base : SystemState :=
    ((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10))).withObject
      tidB1.toObjId (.tcb (mkTcb 101 10))).build
  { base with
      scheduler :=
        (base.scheduler.setCurrentOnCore bootCoreId (some tidA)).setCurrentOnCore core1 (some tidB1),
      -- pin each core's bank to its current thread's saved context (contextMatches holds on both)
      machine :=
        (base.machine.setRegsOnCore bootCoreId (mkTcb 100 10).registerContext).setRegsOnCore
          core1 (mkTcb 101 10).registerContext }

/-- `stMultiCore` with core 1's register bank overwritten by a non-default value
(`pc = 1`).  Core 0's bank is untouched (the SM4.B `Vector` indexing isolates
per-core banks), so core 0's `contextMatchesCurrentOnCore` survives a core-1 bank
write — the genuine cross-core register isolation. -/
private def stMultiCoreBank1Written : SystemState :=
  { stMultiCore with machine :=
      stMultiCore.machine.setRegsOnCore core1 { (default : RegisterFile) with pc := ⟨1⟩ } }

/-- §3.5: the SM4.B register-bank payoff exercised on a genuinely multi-core
fixture — `contextMatchesCurrentOnCore` holds on *two* cores at once (witnessed by
the structural `RegisterFile` `BEq`, since the file has no `DecidableEq`), and a
per-core bank write on one core is isolated from the other. -/
private def runMultiCoreRegisterBankChecks : IO Unit := do
  IO.println "--- §3.5 multi-core register-bank payoff (SM4.B) ---"
  assertBool "core 0's bank matches tidA's saved context (contextMatches witness on core 0)"
    (stMultiCore.machine.regsOnCore bootCoreId == (mkTcb 100 10).registerContext)
  assertBool "core 1's bank matches tidB1's saved context SIMULTANEOUSLY (impossible with one shared regs)"
    (stMultiCore.machine.regsOnCore core1 == (mkTcb 101 10).registerContext)
  assertBool "core 0 and core 1 carry distinct current threads"
    (decide (stMultiCore.scheduler.currentOnCore bootCoreId = some tidA ∧
             stMultiCore.scheduler.currentOnCore core1 = some tidB1))
  -- After overwriting core 1's bank with a non-default value:
  assertBool "core 0's bank is byte-identical after a core-1 bank write (Vector cross-core isolation)"
    (stMultiCoreBank1Written.machine.regsOnCore bootCoreId
      == stMultiCore.machine.regsOnCore bootCoreId)
  assertBool "core 0's contextMatches witness STILL holds after the core-1 bank write (per-core isolation)"
    (stMultiCoreBank1Written.machine.regsOnCore bootCoreId == (mkTcb 100 10).registerContext)
  assertBool "core 1's bank genuinely changed (pc = 1)"
    ((stMultiCoreBank1Written.machine.regsOnCore core1).pc == ⟨1⟩)

/-- §3.4: the SM5.I inventory partition counts. -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.4 SM5.I inventory partition counts ---"
  assertBool "inventory has 79 entries"
    (decide (perCoreInvariantSuiteTheorems.length = 79))
  assertBool "structural category has 14 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .structural)).length = 14))
  assertBool "preservation category has 18 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .preservation)).length = 18))
  assertBool "suite category has 8 entries"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .suite)).length = 8))
  assertBool "registerBank category has 39 entries (SM4.B payoff)"
    (decide ((perCoreInvariantSuiteTheorems.filter (fun t => t.category == .registerBank)).length = 39))

/-- Run all SM5.I runtime checks. -/
def runAllChecks : IO Unit := do
  IO.println "=== WS-SM SM5.I — Per-core invariant suite runtime checks ==="
  runDefaultChecks
  runFramingChecks
  runWakeChecks
  runMultiCoreRegisterBankChecks
  runInventoryChecks
  IO.println "=== all SM5.I suite checks passed ==="

end SeLe4n.Testing.SmpInvariant

def main : IO Unit := SeLe4n.Testing.SmpInvariant.runAllChecks
