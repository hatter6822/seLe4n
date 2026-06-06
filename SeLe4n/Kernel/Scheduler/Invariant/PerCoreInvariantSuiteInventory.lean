-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuite

/-!
# WS-SM SM5.I — Per-core invariant suite theorem inventory

Aggregates the SM5.I per-core invariant-suite theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the SM5.E
`PerCoreIdleInventory.lean` / SM5.D `PerCoreTimerInventory.lean` patterns (and,
further back, the SM3.A `PerObjectLockInventory.lean`).

Three categories matching the plan §5 SM5.I sub-tasks:

* `.structural` — SM5.I.5/I.7: the `schedulerInvariantStructural_perCore` / `_smp`
  safety invariant (def + projections + the full-aggregate bridges +
  default-state + the frame lemma + the per-arbitrary-core SMP-preservation
  engine).
* `.preservation` — SM5.I.8 "preservation by every transition": the
  `<op>_preserves_schedulerInvariantStructural_smp` theorems for every SM5
  per-core transition, plus the missing per-conjunct helpers they compose
  (the wake / switch `runnableThreadsAreTCBs`, the preempt `getTcb?`-isSome /
  run-queue resolution, the dispatcher other-core frame, the idle-fallback
  sibling frames).
* `.suite` — SM5.I.1–I.4/I.6/I.9: the suite index assembling the SM4.C/SM4.D
  per-core predicates under their plan names + the structural cross-core
  pairwise independence + the bridges from the full aggregate and the
  cross-subsystem suite.

## Identifier validation

Identifiers are compile-time-validated via the `pcist!` macro (mirroring SM5.E's
`pcit!`).  A typo or stale rename fails the build at this module's elaboration
step with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

/-- WS-SM SM5.I: category tag for the per-core invariant suite inventory. -/
inductive PerCoreInvariantSuiteCategory where
  /-- SM5.I.5/I.7: the structural invariant + projections + bridges + frame + engine. -/
  | structural
  /-- SM5.I.8: preservation by every SM5 per-core transition + the helper lemmas. -/
  | preservation
  /-- SM5.I.1–I.4/I.6/I.9: the suite index + cross-core independence + bridges. -/
  | suite
  /-- SM4.B register-bank payoff: the `…Reg` / `…RegNodup` extended invariants
  (+ `contextMatchesCurrentOnCore` / `runQueueUniqueOnCore`) and their
  system-wide preservation by every transition. -/
  | registerBank
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.I: a theorem entry in the suite inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pcist!`) forces Lean to
resolve the referenced declaration at construction time. -/
structure PerCoreInvariantSuiteTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreInvariantSuiteCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.I: build a `PerCoreInvariantSuiteTheorem` with a compile-time-validated
identifier. -/
syntax (name := perCoreInvariantSuiteTheoremMacro) "pcist!" str ident term : term

macro_rules
  | `(pcist! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreInvariantSuiteTheorem))

/-- WS-SM SM5.I: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pcist!`. -/
def perCoreInvariantSuiteTheorems : List PerCoreInvariantSuiteTheorem :=
  [-- ── SM5.I.5/I.7 structural invariant (.structural) ──
    pcist! "schedulerInvariantStructural_perCore: the register-bank-independent per-core safety invariant"
      SeLe4n.Kernel.schedulerInvariantStructural_perCore .structural,
    pcist! "schedulerInvariantStructural_smp: the system-wide structural SMP invariant"
      SeLe4n.Kernel.schedulerInvariantStructural_smp .structural,
    pcist! "schedulerInvariantStructural_perCore_to_queueCurrentConsistent: dequeue-on-dispatch projection"
      schedulerInvariantStructural_perCore_to_queueCurrentConsistent .structural,
    pcist! "schedulerInvariantStructural_perCore_to_currentThreadValid: no-dangling-current projection"
      schedulerInvariantStructural_perCore_to_currentThreadValid .structural,
    pcist! "schedulerInvariantStructural_perCore_to_runnableThreadsAreTCBs: runnable-are-TCBs projection"
      schedulerInvariantStructural_perCore_to_runnableThreadsAreTCBs .structural,
    pcist! "schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed: run-queue-wellformed projection"
      schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed .structural,
    pcist! "schedulerInvariantStructural_perCore_aggregateForall: slices aggregate to the SMP form"
      schedulerInvariantStructural_perCore_aggregateForall .structural,
    pcist! "schedulerInvariantStructural_smp_at: project a single core's structural slice"
      schedulerInvariantStructural_smp_at .structural,
    pcist! "schedulerInvariant_perCore_to_structural: the full SM4.C aggregate dominates the structural one"
      schedulerInvariant_perCore_to_structural .structural,
    pcist! "schedulerInvariant_smp_to_structural: the full SMP aggregate dominates the structural SMP form"
      schedulerInvariant_smp_to_structural .structural,
    pcist! "default_schedulerInvariantStructural_perCore: the freshly-booted core satisfies the structural invariant"
      default_schedulerInvariantStructural_perCore .structural,
    pcist! "default_schedulerInvariantStructural_smp: the freshly-booted system satisfies the structural SMP invariant"
      default_schedulerInvariantStructural_smp .structural,
    pcist! "schedulerInvariantStructural_perCore_frame: the register-bank-free per-core frame"
      schedulerInvariantStructural_perCore_frame .structural,
    pcist! "schedulerInvariantStructural_smp_of_establish_and_frame: the per-arbitrary-core SMP-preservation engine"
      schedulerInvariantStructural_smp_of_establish_and_frame .structural,
    -- ── SM5.I.8 preservation by every transition + helpers (.preservation) ──
    pcist! "advanceDomainOnCore_preserves_schedulerInvariantStructural_smp: domain rotation preserves the structural SMP invariant"
      advanceDomainOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore: the wake's missing structural conjunct"
      enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    pcist! "enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp: the per-core wake preserves the structural SMP invariant"
      enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "wakeThread_preserves_schedulerInvariantStructural_smp: the cross-core wake preserves the structural SMP invariant"
      wakeThread_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "idleFallbackOnCore_currentOnCore_ne: the idle fallback frames sibling cores' current slot"
      idleFallbackOnCore_currentOnCore_ne .preservation,
    pcist! "idleFallbackOnCore_runQueueOnCore_ne: the idle fallback frames sibling cores' run queue"
      idleFallbackOnCore_runQueueOnCore_ne .preservation,
    pcist! "scheduleEffectiveOnCore_independent_of_other_core: the dispatcher's sibling-core frame"
      scheduleEffectiveOnCore_independent_of_other_core .preservation,
    pcist! "scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp: the live per-core dispatch preserves the structural SMP invariant"
      scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "scheduleOrIdleOnCore_preserves_schedulerInvariantStructural_smp: the idle-aware dispatcher preserves the structural SMP invariant"
      scheduleOrIdleOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "preemptCurrentOnCore_getTcb?_isSome: the preempt destroys no TCB"
      preemptCurrentOnCore_getTcb?_isSome .preservation,
    pcist! "preemptCurrentOnCore_runQueue_resolves: every preempt-run-queue member resolves to a TCB"
      preemptCurrentOnCore_runQueue_resolves .preservation,
    pcist! "switchToThreadOnCore_getTcb?_isSome: the switch destroys no TCB"
      switchToThreadOnCore_getTcb?_isSome .preservation,
    pcist! "switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore: the switch's missing structural conjunct"
      switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    pcist! "switchToThreadOnCore_preserves_schedulerInvariantStructural_smp: the per-core context switch preserves the structural SMP invariant"
      switchToThreadOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "handleRescheduleSgiOnCore_preserves_schedulerInvariantStructural_smp: the reschedule-SGI handler preserves the structural SMP invariant"
      handleRescheduleSgiOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp: the idle enqueue preserves the structural SMP invariant"
      enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "replenishOnCore_preserves_schedulerInvariantStructural_smp: the CBS replenishment preserves the structural SMP invariant"
      replenishOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    pcist! "decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp: the non-boundary domain decrement preserves the structural SMP invariant"
      decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp .preservation,
    -- ── SM5.I.1–I.4/I.6/I.9 suite index (.suite) ──
    pcist! "currentOnCore_validThreadIfSome: SM5.I.1 no-dangling-current usable form"
      currentOnCore_validThreadIfSome .suite,
    pcist! "runQueueOnCore_wellFormed_of_structural: SM5.I.2 run-queue well-formedness projection"
      runQueueOnCore_wellFormed_of_structural .suite,
    pcist! "schedContextRunQueueConsistent_perCore_of_crossSubsystem: SM5.I.3 SchedContext↔run-queue suite anchor"
      schedContextRunQueueConsistent_perCore_of_crossSubsystem .suite,
    pcist! "priorityInheritance_perCore_iff_blockingAcyclic: SM5.I.4 per-core PIP-acyclicity suite anchor"
      priorityInheritance_perCore_iff_blockingAcyclic .suite,
    pcist! "schedulerInvariant_smp_dominates_structural: SM5.I.5/I.7 full SMP aggregate dominates the suite"
      schedulerInvariant_smp_dominates_structural .suite,
    pcist! "schedulerInvariantStructural_perCore_pairwise: SM5.I.6 structural cross-core independence"
      schedulerInvariantStructural_perCore_pairwise .suite,
    pcist! "schedulerInvariantStructural_perCore_pairwise_iff: SM5.I.6 cross-core independence (biconditional)"
      schedulerInvariantStructural_perCore_pairwise_iff .suite,
    pcist! "crossSubsystemInvariant_smp_dominates_structural: SM5.I.9 cross-subsystem SMP suite dominates the structural core"
      crossSubsystemInvariant_smp_dominates_structural .suite,
    -- ── SM4.B register-bank payoff (.registerBank) ──
    pcist! "RegisterFile.beq_symm: the structural register-file BEq is symmetric (partial equivalence)"
      SeLe4n.RegisterFile.beq_symm .registerBank,
    pcist! "RegisterFile.beq_trans: the structural register-file BEq is transitive (partial equivalence)"
      SeLe4n.RegisterFile.beq_trans .registerBank,
    pcist! "RunQueue.insert_preserves_toList_nodup: RunQueue.insert preserves toList.Nodup"
      SeLe4n.Kernel.RunQueue.insert_preserves_toList_nodup .registerBank,
    pcist! "RunQueue.remove_preserves_toList_nodup: RunQueue.remove preserves toList.Nodup"
      SeLe4n.Kernel.RunQueue.remove_preserves_toList_nodup .registerBank,
    pcist! "contextMatchesCurrentOnCore_frame_at: per-core contextMatches frame (bank + current-thread regContext)"
      contextMatchesCurrentOnCore_frame_at .registerBank,
    pcist! "contextMatchesCurrentOnCore_of_machine_eq_and_regContext: machine-neutral contextMatches frame"
      contextMatchesCurrentOnCore_of_machine_eq_and_regContext .registerBank,
    pcist! "scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore: the dispatch establishes contextMatches on the operated core"
      scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore .registerBank,
    pcist! "switchToThreadOnCore_establishes_contextMatchesCurrentOnCore: the switch establishes contextMatches on the operated core"
      switchToThreadOnCore_establishes_contextMatchesCurrentOnCore .registerBank,
    pcist! "schedulerInvariantStructuralReg_perCore: the register-bank-extended per-core invariant (+ contextMatchesCurrentOnCore)"
      SeLe4n.Kernel.schedulerInvariantStructuralReg_perCore .registerBank,
    pcist! "schedulerInvariantStructuralReg_smp: the system-wide register-bank-extended SMP invariant"
      SeLe4n.Kernel.schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "schedulerInvariant_perCore_to_structuralReg: the full SM4.C aggregate dominates the Reg-extended invariant"
      schedulerInvariant_perCore_to_structuralReg .registerBank,
    pcist! "default_schedulerInvariantStructuralReg_smp: the freshly-booted system satisfies the Reg-extended SMP invariant"
      default_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "schedulerInvariantStructuralReg_smp_of_base_and_ctx: lift base structural preservation + contextMatches into the Reg invariant"
      schedulerInvariantStructuralReg_smp_of_base_and_ctx .registerBank,
    pcist! "scheduleEffectiveOnCore_preserves_contextMatchesCurrentOnCore_sibling: the dispatch frames sibling contextMatches (idempotent save)"
      scheduleEffectiveOnCore_preserves_contextMatchesCurrentOnCore_sibling .registerBank,
    pcist! "switchToThreadOnCore_preserves_contextMatchesCurrentOnCore_sibling: the switch frames sibling contextMatches"
      switchToThreadOnCore_preserves_contextMatchesCurrentOnCore_sibling .registerBank,
    pcist! "advanceDomainOnCore_preserves_schedulerInvariantStructuralReg_smp: domain rotation preserves the Reg invariant"
      advanceDomainOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp: the wake preserves the Reg invariant"
      enqueueRunnableOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "wakeThread_preserves_schedulerInvariantStructuralReg_smp: the cross-core wake preserves the Reg invariant"
      wakeThread_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp: the live dispatch preserves the Reg invariant"
      scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralReg_smp: the idle-aware dispatch preserves the Reg invariant"
      scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp: the switch preserves the Reg invariant"
      switchToThreadOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralReg_smp: the reschedule-SGI handler preserves the Reg invariant"
      handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralReg_smp: the idle enqueue preserves the Reg invariant"
      enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "replenishOnCore_preserves_schedulerInvariantStructuralReg_smp: the CBS replenishment preserves the Reg invariant"
      replenishOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralReg_smp: the domain decrement preserves the Reg invariant"
      decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralReg_smp .registerBank,
    pcist! "schedulerInvariantStructuralRegNodup_perCore: the Nodup-extended invariant (+ runQueueUniqueOnCore)"
      SeLe4n.Kernel.schedulerInvariantStructuralRegNodup_perCore .registerBank,
    pcist! "schedulerInvariantStructuralRegNodup_smp: the system-wide Nodup-extended SMP invariant"
      SeLe4n.Kernel.schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "default_schedulerInvariantStructuralRegNodup_smp: the freshly-booted system satisfies the Nodup-extended SMP invariant"
      default_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "runQueueUniqueOnCore_smp_of_operated_and_frame: discharge system-wide runQueueUnique from operated-core + sibling frame"
      runQueueUniqueOnCore_smp_of_operated_and_frame .registerBank,
    pcist! "advanceDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: domain rotation preserves the Nodup invariant"
      advanceDomainOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "enqueueRunnableOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the wake preserves the Nodup invariant"
      enqueueRunnableOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp: the cross-core wake preserves the Nodup invariant"
      wakeThread_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the live dispatch preserves the Nodup invariant"
      scheduleEffectiveOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the idle-aware dispatch preserves the Nodup invariant"
      scheduleOrIdleOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "switchToThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the switch preserves the Nodup invariant"
      switchToThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the reschedule-SGI handler preserves the Nodup invariant"
      handleRescheduleSgiOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the idle enqueue preserves the Nodup invariant"
      enqueueIdleThreadOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "replenishOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the CBS replenishment preserves the Nodup invariant"
      replenishOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank,
    pcist! "decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralRegNodup_smp: the domain decrement preserves the Nodup invariant"
      decrementDomainTimeOnCore_preserves_schedulerInvariantStructuralRegNodup_smp .registerBank]

/-- WS-SM SM5.I: the inventory has 79 entries. -/
theorem perCoreInvariantSuiteTheorems_count : perCoreInvariantSuiteTheorems.length = 79 := by decide

/-- WS-SM SM5.I: 14 entries in the `structural` category. -/
theorem perCoreInvariantSuiteTheorems_structural_count :
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .structural)).length = 14 := by decide

/-- WS-SM SM5.I: 18 entries in the `preservation` category (SM5.I.8). -/
theorem perCoreInvariantSuiteTheorems_preservation_count :
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .preservation)).length = 18 := by decide

/-- WS-SM SM5.I: 8 entries in the `suite` category (SM5.I.1–I.4/I.6/I.9). -/
theorem perCoreInvariantSuiteTheorems_suite_count :
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .suite)).length = 8 := by decide

/-- WS-SM SM5.I: 39 entries in the `registerBank` category (SM4.B payoff). -/
theorem perCoreInvariantSuiteTheorems_registerBank_count :
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .registerBank)).length = 39 := by decide

/-- WS-SM SM5.I: per-category counts sum to the total. -/
theorem perCoreInvariantSuiteTheorems_partition_sum :
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .structural)).length +
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .preservation)).length +
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .suite)).length +
    (perCoreInvariantSuiteTheorems.filter (fun t => t.category == .registerBank)).length =
    perCoreInvariantSuiteTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.I: every inventory identifier is unique.  Kernel-sound `decide`
(not `native_decide`): a duplicate identifier — which `native_decide` could mask
by trusting the compiled evaluation — fails this proof in the kernel. -/
theorem perCoreInvariantSuiteTheorems_identifiers_nodup :
    (perCoreInvariantSuiteTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.I: every inventory description is unique (kernel-sound `decide`). -/
theorem perCoreInvariantSuiteTheorems_descriptions_nodup :
    (perCoreInvariantSuiteTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
