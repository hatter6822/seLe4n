-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt

/-!
# WS-SM SM5.J — WCRT-under-fine-locks theorem inventory

Aggregates the SM5.J substantive theorems into a single typed inventory with size
and per-category witnesses.  Mirrors the SM5.G `PerCoreDomainInventory.lean` and
SM5.H `PerCoreCbsInventory.lean` patterns.

Four categories matching the plan §3.9 / §5 SM5.J sub-tasks (32 entries):

* `.lockSetWcrt` — SM5.J.1: the `WCRT_lockSet` fine-lock-contention WCRT cost
  function, its product / nil / monotonicity / size-bound forms, and the RPi5
  `coreCount − 1 = 3` core-count grounding (`rpi5OtherCoreCount`,
  `perLockWaitCost_rpi5`, `WCRT_lockSet_rpi5`).
* `.rpi5Bound` — SM5.J.2: the plan §3.9 Theorem 3.9.1 `wcrt_bound_rpi5_smp` and the
  combined `WCRT_smp` (R5 scheduling latency + lock contention) extending the R5
  `wcrtBound`, with its decomposition / component / full-bound theorems.
* `.perOp` — SM5.J.3: the per-operation WCRT bounds (chooseThread / switchToThread /
  wake / timerTick / replenish / advanceDomain), each with its exact value and its
  `≤ maxLockSetSize · 3 · tCs` headline, plus the generic `wcrt_op_bounded_of_size`.
* `.liveness` — SM5.J.4: no thread starves under SMP — the per-core non-stall
  (`schedulerNoStall*`), the bounded-lock-wait no-unbounded-inversion
  (`boundedKernelWait_smp`), the capstone `no_starvation_under_smp`, and the
  R5-latency bridge `r5_latency_within_smp_bound`.

## Identifier validation

Identifiers are compile-time-validated via the `pcwt!` macro, mirroring SM5.G's
`pcdt!`.  A typo or stale rename fails the build at this module's elaboration step
with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

/-- WS-SM SM5.J: category tag for the SM5.J theorem inventory. -/
inductive PerCoreWcrtCategory where
  /-- SM5.J.1 the `WCRT_lockSet` cost function + its forms + RPi5 core-count grounding. -/
  | lockSetWcrt
  /-- SM5.J.2 the RPi5 §3.9 bound `wcrt_bound_rpi5_smp` + the combined `WCRT_smp`. -/
  | rpi5Bound
  /-- SM5.J.3 the per-operation WCRT bounds + exact values. -/
  | perOp
  /-- SM5.J bridge between the static SchedLockId `WCRT_lockSet` and the
  execution-sensitive LockId-domain `Concurrency.WCRT` / `totalWaitCost`. -/
  | executionBridge
  /-- SM5.J.4 no-thread-starves-under-SMP liveness. -/
  | liveness
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.J: a theorem entry in the SM5.J inventory.  Records a description, the
fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pcwt!`) forces Lean to resolve
the referenced declaration at construction time. -/
structure PerCoreWcrtTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreWcrtCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.J: build a `PerCoreWcrtTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreWcrtTheoremMacro) "pcwt!" str ident term : term

macro_rules
  | `(pcwt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreWcrtTheorem))

/-- WS-SM SM5.J: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pcwt!`. -/
def perCoreWcrtTheorems : List PerCoreWcrtTheorem :=
  [-- ── SM5.J.1 `WCRT_lockSet` cost function + forms + RPi5 grounding (.lockSetWcrt) ──
    pcwt! "WCRT_lockSet: the fine-lock-contention WCRT of a per-core op (SM5.J.1)"
      WCRT_lockSet .lockSetWcrt,
    pcwt! "WCRT_lockSet_eq_product: unfolds to |lockSet| · ((numCores−1) · tCs)"
      WCRT_lockSet_eq_product .lockSetWcrt,
    pcwt! "WCRT_lockSet_nil: the empty footprint contributes zero lock-wait"
      WCRT_lockSet_nil .lockSetWcrt,
    pcwt! "WCRT_lockSet_mono_length: monotone in the footprint length"
      WCRT_lockSet_mono_length .lockSetWcrt,
    pcwt! "WCRT_lockSet_mono_cost: monotone in the per-lock critical-section cost"
      WCRT_lockSet_mono_cost .lockSetWcrt,
    pcwt! "WCRT_lockSet_le_maxLockSetSize: uniform bound ≤ maxLockSetSize · (numCores−1) · tCs"
      WCRT_lockSet_le_maxLockSetSize .lockSetWcrt,
    pcwt! "rpi5OtherCoreCount: RPi5 coreCount − 1 = 3 (the §3.9 × 3 factor)"
      rpi5OtherCoreCount .lockSetWcrt,
    pcwt! "perLockWaitCost_rpi5: the RPi5 per-lock wait cost is 3 · tCs"
      perLockWaitCost_rpi5 .lockSetWcrt,
    pcwt! "WCRT_lockSet_rpi5: the RPi5 form |lockSet| · 3 · tCs"
      WCRT_lockSet_rpi5 .lockSetWcrt,
    pcwt! "WCRT_lockSet_mode_independent: the worst-case bound is access-mode-agnostic (sound: all-writers case)"
      WCRT_lockSet_mode_independent .lockSetWcrt,
    -- ── SM5.J.2 RPi5 bound + combined WCRT_smp (.rpi5Bound) ──
    pcwt! "wcrt_bound_rpi5_smp: plan §3.9 Theorem 3.9.1 — RPi5 WCRT ≤ maxLockSetSize · 3 · tCs (SM5.J.2)"
      wcrt_bound_rpi5_smp .rpi5Bound,
    pcwt! "WCRT_smp: the combined SMP WCRT (R5 scheduling latency + lock contention)"
      WCRT_smp .rpi5Bound,
    pcwt! "WCRT_smp_decomposition: the combined bound splits into R5 + lock terms"
      WCRT_smp_decomposition .rpi5Bound,
    pcwt! "WCRT_smp_r5_component_le: the R5 term is a lower component"
      WCRT_smp_r5_component_le .rpi5Bound,
    pcwt! "WCRT_smp_lockSet_component_le: the SM5.J lock term is a lower component"
      WCRT_smp_lockSet_component_le .rpi5Bound,
    pcwt! "wcrt_smp_bound_rpi5: the full extends-R5 bound (R5 latency + maxLockSetSize · 3 · tCs)"
      wcrt_smp_bound_rpi5 .rpi5Bound,
    pcwt! "wcrt_bound_smp: the honest config-free numCores-grounded bound (C8)"
      wcrt_bound_smp .rpi5Bound,
    pcwt! "WCRT_smp_cycles: the cycle-commensurate combined bound (cyclesPerTick·wcrtBound + WCRT_lockSet) (C9)"
      WCRT_smp_cycles .rpi5Bound,
    pcwt! "WCRT_smp_cycles_one: WCRT_smp is the cyclesPerTick = 1 instance"
      WCRT_smp_cycles_one .rpi5Bound,
    pcwt! "WCRT_smp_cycles_decomposition: the cycle-commensurate bound's R5 + lock split"
      WCRT_smp_cycles_decomposition .rpi5Bound,
    -- ── SM5.J.3 per-operation WCRT bounds (.perOp) ──
    pcwt! "wcrt_op_bounded_of_size: generic per-op RPi5 bound from a footprint-size witness"
      wcrt_op_bounded_of_size .perOp,
    pcwt! "wcrt_chooseThreadOnCore_eq: chooseThreadOnCore lock-WCRT = 2 · 3 · tCs (SM5.J.3)"
      wcrt_chooseThreadOnCore_eq .perOp,
    pcwt! "wcrt_chooseThreadOnCore_bounded: chooseThreadOnCore ≤ maxLockSetSize · 3 · tCs"
      wcrt_chooseThreadOnCore_bounded .perOp,
    pcwt! "wcrt_switchToThreadOnCore_eq: switchToThreadOnCore lock-WCRT = 2 · 3 · tCs"
      wcrt_switchToThreadOnCore_eq .perOp,
    pcwt! "wcrt_switchToThreadOnCore_bounded: switchToThreadOnCore ≤ maxLockSetSize · 3 · tCs"
      wcrt_switchToThreadOnCore_bounded .perOp,
    pcwt! "wcrt_wakeThread_eq: wakeThread lock-WCRT = 2 · 3 · tCs"
      wcrt_wakeThread_eq .perOp,
    pcwt! "wcrt_wakeThread_bounded: wakeThread ≤ maxLockSetSize · 3 · tCs"
      wcrt_wakeThread_bounded .perOp,
    pcwt! "wcrt_timerTickOnCore_eq: timerTickOnCore lock-WCRT = 3 · 3 · tCs"
      wcrt_timerTickOnCore_eq .perOp,
    pcwt! "wcrt_timerTickOnCore_bounded: timerTickOnCore ≤ maxLockSetSize · 3 · tCs"
      wcrt_timerTickOnCore_bounded .perOp,
    pcwt! "wcrt_replenishOnCore_eq: replenishOnCore lock-WCRT = 1 · 3 · tCs"
      wcrt_replenishOnCore_eq .perOp,
    pcwt! "wcrt_replenishOnCore_bounded: replenishOnCore ≤ maxLockSetSize · 3 · tCs"
      wcrt_replenishOnCore_bounded .perOp,
    pcwt! "wcrt_advanceDomainOnCore_bounded: advanceDomainOnCore ≤ maxLockSetSize · 3 · tCs"
      wcrt_advanceDomainOnCore_bounded .perOp,
    pcwt! "wcrt_handleRescheduleSgiOnCore_bounded: the cross-core SGI handler ≤ maxLockSetSize · 3 · tCs"
      wcrt_handleRescheduleSgiOnCore_bounded .perOp,
    pcwt! "wcrt_timerTickOnCoreComplete_bounded: the complete (3-or-4-lock) tick footprint ≤ maxLockSetSize · 3 · tCs"
      wcrt_timerTickOnCoreComplete_bounded .perOp,
    -- ── SM5.J execution bridge to Concurrency.WCRT (.executionBridge) ──
    pcwt! "WCRT_lockSet_eq_totalWaitCost_of_length_eq: WCRT_lockSet = SM3.D totalWaitCost (same uniform cost)"
      WCRT_lockSet_eq_totalWaitCost_of_length_eq .executionBridge,
    pcwt! "kernelWait_le_WCRT_lockSet_of_length_eq: the execution-sensitive Concurrency.WCRT ≤ the static WCRT_lockSet"
      kernelWait_le_WCRT_lockSet_of_length_eq .executionBridge,
    -- ── SM5.J.4 no-thread-starves-under-SMP liveness (.liveness) ──
    pcwt! "schedulerNoStallOnCore: per-core idle fallback ⇒ chooseThreadOnCore succeeds (SM5.J.4)"
      schedulerNoStallOnCore .liveness,
    pcwt! "schedulerNoStall_smp: every core makes a scheduling decision (∀-core no-stall)"
      schedulerNoStall_smp .liveness,
    pcwt! "schedulerNoStall_smp_of_idleAvailableB: the decidable no-stall discharge (closes the hypothesis-never-discharged gap)"
      schedulerNoStall_smp_of_idleAvailableB .liveness,
    pcwt! "boundedKernelWait_smp: deadlock-free + WCRT ≤ maxLockSetSize · 3 · tCs (no unbounded inversion)"
      boundedKernelWait_smp .liveness,
    pcwt! "thread_eventually_scheduled_onCore: the GENUINE per-core eventually-scheduled liveness (SM5.J.4 keystone)"
      thread_eventually_scheduled_onCore .liveness,
    pcwt! "thread_eventually_scheduled_within_smp_bound: per-core progress within the combined R5 + lock bound"
      thread_eventually_scheduled_within_smp_bound .liveness,
    pcwt! "no_starvation_under_smp: the genuine SMP no-starvation capstone (no stall ∧ eventually-scheduled ∧ bounded lock-wait)"
      no_starvation_under_smp .liveness,
    pcwt! "r5_latency_within_smp_bound: single-core R5 selection within the combined SMP bound"
      r5_latency_within_smp_bound .liveness]

/-- WS-SM SM5.J: the inventory has 44 substantive entries (32 at the SM5.J initial
landing + 12 from the completion pass: the genuine per-core eventually-scheduled
liveness, the execution-sensitive bridge, the cycle-commensurate units, the honest
config-free grounding, the access-mode-soundness, and the SGI-handler /
complete-timer per-op bounds).  A regression that adds a new SM5.J theorem without
registering it fails this count witness at the Tier-3 surface check. -/
theorem perCoreWcrtTheorems_count : perCoreWcrtTheorems.length = 44 := by decide

/-- WS-SM SM5.J: 10 entries in the `lockSetWcrt` category (+1: access-mode soundness). -/
theorem perCoreWcrtTheorems_lockSetWcrt_count :
    (perCoreWcrtTheorems.filter (fun t => t.category == .lockSetWcrt)).length = 10 := by decide

/-- WS-SM SM5.J: 10 entries in the `rpi5Bound` category (+4: config-free bound + cycle units). -/
theorem perCoreWcrtTheorems_rpi5Bound_count :
    (perCoreWcrtTheorems.filter (fun t => t.category == .rpi5Bound)).length = 10 := by decide

/-- WS-SM SM5.J: 14 entries in the `perOp` category (+2: SGI handler + complete timer). -/
theorem perCoreWcrtTheorems_perOp_count :
    (perCoreWcrtTheorems.filter (fun t => t.category == .perOp)).length = 14 := by decide

/-- WS-SM SM5.J: 2 entries in the `executionBridge` category. -/
theorem perCoreWcrtTheorems_executionBridge_count :
    (perCoreWcrtTheorems.filter (fun t => t.category == .executionBridge)).length = 2 := by decide

/-- WS-SM SM5.J: 8 entries in the `liveness` category (+3: decidable no-stall discharge +
the genuine eventually-scheduled keystone + the combined-bound progress). -/
theorem perCoreWcrtTheorems_liveness_count :
    (perCoreWcrtTheorems.filter (fun t => t.category == .liveness)).length = 8 := by decide

/-- WS-SM SM5.J: per-category counts sum to the total. -/
theorem perCoreWcrtTheorems_partition_sum :
    (perCoreWcrtTheorems.filter (fun t => t.category == .lockSetWcrt)).length +
    (perCoreWcrtTheorems.filter (fun t => t.category == .rpi5Bound)).length +
    (perCoreWcrtTheorems.filter (fun t => t.category == .perOp)).length +
    (perCoreWcrtTheorems.filter (fun t => t.category == .executionBridge)).length +
    (perCoreWcrtTheorems.filter (fun t => t.category == .liveness)).length =
    perCoreWcrtTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.J: every inventory identifier is unique.  Kernel-sound `decide` (not
`native_decide`): a duplicate identifier — which `native_decide` could mask by
trusting the compiled evaluation — fails this proof in the kernel. -/
theorem perCoreWcrtTheorems_identifiers_nodup :
    (perCoreWcrtTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.J: every inventory description is unique.  Kernel-sound `decide` under
an elevated `maxRecDepth` (see `perCoreWcrtTheorems_identifiers_nodup`). -/
theorem perCoreWcrtTheorems_descriptions_nodup :
    (perCoreWcrtTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
