-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain

/-!
# WS-SM SM5.G — Theorem inventory

Aggregates the SM5.G per-core domain-scheduling substantive theorems into a single
typed inventory with size and per-category witnesses.  Mirrors the SM5.E
`PerCoreIdleInventory.lean` and SM5.D `PerCoreTimerInventory.lean` patterns.

Six categories matching the plan §3.7 / §5 sub-tasks:

* `.rotation` — SM5.G.1 / SM5.G.2: the pure rotation `advanceDomainOnCore`, its
  frame lemmas (objects / getTcb? / domainSchedule / run-queue / current /
  per-other-core domain triple), and the single-step index/domain/time formulas +
  boundedness.
* `.cyclic` — SM5.G.2: the `advanceDomainOnCoreN` `k`-fold iteration, its schedule
  frame + index formula, and the cyclic theorem `advanceDomainOnCore_cyclic`.
* `.bridge` — SM5.G.2: `switchDomainOnCore_activeDomain_eq_advanceDomainOnCore`
  (the operational switch's domain effect is this rotation).
* `.domainSchedule` — SM5.G.3: `activeDomainOnCore_isInDomainSchedule`
  establishment / per-other-core preservation / SMP preservation, and the
  plan §3.7 Theorem 3.7.1 membership form.
* `.respects` — SM5.G.4: `chooseThreadOnCore_respects_activeDomain` (+ the
  budget-aware companion and the fold-eligibility helpers).
* `.independence` — SM5.G.5: cross-core domain independence + the
  `advanceDomainOnCoreLockSet` footprint and its cross-core disjointness witness.

## Identifier validation

Identifiers are compile-time-validated via the `pcdt!` macro, mirroring SM5.E's
`pcit!`.  A typo or stale rename fails the build at this module's elaboration step
with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

/-- WS-SM SM5.G: category tag for the SM5.G theorem inventory. -/
inductive PerCoreDomainCategory where
  /-- SM5.G.1 / SM5.G.2 the pure rotation `advanceDomainOnCore` + frames + single-step. -/
  | rotation
  /-- SM5.G.2 the `advanceDomainOnCoreN` iteration + cyclic theorem. -/
  | cyclic
  /-- SM5.G.2 the bridge to the operational `switchDomainOnCore`. -/
  | bridge
  /-- SM5.G.3 `activeDomainOnCore_isInDomainSchedule` establish / preserve / membership. -/
  | domainSchedule
  /-- SM5.G.4 `chooseThreadOnCore_respects_activeDomain` + helpers. -/
  | respects
  /-- SM5.G.5 cross-core independence + footprint. -/
  | independence
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.G: a theorem entry in the SM5.G inventory.  Records a description, the
fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pcdt!`) forces Lean to resolve
the referenced declaration at construction time. -/
structure PerCoreDomainTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreDomainCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.G: build a `PerCoreDomainTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreDomainTheoremMacro) "pcdt!" str ident term : term

macro_rules
  | `(pcdt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreDomainTheorem))

/-- WS-SM SM5.G: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pcdt!`. -/
def perCoreDomainTheorems : List PerCoreDomainTheorem :=
  [-- ── SM5.G.1 / .2 rotation primitive + frames + single-step (.rotation) ──
    pcdt! "advanceDomainOnCore: the pure per-core domain rotation (SM5.G.2)"
      advanceDomainOnCore .rotation,
    pcdt! "advanceDomainOnCore_empty: single-domain mode is a no-op"
      advanceDomainOnCore_empty .rotation,
    pcdt! "advanceDomainOnCore_objects: the rotation never touches the object store"
      advanceDomainOnCore_objects .rotation,
    pcdt! "advanceDomainOnCore_getTcb?: the rotation frames every TCB resolution"
      advanceDomainOnCore_getTcb? .rotation,
    pcdt! "advanceDomainOnCore_domainSchedule: the schedule table is invariant under rotation"
      advanceDomainOnCore_domainSchedule .rotation,
    pcdt! "advanceDomainOnCore_runQueueOnCore: the rotation frames every core's run queue"
      advanceDomainOnCore_runQueueOnCore .rotation,
    pcdt! "advanceDomainOnCore_currentOnCore: the rotation frames every core's current thread"
      advanceDomainOnCore_currentOnCore .rotation,
    pcdt! "advanceDomainOnCore_activeDomainOnCore_ne: frames another core's active domain"
      advanceDomainOnCore_activeDomainOnCore_ne .rotation,
    pcdt! "advanceDomainOnCore_domainTimeRemainingOnCore_ne: frames another core's domain time"
      advanceDomainOnCore_domainTimeRemainingOnCore_ne .rotation,
    pcdt! "advanceDomainOnCore_domainScheduleIndexOnCore_ne: frames another core's schedule index"
      advanceDomainOnCore_domainScheduleIndexOnCore_ne .rotation,
    pcdt! "advanceDomainOnCore_rotates: the rotated active domain is the next entry's domain (SM5.G.1)"
      advanceDomainOnCore_rotates .rotation,
    pcdt! "advanceDomainOnCore_domainTimeRemainingOnCore_self: the rotation resets the domain quantum"
      advanceDomainOnCore_domainTimeRemainingOnCore_self .rotation,
    pcdt! "advanceDomainOnCore_domainScheduleIndexOnCore_self: the single-step index advance (idx+1 mod length)"
      advanceDomainOnCore_domainScheduleIndexOnCore_self .rotation,
    pcdt! "advanceDomainOnCore_index_lt: the rotated index stays in [0, length)"
      advanceDomainOnCore_index_lt .rotation,
    -- ── SM5.G.2 cyclic iteration (.cyclic) ──
    pcdt! "advanceDomainOnCoreN: k-fold per-core domain rotation"
      advanceDomainOnCoreN .cyclic,
    pcdt! "advanceDomainOnCoreN_zero: zero rotations is the identity"
      advanceDomainOnCoreN_zero .cyclic,
    pcdt! "advanceDomainOnCoreN_succ: (k+1)-fold rotation unfolds"
      advanceDomainOnCoreN_succ .cyclic,
    pcdt! "advanceDomainOnCoreN_domainSchedule: the schedule table is invariant under k rotations"
      advanceDomainOnCoreN_domainSchedule .cyclic,
    pcdt! "advanceDomainOnCoreN_index: the index after k rotations is (idx+k) mod length"
      advanceDomainOnCoreN_index .cyclic,
    pcdt! "advanceDomainOnCore_cyclic: rotating length times returns the schedule index to its start (SM5.G.2)"
      advanceDomainOnCore_cyclic .cyclic,
    -- ── SM5.G.2 bridge to production (.bridge) ──
    pcdt! "switchDomainOnCore_activeDomain_eq_advanceDomainOnCore: the production switch's domain effect IS this rotation"
      switchDomainOnCore_activeDomain_eq_advanceDomainOnCore .bridge,
    -- ── SM5.G.3 isInDomainSchedule (.domainSchedule) ──
    pcdt! "advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule: rotation lands on a real schedule domain (SM5.G.3)"
      advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule .domainSchedule,
    pcdt! "advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne: preserved on the untouched cores"
      advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne .domainSchedule,
    pcdt! "advanceDomainOnCore_preserves_isInDomainSchedule_smp: the SMP-wide preservation"
      advanceDomainOnCore_preserves_isInDomainSchedule_smp .domainSchedule,
    pcdt! "activeDomainOnCore_isInDomainSchedule_mem: plan §3.7 Theorem 3.7.1 membership form"
      activeDomainOnCore_isInDomainSchedule_mem .domainSchedule,
    pcdt! "activeDomainOnCore_isInDomainSchedule_mem_of_smp: Theorem 3.7.1 from the SMP cross-subsystem invariant"
      activeDomainOnCore_isInDomainSchedule_mem_of_smp .domainSchedule,
    pcdt! "advanceDomainOnCore_activeDomain_mem: post-rotation active domain is in the schedule"
      advanceDomainOnCore_activeDomain_mem .domainSchedule,
    -- ── SM5.G.4 respects_activeDomain (.respects) ──
    pcdt! "chooseBestRunnableBy_result_eligible: a selected candidate passed the eligibility filter"
      chooseBestRunnableBy_result_eligible .respects,
    pcdt! "chooseBestInBucket_result_eligible: a bucket-first selection records an in-domain thread"
      chooseBestInBucket_result_eligible .respects,
    pcdt! "chooseThreadOnCore_respects_activeDomain: a selected thread is in core c's active domain (SM5.G.4)"
      chooseThreadOnCore_respects_activeDomain .respects,
    pcdt! "chooseThreadEffectiveOnCore_respects_activeDomain: the budget-aware companion respects the domain"
      chooseThreadEffectiveOnCore_respects_activeDomain .respects,
    -- ── SM5.G.5 cross-core independence + footprint (.independence) ──
    pcdt! "advanceDomainOnCore_independent_of_other_core: a sibling core's selection is unaffected (SM5.G.5)"
      advanceDomainOnCore_independent_of_other_core .independence,
    pcdt! "advanceDomainOnCore_perCore_independence: the c₁ ≠ c₂ named independence form"
      advanceDomainOnCore_perCore_independence .independence,
    pcdt! "advanceDomainOnCoreLockSet: the rotation's per-core run-queue WRITE footprint"
      advanceDomainOnCoreLockSet .independence,
    pcdt! "advanceDomainOnCoreLockSet_length: the footprint is the single per-core lock"
      advanceDomainOnCoreLockSet_length .independence,
    pcdt! "advanceDomainOnCoreLockSet_write_only: every lock is WRITE mode"
      advanceDomainOnCoreLockSet_write_only .independence,
    pcdt! "advanceDomainOnCoreLockSet_contains_runQueue_write: the run-queue write lock is present"
      advanceDomainOnCoreLockSet_contains_runQueue_write .independence,
    pcdt! "advanceDomainOnCoreLockSet_keys_nodup: footprint keys are duplicate-free"
      advanceDomainOnCoreLockSet_keys_nodup .independence,
    pcdt! "advanceDomainOnCoreLockSet_disjoint_of_ne: disjoint cores have disjoint footprints"
      advanceDomainOnCoreLockSet_disjoint_of_ne .independence]

/-- WS-SM SM5.G: the inventory has 39 substantive entries.  A regression that adds a
new SM5.G theorem without registering it fails this count witness at the Tier-3
surface check. -/
theorem perCoreDomainTheorems_count : perCoreDomainTheorems.length = 39 := by decide

/-- WS-SM SM5.G: 14 entries in the `rotation` category. -/
theorem perCoreDomainTheorems_rotation_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .rotation)).length = 14 := by decide

/-- WS-SM SM5.G: 6 entries in the `cyclic` category. -/
theorem perCoreDomainTheorems_cyclic_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .cyclic)).length = 6 := by decide

/-- WS-SM SM5.G: 1 entry in the `bridge` category. -/
theorem perCoreDomainTheorems_bridge_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .bridge)).length = 1 := by decide

/-- WS-SM SM5.G: 6 entries in the `domainSchedule` category. -/
theorem perCoreDomainTheorems_domainSchedule_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .domainSchedule)).length = 6 := by decide

/-- WS-SM SM5.G: 4 entries in the `respects` category. -/
theorem perCoreDomainTheorems_respects_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .respects)).length = 4 := by decide

/-- WS-SM SM5.G: 8 entries in the `independence` category. -/
theorem perCoreDomainTheorems_independence_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .independence)).length = 8 := by decide

/-- WS-SM SM5.G: per-category counts sum to the total. -/
theorem perCoreDomainTheorems_partition_sum :
    (perCoreDomainTheorems.filter (fun t => t.category == .rotation)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .cyclic)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .bridge)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .domainSchedule)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .respects)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .independence)).length =
    perCoreDomainTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.G: every inventory identifier is unique.  Kernel-sound `decide` (not
`native_decide`): a duplicate identifier — which `native_decide` could mask by
trusting the compiled evaluation — fails this proof in the kernel. -/
theorem perCoreDomainTheorems_identifiers_nodup :
    (perCoreDomainTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.G: every inventory description is unique.  Kernel-sound `decide` under
an elevated `maxRecDepth` (see `perCoreDomainTheorems_identifiers_nodup`). -/
theorem perCoreDomainTheorems_descriptions_nodup :
    (perCoreDomainTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
