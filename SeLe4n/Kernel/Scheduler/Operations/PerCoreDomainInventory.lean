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

Nine categories matching the plan §3.7 / §5 sub-tasks (75 entries; 39 at the initial
SM5.G landing + 28 from the completion audit-pass + 8 from the §11 deep-audit pass —
the SM5.G invariants maintained by the live domain tick):

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
  `advanceDomainOnCoreLockSet` footprint, its acquisition-order witness, its
  cross-core disjointness witness, and the write-containment theorem.
* `.query` — SM5.G.1: the literal §3.7 `SystemState.activeDomainOnCore` accessor,
  its `@[simp]` bridge, and the §3.7 Theorem 3.7.1 membership form over it.
* `.invariant` — SM5.G.2: the `domainScheduleIndexInBoundsOnCore` and
  `domainConsistentOnCore` invariants (the cyclic theorem's discharged preconditions)
  + their default-state / establishment / frame witnesses.
* `.livePreservation` — SM5.G.3: invariant preservation by the **live** transitions
  `switchDomainOnCore` / `scheduleDomainOnCore` + the `scheduleEffectiveOnCore` /
  `idleFallbackOnCore` / `decrementDomainTimeOnCore` domain frames they consume.

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
  /-- SM5.G.1 the `SystemState.activeDomainOnCore` query + its §3.7 membership form. -/
  | query
  /-- SM5.G.2 the index-bounds + domain-consistency invariants (the cyclic theorem's
  discharged preconditions). -/
  | invariant
  /-- SM5.G.3 live-transition invariant preservation (`switchDomainOnCore` /
  `scheduleDomainOnCore`) + the `scheduleEffectiveOnCore` domain frames. -/
  | livePreservation
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
      advanceDomainOnCoreLockSet_disjoint_of_ne .independence,
    -- ── SM5.G completion: cyclic extensions (.cyclic) ──
    pcdt! "advanceDomainOnCore_cyclic_of_inBounds: cyclic discharged from the index-bounds invariant"
      advanceDomainOnCore_cyclic_of_inBounds .cyclic,
    pcdt! "advanceDomainOnCore_cyclic_activeDomain: the active domain (not just the index) cycles with period length"
      advanceDomainOnCore_cyclic_activeDomain .cyclic,
    -- ── SM5.G completion: full domain-triple bridge (.bridge) ──
    pcdt! "switchDomainOnCore_domainScheduleIndexOnCore_self: the operational switch's index effect"
      switchDomainOnCore_domainScheduleIndexOnCore_self .bridge,
    pcdt! "switchDomainOnCore_domainTimeRemainingOnCore_self: the operational switch's time effect"
      switchDomainOnCore_domainTimeRemainingOnCore_self .bridge,
    pcdt! "switchDomainOnCore_domainTriple_eq_advanceDomainOnCore: the FULL domain-triple bridge (all 3 fields)"
      switchDomainOnCore_domainTriple_eq_advanceDomainOnCore .bridge,
    -- ── SM5.G completion: respects-without-hwf eligibility helpers (.respects) ──
    pcdt! "chooseBestRunnableEffective_result_eligible: budget-aware fold records an in-domain thread (no hwf)"
      chooseBestRunnableEffective_result_eligible .respects,
    pcdt! "chooseBestInBucketEffective_result_eligible: budget-aware bucket selection records an in-domain thread (no hwf)"
      chooseBestInBucketEffective_result_eligible .respects,
    -- ── SM5.G completion: cross-core footprint witnesses (.independence) ──
    pcdt! "advanceDomainOnCoreLockSet_pairwise_le: footprint keys form a valid acquisition order"
      advanceDomainOnCoreLockSet_pairwise_le .independence,
    pcdt! "advanceDomainOnCore_frames_outside_core: the rotation writes only core c's per-core scheduler state"
      advanceDomainOnCore_frames_outside_core .independence,
    -- ── SM5.G.1 query accessor (.query) ──
    pcdt! "SystemState.activeDomainOnCore: the §3.7 SystemState-level active-domain query"
      SeLe4n.Model.SystemState.activeDomainOnCore .query,
    pcdt! "SystemState.activeDomainOnCore_eq: the @[simp] bridge to the scheduler accessor"
      SeLe4n.Model.SystemState.activeDomainOnCore_eq .query,
    pcdt! "activeDomainOnCore_systemState_mem: §3.7 Theorem 3.7.1 over the SystemState accessor"
      activeDomainOnCore_systemState_mem .query,
    -- ── SM5.G.2 invariants (index-bounds + domain-consistency) (.invariant) ──
    pcdt! "domainScheduleIndexInBoundsOnCore: the schedule-index-bounds invariant"
      domainScheduleIndexInBoundsOnCore .invariant,
    pcdt! "default_domainScheduleIndexInBoundsOnCore: boot satisfies the index-bounds invariant"
      default_domainScheduleIndexInBoundsOnCore .invariant,
    pcdt! "advanceDomainOnCore_establishes_domainScheduleIndexInBoundsOnCore: rotation establishes index-bounds"
      advanceDomainOnCore_establishes_domainScheduleIndexInBoundsOnCore .invariant,
    pcdt! "advanceDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore_ne: index-bounds framed on other cores"
      advanceDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore_ne .invariant,
    pcdt! "domainConsistentOnCore: the domain-consistency invariant (activeDomain = entry-at-index domain)"
      domainConsistentOnCore .invariant,
    pcdt! "default_domainConsistentOnCore: boot satisfies the domain-consistency invariant"
      default_domainConsistentOnCore .invariant,
    pcdt! "advanceDomainOnCore_establishes_domainConsistentOnCore: rotation establishes domain consistency"
      advanceDomainOnCore_establishes_domainConsistentOnCore .invariant,
    -- ── SM5.G.3 live-transition preservation + scheduleEffective frames (.livePreservation) ──
    pcdt! "idleFallbackOnCore_activeDomainOnCore: the idle fallback frames the active domain"
      idleFallbackOnCore_activeDomainOnCore .livePreservation,
    pcdt! "idleFallbackOnCore_domainSchedule: the idle fallback frames the domain schedule"
      idleFallbackOnCore_domainSchedule .livePreservation,
    pcdt! "scheduleEffectiveOnCore_activeDomainOnCore: the per-core reschedule frames the active domain"
      scheduleEffectiveOnCore_activeDomainOnCore .livePreservation,
    pcdt! "scheduleEffectiveOnCore_domainSchedule: the per-core reschedule frames the domain schedule"
      scheduleEffectiveOnCore_domainSchedule .livePreservation,
    pcdt! "switchDomainOnCore_domainSchedule: the operational switch frames the domain schedule"
      switchDomainOnCore_domainSchedule .livePreservation,
    pcdt! "decrementDomainTimeOnCore_domainSchedule: the domain decrement frames the domain schedule"
      decrementDomainTimeOnCore_domainSchedule .livePreservation,
    pcdt! "switchDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule: live rotation preserves the membership invariant"
      switchDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule .livePreservation,
    pcdt! "switchDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore: live rotation preserves index-bounds"
      switchDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore .livePreservation,
    pcdt! "scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule: live domain tick preserves the membership invariant"
      scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule .livePreservation,
    -- ── SM5.G completion §11: the SM5.G invariants maintained by the LIVE domain tick ──
    pcdt! "domainScheduleIndexInBoundsOnCore_frame: the index-bounds invariant's read-footprint frame"
      domainScheduleIndexInBoundsOnCore_frame .invariant,
    pcdt! "domainConsistentOnCore_frame: the domain-consistency invariant's read-footprint frame"
      domainConsistentOnCore_frame .invariant,
    pcdt! "idleFallbackOnCore_domainScheduleIndexOnCore: the idle fallback frames the schedule index"
      idleFallbackOnCore_domainScheduleIndexOnCore .livePreservation,
    pcdt! "scheduleEffectiveOnCore_domainScheduleIndexOnCore: the reschedule frames the schedule index"
      scheduleEffectiveOnCore_domainScheduleIndexOnCore .livePreservation,
    pcdt! "decrementDomainTimeOnCore_domainScheduleIndexOnCore: the domain decrement frames the schedule index"
      decrementDomainTimeOnCore_domainScheduleIndexOnCore .livePreservation,
    pcdt! "scheduleDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore: live domain tick preserves index-bounds"
      scheduleDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore .livePreservation,
    pcdt! "switchDomainOnCore_preserves_domainConsistentOnCore: live rotation preserves domain consistency"
      switchDomainOnCore_preserves_domainConsistentOnCore .livePreservation,
    pcdt! "scheduleDomainOnCore_preserves_domainConsistentOnCore: live domain tick preserves domain consistency"
      scheduleDomainOnCore_preserves_domainConsistentOnCore .livePreservation]

/-- WS-SM SM5.G: the inventory has 67 substantive entries (39 at the initial SM5.G
landing + 28 from the completion audit-pass).  A regression that adds a new SM5.G
theorem without registering it fails this count witness at the Tier-3 surface check. -/
theorem perCoreDomainTheorems_count : perCoreDomainTheorems.length = 75 := by decide

/-- WS-SM SM5.G: 14 entries in the `rotation` category. -/
theorem perCoreDomainTheorems_rotation_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .rotation)).length = 14 := by decide

/-- WS-SM SM5.G: 8 entries in the `cyclic` category (+2 completion: discharged + active-domain). -/
theorem perCoreDomainTheorems_cyclic_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .cyclic)).length = 8 := by decide

/-- WS-SM SM5.G: 4 entries in the `bridge` category (+3 completion: full domain-triple bridge). -/
theorem perCoreDomainTheorems_bridge_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .bridge)).length = 4 := by decide

/-- WS-SM SM5.G: 6 entries in the `domainSchedule` category. -/
theorem perCoreDomainTheorems_domainSchedule_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .domainSchedule)).length = 6 := by decide

/-- WS-SM SM5.G: 6 entries in the `respects` category (+2 completion: budget eligibility helpers). -/
theorem perCoreDomainTheorems_respects_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .respects)).length = 6 := by decide

/-- WS-SM SM5.G: 10 entries in the `independence` category (+2 completion: pairwise + write-containment). -/
theorem perCoreDomainTheorems_independence_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .independence)).length = 10 := by decide

/-- WS-SM SM5.G: 3 entries in the `query` category (SM5.G.1 accessor + membership). -/
theorem perCoreDomainTheorems_query_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .query)).length = 3 := by decide

/-- WS-SM SM5.G: 9 entries in the `invariant` category (index-bounds + domain-consistency
+ §11 read-footprint frames). -/
theorem perCoreDomainTheorems_invariant_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .invariant)).length = 9 := by decide

/-- WS-SM SM5.G: 15 entries in the `livePreservation` category (live-transition preservation
+ frames; +6 §11: the SM5.G invariants maintained by the live domain tick). -/
theorem perCoreDomainTheorems_livePreservation_count :
    (perCoreDomainTheorems.filter (fun t => t.category == .livePreservation)).length = 15 := by decide

/-- WS-SM SM5.G: per-category counts sum to the total. -/
theorem perCoreDomainTheorems_partition_sum :
    (perCoreDomainTheorems.filter (fun t => t.category == .rotation)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .cyclic)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .bridge)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .domainSchedule)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .respects)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .independence)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .query)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .invariant)).length +
    (perCoreDomainTheorems.filter (fun t => t.category == .livePreservation)).length =
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
