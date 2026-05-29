-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for H3 hardware binding (AN12-B / Theme 4.4 inventory)

import SeLe4n.Prelude
import SeLe4n.Model.State

/-!
# AN12-B (Theme 4.4) — SMP-latent single-core assumption inventory

This module is the **post-AN9-J SMP-implementation confirmation inventory**.
Each entry below records a kernel site that was SMP-latent before AN9-J's
secondary-core bring-up landed and is now SMP-implemented with runtime
gating (`SMP_ENABLED = false` at v1.0.0; the cost of activation is a
runtime flag flip).

The module does NOT itself impose any new proof obligation: every entry
is a documentation-as-code record cross-referencing the proof / Rust HAL /
audit artefacts that establish the property at the post-AN9-J state. The
schema below is decidable so a tier-3 surface anchor can grep for the
inventory and verify it is reachable from `Platform.Staged`.

See `docs/spec/SELE4N_SPEC.md` §6 for the table form and the Rust HAL
contract that AN9-J closed (`SMP_ENABLED`, PSCI bring-up, per-core stack
allocation in `.smp_stacks`).
-/

namespace SeLe4n.Kernel.Concurrency

/-- AN12-B (Theme 4.4): record schema for an SMP-latent assumption.

Each entry carries:
- `identifier` — the canonical Lean `Name` of the kernel site whose proof
  body or signature relied on a single-core ordering assumption.
- `singleCoreWitness` — prose describing what holds today under the
  single-core kernel model.
- `smpDischarge` — prose describing what AN9-J's runtime gating + the
  Rust HAL bracket discipline guarantees once `SMP_ENABLED = true`.
- `sourceTheorem` — the canonical Lean `Name` of the theorem (or boot
  bridge) that anchors the property in the proof surface.
- `auditReference` — short audit-ID string identifying the originating
  finding or workstream sub-task.

The `identifier` and `sourceTheorem` fields hold `Lean.Name` literals.
Lean does not enforce that a `Lean.Name` literal resolves to a defined
symbol — the name is just a structural reference. The inventory's
canonical names are **audited by source-read at every WS-AN closure**;
each name in the 8 entries below was verified to resolve to a real
kernel symbol at v0.30.11 (AN12-B audit pass). Importing every named
symbol's owning module here would balloon the dependency graph; the
audit-by-source-read pattern keeps the inventory lightweight while
maintaining accuracy. Future maintainers who add or rename an entry
must re-run the source-read audit and update names accordingly — the
non-resolution case is a documentation regression, not a proof failure.

The structure is a plain Lean record so the per-entry record-builder
syntax collapses to literal data at elaboration; the inventory list below
is therefore a concrete value that can be grepped and decided at term
level. -/
structure SmpLatentAssumption where
  identifier        : Lean.Name
  singleCoreWitness : String
  smpDischarge      : String
  sourceTheorem     : Lean.Name
  auditReference    : String
deriving Inhabited

/-! ## AN12-B.2 — capability / lifecycle / scheduler entries (5)

These entries record sites whose proof body or composition pattern
assumed strict sequential ordering between adjacent kernel calls. Under
AN9-J's runtime model each is preserved by the FFI bracket
`interrupts::with_interrupts_disabled` plus, for cross-core sites, the
`SMP_ENABLED = false` runtime flag at v1.0.0. -/

/-- H-05 / AN4-D: resolved-CNode validity across multi-level lookup
calls in `cspaceLookupMultiLevel`. -/
def cspaceLookupMultiLevel_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.cspaceLookupMultiLevel
    singleCoreWitness :=
      "Single-core: no retype between resolveCapAddress and cspaceLookupSlot — \
       the resolved CNode reference remains valid for the full multi-level walk."
    smpDischarge      :=
      "SMP: AN9-D HAL-bracket atomicity (interrupt-disabled dispatch path) \
       preserves the no-retype invariant across the walk on the calling core."
    sourceTheorem     := `SeLe4n.Kernel.resolveCapAddress_result_valid_cnode
    auditReference    := "H-05 / AN4-D" }

/-- AK7-F.cascade: CDT post-state composition assumes no concurrent
mutation between `cspaceCopy` / `cspaceMove` / `cspaceMutate`. -/
def cspaceCopyMoveMutate_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.cspaceCopy
    singleCoreWitness :=
      "Single-core: AM4 lifecycleObjectTypeLockstep invariant pins object kind \
       per ObjId; CDT post-state (`hCdtPost`) discharge composes uniformly."
    smpDischarge      :=
      "SMP: same AM4 invariant carries; storeObject is a single Lean step \
       and the FFI bracket prevents interleaved capability operations."
    sourceTheorem     := `SeLe4n.Kernel.cspaceCopy_preserves_capabilityInvariantBundle
    auditReference    := "AK7-F.cascade / AN10-B" }

/-- C-M04 / AN9-D: lifecyclePreRetypeCleanup sequential cleanup ordering. -/
def lifecyclePreRetypeCleanup_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.lifecyclePreRetypeCleanup
    singleCoreWitness :=
      "Single-core: cleanup walks endpoint queues / TCB IPC fields in a \
       fixed order with no concurrent mutation."
    smpDischarge      :=
      "SMP: AN9-D's `sele4n_suspend_thread` FFI bracket idiom is reused — \
       cleanup runs interrupts-disabled on the calling core."
    sourceTheorem     := `SeLe4n.Kernel.lifecyclePreRetypeCleanup
    auditReference    := "C-M04 / AN9-D" }

/-- SVC-M01 / AN4-H: serviceHasPathTo non-atomic graph traversal. -/
def serviceHasPathTo_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.serviceHasPathTo
    singleCoreWitness :=
      "Single-core: BFS over the registry's dependency map sees a stable \
       snapshot — no concurrent registerService can extend the graph mid-walk."
    smpDischarge      :=
      "SMP: ServiceRegistry mutations route through capability operations; \
       AN9-D bracket discipline serialises them on the calling core."
    sourceTheorem     := `SeLe4n.Kernel.serviceHasPathTo
    auditReference    := "SVC-M01 / AN4-H" }

/-- AK2-K / AN5-D: timer-tick + replenishment-pipeline atomicity. -/
def timerTickReplenishmentPipeline_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.timerTickWithBudget
    singleCoreWitness :=
      "Single-core: timer ISR runs to completion before any other kernel \
       transition — pop-due / refill / process pipeline is atomic."
    smpDischarge      :=
      "SMP: per-core timer bookkeeping; the Rust HAL emits the GIC EOI \
       before re-enabling IRQs (AN8-C ordering). v1.0.0 ships with \
       `SMP_ENABLED = false` so the single-core pipeline is the live path."
    sourceTheorem     := `SeLe4n.Kernel.replenishmentPipelineOrder
    auditReference    := "AK2-K / AN5-D" }

/-! ## AN12-B.3 — foundation / architecture entries (3) -/

/-- H-10 / AN2-D: typed-id disjointness. -/
def typedIdDisjointness_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.typedIdDisjointness
    singleCoreWitness :=
      "Single-core: AN2-D's typedIdDisjointness invariant holds structurally — \
       ThreadId / SchedContextId / ServiceId never collide on a shared ObjId \
       under the Valid*Id smart-constructor discipline (AL1b/AL8)."
    smpDischarge      :=
      "SMP: the invariant is a Prop on the immutable typed-id namespaces, not \
       on a mutable cross-core resource. SMP atomicity on storeObject (single \
       Lean step) preserves it without additional witnesses."
    sourceTheorem     := `SeLe4n.Kernel.typedIdDisjointness
    auditReference    := "H-10 / AN2-D" }

/-- AG-* / Architecture/Assumptions.lean: explicit single-core kernel model. -/
def architecture_singleCoreOnly_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.Architecture.ArchAssumption
    singleCoreWitness :=
      "Single-core operation: WS-SM SM4.B (v0.31.12) replaced the singular \
       `SchedulerState` fields with per-core `Vector α Concurrency.numCores` \
       (path-a), but the *verified kernel still drives only `bootCoreId`* — \
       every transition reads/writes `…OnCore bootCoreId`. The canonical \
       single-core kernel model is recorded in `Architecture/Assumptions.lean` \
       via the `ArchAssumption` inductive (incl. the `singleCoreOperation` \
       arm) + `assumptionInventory` aggregator."
    smpDischarge      :=
      "Implemented in SM4 path-a (v0.31.12, SM4.B): the singular \
       `SchedulerState` fields are now per-core `Vector α numCores` indexed \
       by `CoreId`, so the single-core *state shape* is structurally retired — \
       `SchedulerState.current` IS a per-core map. The SMP shape is witnessed \
       for every core by `Platform.Boot.bootFromPlatform_smp_witness` \
       (`∀ c : CoreId`). SM4.E.1 retired the boot-core-only \
       `bootFromPlatform_singleCore_witness` accordingly. SM5 wires the \
       per-core scheduler so transitions act on `Concurrency.currentCoreId`; \
       cross-core *scheduling* remains gated until SM5, but the state shape is \
       no longer single-core."
    sourceTheorem     := `SeLe4n.Platform.Boot.bootFromPlatform_smp_witness
    auditReference    := "AG-* baseline / AN12-B / SM4.E.3" }

/-- CX-M03 / AN6-F: bootFromPlatform single-core boot bridge. -/
def bootFromPlatform_currentCore_is_zero_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Platform.Boot.bootFromPlatform
    singleCoreWitness :=
      "Single-core: `bootFromPlatform` returns an IntermediateState whose \
       scheduler holds no running thread at boot. Historically the AN6-F \
       witness `bootFromPlatform_singleCore_witness` characterised only the \
       boot core's `current` slot (a single `Option ThreadId` before SM4.B)."
    smpDischarge      :=
      "Implemented in SM4 path-a (v0.31.12, SM4.B): `bootFromPlatform`'s \
       scheduler is per-core-shaped, so `Platform.Boot.bootFromPlatform_smp_currentAllNone` \
       proves the boot current is `none` on *every* core (`∀ c : CoreId`), not \
       just `bootCoreId` — the genuine per-core boot shape. The disjunctive \
       `bootFromPlatform_smp_witness` is forward-compatible: it survives SM4.G's \
       per-core idle-thread bootstrap (`some (idleThreadId c)`) unchanged. \
       Secondary cores still enter through `rust_secondary_main`, a separate \
       proof obligation gated on SM5."
    sourceTheorem     := `SeLe4n.Platform.Boot.bootFromPlatform_smp_currentAllNone
    auditReference    := "CX-M03 / AN6-F / SM4.E.4" }

/-- AN12-B.4: aggregator. The full inventory aggregates the 8 entries above
into a single value that downstream tooling (e.g. `audit_testing_framework.sh`)
can grep / decide on. -/
def smpLatentInventory : List SmpLatentAssumption :=
  [ cspaceLookupMultiLevel_smpLatent
  , cspaceCopyMoveMutate_smpLatent
  , lifecyclePreRetypeCleanup_smpLatent
  , serviceHasPathTo_smpLatent
  , timerTickReplenishmentPipeline_smpLatent
  , typedIdDisjointness_smpLatent
  , architecture_singleCoreOnly_smpLatent
  , bootFromPlatform_currentCore_is_zero_smpLatent ]

/-- AN12-B.4: tier-3-anchorable size witness. The inventory has exactly 8
entries at v0.30.11; if a future entry is added or removed, this theorem
must be updated in the same PR (it is the single point that pins the
inventory cardinality). -/
theorem smpLatentInventory_count : smpLatentInventory.length = 8 := by decide

/-- AN12-B.4: structural decidability — every entry's `identifier` is
non-empty (sanity check for the inventory schema). Each of the 8 entries
is a literal record with a fully-qualified `Lean.Name`, so the
non-anonymous predicate is decidable per-entry by `simp` on the field. -/
theorem smpLatentInventory_identifiers_nonAnonymous :
    ∀ entry ∈ smpLatentInventory, entry.identifier ≠ Lean.Name.anonymous := by
  intro entry hEntry
  simp [smpLatentInventory] at hEntry
  rcases hEntry with h|h|h|h|h|h|h|h <;>
    subst h <;>
    simp [cspaceLookupMultiLevel_smpLatent, cspaceCopyMoveMutate_smpLatent,
          lifecyclePreRetypeCleanup_smpLatent, serviceHasPathTo_smpLatent,
          timerTickReplenishmentPipeline_smpLatent, typedIdDisjointness_smpLatent,
          architecture_singleCoreOnly_smpLatent,
          bootFromPlatform_currentCore_is_zero_smpLatent]

/-- **WS-SM SM0.D** (closes SMP-L1): structural pinning that no two
inventory entries share an `identifier`.

The 8-entry size is witnessed by `smpLatentInventory_count`, but a
maintainer who *renames* one entry's `identifier` to collide with
another existing entry would slip past the size check.  This NoDup
witness catches the collision at build time: `decide` performs the
8 × 7 / 2 = 28 pairwise inequality checks on the `Lean.Name`
literals and fails to elaborate if any pair matches. -/
theorem smpLatentInventory_identifiers_nodup :
    (smpLatentInventory.map (·.identifier)).Nodup := by
  unfold smpLatentInventory
  simp only [List.map_cons, List.map_nil,
    cspaceLookupMultiLevel_smpLatent, cspaceCopyMoveMutate_smpLatent,
    lifecyclePreRetypeCleanup_smpLatent, serviceHasPathTo_smpLatent,
    timerTickReplenishmentPipeline_smpLatent, typedIdDisjointness_smpLatent,
    architecture_singleCoreOnly_smpLatent,
    bootFromPlatform_currentCore_is_zero_smpLatent]
  decide

/-- **WS-SM SM0.D**: parallel NoDup witness for the `sourceTheorem`
projection.  Catches collisions in the consumer-theorem mapping
(distinct singleCore witnesses must point at distinct theorems)
that the identifier-only NoDup misses — for example, two distinct
inventory entries that document different singleCore properties
but accidentally cite the same proof obligation. -/
theorem smpLatentInventory_sourceTheorems_nodup :
    (smpLatentInventory.map (·.sourceTheorem)).Nodup := by
  unfold smpLatentInventory
  simp only [List.map_cons, List.map_nil,
    cspaceLookupMultiLevel_smpLatent, cspaceCopyMoveMutate_smpLatent,
    lifecyclePreRetypeCleanup_smpLatent, serviceHasPathTo_smpLatent,
    timerTickReplenishmentPipeline_smpLatent, typedIdDisjointness_smpLatent,
    architecture_singleCoreOnly_smpLatent,
    bootFromPlatform_currentCore_is_zero_smpLatent]
  decide

/-! ## WS-SM SM4.E.5 — retirement inventory (`smpRetiredInventory`)

SM4 path-a (the per-core `Vector` replacement of the singular
`SchedulerState` fields) begins discharging the SMP-latent single-core
assumptions recorded in `smpLatentInventory`.  `smpRetiredInventory` is the
companion ledger that tracks the retirement of each of the 8 latent
assumptions toward the v1.0.0 SMP release; it mirrors `smpLatentInventory`
one-to-one by `identifier` (`smpRetiredInventory_covers_latent`).

At SM4.E exactly two assumptions are genuinely retired by path-a — the
scheduler-state shape (`Architecture.ArchAssumption`) and the boot-core
current-thread shape (`Platform.Boot.bootFromPlatform`) — because SM4.B
made `SchedulerState.current` (and the other six per-core fields) a
`Vector α numCores`, so the single-core *state shape* no longer applies.
The other six remain `perCoreBracketGated`: their single-core property is
preserved per-core by the FFI interrupt-disabled dispatch bracket, with
full cross-core retirement tracked against later WS-SM phases (SM5 per-core
scheduler / SM6 cross-core IPC).  This honest disposition is pinned by
`smpRetiredInventory_pathARetired_count` (= 2 at SM4.E); WS-SM SM9 (release
closure) adds `smpRetiredInventory_complete` once every entry is
discharged. -/

/-- WS-SM SM4.E.5: retirement disposition of an `smpLatentInventory` entry. -/
inductive SmpRetirementStatus where
  /-- The SM4 path-a per-core `Vector` replacement makes the single-core
      *state shape* structurally inapplicable (the scheduler field IS a
      per-core map now).  The `retiredBy` theorem witnesses the
      post-retirement SMP shape. -/
  | pathARetired
  /-- The assumption's single-core property is preserved on the calling
      core by the FFI interrupt-disabled dispatch bracket; full cross-core
      retirement is gated on a later WS-SM phase (SM5 per-core scheduler /
      SM6 cross-core IPC).  Tracked here for completeness. -/
  | perCoreBracketGated
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM4.E.5: record schema for the retirement of an SMP-latent
assumption.  Parallels `SmpLatentAssumption`; `smpRetiredInventory` mirrors
`smpLatentInventory` one-to-one (every latent assumption has a retirement
record).  `retiredBy` is a `Lean.Name` literal (audited by source-read,
build-anchored in `Concurrency.Anchors`) naming the theorem that witnesses
the retirement (for `.pathARetired`) or the per-core consumer that
discharges the single-core property today (for `.perCoreBracketGated`). -/
structure SmpRetiredAssumption where
  identifier     : Lean.Name
  status         : SmpRetirementStatus
  retirement     : String
  retiredBy      : Lean.Name
  auditReference : String
deriving Inhabited

/-- H-05 / AN4-D: resolved-CNode validity across the multi-level walk. -/
def cspaceLookupMultiLevel_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.cspaceLookupMultiLevel
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: the no-retype-during-walk invariant holds on the calling \
       core under the AN9-D interrupt-disabled dispatch bracket. Cross-core \
       retirement tracked against SM5 (per-core scheduler)."
    retiredBy      := `SeLe4n.Kernel.resolveCapAddress_result_valid_cnode
    auditReference := "H-05 / AN4-D" }

/-- AK7-F.cascade: CDT post-state composition for cspaceCopy/Move/Mutate. -/
def cspaceCopyMoveMutate_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.cspaceCopy
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: the AM4 lifecycleObjectTypeLockstep invariant + single-step \
       storeObject + FFI bracket serialise capability ops on the calling \
       core. Cross-core retirement tracked against SM5."
    retiredBy      := `SeLe4n.Kernel.cspaceCopy_preserves_capabilityInvariantBundle
    auditReference := "AK7-F.cascade / AN10-B" }

/-- C-M04 / AN9-D: lifecyclePreRetypeCleanup sequential cleanup ordering. -/
def lifecyclePreRetypeCleanup_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.lifecyclePreRetypeCleanup
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: cleanup runs interrupts-disabled on the calling core via the \
       `sele4n_suspend_thread` FFI bracket idiom. Cross-core retirement \
       tracked against SM5."
    retiredBy      := `SeLe4n.Kernel.lifecyclePreRetypeCleanup
    auditReference := "C-M04 / AN9-D" }

/-- SVC-M01 / AN4-H: serviceHasPathTo graph traversal. -/
def serviceHasPathTo_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.serviceHasPathTo
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: ServiceRegistry mutations route through capability ops, \
       serialised on the calling core by the AN9-D bracket. Cross-core \
       retirement tracked against SM5."
    retiredBy      := `SeLe4n.Kernel.serviceHasPathTo
    auditReference := "SVC-M01 / AN4-H" }

/-- AK2-K / AN5-D: timer-tick + replenishment-pipeline atomicity. -/
def timerTickReplenishmentPipeline_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.timerTickWithBudget
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: each core runs its own timer tick; the GIC EOI precedes the \
       IRQ re-enable (AN8-C ordering) so the pop-due/refill/process pipeline \
       is atomic per core. Cross-core retirement tracked against SM5."
    retiredBy      := `SeLe4n.Kernel.replenishmentPipelineOrder
    auditReference := "AK2-K / AN5-D" }

/-- H-10 / AN2-D: typed-id disjointness. -/
def typedIdDisjointness_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.typedIdDisjointness
    status         := .perCoreBracketGated
    retirement     :=
      "Per-core: the invariant is a Prop on the immutable typed-id namespaces, \
       preserved by the single Lean step storeObject; no cross-core mutable \
       resource is involved. Tracked against SM5 for uniformity with the other \
       runtime entries."
    retiredBy      := `SeLe4n.Kernel.typedIdDisjointness
    auditReference := "H-10 / AN2-D" }

/-- AG-* / AN12-B: single-core kernel *state shape* — RETIRED by SM4 path-a. -/
def architecture_singleCoreOnly_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Kernel.Architecture.ArchAssumption
    status         := .pathARetired
    retirement     :=
      "Retired by SM4 path-a (v0.31.12, SM4.B): the singular `SchedulerState` \
       fields are now per-core `Vector α numCores`, so the single-core state \
       shape is structurally inapplicable. The per-core SMP shape is witnessed \
       by `bootFromPlatform_smp_witness` (`∀ c : CoreId`). SM4.E.1 retired the \
       boot-core-only `bootFromPlatform_singleCore_witness`."
    retiredBy      := `SeLe4n.Platform.Boot.bootFromPlatform_smp_witness
    auditReference := "AG-* baseline / AN12-B / SM4.E.3" }

/-- CX-M03 / AN6-F: bootFromPlatform boot-core current — RETIRED by SM4 path-a. -/
def bootFromPlatform_currentCore_is_zero_smpRetired : SmpRetiredAssumption :=
  { identifier     := `SeLe4n.Platform.Boot.bootFromPlatform
    status         := .pathARetired
    retirement     :=
      "Retired by SM4 path-a (v0.31.12, SM4.B): `bootFromPlatform`'s scheduler \
       is per-core-shaped, so `bootFromPlatform_smp_currentAllNone` proves the \
       boot current is `none` on every core (`∀ c : CoreId`). The boot-core- \
       only `bootFromPlatform_singleCore_witness` was retired at SM4.E.1."
    retiredBy      := `SeLe4n.Platform.Boot.bootFromPlatform_smp_currentAllNone
    auditReference := "CX-M03 / AN6-F / SM4.E.4" }

/-- WS-SM SM4.E.5: the retirement ledger.  One record per `smpLatentInventory`
entry, in the same order, so `smpRetiredInventory_covers_latent` is a clean
identifier-list equality. -/
def smpRetiredInventory : List SmpRetiredAssumption :=
  [ cspaceLookupMultiLevel_smpRetired
  , cspaceCopyMoveMutate_smpRetired
  , lifecyclePreRetypeCleanup_smpRetired
  , serviceHasPathTo_smpRetired
  , timerTickReplenishmentPipeline_smpRetired
  , typedIdDisjointness_smpRetired
  , architecture_singleCoreOnly_smpRetired
  , bootFromPlatform_currentCore_is_zero_smpRetired ]

/-- WS-SM SM4.E.5: tier-3-anchorable size witness — the retirement ledger has
exactly 8 entries, one per `smpLatentInventory` entry.  Pinned so a future
entry added to (or removed from) either inventory without updating the other
fails this size check (in concert with `smpRetiredInventory_covers_latent`). -/
theorem smpRetiredInventory_count : smpRetiredInventory.length = 8 := by decide

/-- WS-SM SM4.E.5: structural mirror — the retirement ledger covers exactly
the SMP-latent assumptions, in the same order.  This is the substantive
content of the ledger: every latent single-core assumption has a retirement
record, and no spurious record exists.  Together with `smpRetiredInventory_count`
it pins the 1:1 correspondence with `smpLatentInventory`. -/
theorem smpRetiredInventory_covers_latent :
    smpRetiredInventory.map (·.identifier) = smpLatentInventory.map (·.identifier) := by
  unfold smpRetiredInventory smpLatentInventory
  simp only [List.map_cons, List.map_nil,
    cspaceLookupMultiLevel_smpRetired, cspaceCopyMoveMutate_smpRetired,
    lifecyclePreRetypeCleanup_smpRetired, serviceHasPathTo_smpRetired,
    timerTickReplenishmentPipeline_smpRetired, typedIdDisjointness_smpRetired,
    architecture_singleCoreOnly_smpRetired,
    bootFromPlatform_currentCore_is_zero_smpRetired,
    cspaceLookupMultiLevel_smpLatent, cspaceCopyMoveMutate_smpLatent,
    lifecyclePreRetypeCleanup_smpLatent, serviceHasPathTo_smpLatent,
    timerTickReplenishmentPipeline_smpLatent, typedIdDisjointness_smpLatent,
    architecture_singleCoreOnly_smpLatent,
    bootFromPlatform_currentCore_is_zero_smpLatent]

/-- WS-SM SM4.E.5: NoDup on the retirement ledger's `identifier` projection.
Inherits from `smpRetiredInventory_covers_latent` + the latent inventory's
own `smpLatentInventory_identifiers_nodup`, but proved directly so a rename
collision is caught at this file's build step. -/
theorem smpRetiredInventory_identifiers_nodup :
    (smpRetiredInventory.map (·.identifier)).Nodup := by
  unfold smpRetiredInventory
  simp only [List.map_cons, List.map_nil,
    cspaceLookupMultiLevel_smpRetired, cspaceCopyMoveMutate_smpRetired,
    lifecyclePreRetypeCleanup_smpRetired, serviceHasPathTo_smpRetired,
    timerTickReplenishmentPipeline_smpRetired, typedIdDisjointness_smpRetired,
    architecture_singleCoreOnly_smpRetired,
    bootFromPlatform_currentCore_is_zero_smpRetired]
  decide

/-- WS-SM SM4.E.5: NoDup on the `retiredBy` projection — every retirement
record cites a distinct anchoring theorem (the two `.pathARetired` boot
witnesses plus the six per-core-bracket consumers). -/
theorem smpRetiredInventory_retiredBy_nodup :
    (smpRetiredInventory.map (·.retiredBy)).Nodup := by
  unfold smpRetiredInventory
  simp only [List.map_cons, List.map_nil,
    cspaceLookupMultiLevel_smpRetired, cspaceCopyMoveMutate_smpRetired,
    lifecyclePreRetypeCleanup_smpRetired, serviceHasPathTo_smpRetired,
    timerTickReplenishmentPipeline_smpRetired, typedIdDisjointness_smpRetired,
    architecture_singleCoreOnly_smpRetired,
    bootFromPlatform_currentCore_is_zero_smpRetired]
  decide

/-- WS-SM SM4.E.5: honest disposition pin — at SM4.E exactly **two** entries
are genuinely retired by path-a (the scheduler-state shape and the boot-core
current-thread shape); the other six are `perCoreBracketGated` (single-core
property preserved per-core by the FFI bracket, full retirement gated on
SM5+).  This count is the honest current state per the implement-the-improvement
rule — it deliberately does NOT claim all 8 are retired.  WS-SM SM9 (release
closure) flips the gated entries to retired as SM5..SM8 land and proves
`smpRetiredInventory_complete`. -/
theorem smpRetiredInventory_pathARetired_count :
    (smpRetiredInventory.filter (fun e => decide (e.status = .pathARetired))).length = 2 := by
  decide

end SeLe4n.Kernel.Concurrency
