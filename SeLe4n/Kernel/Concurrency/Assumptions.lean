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
      "Single-core: SchedulerState has a single `current : Option ThreadId` \
       slot rather than a per-core array; this is the canonical single-core \
       kernel model recorded in `Architecture/Assumptions.lean` via the \
       `ArchAssumption` inductive + `assumptionInventory` aggregator."
    smpDischarge      :=
      "SMP: model extension would replace the slot with `Array (Option ThreadId)`. \
       AN9-J ships SMP code merged but `SMP_ENABLED = false` at v1.0.0 — the \
       runtime flag inhibits cross-core transitions until the model extension \
       is wired."
    sourceTheorem     := `SeLe4n.Kernel.Architecture.architecture_assumptions_index
    auditReference    := "AG-* baseline / AN12-B" }

/-- CX-M03 / AN6-F: bootFromPlatform single-core boot bridge. -/
def bootFromPlatform_currentCore_is_zero_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Platform.Boot.bootFromPlatform
    singleCoreWitness :=
      "Single-core: bootFromPlatform returns IntermediateState whose scheduler \
       runs on the boot core with implicit core-id = 0; the AN6-F witness \
       `bootFromPlatform_singleCore_witness` confirms the slot semantics."
    smpDischarge      :=
      "SMP: AN9-J's bring_up_secondaries() spins up secondary cores after the \
       boot core has finished bootFromPlatform; the boot bridge predicate \
       holds for the boot core specifically. Secondary cores enter through \
       `rust_secondary_main` which is a separate proof obligation."
    sourceTheorem     := `SeLe4n.Kernel.bootFromPlatform_singleCore_witness
    auditReference    := "CX-M03 / AN6-F" }

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

end SeLe4n.Kernel.Concurrency
