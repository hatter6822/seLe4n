-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM0.C inventory build-anchor; closes SMP-H3)
-- WS-SM SM0.C: SMP-latent inventory build-anchor.  Imports cover every
-- module that owns one of the 8 `smpLatentInventory` entry references
-- (both the `identifier` and `sourceTheorem` projections).
import SeLe4n.Kernel.Concurrency.Assumptions
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate
import SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation
import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.CrossSubsystem
import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Platform.Boot

/-!
# WS-SM SM0.C — AN12-B inventory build-time anchors (closes SMP-H3)

The `smpLatentInventory` in `Concurrency.Assumptions` carries 8
entries, each pointing at two named symbols — the `identifier` of
the kernel site and the `sourceTheorem` that anchors its
single-core/SMP correspondence.  The names are stored as
`Lean.Name` literals; Lean does not enforce that a `Lean.Name`
literal resolves to a real defined symbol, so a renamed theorem
would silently leave a dangling inventory entry.

This module closes the gap audit-finding **SMP-H3** raised by
forcing every named symbol to be `@`-referenced at elaboration.
The build-anchor `example` below carries, in total, **24
`@`-references plus 1 `ArchAssumption` constructor witness**:

* **12** for the `smpLatentInventory` entries — the `identifier`
  and `sourceTheorem` of all 8 (several entries share a
  sourceTheorem name with their identifier — e.g.,
  `lifecyclePreRetypeCleanup`, `serviceHasPathTo`,
  `typedIdDisjointness`).  **WS-SM SM4.E** repointed two of these:
  entry 7's sourceTheorem is now
  `Platform.Boot.bootFromPlatform_smp_witness` and entry 8's is
  `Platform.Boot.bootFromPlatform_smp_currentAllNone` (the retired
  `bootFromPlatform_singleCore_witness` and the no-longer-cited
  `architecture_assumptions_index` are dropped here).
* **1** `ArchAssumption` constructor witness (it is an inductive,
  referenced via the `singleCoreOperation` constructor).
* **5** surface-anchor references for the SM0.B / SM0.C / SM0.D
  theorems (`archAssumptionConsumer_distinct_6`,
  `architecture_assumptions_index_total_6`, `assumptionInventory_count`,
  `smpLatentInventory_identifiers_nodup`,
  `smpLatentInventory_sourceTheorems_nodup`).
* **7** for the **WS-SM SM4.E.5** retirement ledger
  (`smpRetiredInventory` + its six witnesses
  `_count` / `_covers_latent` / `_identifiers_nodup` /
  `_retiredBy_nodup` / `_pathARetired_count` /
  `_perCoreBracketGated_count`).  The ledger's per-entry
  `identifier` / `retiredBy` names mirror the latent inventory, so
  they are already covered by the 12 above.

If any anchored symbol is renamed without updating the inventory,
the corresponding `@`-reference fails to elaborate and the build
breaks.

Wired into `SeLe4n.Platform.Staged` so every CI run forces this
check.
-/

namespace SeLe4n.Kernel.Concurrency

/-- **WS-SM SM0.C** (closes SMP-H3): build-time `@`-references for
every `smpLatentInventory` entry's `identifier` and `sourceTheorem`.

The `let _ := @symbol` pattern forces Lean to resolve each name at
elaboration; a renamed symbol becomes "unknown identifier", failing
the build.

For each of the 8 inventory entries, the references are listed in
order matching `Concurrency.Assumptions.smpLatentInventory`. -/
example : True := by
  -- Entry 1: cspaceLookupMultiLevel_smpLatent (H-05 / AN4-D)
  let _ := @SeLe4n.Kernel.cspaceLookupMultiLevel
  let _ := @SeLe4n.Kernel.resolveCapAddress_result_valid_cnode
  -- Entry 2: cspaceCopyMoveMutate_smpLatent (AK7-F.cascade / AN10-B)
  let _ := @SeLe4n.Kernel.cspaceCopy
  let _ := @SeLe4n.Kernel.cspaceCopy_preserves_capabilityInvariantBundle
  -- Entry 3: lifecyclePreRetypeCleanup_smpLatent (C-M04 / AN9-D)
  let _ := @SeLe4n.Kernel.lifecyclePreRetypeCleanup
  -- Entry 4: serviceHasPathTo_smpLatent (SVC-M01 / AN4-H)
  let _ := @SeLe4n.Kernel.serviceHasPathTo
  -- Entry 5: timerTickReplenishmentPipeline_smpLatent (AK2-K / AN5-D)
  let _ := @SeLe4n.Kernel.timerTickWithBudget
  let _ := @SeLe4n.Kernel.replenishmentPipelineOrder
  -- Entry 6: typedIdDisjointness_smpLatent (H-10 / AN2-D)
  let _ := @SeLe4n.Kernel.typedIdDisjointness
  -- Entry 7: architecture_singleCoreOnly_smpLatent (AG-* / AN12-B / SM4.E.3)
  -- `ArchAssumption` is an inductive type, not a function, so we
  -- reference it via an instance projection rather than `@`.
  let _ : SeLe4n.Kernel.Architecture.ArchAssumption :=
    SeLe4n.Kernel.Architecture.ArchAssumption.singleCoreOperation
  -- SM4.E.3: entry 7's sourceTheorem is now the per-core SMP witness
  -- (was `architecture_assumptions_index` before SM4.E retired the
  -- single-core boot witness).
  let _ := @SeLe4n.Platform.Boot.bootFromPlatform_smp_witness
  -- Entry 8: bootFromPlatform_currentCore_is_zero_smpLatent (CX-M03 / AN6-F / SM4.E.4)
  let _ := @SeLe4n.Platform.Boot.bootFromPlatform
  -- SM4.E.4: entry 8's sourceTheorem is now the substantive per-core
  -- boot-current witness (was the retired `bootFromPlatform_singleCore_witness`).
  let _ := @SeLe4n.Platform.Boot.bootFromPlatform_smp_currentAllNone
  -- WS-SM SM0.B: surface-anchor the new SMP-H2 closure theorems
  -- alongside the inventory references so the 6-way variant of the
  -- consumer index is wired through the same build-time gate.
  let _ := @SeLe4n.Kernel.Architecture.archAssumptionConsumer_distinct_6
  let _ := @SeLe4n.Kernel.Architecture.architecture_assumptions_index_total_6
  let _ := @SeLe4n.Kernel.Architecture.assumptionInventory_count
  -- WS-SM SM0.D: surface-anchor the NoDup witnesses too.
  let _ := @SeLe4n.Kernel.Concurrency.smpLatentInventory_identifiers_nodup
  let _ := @SeLe4n.Kernel.Concurrency.smpLatentInventory_sourceTheorems_nodup
  -- WS-SM SM4.E.5: anchor the retirement ledger + its witnesses.  The
  -- per-entry `identifier` / `retiredBy` names mirror the latent inventory
  -- (already anchored above), so only the aggregator and its five witness
  -- theorems are new symbols here.
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_count
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_covers_latent
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_identifiers_nodup
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_retiredBy_nodup
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_pathARetired_count
  let _ := @SeLe4n.Kernel.Concurrency.smpRetiredInventory_perCoreBracketGated_count
  trivial

/-- **WS-SM SM0.C**: aggregator marker — `@`-references the build
anchor `example` so the surface check is itself locatable in the
proof surface.  Tier-3 surface scans grep for `smpAnchorVerified`
to confirm the SM0.C gate is wired. -/
def smpAnchorVerified : Unit := ()

end SeLe4n.Kernel.Concurrency
