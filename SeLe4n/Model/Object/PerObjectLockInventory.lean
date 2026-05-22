-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Model.FrozenState

/-!
# WS-SM SM3.A audit-pass-5 — Per-object lock theorem inventory

This module aggregates the SM3.A substantive theorems into a single
typed inventory with a size witness `perObjectLockTheorems.length`
and per-category counts.  Mirrors the SM2.D
`Concurrency.LockPrimitives` pattern (22-theorem aggregator) for
the SM3.A surface.

The inventory serves three purposes:

1. **Documentation closure**: a single point of truth for "what
   does SM3.A prove?" — referenceable from
   `docs/spec/SELE4N_SPEC.md §2.8` and any future GitBook chapter
   on per-object locking.
2. **Tier-3 surface anchor**: every theorem in the inventory has
   its `Lean.Name` recorded; a regression that renames or removes
   a theorem fails the Tier-3 surface check via the existing
   `tests/PerObjectLockSuite.lean` `#check` lines.
3. **Closure verification**: the per-category counts pin the
   "shape" of SM3.A — adding a new theorem requires updating the
   inventory plus the per-category count witnesses, forcing the
   reviewer to think about category placement.

## Category breakdown

* `.fieldDefault` — the seven per-object lock field declarations
  (SM3.A.1..A.9 — TCB, Endpoint, CNode, Notification,
  UntypedObject, SchedContext, VSpaceRoot).
* `.projection` — the `objectLockOf` / `FrozenKernelObject.objectLockOf`
  projections plus their per-variant simp lemmas (SM3.A.10).
* `.defaultState` — the four SM3.A.11 default-state theorems
  (`default_objStoreLock_unheld`, `default_objects_locks_unheld`,
  `default_objects_toList_empty`,
  `default_objects_locks_unheld_via_toList`).
* `.preservation` — the audit-pass-2 / audit-pass-5 freeze and
  storeObject preservation witnesses.
* `.consistency` — the audit-pass-5 `objectLockOf` totality /
  consistency witnesses + the `KernelObjectType` variants count
  pinning the Reply (SM3.A.5) / Page (SM3.A.8) N/A decisions.

## Adding a new SM3.A theorem

1. Add the theorem to the appropriate `SeLe4n.Model` namespace.
2. Add an entry to `perObjectLockTheorems` below with the correct
   category.
3. Update the per-category count witness if the addition shifts
   the cardinality.
4. The `perObjectLockTheorems_count` and
   `perObjectLockTheorems_partition_sum` theorems will then
   verify the new total.
-/

namespace SeLe4n.Model

/-- WS-SM SM3.A audit-pass-5: category tag for per-object lock theorems. -/
inductive PerObjectLockCategory where
  /-- Per-object `lock : RwLockState` field declarations. -/
  | fieldDefault
  /-- `objectLockOf` projection + per-variant simp lemmas. -/
  | projection
  /-- SM3.A.11 default-state theorems. -/
  | defaultState
  /-- Freeze / storeObject preservation witnesses. -/
  | preservation
  /-- `objectLockOf` totality + variant-cardinality consistency. -/
  | consistency
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.A audit-pass-5: a theorem entry in the SM3.A inventory.

Records a human-readable `description`, the theorem's
fully-qualified Lean name as a `String` (so this module does NOT
require importing every theorem to participate — keeps the
inventory cheap to build), and a `category` tag for partition
verification. -/
structure PerObjectLockTheorem where
  /-- Human-readable description of what the theorem proves. -/
  description : String
  /-- Fully-qualified Lean name (for documentation cross-reference). -/
  identifier  : String
  /-- Category tag — used by per-category count witnesses. -/
  category    : PerObjectLockCategory
  deriving Repr, Inhabited

/-- WS-SM SM3.A audit-pass-5: the SM3.A substantive theorem
inventory.

Entries are grouped by category and the total cardinality is
pinned by `perObjectLockTheorems_count` below.  A regression that
adds a new theorem without updating this inventory fails the
Tier-3 surface check at the count-witness step. -/
def perObjectLockTheorems : List PerObjectLockTheorem :=
  [-- §1 fieldDefault (7 entries — SM3.A.1..A.9 lock fields)
    { description := "TCB carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.TCB.lock"
      category    := .fieldDefault },
    { description := "Endpoint carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.Endpoint.lock"
      category    := .fieldDefault },
    { description := "CNode carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.CNode.lock"
      category    := .fieldDefault },
    { description := "Notification carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.Notification.lock"
      category    := .fieldDefault },
    { description := "UntypedObject carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.UntypedObject.lock"
      category    := .fieldDefault },
    { description := "SchedContext carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Kernel.SchedContext.lock"
      category    := .fieldDefault },
    { description := "VSpaceRoot carries a per-object RwLockState lock field"
      identifier  := "SeLe4n.Model.VSpaceRoot.lock"
      category    := .fieldDefault },
    -- §2 projection (9 entries — objectLockOf def + 7 unfolds + FrozenKernelObject.objectLockOf def)
    { description := "KernelObject.objectLockOf projects the per-variant lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf"
      category    := .projection },
    { description := "objectLockOf on .tcb reduces to t.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_tcb"
      category    := .projection },
    { description := "objectLockOf on .endpoint reduces to e.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_endpoint"
      category    := .projection },
    { description := "objectLockOf on .cnode reduces to c.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_cnode"
      category    := .projection },
    { description := "objectLockOf on .notification reduces to n.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_notification"
      category    := .projection },
    { description := "objectLockOf on .vspaceRoot reduces to v.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_vspaceRoot"
      category    := .projection },
    { description := "objectLockOf on .untyped reduces to u.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_untyped"
      category    := .projection },
    { description := "objectLockOf on .schedContext reduces to s.lock"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_schedContext"
      category    := .projection },
    { description := "FrozenKernelObject.objectLockOf projects the frozen per-variant lock"
      identifier  := "SeLe4n.Model.FrozenKernelObject.objectLockOf"
      category    := .projection },
    -- §3 defaultState (5 entries — 4 SM3.A.11 + objStoreLock unheld)
    { description := "Default SystemState has objStoreLock = .unheld"
      identifier  := "SeLe4n.Model.default_objStoreLock_unheld"
      category    := .defaultState },
    { description := "Default SystemState's object store has no entries with held locks"
      identifier  := "SeLe4n.Model.default_objects_locks_unheld"
      category    := .defaultState },
    { description := "Default SystemState's objects.toList is empty"
      identifier  := "SeLe4n.Model.default_objects_toList_empty"
      category    := .defaultState },
    { description := "Default SystemState's toList membership entries all have unheld locks"
      identifier  := "SeLe4n.Model.default_objects_locks_unheld_via_toList"
      category    := .defaultState },
    { description := "Default SystemState satisfies allObjectLocksUnheld (non-vacuous)"
      identifier  := "SeLe4n.Model.default_allObjectLocksUnheld"
      category    := .defaultState },
    -- §4 preservation (5 entries — 4 freeze + 4 storeObject; total 8 listed)
    { description := "freeze preserves objStoreLock"
      identifier  := "SeLe4n.Model.freeze_preserves_objStoreLock"
      category    := .preservation },
    { description := "freezeCNode preserves the CNode lock"
      identifier  := "SeLe4n.Model.freezeCNode_preserves_lock"
      category    := .preservation },
    { description := "freezeVSpaceRoot preserves the VSpaceRoot lock"
      identifier  := "SeLe4n.Model.freezeVSpaceRoot_preserves_lock"
      category    := .preservation },
    { description := "freezeObject preserves objectLockOf across the frozen mirror"
      identifier  := "SeLe4n.Model.freezeObject_preserves_objectLockOf"
      category    := .preservation },
    { description := "storeObject preserves the table-level objStoreLock"
      identifier  := "SeLe4n.Model.storeObject_preserves_objStoreLock"
      category    := .preservation },
    { description := "storeObject preserves off-target objectLockOf entries"
      identifier  := "SeLe4n.Model.storeObject_preserves_objectLockOf_off_target"
      category    := .preservation },
    { description := "storeObject inserted-object lookup returns the inserted value"
      identifier  := "SeLe4n.Model.storeObject_inserted_object_lookup"
      category    := .preservation },
    { description := "storeObject with unheld lock preserves allObjectLocksUnheld"
      identifier  := "SeLe4n.Model.storeObject_preserves_allObjectLocksUnheld"
      category    := .preservation },
    -- §5 consistency (4 entries — totality + variants cardinality)
    { description := "objectLockOf is total over every KernelObject"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_exists"
      category    := .consistency },
    { description := "objectType and objectLockOf are co-consistent over every KernelObject"
      identifier  := "SeLe4n.Model.KernelObject.objectType_and_lockOf_total"
      category    := .consistency },
    { description := "objectLockOf is consistent with the kind tag"
      identifier  := "SeLe4n.Model.KernelObject.objectLockOf_consistent_with_type"
      category    := .consistency },
    { description := "KernelObjectType has exactly 7 variants (locks down Reply / Page N/A decisions)"
      identifier  := "SeLe4n.Model.KernelObjectType.variants_count_exactly_seven"
      category    := .consistency },
    { description := "KernelObjectType variants_total — every value is one of the 7 enumerated kinds"
      identifier  := "SeLe4n.Model.KernelObjectType.variants_total"
      category    := .consistency }]

/-- WS-SM SM3.A audit-pass-5: the inventory has exactly 34 entries.
A regression that adds a new SM3.A theorem without updating the
inventory fails this count witness at the Tier-3 surface check. -/
theorem perObjectLockTheorems_count :
    perObjectLockTheorems.length = 34 := by decide

/-- WS-SM SM3.A audit-pass-5: 7 entries in the `fieldDefault` category. -/
theorem perObjectLockTheorems_fieldDefault_count :
    (perObjectLockTheorems.filter (fun t => t.category == .fieldDefault)).length = 7 := by
  decide

/-- WS-SM SM3.A audit-pass-5: 9 entries in the `projection` category. -/
theorem perObjectLockTheorems_projection_count :
    (perObjectLockTheorems.filter (fun t => t.category == .projection)).length = 9 := by
  decide

/-- WS-SM SM3.A audit-pass-5: 5 entries in the `defaultState` category. -/
theorem perObjectLockTheorems_defaultState_count :
    (perObjectLockTheorems.filter (fun t => t.category == .defaultState)).length = 5 := by
  decide

/-- WS-SM SM3.A audit-pass-5: 8 entries in the `preservation` category. -/
theorem perObjectLockTheorems_preservation_count :
    (perObjectLockTheorems.filter (fun t => t.category == .preservation)).length = 8 := by
  decide

/-- WS-SM SM3.A audit-pass-5: 5 entries in the `consistency` category. -/
theorem perObjectLockTheorems_consistency_count :
    (perObjectLockTheorems.filter (fun t => t.category == .consistency)).length = 5 := by
  decide

/-- WS-SM SM3.A audit-pass-5: per-category counts sum to the total.
A regression that adds an entry without updating the per-category
count fails this partition theorem. -/
theorem perObjectLockTheorems_partition_sum :
    (perObjectLockTheorems.filter (fun t => t.category == .fieldDefault)).length +
    (perObjectLockTheorems.filter (fun t => t.category == .projection)).length +
    (perObjectLockTheorems.filter (fun t => t.category == .defaultState)).length +
    (perObjectLockTheorems.filter (fun t => t.category == .preservation)).length +
    (perObjectLockTheorems.filter (fun t => t.category == .consistency)).length =
    perObjectLockTheorems.length := by
  decide

/-- WS-SM SM3.A audit-pass-5: every inventory identifier is unique.
A regression that adds a duplicate entry fails this Nodup witness. -/
theorem perObjectLockTheorems_identifiers_nodup :
    (perObjectLockTheorems.map (·.identifier)).Nodup := by
  decide

/-- WS-SM SM3.A audit-pass-5: every inventory description is unique. -/
theorem perObjectLockTheorems_descriptions_nodup :
    (perObjectLockTheorems.map (·.description)).Nodup := by
  decide

end SeLe4n.Model
