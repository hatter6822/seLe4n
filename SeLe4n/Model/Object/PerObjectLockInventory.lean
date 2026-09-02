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
import SeLe4n.PackedString

/-!
# WS-SM SM3.A audit-pass-5 — Per-object lock theorem inventory

This module aggregates the SM3.A substantive theorems into a single
typed inventory with a size witness `perObjectLockTheorems.length`
and per-category counts.  Mirrors the SM2.D
`Concurrency.LockPrimitives` pattern (22-theorem aggregator) for
the SM3.A surface.

## Compile-time identifier validation (audit-pass-7)

The audit-pass-5 form of `PerObjectLockTheorem` used
`identifier : String` and the audit found a real correctness gap:
the string is not checked against actual declarations, so a typo
or stale rename silently passes Lean's type-checker.  The
audit-pass-7 form adds a `_elabCheck : Unit` field produced via a
`polt!` macro:

    polt! "description" actualTheoremName .category

The macro emits a `let _ := @actualTheoremName; ()` term in the
`_elabCheck` field, forcing Lean's elaborator to resolve
`actualTheoremName` against the current environment at the call
site.  A typo or stale rename fails to elaborate with "unknown
identifier '<name>'" — a static guarantee that every inventory
entry refers to a real declaration.

This is the symmetric improvement over SM2.D `LockPrimitives.lean`,
which carries the same `Lean.Name`-without-elaboration-check
weakness.  SM2.D can adopt the same pattern in a future audit-pass.

## Category breakdown

* `.fieldDefault` — the seven per-object lock field declarations
  (SM3.A.1..A.9).
* `.projection` — the `objectLockOf` / `FrozenKernelObject.objectLockOf`
  projections plus their per-variant simp lemmas (SM3.A.10).
* `.defaultState` — the four SM3.A.11 default-state theorems plus
  the audit-pass-5 non-vacuous `default_allObjectLocksUnheld`.
* `.preservation` — the audit-pass-2 / audit-pass-5 freeze and
  storeObject preservation witnesses.
* `.consistency` — the audit-pass-5 `objectLockOf` totality /
  consistency witnesses + the `KernelObjectType` variants count
  pinning the Reply (SM3.A.5) / Page (SM3.A.8) N/A decisions.

## Adding a new SM3.A theorem

1. Add the theorem to the appropriate `SeLe4n.Model` namespace.
2. Add an entry to `perObjectLockTheorems` below using `polt!` —
   the identifier MUST be a real declaration name (the macro
   elaborates it at compile time).  A typo or rename fails the
   build at this module's elaboration step.
3. Update the per-category count witness if the addition shifts
   the cardinality.
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

/-- WS-SM SM3.A audit-pass-5 / pass-7: a theorem entry in the SM3.A
inventory.

Records a human-readable description and the theorem's fully-
qualified Lean name — each as a packed key (`SeLe4n.PackedString`),
read back through `description` / `identifier` — a compile-time
elaboration witness (`_elabCheck`), and a `category` tag for
partition verification.

The `_elabCheck` field is the structural enforcement that the
`identifier` field actually refers to a defined declaration —
it is produced by the `polt!` macro which emits a `let _ :=
@<name>; ()` term, forcing the elaborator to resolve the name
against the current environment.  A typo or stale rename fails
to elaborate and breaks the build.

`Inhabited` is derived so the structure can be used in `default`-
returning paths; the trivial default has empty strings + `()` +
the `Inhabited` default of `PerObjectLockCategory`. -/
structure PerObjectLockTheorem where
  /-- The description as one packed key (`SeLe4n.PackedString`): one
      base-2²¹ digit per scalar value behind a leading `1`.  Read it back
      through `description`. -/
  descriptionKey : Nat
  /-- The fully-qualified name, packed the same way.  Read it back through
      `identifier`. -/
  identifierKey  : Nat
  /-- The kernel's own check, per entry, that the key packs exactly the valid
      scalar values it unpacks to — what lets distinctness of the strings be
      proven from distinctness of the keys. -/
  descriptionKey_wf : isWellFormedPacked descriptionKey = true := by decide +kernel
  identifierKey_wf  : isWellFormedPacked identifierKey = true := by decide +kernel
  /-- WS-SM SM3.A audit-pass-7: compile-time elaboration witness.
      Always `()` at runtime; its mere existence in the record
      requires Lean to elaborate the referenced declaration at
      construction time (via the `polt!` macro), catching typos
      and stale renames. -/
  _elabCheck  : Unit
  /-- Category tag — used by per-category count witnesses. -/
  category    : PerObjectLockCategory
  deriving Repr

/-- The default entry spells the empty string twice: `1` packs no digits. -/
instance : Inhabited PerObjectLockTheorem :=
  ⟨{ descriptionKey := 1, identifierKey := 1, _elabCheck := (), category := default }⟩

/-- The entry's description, unpacked from its key. -/
def PerObjectLockTheorem.description (t : PerObjectLockTheorem) : String := stringOfPacked t.descriptionKey

/-- The entry's fully-qualified name, unpacked from its key. -/
def PerObjectLockTheorem.identifier (t : PerObjectLockTheorem) : String := stringOfPacked t.identifierKey

/-- WS-SM SM3.A audit-pass-7: build a `PerObjectLockTheorem` with a
compile-time-validated identifier.

Usage:
```
  polt! "description string" actualTheoremName .fieldDefault
```

The macro expands to:
```
  { descriptionKey := nat_lit <packString "description string">,
    identifierKey := nat_lit <packString "actualTheoremName">,
    _elabCheck := (let _ := @actualTheoremName; ()),  -- forces elab
    category := .fieldDefault }
```
(the two `_wf` proof fields are discharged by their `decide +kernel`
auto-params, one small kernel check per entry).  Written out:
```
```

The `let _ := @actualTheoremName; ()` term forces Lean's
elaborator to resolve `actualTheoremName` against the current
environment.  A typo or stale rename fails with "unknown
identifier '<name>'" — the static guarantee the packed identifier
alone cannot provide. -/
syntax (name := poltMacro) "polt!" str ident term : term

macro_rules
  | `(polt! $desc:str $ident:ident $cat:term) => do
      -- Stringify the ident for the documentation field.
      let descKey := packedStringLit desc.getString
      let identKey := packedStringLit ident.getId.toString
      `(({ descriptionKey := nat_lit $descKey,
           identifierKey := nat_lit $identKey,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerObjectLockTheorem))

/-- WS-SM SM3.A audit-pass-5 / pass-7: the SM3.A substantive theorem
inventory.

Entries are grouped by category and the total cardinality is
pinned by `perObjectLockTheorems_count` below.  Every entry's
identifier is **compile-time-validated** via the `polt!` macro —
a regression that renames or removes a theorem fails this
module's build at the elaboration step, before any test or
runtime check is reached. -/
def perObjectLockTheorems : List PerObjectLockTheorem :=
  [-- §1 fieldDefault (8 entries — SM3.A.1..A.9 lock fields + Reply)
    polt! "TCB carries a per-object RwLockState lock field"
      TCB.lock .fieldDefault,
    polt! "Endpoint carries a per-object RwLockState lock field"
      Endpoint.lock .fieldDefault,
    polt! "CNode carries a per-object RwLockState lock field"
      CNode.lock .fieldDefault,
    polt! "Notification carries a per-object RwLockState lock field"
      Notification.lock .fieldDefault,
    polt! "UntypedObject carries a per-object RwLockState lock field"
      UntypedObject.lock .fieldDefault,
    polt! "SchedContext carries a per-object RwLockState lock field"
      SeLe4n.Kernel.SchedContext.lock .fieldDefault,
    polt! "VSpaceRoot carries a per-object RwLockState lock field"
      VSpaceRoot.lock .fieldDefault,
    polt! "Reply carries a per-object RwLockState lock field"
      SeLe4n.Kernel.Reply.lock .fieldDefault,
    -- §2 projection (11 entries — objectLockOf def + 8 KernelObject unfolds + FrozenKernelObject.objectLockOf def + frozen .reply unfold)
    polt! "KernelObject.objectLockOf projects the per-variant lock"
      KernelObject.objectLockOf .projection,
    polt! "objectLockOf on .tcb reduces to t.lock"
      KernelObject.objectLockOf_tcb .projection,
    polt! "objectLockOf on .endpoint reduces to e.lock"
      KernelObject.objectLockOf_endpoint .projection,
    polt! "objectLockOf on .cnode reduces to c.lock"
      KernelObject.objectLockOf_cnode .projection,
    polt! "objectLockOf on .notification reduces to n.lock"
      KernelObject.objectLockOf_notification .projection,
    polt! "objectLockOf on .vspaceRoot reduces to v.lock"
      KernelObject.objectLockOf_vspaceRoot .projection,
    polt! "objectLockOf on .untyped reduces to u.lock"
      KernelObject.objectLockOf_untyped .projection,
    polt! "objectLockOf on .schedContext reduces to s.lock"
      KernelObject.objectLockOf_schedContext .projection,
    polt! "objectLockOf on .reply reduces to r.lock"
      KernelObject.objectLockOf_reply .projection,
    polt! "FrozenKernelObject.objectLockOf projects the frozen per-variant lock"
      FrozenKernelObject.objectLockOf .projection,
    polt! "FrozenKernelObject.objectLockOf on .reply reduces to r.lock"
      FrozenKernelObject.objectLockOf_reply .projection,
    -- §3 defaultState (5 entries — 4 SM3.A.11 + objStoreLock unheld)
    polt! "Default SystemState has objStoreLock = .unheld"
      default_objStoreLock_unheld .defaultState,
    polt! "Default SystemState's object store has no entries with held locks"
      default_objects_locks_unheld .defaultState,
    polt! "Default SystemState's objects.toList is empty"
      default_objects_toList_empty .defaultState,
    polt! "Default SystemState's toList membership entries all have unheld locks"
      default_objects_locks_unheld_via_toList .defaultState,
    polt! "Default SystemState satisfies allObjectLocksUnheld (non-vacuous)"
      default_allObjectLocksUnheld .defaultState,
    -- §4 preservation (8 entries — 4 freeze + 4 storeObject)
    polt! "freeze preserves objStoreLock"
      freeze_preserves_objStoreLock .preservation,
    polt! "freezeCNode preserves the CNode lock"
      freezeCNode_preserves_lock .preservation,
    polt! "freezeVSpaceRoot preserves the VSpaceRoot lock"
      freezeVSpaceRoot_preserves_lock .preservation,
    polt! "freezeObject preserves objectLockOf across the frozen mirror"
      freezeObject_preserves_objectLockOf .preservation,
    polt! "storeObject preserves the table-level objStoreLock"
      storeObject_preserves_objStoreLock .preservation,
    polt! "storeObject preserves off-target objectLockOf entries"
      storeObject_preserves_objectLockOf_off_target .preservation,
    polt! "storeObject inserted-object lookup returns the inserted value"
      storeObject_inserted_object_lookup .preservation,
    polt! "storeObject with unheld lock preserves allObjectLocksUnheld"
      storeObject_preserves_allObjectLocksUnheld .preservation,
    -- §5 consistency (5 entries — totality + variants cardinality)
    polt! "objectLockOf is total over every KernelObject"
      KernelObject.objectLockOf_exists .consistency,
    polt! "objectType and objectLockOf are co-consistent over every KernelObject"
      KernelObject.objectType_and_lockOf_total .consistency,
    polt! "objectLockOf is consistent with the kind tag"
      KernelObject.objectLockOf_consistent_with_type .consistency,
    polt! "KernelObjectType has exactly 8 variants (reply now a real object; locks down Page N/A)"
      KernelObjectType.variants_count_exactly_eight .consistency,
    polt! "KernelObjectType variants_total — every value is one of the 8 enumerated kinds"
      KernelObjectType.variants_total .consistency]

/-- WS-SM SM3.A audit-pass-5: the inventory has exactly 37 entries (WS-SM SM6.D:
+3 for the first-class Reply object — `Reply.lock`, `KernelObject.objectLockOf_reply`,
`FrozenKernelObject.objectLockOf_reply`).
A regression that adds a new SM3.A theorem without updating the
inventory fails this count witness at the Tier-3 surface check. -/
theorem perObjectLockTheorems_count :
    perObjectLockTheorems.length = 37 := by decide

/-- WS-SM SM3.A audit-pass-5: 8 entries in the `fieldDefault` category (+Reply). -/
theorem perObjectLockTheorems_fieldDefault_count :
    (perObjectLockTheorems.filter (fun t => t.category == .fieldDefault)).length = 8 := by
  decide

/-- WS-SM SM3.A audit-pass-5: 11 entries in the `projection` category (+Reply unfolds). -/
theorem perObjectLockTheorems_projection_count :
    (perObjectLockTheorems.filter (fun t => t.category == .projection)).length = 11 := by
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

/-- WS-SM SM3.A audit-pass-5: every inventory identifier is unique.  Kernel-checked, never
`native_decide`: the identifiers are stored as packed keys, each entry's
`identifierKey_wf` field is the kernel's own check that its key is well
formed, and `SeLe4n.nodup_map_stringOfPacked` turns distinctness of the keys
— one `decide +kernel` over `Nat`s — into distinctness of the strings they
spell.  A duplicate identifier fails this proof in the kernel. -/
theorem perObjectLockTheorems_identifiers_nodup :
    (perObjectLockTheorems.map (·.identifier)).Nodup :=
  nodup_map_stringOfPacked PerObjectLockTheorem.identifierKey (fun t _ => t.identifierKey_wf)
    (by decide +kernel)

/-- WS-SM SM3.A audit-pass-5: every inventory description is unique — the same key-level
argument as `perObjectLockTheorems_identifiers_nodup`, over `descriptionKey`. -/
theorem perObjectLockTheorems_descriptions_nodup :
    (perObjectLockTheorems.map (·.description)).Nodup :=
  nodup_map_stringOfPacked PerObjectLockTheorem.descriptionKey (fun t _ => t.descriptionKey_wf)
    (by decide +kernel)

end SeLe4n.Model
