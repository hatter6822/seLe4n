-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.RobinHood

/-! # `UniqueSlotMap V` — structural smart-constructor wrapper around `RHTable Slot V`

WS-RC R4.A (DEEP-MODEL-01): wrapper structure carrying the `invExtK`
extended invariant (no-duplicate-keys + `size < capacity` + `4 ≤ capacity`)
at construction time. Every smart constructor in this namespace
discharges the obligation via the corresponding
`RHTable._preserves_invExtK` lemma, so the structural property cannot be
regressed by future refactors without breaking elaboration.

The wrapper is **parametric over the value type** `V` so it can live in
`SeLe4n.Prelude`-import-only territory and be referenced from
`SeLe4n.Model.Object.Types` (which defines `Capability`) without an
import cycle. The kernel-facing specialisation is
`UniqueSlotMap Capability` — used as the type of `CNode.slots`.

## Operational vs. proof-side API

* Operational sites (kernel transitions) use `empty`, `insert`, `erase`,
  `filter`, and `ofListWF` (boot/initial state). The smart constructors
  discharge `invExtK` inline.
* Proof sites (preservation theorems) destructure `.table` to recover the
  underlying `RHTable` for pattern-matching tactics, or rely on the
  `CoeHead` coercion for dot-notation forwarding.
-/

namespace SeLe4n

open SeLe4n.Kernel.RobinHood

/-- WS-RC R4.A: wrapper around `RHTable Slot V` carrying `invExtK`
    invariantly. -/
structure UniqueSlotMap (V : Type) where
  table : RHTable SeLe4n.Slot V
  hWF   : table.invExtK

namespace UniqueSlotMap

variable {V : Type}

/-! ## Smart constructors -/

/-- The empty slot map at capacity 16 (the default kernel CNode capacity).
    `invExtK` is discharged via `RHTable.empty_invExtK`. -/
@[inline] def empty : UniqueSlotMap V :=
  ⟨RHTable.empty 16, RHTable.empty_invExtK 16 (by omega)⟩

/-- Insert preserves `invExtK` via `RHTable.insert_preserves_invExtK`. -/
@[inline] def insert (u : UniqueSlotMap V) (s : SeLe4n.Slot) (c : V) :
    UniqueSlotMap V :=
  ⟨u.table.insert s c, u.table.insert_preserves_invExtK s c u.hWF⟩

/-- Erase preserves `invExtK` via `RHTable.erase_preserves_invExtK`. -/
@[inline] def erase (u : UniqueSlotMap V) (s : SeLe4n.Slot) : UniqueSlotMap V :=
  ⟨u.table.erase s, u.table.erase_preserves_invExtK s u.hWF⟩

/-- Filter preserves `invExtK` via `RHTable.filter_preserves_invExtK`. -/
@[inline] def filter (u : UniqueSlotMap V)
    (f : SeLe4n.Slot → V → Bool) : UniqueSlotMap V :=
  ⟨u.table.filter f, u.table.filter_preserves_invExtK f u.hWF⟩

/-- Build a `UniqueSlotMap` from a list of (slot, value) pairs by folding
    `insert`. Duplicates in the input list are resolved last-wins
    (matching the underlying `RHTable.insert` semantics). `invExtK` is
    preserved at every fold step via `insert_preserves_invExtK`. -/
@[inline] def ofListWF (xs : List (SeLe4n.Slot × V)) : UniqueSlotMap V :=
  xs.foldl (fun acc kv => acc.insert kv.1 kv.2) empty

/-! ## Read-only accessors

These exist as explicit `@[inline]` wrappers so dot-notation lookup finds
them in the `UniqueSlotMap` namespace before falling back through `CoeHead`
to the underlying `RHTable` namespace. Keeps elaboration fast on the
hot read-only paths. -/

@[inline] def get? (u : UniqueSlotMap V) (s : SeLe4n.Slot) : Option V :=
  u.table.get? s

@[inline] def size (u : UniqueSlotMap V) : Nat := u.table.size

@[inline] def capacity (u : UniqueSlotMap V) : Nat := u.table.capacity

@[inline] def fold {β : Type} (u : UniqueSlotMap V) (init : β)
    (f : β → SeLe4n.Slot → V → β) : β :=
  u.table.fold init f

@[inline] def toList (u : UniqueSlotMap V) :
    List (SeLe4n.Slot × V) := u.table.toList

@[inline] def contains (u : UniqueSlotMap V) (s : SeLe4n.Slot) : Bool :=
  (u.get? s).isSome

/-! ## Instances -/

instance : CoeHead (UniqueSlotMap V) (RHTable SeLe4n.Slot V) where
  coe := UniqueSlotMap.table

instance [Repr V] : Repr (UniqueSlotMap V) where
  reprPrec u n := reprPrec u.table n

instance : Inhabited (UniqueSlotMap V) := ⟨empty⟩

/-- `cn.slots[s]?` notation: Lean resolves this via `GetElem?` (the `?`
    variant returning `Option`). The total-access `[s]` variant requires an
    `Inhabited V` witness for a default fallback; callers should prefer
    `[s]?` (the `Option`-returning form) which is total without Inhabited. -/
instance [Inhabited V] : GetElem? (UniqueSlotMap V) SeLe4n.Slot V (fun _ _ => True) where
  getElem  u s _ := (u.table.get? s).getD default
  getElem? u s   := u.table.get? s

/-! ## Forwarding `@[simp]` lemmas -/

@[simp] theorem table_empty : (empty : UniqueSlotMap V).table = RHTable.empty 16 := rfl

@[simp] theorem table_insert (u : UniqueSlotMap V) (s : SeLe4n.Slot) (c : V) :
    (u.insert s c).table = u.table.insert s c := rfl

@[simp] theorem table_erase (u : UniqueSlotMap V) (s : SeLe4n.Slot) :
    (u.erase s).table = u.table.erase s := rfl

@[simp] theorem table_filter (u : UniqueSlotMap V)
    (f : SeLe4n.Slot → V → Bool) :
    (u.filter f).table = u.table.filter f := rfl

/-! ## Witness theorems for the WS-RC R4.A discharge index -/

/-- WS-RC R4.A / DEEP-MODEL-01: every `UniqueSlotMap` has unique keys
    structurally; the witness theorem codifies the discharge-index closure. -/
theorem keys_unique (u : UniqueSlotMap V) : u.table.invExtK := u.hWF

end UniqueSlotMap
end SeLe4n

namespace SeLe4n.Kernel

theorem uniqueSlotMap_module_ready : True := trivial
-- Cross-reference: docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md §8.3 (Track A)

end SeLe4n.Kernel
