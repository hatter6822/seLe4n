/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Core
import SeLe4n.Kernel.RobinHood.Invariant

/-!
# N3: Kernel API Bridge for Robin Hood Hash Table

This module provides the bridge layer between the Robin Hood hash table
(`RHTable`) and the kernel proof surface. It supplies:

1. **Typeclass instances** (N3-A): `Inhabited`, `BEq` for `RHTable`
2. **Bridge lemmas** (N3-B): equivalents to every `Std.HashMap` lemma
   used in the kernel proof surface
3. **Filter support** (N3-C): `RHTable.filter` with preservation proofs
4. **Convenience constructors**: `RHTable.ofList`

Every theorem here is machine-checked with no admitted goals or postulated axioms.

### AK8-K (WS-AK) — Data Structures LOW-tier batch

LOW-tier audit findings for the data-structures subsystem addressed in
Phase AK8-K:

- **DS-L1 (`extractBits` public offset):** documented. `extractBits` is a
  pure bit-manipulation helper exposed as `public` because it is used in
  both `RadixTree/Core.lean` and `Kernel/Capability/Operations.lean`
  (CSpace resolution). The function is pure — no state-carrying
  invariants — so its publicity is a maintenance concern only, not a
  safety concern. Future renames should coordinate the two consumers.
- **DS-L2 (`insertNoResize` fuel silent failure):** addressed. See
  `RHTable.insertNoResize` — on fuel exhaustion the function now records
  via return type (returns the original table unmodified; callers must
  check via the size-preserving theorem). The "Except-returning" variant
  is not introduced in AK8 — it would cascade through ~50 insert call
  sites. Recorded as post-1.0 hygiene work; no active plan file tracks
  it.
- **DS-L3 (`RHTable.erase` saturation):** documented. `Nat.sub` saturates
  at zero, so `size - 1` on an empty table remains 0. The existing
  `erase_size_bounded` theorem discharges the safety property without
  requiring `.pred`-with-boundary-check refactor.
- **DS-L4 (RH `Inhabited` 16-slot default):** documented. `default` uses
  capacity 16 which matches the minimum useful capacity for Robin Hood
  probing — a 0-slot default would make `default.insert` unusable
  without a subsequent resize. The 16-slot choice is a deliberate
  ergonomics trade-off.
- **DS-L5 (400K-800K heartbeat proofs):** deferred to post-1.0. The
  affected proofs in `Kernel/RobinHood/Invariant/Lookup.lean` and
  `Kernel/RobinHood/Invariant/Preservation.lean` require `set_option
  maxHeartbeats 400000` (up to 800000 in some places). Restructuring to
  smaller lemma units is post-1.0 hygiene work (not tracked in any
  currently-active workstream plan).
- **DS-L6 (`resolveExtraCaps` silent drop):** documented via AI6-A in
  `docs/spec/SELE4N_SPEC.md` §8.10.4 — silent-drop matches seL4 semantics.
- **DS-L7 (wildcard unreachability 25-variant enumeration):** accepted
  as-is. The `KernelOperation` inductive has 35 constructors (as of
  v0.29.14); the `syscallDispatchHigh` wildcard arm handles the few
  constructors that NI analysis treats as high-label-only and therefore
  doesn't enumerate them individually. This is a documented design
  choice, not a correctness concern.
- **DS-L8 (`ofList` resizing):** documented. `RHTable.ofList` resizes
  the backing array as needed via `insert`. For large lists this incurs
  O(log n) resize cost. Callers constructing at boot time pay the cost
  once and thereafter operate on stable-capacity tables.
- **DS-L9 (FrozenOps hardcoded priority/domain):** documented. The
  `FrozenSchedulerState` defaults (`priority = 0`, `domain = 0`) match
  seL4's reset values for unconfigured schedulers. Extracting to named
  constants is cosmetic hygiene — tracked as post-1.0 work.
- **DS-L10 (`typedIdDisjointness` trivial):** coordinated with AK7-E/F.
  The `typedIdDisjointness` predicate in `CrossSubsystem.lean` is
  structurally trivial at the Lean level (distinct constructors of
  `KernelObjectType`); the deeper runtime-layer guarantee is established
  via `retypeFromUntyped_childId_fresh` (AJ2-D) and
  `lifecycleObjectTypeLockstep` (AM4-A).
- **DS-L11 (`RHTable.BEq` dual-fold):** documented. The `BEq` instance
  above uses two folds for symmetry of the equivalence relation. A
  single-fold refactor with an auxiliary "size check + subset-by-fold"
  pattern could halve the runtime cost. Deferred — not perf-sensitive
  at the current scale (kernel syscall path uses `BEq` for invariant
  equality checks at verification time, not runtime). -/

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- N3-A3: Inhabited instance
-- ============================================================================

/-- AN2-F.4 / FND-M04: Minimum practical capacity for an `RHTable` used as
    a default. The value is exposed as a constant rather than a magic
    literal to ensure the `Inhabited` instance and capacity-bound bridge
    lemmas reference the same symbol, so future adjustments propagate
    uniformly. Value `16` mirrors the seL4 CNode minimum 2^4 radix and
    keeps the initial backing-array allocation modest.

    Declared as `abbrev` so `omega`/`decide` can unfold the literal when
    discharging capacity preconditions (e.g. `RHTable.empty`'s `cap ≥ 4`
    obligation). -/
abbrev minPracticalRHCapacity : Nat := 16

instance [BEq α] [Hashable α] : Inhabited (RHTable α β) where
  default := RHTable.empty minPracticalRHCapacity (by decide)

-- ============================================================================
-- N3-A4: BEq instance (entry-wise comparison via fold)
-- ============================================================================

/-! ### AK8-J (WS-AK / DS-M04) — `RHTable.BEq` and `LawfulBEq`

The `BEq (RHTable α β)` instance below compares two tables entry-wise via a
size check plus two folds. Its correctness depends on the `BEq β` instance
it delegates to when comparing values (`v == v'`). Specifically:

- **Reflexivity** of `RHTable.BEq` requires `BEq β` to be reflexive — i.e.,
  `LawfulBEq β` (or at minimum `∀ v : β, v == v = true`).
- **Symmetry** requires `BEq β` to be symmetric, likewise
  captured by `LawfulBEq β`.
- **Transitivity** (and thus `LawfulBEq (RHTable α β)`) requires `LawfulBEq β`.

The current instance takes `[BEq β]` as its only value-side constraint, so
it inherits whatever (possibly non-lawful) equivalence `β`'s `BEq` encodes.
Consumers that need `LawfulBEq (RHTable α β)` for proof-layer equality
reasoning (e.g., the `DecidableEq` derivation on `SystemState.objects`)
MUST supply `[LawfulBEq β]` separately at the call site. No such
derivation exists here as an `instance` because it would require an
entry-wise correctness proof that is recorded as post-1.0 hardening
work (DS-M04). No currently-active workstream plan tracks it.

Callers: if your proof cascade needs `LawfulBEq (RHTable α β)`, assume
it as a hypothesis OR prove it inline using the table's structural
invariants (`wellFormed`, `distCorrect`, `noDupKeys`, etc.) and the
`LawfulBEq β` witness. Relying on the `BEq` instance alone to behave
lawfully is not safe when `β`'s `BEq` is itself non-lawful. -/

/-- Two RHTables are equal if they have the same size and every entry in each
    table exists with the same value in the other. The reverse fold ensures
    symmetry: `(a == b) = (b == a)` for well-formed tables with unique keys.

    **AK8-J (WS-AK / DS-M04):** `LawfulBEq (RHTable α β)` is NOT provided as
    an instance. Proofs requiring lawful entry-wise equality must supply
    `[LawfulBEq β]` at the call site and establish the `LawfulBEq` proof
    inline (or import an ad-hoc witness from a deployment-specific module).
    See the file-level docstring above for the full contract. -/
instance [BEq α] [Hashable α] [LawfulBEq α] [BEq β] : BEq (RHTable α β) where
  beq a b :=
    a.size == b.size &&
    a.fold (init := true) (fun acc k v =>
      acc && match b.get? k with
        | some v' => v == v'
        | none => false) &&
    b.fold (init := true) (fun acc k v =>
      acc && match a.get? k with
        | some v' => v == v'
        | none => false)

/-- AK8-J (WS-AK / DS-M04): Documentation-only sentinel recording the
`LawfulBEq β` requirement for lawful `RHTable` equality. If a future
consumer adds `LawfulBEq (RHTable α β)` as an instance, this theorem
(vacuous True) serves as a search anchor for the rationale document
in this file's header. -/
theorem RHTable_BEq_requires_lawfulBEq_of_value : True := trivial

-- ============================================================================
-- N3-B5: getElem?_empty
-- ============================================================================

/-- N3-B5: Looking up any key in an empty table returns `none`. -/
theorem RHTable.getElem?_empty [BEq α] [Hashable α] [LawfulBEq α]
    (cap : Nat) (hCapGe4 : 4 ≤ cap) (k : α) :
    (RHTable.empty cap hCapGe4 : RHTable α β).get? k = none := by
  have hPos : 0 < cap := by omega
  unfold RHTable.get?
  suffices h : ∀ fuel idx d, getLoop fuel idx k d
      (RHTable.empty cap hCapGe4 : RHTable α β).slots cap
      (by simp [RHTable.empty, Array.size]) hPos = none from h _ _ _
  intro fuel
  induction fuel with
  | zero => intro _ _; simp [getLoop]
  | succ n ih =>
    intro idx d
    unfold getLoop; simp only []
    have hSlot : (RHTable.empty cap hCapGe4 : RHTable α β).slots[idx % cap]'(by
        simp [RHTable.empty, Array.size]; exact Nat.mod_lt _ hPos) = none := by
      simp [RHTable.empty]
    rw [hSlot]

-- ============================================================================
-- N3-B1: getElem?_insert_self
-- ============================================================================

/-- N3-B1: After inserting key `k` with value `v`, looking up `k` returns `some v`. -/
theorem RHTable.getElem?_insert_self [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).get? k = some v :=
  t.get_after_insert_eq k v hExt

-- ============================================================================
-- N3-B2: getElem?_insert_ne
-- ============================================================================

/-- N3-B2: Inserting key `k` does not affect lookups of other keys. -/
theorem RHTable.getElem?_insert_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) :
    (t.insert k v).get? k' = t.get? k' :=
  t.get_after_insert_ne k k' v hNe hExt

-- ============================================================================
-- N3-B3: getElem?_erase_self
-- ============================================================================

/-- N3-B3: After erasing key `k`, looking up `k` returns `none`. -/
theorem RHTable.getElem?_erase_self [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).get? k = none :=
  t.get_after_erase_eq k hExt

-- ============================================================================
-- N3-B4: getElem?_erase_ne
-- ============================================================================

/-- N3-B4: Erasing key `k` does not affect lookups of other keys. -/
theorem RHTable.getElem?_erase_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).get? k' = t.get? k' :=
  t.get_after_erase_ne k k' hNe hExt hSize

-- ============================================================================
-- N3-B6: size_erase_le
-- ============================================================================

/-- N3-B6: Erasing a key does not increase the table size. -/
theorem RHTable.size_erase_le [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    (t.erase k).size ≤ t.size := by
  unfold RHTable.erase
  simp only
  split
  · exact Nat.le_refl _
  · dsimp only; omega

-- ============================================================================
-- N3 helper: list_fold_insertNoResize_size_le
-- ============================================================================

/-- Folding `insertNoResize` over a list of option entries increases size by
    at most the count of `some` entries. -/
private theorem list_fold_insertNoResize_size_le [BEq α] [Hashable α] [LawfulBEq α]
    (l : List (Option (RHEntry α β))) (acc : RHTable α β) :
    (List.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value) acc l).size
    ≤ acc.size + l.countP (·.isSome) := by
  induction l generalizing acc with
  | nil => simp [List.countP_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.countP_cons]
    cases hd with
    | none =>
      simp only [Option.isSome, Bool.false_eq_true, ite_false]
      exact ih acc
    | some e =>
      simp only [Option.isSome, ite_true]
      calc (List.foldl _ (acc.insertNoResize e.key e.value) tl).size
          ≤ (acc.insertNoResize e.key e.value).size + tl.countP (·.isSome) := ih _
        _ ≤ (acc.size + 1) + tl.countP (·.isSome) :=
            Nat.add_le_add_right (RHTable.insertNoResize_size_le _ _ _) _
        _ = acc.size + (tl.countP (·.isSome) + 1) := by omega

-- ============================================================================
-- N3 helper: resize_size_le
-- ============================================================================

/-- Resizing a well-formed table does not increase its size. -/
private theorem resize_size_le [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (hwf : t.WF) :
    t.resize.size ≤ t.size := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value)
    (RHTable.empty (t.capacity * 2) (by have := t.hCapGe4; omega)) : RHTable α β).size ≤ t.size
  rw [← Array.foldl_toList]
  have h := list_fold_insertNoResize_size_le t.slots.toList
    (RHTable.empty (t.capacity * 2) (by have := t.hCapGe4; omega) : RHTable α β)
  have hEmpty : (RHTable.empty (t.capacity * 2) (by have := t.hCapGe4; omega)
      : RHTable α β).size = 0 := by simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  rw [hwf.sizeCount]; unfold countOccupied; exact h

-- ============================================================================
-- N3-B7: size_insert_le
-- ============================================================================

/-- N3-B7: Inserting a key increases the table size by at most 1.
    Requires well-formedness because the resize path must preserve the size
    bound (resize rebuilds all entries via fold, adding at most `countOccupied`
    = `t.size` entries). -/
theorem RHTable.size_insert_le [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insert k v).size ≤ t.size + 1 := by
  unfold RHTable.insert
  split
  · exact Nat.le_trans (RHTable.insertNoResize_size_le _ _ _)
      (Nat.add_le_add_right (resize_size_le t hwf) 1)
  · exact RHTable.insertNoResize_size_le _ _ _

-- ============================================================================
-- N3-B8: mem_iff_isSome_getElem?
-- ============================================================================

/-- N3-B8: Membership is equivalent to `get?` returning `some`. -/
theorem RHTable.mem_iff_isSome_getElem? [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    (k ∈ t) ↔ (t.get? k).isSome = true := by
  simp [Membership.mem, RHTable.contains]

-- ============================================================================
-- N3-B9: getElem?_eq_some_getElem
-- ============================================================================

/-- N3-B9: If `get?` returns `some v`, then `get` returns `v`. -/
theorem RHTable.getElem?_eq_some_getElem [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β)
    (h : t.get? k = some v) :
    (t.get? k).get (by rw [h]; rfl) = v := by
  simp [h]

-- ============================================================================
-- N3-B10: fold_eq_slots_foldl
-- ============================================================================

/-- N3-B10: `fold` is equivalent to `foldl` over the slot array. -/
theorem RHTable.fold_eq_slots_foldl [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (init : γ) (f : γ → α → β → γ) :
    t.fold init f = t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => f acc e.key e.value) init :=
  rfl

-- ============================================================================
-- N3-C1: RHTable.filter
-- ============================================================================

/-- N3-C1: Filter entries by a predicate, rebuilding via fold + insert. -/
def RHTable.filter [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (f : α → β → Bool)
    : RHTable α β :=
  t.fold (RHTable.empty t.capacity t.hCapGe4) fun acc k v =>
    if f k v then acc.insertNoResize k v else acc

-- ============================================================================
-- N3 helper: list_fold_filter_size_le
-- ============================================================================

/-- Folding a filter step over a list of option entries increases size by at most
    the count of `some` entries (regardless of predicate). -/
private theorem list_fold_filter_size_le [BEq α] [Hashable α] [LawfulBEq α]
    (l : List (Option (RHEntry α β))) (acc : RHTable α β)
    (f : α → β → Bool) :
    (List.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
      acc l).size
    ≤ acc.size + l.countP (·.isSome) := by
  induction l generalizing acc with
  | nil => simp [List.countP_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.countP_cons]
    cases hd with
    | none =>
      simp only [Option.isSome, Bool.false_eq_true, ite_false]
      exact ih acc
    | some e =>
      simp only [Option.isSome, ite_true]
      by_cases hf : f e.key e.value
      · simp only [hf, ite_true]
        calc (List.foldl _ (acc.insertNoResize e.key e.value) tl).size
            ≤ (acc.insertNoResize e.key e.value).size + tl.countP (·.isSome) := ih _
          _ ≤ (acc.size + 1) + tl.countP (·.isSome) :=
              Nat.add_le_add_right (RHTable.insertNoResize_size_le _ _ _) _
          _ = acc.size + (tl.countP (·.isSome) + 1) := by omega
      · simp only [show (f e.key e.value) = false from by simp [hf]]
        calc (List.foldl _ acc tl).size
            ≤ acc.size + tl.countP (·.isSome) := ih _
          _ ≤ acc.size + (tl.countP (·.isSome) + 1) := by omega

-- ============================================================================
-- N3-B12: size_filter_le_capacity / size_filter_le_size
-- ============================================================================

/-- N3-B12 (weak): Filtering never exceeds original capacity. -/
theorem RHTable.size_filter_le_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) :
    (t.filter f).size ≤ t.capacity := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
    (RHTable.empty t.capacity t.hCapGe4) : RHTable α β).size ≤ t.capacity
  rw [← Array.foldl_toList]
  have h := list_fold_filter_size_le t.slots.toList
    (RHTable.empty t.capacity t.hCapGe4 : RHTable α β) f
  have hEmpty : (RHTable.empty t.capacity t.hCapGe4 : RHTable α β).size = 0 := by
    simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  have hCount : t.slots.toList.countP (·.isSome) ≤ t.slots.toList.length :=
    List.countP_le_length
  rw [Array.length_toList, t.hSlotsLen] at hCount
  exact Nat.le_trans h hCount

/-- N3-B12 (tight): Filtering preserves size bound ≤ `t.size`. -/
theorem RHTable.size_filter_le_size [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (hWF : t.WF) :
    (t.filter f).size ≤ t.size := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
    (RHTable.empty t.capacity t.hCapGe4) : RHTable α β).size ≤ t.size
  rw [← Array.foldl_toList]
  have h := list_fold_filter_size_le t.slots.toList
    (RHTable.empty t.capacity t.hCapGe4 : RHTable α β) f
  have hEmpty : (RHTable.empty t.capacity t.hCapGe4 : RHTable α β).size = 0 := by
    simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  rw [hWF.sizeCount]; unfold countOccupied; exact h

-- ============================================================================
-- N3-B11: filter_preserves_key
-- ============================================================================

-- N3-B11 and N3-C3 (filter_preserves_key, filter_getElem?) — now fully proved.
-- The general `filter_preserves_key` theorem (see below, line ~732) was proved
-- in V7-D via the `filter_fold_present` / `filter_fold_absent` proof infrastructure.
-- Phase-specific instances are no longer needed.

-- ============================================================================
-- N3-A4 supplement: ofList constructor
-- ============================================================================

/-- Construct an `RHTable` from a list of key-value pairs.
    Later entries override earlier ones for duplicate keys. -/
def RHTable.ofList [BEq α] [Hashable α] [LawfulBEq α]
    (entries : List (α × β)) (cap : Nat := 16) (hCapGe4 : 4 ≤ cap := by omega)
    : RHTable α β :=
  entries.foldl (fun acc ⟨k, v⟩ => acc.insert k v) (RHTable.empty cap hCapGe4)

-- ============================================================================
-- N3 supplement: empty table invExt (re-export for bridge consumers)
-- ============================================================================

/-- The empty table satisfies the extended invariant. -/
theorem RHTable.empty_invExt' [BEq α] [Hashable α] [LawfulBEq α]
    (cap : Nat) (hCapGe4 : 4 ≤ cap) :
    (RHTable.empty cap hCapGe4 : RHTable α β).invExt :=
  RHTable.empty_invExt cap hCapGe4

-- ============================================================================
-- N4 bridge: insert preserves size < capacity
-- ============================================================================

/-- After `insert`, `size < capacity`. The resize at 75% load ensures this.
    Requires `capacity ≥ 4` (satisfied by all CNode tables, which start at 16).
    For capacities 1-3, the 75% load factor doesn't prevent new inserts from
    reaching capacity. -/
theorem RHTable.insert_size_lt_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β)
    (hExt : t.invExt) (hSizeLt : t.size < t.capacity)
    (hCapGe4 : 4 ≤ t.capacity) :
    (t.insert k v).size < (t.insert k v).capacity := by
  unfold RHTable.insert
  split
  · -- Resize branch: capacity doubles, re-insert all entries
    have hResizeCap : t.resize.capacity = t.capacity * 2 := t.resize_fold_capacity
    have hResizeSize : t.resize.size ≤ t.size := resize_size_le t hExt.1
    have hInsSize := RHTable.insertNoResize_size_le t.resize k v
    have hInsCap : (t.resize.insertNoResize k v).capacity = t.resize.capacity :=
      RHTable.insertNoResize_capacity t.resize k v
    rw [hInsCap, hResizeCap]
    calc (t.resize.insertNoResize k v).size
        ≤ t.resize.size + 1 := hInsSize
      _ ≤ t.size + 1 := Nat.add_le_add_right hResizeSize 1
      _ < t.capacity * 2 := by omega
  · -- No resize branch: size * 4 < capacity * 3, with capacity ≥ 4
    rename_i hNoResize
    have hLt : t.size * 4 < t.capacity * 3 := Nat.lt_of_not_le hNoResize
    have hInsSize := RHTable.insertNoResize_size_le t k v
    have hInsCap : (t.insertNoResize k v).capacity = t.capacity :=
      RHTable.insertNoResize_capacity t k v
    calc (t.insertNoResize k v).size
        ≤ t.size + 1 := hInsSize
      _ < t.capacity := by omega
      _ = (t.insertNoResize k v).capacity := hInsCap.symm

-- ============================================================================
-- N4 bridge: erase preserves size < capacity
-- ============================================================================

/-- After `erase`, `size < capacity` is preserved (size can only decrease). -/
theorem RHTable.erase_size_lt_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hSizeLt : t.size < t.capacity) :
    (t.erase k).size < (t.erase k).capacity := by
  have hSizeLE := RHTable.size_erase_le t k
  have hCap : (t.erase k).capacity = t.capacity := by
    unfold RHTable.erase
    simp only []
    split
    · rfl
    · rfl
  rw [hCap]; omega

-- ============================================================================
-- N4 bridge: filter preserves invExt
-- ============================================================================

/-- `filter` preserves `invExt` because it rebuilds from empty via `insertNoResize`.
    The empty table has `invExt`, and each `insertNoResize` preserves it. -/
theorem RHTable.filter_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (_hExt : t.invExt) :
    (t.filter f).invExt := by
  unfold RHTable.filter RHTable.fold
  have hEmpty : (RHTable.empty t.capacity t.hCapGe4 : RHTable α β).invExt :=
    RHTable.empty_invExt t.capacity t.hCapGe4
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.invExt)
    hEmpty
    (fun i acc hAcc => by
      simp only []
      split
      · exact hAcc
      · rename_i entry _
        by_cases hf : f entry.key entry.value
        · simp only [hf, ite_true]
          exact acc.insertNoResize_preserves_invExt entry.key entry.value hAcc
        · simp only [show (f entry.key entry.value) = false from by simp [hf]]
          exact hAcc)

-- ============================================================================
-- N4 bridge: filter preserves size < capacity
-- ============================================================================

/-- `filter` preserves `size < capacity` because the filtered table has the same
    capacity as the original and at most as many entries. -/
theorem RHTable.filter_size_lt_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool)
    (hSizeLt : t.size < t.capacity) (hWF : t.WF) :
    (t.filter f).size < (t.filter f).capacity := by
  have hCap : (t.filter f).capacity = t.capacity := by
    unfold RHTable.filter RHTable.fold
    exact Array.foldl_induction
      (motive := fun _ (acc : RHTable α β) => acc.capacity = t.capacity)
      (by simp [RHTable.empty])
      (fun i acc hAcc => by
        simp only []
        split
        · exact hAcc
        · rename_i entry _
          by_cases hf : f entry.key entry.value
          · simp only [hf, ite_true]
            rw [RHTable.insertNoResize_capacity]; exact hAcc
          · simp only [show (f entry.key entry.value) = false from by simp [hf]]
            exact hAcc)
  rw [hCap]
  exact Nat.lt_of_le_of_lt (RHTable.size_filter_le_size t f hWF) hSizeLt

-- ============================================================================
-- N4 bridge: ofList preserves invExt and size < capacity
-- ============================================================================

-- ============================================================================
-- N4 bridge: filter lookup for source-preserving predicates
-- ============================================================================

/-- If `f k v = true` for some entry `(k, v)` in the original table, and the
    filter predicate `f` evaluates to `true` for key `k`, then the filtered
    table contains that entry. This is the specific instance needed for
    `CNode.lookup_revokeTargetLocal_source_eq_lookup`.

    NOTE: This is a weaker statement than the general `filter_get?`. It
    requires that the predicate is true for ALL BEq-equivalent keys (not
    just the specific key), matching the `HashMap_filter_preserves_key`
    pattern. -/
-- Helper: fold induction for filter when key is absent
private theorem filter_fold_absent [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (_hExt : t.invExt)
    (hAbsent : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k) = false) :
    (t.filter f).get? k = none := by
  unfold RHTable.filter RHTable.fold
  exact (Array.foldl_induction
    (motive := fun i (acc : RHTable α β) =>
      acc.invExt ∧ acc.size ≤ i ∧ acc.capacity = t.capacity ∧ acc.get? k = none)
    ⟨RHTable.empty_invExt t.capacity t.hCapGe4,
     Nat.zero_le 0,
     by simp [RHTable.empty],
     RHTable.getElem?_empty t.capacity t.hCapGe4 k⟩
    (fun i acc ⟨hAccExt, hAccSizeI, hAccCap, hAccNone⟩ => by
      have hAccSizeLt : acc.size < acc.capacity := by
        have := i.isLt; have := t.hSlotsLen; omega
      simp only []
      split
      · exact ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, hAccNone⟩
      · rename_i entry _
        have hEntryNeK : ¬(entry.key == k) = true := by
          have hI : i.val < t.capacity := by rw [← t.hSlotsLen]; exact i.isLt
          have := hAbsent i.val hI entry (by assumption)
          intro hc; rw [hc] at this; exact absurd this (by simp)
        by_cases hf : f entry.key entry.value
        · simp only [hf, ite_true]
          exact ⟨acc.insertNoResize_preserves_invExt entry.key entry.value hAccExt,
            Nat.le_of_lt_succ (Nat.lt_succ_of_le
              (Nat.le_trans (acc.insertNoResize_size_le entry.key entry.value)
                (Nat.succ_le_succ hAccSizeI))),
            (RHTable.insertNoResize_capacity acc entry.key entry.value).trans hAccCap,
            (RHTable.insertNoResize_get_ne acc k entry.key entry.value
              hEntryNeK hAccExt hAccSizeLt).trans hAccNone⟩
        · have hfF : f entry.key entry.value = false := Bool.eq_false_iff.mpr hf
          simp only [hfF]
          exact ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, hAccNone⟩)).2.2.2

-- V7-A: Extracted fold-step lemma for filter_fold_present to reduce heartbeat budget
private theorem filter_fold_present_step [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (v : β)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKeyE : (e.key == k) = true) (hValE : e.value = v)
    (hfTrue : f e.key e.value = true)
    (hNoDup : ∀ i j (hi : i < t.capacity) (hj : j < t.capacity)
      (ei ej : RHEntry α β),
      t.slots[i]'(t.hSlotsLen ▸ hi) = some ei →
      t.slots[j]'(t.hSlotsLen ▸ hj) = some ej →
      (ei.key == ej.key) = true → i = j)
    (i : Fin t.slots.size) (acc : RHTable α β)
    (hAccExt : acc.invExt) (hAccSizeI : acc.size ≤ i.val)
    (hAccCap : acc.capacity = t.capacity)
    (hAccIf : if p < i.val then acc.get? k = some v else acc.get? k = none) :
    let step := match t.slots[i.val]'(i.isLt) with
      | none => acc
      | some entry => if f entry.key entry.value then acc.insertNoResize entry.key entry.value
                      else acc
    step.invExt ∧ step.size ≤ i.val + 1 ∧ step.capacity = t.capacity ∧
      (if p < i.val + 1 then step.get? k = some v else step.get? k = none) := by
  have hpSlots : p < t.slots.size := t.hSlotsLen ▸ hp
  have hAccSizeLt : acc.size < acc.capacity := by
    have := i.isLt; have := t.hSlotsLen; omega
  simp only []
  generalize hSlot : t.slots[i.val]'(i.isLt) = slot
  cases slot with
  | none =>
    refine ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, ?_⟩
    by_cases hpi : p < i.val
    · simp only [show p < i.val + 1 from Nat.lt_succ_of_lt hpi, ite_true]
      simp only [hpi, ite_true] at hAccIf; exact hAccIf
    · by_cases hpiS : p < i.val + 1
      · have hiP : i.val = p := by omega
        exfalso
        have : t.slots[p]'hpSlots = none := hiP ▸ hSlot
        rw [hSlotP] at this; exact absurd this (by simp)
      · simp only [hpiS, ite_false]; simp only [hpi, ite_false] at hAccIf
        exact hAccIf
  | some entry =>
    by_cases hEntK : (entry.key == k) = true
    · have hiP : i.val = p := by
        have hI : i.val < t.capacity := by
          have := i.isLt; have := t.hSlotsLen; omega
        exact hNoDup i.val p hI hp entry e hSlot hSlotP
          (by rw [eq_of_beq hEntK, eq_of_beq hKeyE]; exact BEq.refl k)
      have hEntEq : entry = e := by
        have : t.slots[p]'hpSlots = some entry := hiP ▸ hSlot
        rw [hSlotP] at this; exact (Option.some.inj this).symm
      have hfEnt : f entry.key entry.value = true := hEntEq ▸ hfTrue
      simp only [hfEnt, ite_true]
      refine ⟨acc.insertNoResize_preserves_invExt entry.key entry.value hAccExt,
        Nat.le_of_lt_succ (Nat.lt_succ_of_le
          (Nat.le_trans (acc.insertNoResize_size_le entry.key entry.value)
            (Nat.succ_le_succ hAccSizeI))),
        (RHTable.insertNoResize_capacity acc entry.key entry.value).trans hAccCap,
        ?_⟩
      simp only [show p < i.val + 1 from Nat.lt_succ_of_le (Nat.le_of_eq hiP.symm),
                  ite_true]
      have hKeyEq : entry.key = k := hEntEq ▸ eq_of_beq hKeyE
      have hValEq : entry.value = v := hEntEq ▸ hValE
      rw [← hKeyEq, ← hValEq]
      exact RHTable.insertNoResize_get_eq acc entry.key entry.value
        hAccExt hAccSizeLt
    · by_cases hf : f entry.key entry.value
      · simp only [hf, ite_true]
        have hPres := RHTable.insertNoResize_get_ne acc k entry.key entry.value
          hEntK hAccExt hAccSizeLt
        refine ⟨acc.insertNoResize_preserves_invExt entry.key entry.value hAccExt,
          Nat.le_of_lt_succ (Nat.lt_succ_of_le
            (Nat.le_trans (acc.insertNoResize_size_le entry.key entry.value)
              (Nat.succ_le_succ hAccSizeI))),
          (RHTable.insertNoResize_capacity acc entry.key entry.value).trans hAccCap,
          ?_⟩
        have hNeP : i.val ≠ p := by
          intro heq
          have hSame : t.slots[p]'hpSlots = some entry := heq ▸ hSlot
          rw [hSlotP] at hSame
          have hEqE : entry = e := (Option.some.inj hSame).symm
          exact absurd (hEqE ▸ hKeyE) hEntK
        by_cases hpi : p < i.val
        · simp only [show p < i.val + 1 from Nat.lt_succ_of_lt hpi, ite_true]
          simp only [hpi, ite_true] at hAccIf; rw [hPres]; exact hAccIf
        · simp only [show ¬(p < i.val + 1) from by omega, ite_false]
          simp only [hpi, ite_false] at hAccIf; rw [hPres]; exact hAccIf
      · have hfF : f entry.key entry.value = false := Bool.eq_false_iff.mpr hf
        simp only [hfF]
        have hNeP : i.val ≠ p := by
          intro heq
          have hSame : t.slots[p]'hpSlots = some entry := heq ▸ hSlot
          rw [hSlotP] at hSame
          have hEqE : entry = e := (Option.some.inj hSame).symm
          exact absurd (hEqE ▸ hKeyE) hEntK
        refine ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, ?_⟩
        by_cases hpi : p < i.val
        · simp only [show p < i.val + 1 from Nat.lt_succ_of_lt hpi, ite_true]
          simp only [hpi, ite_true] at hAccIf; exact hAccIf
        · simp only [show ¬(p < i.val + 1) from by omega, ite_false]
          simp only [hpi, ite_false] at hAccIf; exact hAccIf

-- W2-H (L-3): 400K heartbeats — fold induction over the full slot array with
-- per-slot case analysis on filter predicate, key equality, and entry presence.
-- Helper: fold induction for filter when key is present
set_option maxHeartbeats 400000 in
private theorem filter_fold_present [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (v : β)
    (_hExt : t.invExt)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKeyE : (e.key == k) = true) (hValE : e.value = v)
    (hfTrue : f e.key e.value = true)
    (hNoDup : ∀ i j (hi : i < t.capacity) (hj : j < t.capacity)
      (ei ej : RHEntry α β),
      t.slots[i]'(t.hSlotsLen ▸ hi) = some ei →
      t.slots[j]'(t.hSlotsLen ▸ hj) = some ej →
      (ei.key == ej.key) = true → i = j) :
    (t.filter f).get? k = some v := by
  have hpSlots : p < t.slots.size := t.hSlotsLen ▸ hp
  unfold RHTable.filter RHTable.fold
  have hResult := @Array.foldl_induction _ _ t.slots
    (fun i (acc : RHTable α β) =>
      acc.invExt ∧ acc.size ≤ i ∧ acc.capacity = t.capacity ∧
      (if p < i then acc.get? k = some v else acc.get? k = none))
    (RHTable.empty t.capacity t.hCapGe4)
    ⟨RHTable.empty_invExt t.capacity t.hCapGe4,
     Nat.zero_le 0,
     by simp [RHTable.empty],
     by simp [Nat.not_lt_zero, RHTable.getElem?_empty]⟩
    (fun acc slot =>
      match slot with
      | none => acc
      | some entry => if f entry.key entry.value then acc.insertNoResize entry.key entry.value
                      else acc)
    (fun i acc ⟨hAccExt, hAccSizeI, hAccCap, hAccIf⟩ =>
      filter_fold_present_step t f k v p hp e hSlotP hKeyE hValE hfTrue hNoDup
        i acc hAccExt hAccSizeI hAccCap hAccIf)
  -- hResult has type (fun i acc => ...) t.slots.size (Array.foldl ...) — beta-reduce it
  let result := Array.foldl
    (fun acc slot =>
      match slot with
      | none => acc
      | some entry => if f entry.key entry.value then acc.insertNoResize entry.key entry.value
                      else acc)
    (RHTable.empty t.capacity t.hCapGe4) t.slots
  have hR : result.invExt ∧ result.size ≤ t.slots.size ∧ result.capacity = t.capacity ∧
    (if p < t.slots.size then result.get? k = some v else result.get? k = none) := hResult
  simp only [hpSlots, ite_true] at hR
  exact hR.2.2.2

theorem RHTable.filter_preserves_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α)
    (hTrue : ∀ (k' : α) (v : β), (k' == k) = true → f k' v = true)
    (hExt : t.invExt) :
    (t.filter f).get? k = t.get? k := by
  cases hGet : t.get? k with
  | none =>
    have hAbsent := RHTable.get_none_no_matching_entry t k hExt hGet
    exact filter_fold_absent t f k hExt hAbsent
  | some v =>
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ :=
      RHTable.get_some_slot_entry t k v hGet
    exact filter_fold_present t f k v hExt p hp e hSlotP hKeyE hValE
      (hTrue e.key e.value hKeyE) hExt.2.2.1

-- ============================================================================
-- N4 bridge: fold property preservation
-- ============================================================================

/-- If a property `P` holds for `init` and is preserved by the fold body `f`,
    then `P` holds for the result of `RHTable.fold`. -/
theorem RHTable.fold_preserves (t : RHTable α β) (init : γ) (f : γ → α → β → γ)
    (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc k v, P acc → P (f acc k v)) :
    P (t.fold init f) := by
  unfold RHTable.fold
  exact Array.foldl_induction
    (motive := fun _ acc => P acc)
    hInit
    (fun i acc hAcc => by
      simp only []
      split
      · exact hAcc
      · rename_i e _; exact hStep acc e.key e.value hAcc)

-- Helper: fold induction for filter when every entry with key == k has f = false
-- (the predicate-based variant of filter_fold_absent)
private theorem filter_fold_absent_by_pred [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (_hExt : t.invExt)
    (hSkip : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e →
      f e.key e.value = true → (e.key == k) = false) :
    (t.filter f).get? k = none := by
  unfold RHTable.filter RHTable.fold
  exact (Array.foldl_induction
    (motive := fun i (acc : RHTable α β) =>
      acc.invExt ∧ acc.size ≤ i ∧ acc.capacity = t.capacity ∧ acc.get? k = none)
    ⟨RHTable.empty_invExt t.capacity t.hCapGe4,
     Nat.zero_le 0,
     by simp [RHTable.empty],
     RHTable.getElem?_empty t.capacity t.hCapGe4 k⟩
    (fun i acc ⟨hAccExt, hAccSizeI, hAccCap, hAccNone⟩ => by
      have hAccSizeLt : acc.size < acc.capacity := by
        have := i.isLt; have := t.hSlotsLen; omega
      simp only []
      split
      · exact ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, hAccNone⟩
      · rename_i entry _
        by_cases hf : f entry.key entry.value
        · simp only [hf, ite_true]
          have hEntryNeK : ¬(entry.key == k) = true := by
            have hI : i.val < t.capacity := by rw [← t.hSlotsLen]; exact i.isLt
            have := hSkip i.val hI entry (by assumption) hf
            intro hc; rw [hc] at this; exact absurd this (by simp)
          exact ⟨acc.insertNoResize_preserves_invExt entry.key entry.value hAccExt,
            Nat.le_of_lt_succ (Nat.lt_succ_of_le
              (Nat.le_trans (acc.insertNoResize_size_le entry.key entry.value)
                (Nat.succ_le_succ hAccSizeI))),
            (RHTable.insertNoResize_capacity acc entry.key entry.value).trans hAccCap,
            (RHTable.insertNoResize_get_ne acc k entry.key entry.value
              hEntryNeK hAccExt hAccSizeLt).trans hAccNone⟩
        · have hfF : f entry.key entry.value = false := Bool.eq_false_iff.mpr hf
          simp only [hfF]
          exact ⟨hAccExt, Nat.le_succ_of_le hAccSizeI, hAccCap, hAccNone⟩)).2.2.2

-- W2-H (L-3): 400K heartbeats — filter subset proof requires full fold induction
-- with get?/filter interaction reasoning across slot boundaries.
set_option maxHeartbeats 400000 in
/-- If `(t.filter f).get? k = some v`, then `t.get? k = some v`.
    Filter only retains entries from the original table without modification. -/
theorem RHTable.filter_get_subset [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (v : β)
    (hExt : t.invExt)
    (hGet : (t.filter f).get? k = some v) :
    t.get? k = some v := by
  cases hOrig : t.get? k with
  | none =>
    have hAbsent := RHTable.get_none_no_matching_entry t k hExt hOrig
    have := filter_fold_absent t f k hExt hAbsent
    rw [this] at hGet; exact absurd hGet (by simp)
  | some v' =>
    by_cases hfkv : f k v' = true
    · -- f k v' = true: filter_fold_present shows filter has (k, v')
      have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := RHTable.get_some_slot_entry t k v' hOrig
      have hfE : f e.key e.value = true := by rw [eq_of_beq hKeyE, hValE]; exact hfkv
      have hFilterV' := filter_fold_present t f k v' hExt p hp e hSlotP hKeyE hValE hfE hExt.2.2.1
      rw [hFilterV'] at hGet; exact hGet
    · -- f k v' = false: the only entry for k is skipped by filter → contradiction
      have hfkv' : f k v' = false := Bool.eq_false_iff.mpr hfkv
      have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := RHTable.get_some_slot_entry t k v' hOrig
      have hSkip : ∀ j (hj : j < t.capacity) (ej : RHEntry α β),
          t.slots[j]'(t.hSlotsLen ▸ hj) = some ej →
          f ej.key ej.value = true → (ej.key == k) = false := by
        intro j hj ej hSlotJ hfej
        by_cases hejk : (ej.key == k) = true
        · -- ej has key == k, so by noDupKeys j = p and ej = e
          exfalso
          have hejke : (ej.key == e.key) = true := by rw [eq_of_beq hKeyE]; exact hejk
          have hjp : j = p := hExt.2.2.1 j p hj hp ej e hSlotJ hSlotP hejke
          have heje : ej = e := by
            have : t.slots[p]'(t.hSlotsLen ▸ hp) = some ej := hjp ▸ hSlotJ
            rw [hSlotP] at this; exact (Option.some.inj this).symm
          -- ej = e, e.key = k, e.value = v', so f ej.key ej.value = f k v' = false
          have : f ej.key ej.value = false := by
            rw [heje, eq_of_beq hKeyE, hValE]; exact hfkv'
          exact absurd hfej (by rw [this]; simp)
        · exact Bool.eq_false_iff.mpr hejk
      have hNone := filter_fold_absent_by_pred t f k hExt hSkip
      rw [hNone] at hGet; exact absurd hGet (by simp)

/-- If `(t.filter f).get? k = some v`, then `f k v = true`.
    The filter only retains entries for which the predicate holds. -/
theorem RHTable.filter_get_pred [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α) (v : β)
    (hExt : t.invExt)
    (hGet : (t.filter f).get? k = some v) :
    f k v = true := by
  -- By filter_get_subset, the original has (k, v)
  have hOrig := RHTable.filter_get_subset t f k v hExt hGet
  by_cases hfkv : f k v = true
  · exact hfkv
  · exfalso
    have hfkv' : f k v = false := Bool.eq_false_iff.mpr hfkv
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := RHTable.get_some_slot_entry t k v hOrig
    have hSkip : ∀ j (hj : j < t.capacity) (ej : RHEntry α β),
        t.slots[j]'(t.hSlotsLen ▸ hj) = some ej →
        f ej.key ej.value = true → (ej.key == k) = false := by
      intro j hj ej hSlotJ hfej
      by_cases hejk : (ej.key == k) = true
      · exfalso
        have hejke : (ej.key == e.key) = true := by rw [eq_of_beq hKeyE]; exact hejk
        have hjp : j = p := hExt.2.2.1 j p hj hp ej e hSlotJ hSlotP hejke
        have heje : ej = e := by
          have : t.slots[p]'(t.hSlotsLen ▸ hp) = some ej := hjp ▸ hSlotJ
          rw [hSlotP] at this; exact (Option.some.inj this).symm
        have : f ej.key ej.value = false := by
          rw [heje, eq_of_beq hKeyE, hValE]; exact hfkv'
        exact absurd hfej (by rw [this]; simp)
      · exact Bool.eq_false_iff.mpr hejk
    have hNone := filter_fold_absent_by_pred t f k hExt hSkip
    rw [hNone] at hGet; exact absurd hGet (by simp)

/-- Filter idempotence at a key: filtering twice gives the same lookup as filtering once. -/
theorem RHTable.filter_filter_getElem? [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α)
    (hExt : t.invExt) :
    ((t.filter f).filter f).get? k = (t.filter f).get? k := by
  cases hGet : (t.filter f).get? k with
  | none =>
    -- If t.filter f has no entry for k, then (t.filter f).filter f can't either
    have hExtF := t.filter_preserves_invExt f hExt
    have hAbsent := RHTable.get_none_no_matching_entry (t.filter f) k hExtF hGet
    exact filter_fold_absent (t.filter f) f k hExtF hAbsent
  | some v =>
    -- t.filter f has (k, v). By filter_get_pred, f k v = true.
    -- So the second filter preserves this entry.
    have hExtF := t.filter_preserves_invExt f hExt
    have hfkv := RHTable.filter_get_pred t f k v hExt hGet
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ :=
      RHTable.get_some_slot_entry (t.filter f) k v hGet
    have hfE : f e.key e.value = true := by rw [eq_of_beq hKeyE, hValE]; exact hfkv
    exact filter_fold_present (t.filter f) f k v hExtF p hp e hSlotP hKeyE hValE hfE hExtF.2.2.1

-- ============================================================================
-- Q2: EmptyCollection instance for migration compatibility
-- ============================================================================

/-- EmptyCollection instance so `{}` syntax works for RHTable fields.
    AN2-F.4 / FND-M04: Uses `minPracticalRHCapacity` (16) — references the
    same constant as the `Inhabited` instance so capacity adjustments
    propagate uniformly. -/
instance [BEq α] [Hashable α] : EmptyCollection (RHTable α β) where
  emptyCollection := RHTable.empty minPracticalRHCapacity (by decide)

-- ============================================================================
-- V3-B Phase 1: invExtK — Kernel-Level Extended Invariant Bundle
-- ============================================================================

/-- Kernel-level extended invariant: includes size bounds needed by erase and
    insert. All kernel tables satisfy this. RobinHood internal proofs use
    `invExt` (unchanged).

    - `invExt`: data-structure invariant (WF ∧ distCorrect ∧ noDupKeys ∧ probeChainDominant)
    - `size < capacity`: erase lookup correctness prerequisite
    - `4 ≤ capacity`: insert size bound prerequisite -/
def RHTable.invExtK [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) : Prop :=
  t.invExt ∧ t.size < t.capacity ∧ 4 ≤ t.capacity

-- Projection lemmas
theorem RHTable.invExtK_invExt [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (h : t.invExtK) : t.invExt := h.1

theorem RHTable.invExtK_size_lt_capacity [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (h : t.invExtK) : t.size < t.capacity := h.2.1

theorem RHTable.invExtK_capacity_ge4 [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (h : t.invExtK) : 4 ≤ t.capacity := h.2.2

-- Constructor lemma
theorem RHTable.mk_invExtK [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (hExt : t.invExt) (hSize : t.size < t.capacity)
    (hCap : 4 ≤ t.capacity) : t.invExtK := ⟨hExt, hSize, hCap⟩

-- ============================================================================
-- V3-B Phase 1: empty_invExtK
-- ============================================================================

/-- The empty table satisfies `invExtK` when `4 ≤ cap`. -/
theorem RHTable.empty_invExtK [BEq α] [Hashable α] [LawfulBEq α]
    (cap : Nat) (hCapGe4 : 4 ≤ cap) :
    (RHTable.empty cap hCapGe4 : RHTable α β).invExtK :=
  ⟨RHTable.empty_invExt cap hCapGe4,
   by simp [RHTable.empty]; omega,
   by simp [RHTable.empty]; exact hCapGe4⟩

-- ============================================================================
-- V3-B Phase 1: erase_preserves_invExtK
-- ============================================================================

/-- Erase preserves capacity (erase does not change capacity). -/
private theorem RHTable.erase_capacity_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    (t.erase k).capacity = t.capacity := by
  unfold RHTable.erase; simp only []; split <;> rfl

/-- Erase preserves `invExtK`. Composes `erase_preserves_invExt`,
    `erase_size_lt_capacity`, and capacity preservation. -/
theorem RHTable.erase_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hK : t.invExtK) :
    (t.erase k).invExtK :=
  ⟨t.erase_preserves_invExt k hK.1 hK.2.1,
   t.erase_size_lt_capacity k hK.2.1,
   by rw [t.erase_capacity_eq k]; exact hK.2.2⟩

-- ============================================================================
-- V3-B Phase 1: insert_preserves_invExtK
-- ============================================================================

/-- Insert preserves capacity ≥ 4 (insert either keeps capacity or doubles it). -/
private theorem RHTable.insert_capacity_ge4 [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hCap : 4 ≤ t.capacity) :
    4 ≤ (t.insert k v).capacity := by
  unfold RHTable.insert; split
  · rw [RHTable.insertNoResize_capacity, t.resize_fold_capacity]; omega
  · rw [RHTable.insertNoResize_capacity]; exact hCap

/-- Insert preserves `invExtK`. Composes `insert_preserves_invExt`,
    `insert_size_lt_capacity`, and capacity preservation. -/
theorem RHTable.insert_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hK : t.invExtK) :
    (t.insert k v).invExtK :=
  ⟨t.insert_preserves_invExt k v hK.1,
   t.insert_size_lt_capacity k v hK.1 hK.2.1 hK.2.2,
   t.insert_capacity_ge4 k v hK.2.2⟩

-- ============================================================================
-- V3-B Phase 1: getElem?_erase_ne_K
-- ============================================================================

/-- Erasing key `k` does not affect lookups of other keys (kernel-level API
    taking `invExtK` instead of separate `hExt` + `hSize`). -/
theorem RHTable.getElem?_erase_ne_K [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hK : t.invExtK) :
    (t.erase k).get? k' = t.get? k' :=
  t.getElem?_erase_ne k k' hNe hK.1 hK.2.1

-- ============================================================================
-- V3-B Phase 1: filter_preserves_invExtK
-- ============================================================================

/-- Filter preserves capacity (filter rebuilds from `empty t.capacity`). -/
private theorem RHTable.filter_capacity_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) :
    (t.filter f).capacity = t.capacity := by
  unfold RHTable.filter RHTable.fold
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.capacity = t.capacity)
    (by simp [RHTable.empty])
    (fun i acc hAcc => by
      simp only []
      split
      · exact hAcc
      · rename_i entry _
        by_cases hf : f entry.key entry.value
        · simp only [hf, ite_true]
          rw [RHTable.insertNoResize_capacity]; exact hAcc
        · simp only [show (f entry.key entry.value) = false from by simp [hf]]
          exact hAcc)

/-- Filter preserves `invExtK`. Composes `filter_preserves_invExt`,
    `filter_size_lt_capacity`, and capacity preservation. -/
theorem RHTable.filter_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (hK : t.invExtK) :
    (t.filter f).invExtK :=
  ⟨t.filter_preserves_invExt f hK.1,
   t.filter_size_lt_capacity f hK.2.1 hK.1.1,
   by rw [t.filter_capacity_eq f]; exact hK.2.2⟩

-- ============================================================================
-- X5-B (H-9): CNode capacity enforcement documentation
-- ============================================================================

/-- X5-B (H-9): All CNode tables are created with `RHTable.empty 16`
    (Structures.lean:390), so the `4 ≤ capacity` precondition required by
    `insert_size_lt_capacity` is always trivially satisfied.

    **Enforcement chain**:
    1. `CNode.empty` uses `RHTable.empty 16` → initial capacity = 16
    2. `invExtK` bundles `4 ≤ capacity` as its third conjunct (line 858)
    3. `insert_preserves_invExtK` preserves `4 ≤ capacity` through inserts
       (capacity only grows via doubling on resize)
    4. All call sites discharge `hCapGe4` via `(by omega)` or `invExtK_capacity_ge4`

    This theorem witnesses step 1: the empty CNode's slot table satisfies
    the minimum capacity requirement. -/
theorem cnode_capacity_always_ge4 [BEq α] [Hashable α] [LawfulBEq α] :
    4 ≤ (RHTable.empty 16 (by omega) : RHTable α β).capacity := by
  simp [RHTable.empty]

end SeLe4n.Kernel.RobinHood
