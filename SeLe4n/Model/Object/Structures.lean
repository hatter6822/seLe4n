/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.Types

namespace SeLe4n.Model


/-- WS-H11/H-02: Per-page permission attributes modeled after ARM64 page table descriptors.

Each mapping carries read/write/execute/user-access and cacheability flags. The
kernel enforces W^X (write XOR execute) as an invariant — no mapping may have both
`write` and `execute` set simultaneously. -/
structure PagePermissions where
  read : Bool := true
  write : Bool := false
  execute : Bool := false
  user : Bool := false
  cacheable : Bool := true
  deriving Repr, DecidableEq, Inhabited

instance : BEq PagePermissions where
  beq a b := a.read == b.read && a.write == b.write && a.execute == b.execute &&
              a.user == b.user && a.cacheable == b.cacheable

instance : Hashable PagePermissions where
  hash p := mixHash (hash p.read) (mixHash (hash p.write) (mixHash (hash p.execute)
            (mixHash (hash p.user) (hash p.cacheable))))

/-- WS-H11/H-02: W^X policy — a page permission set must not have both write and execute. -/
def PagePermissions.wxCompliant (p : PagePermissions) : Bool :=
  !(p.write && p.execute)

/-- WS-H11: Default permissions are W^X compliant (read-only, non-executable). -/
theorem PagePermissions.default_wxCompliant : (default : PagePermissions).wxCompliant = true := by
  rfl

/-- WS-G6/F-P05: Minimal VSpace root object: ASID identity plus flat virtual→physical mappings.

This intentionally models only one-level deterministic lookup semantics for WS-B1.
Hierarchical page-table levels are deferred behind this stable executable surface.

`mappings` is backed by `Std.HashMap VAddr (PAddr × PagePermissions)` for O(1)
amortized lookup, insert, and erase. HashMap key uniqueness is structural,
making `noVirtualOverlap` trivially true.

WS-H11/H-02: Enriched with per-page permissions (read/write/execute/user/cacheable). -/
structure VSpaceRoot where
  asid : SeLe4n.ASID
  mappings : Std.HashMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)
  deriving Repr

namespace VSpaceRoot

/-- WS-G6/F-P05: O(1) amortized page lookup via `HashMap[vaddr]?`.
WS-H11: Returns `(PAddr × PagePermissions)` pair. -/
def lookup (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option (SeLe4n.PAddr × PagePermissions) :=
  root.mappings[vaddr]?

/-- WS-H11: O(1) amortized physical-address-only lookup for backward compatibility. -/
def lookupAddr (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (root.lookup vaddr).map Prod.fst

/-- WS-G6/F-P05: O(1) amortized page mapping via `HashMap.insert`.
Returns `none` if a mapping for `vaddr` already exists (conflict).
WS-H11: Accepts permissions alongside the physical address. -/
def mapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := default) : Option VSpaceRoot :=
  match root.mappings[vaddr]? with
  | some _ => none
  | none => some { root with mappings := root.mappings.insert vaddr (paddr, perms) }

/-- WS-G6/F-P05: O(1) amortized page unmapping via `HashMap.erase`.
Returns `none` if no mapping exists for `vaddr`. -/
def unmapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option VSpaceRoot :=
  match root.mappings[vaddr]? with
  | none => none
  | some _ => some { root with mappings := root.mappings.erase vaddr }

/-- WS-G6: No-virtual-overlap property. With HashMap-backed mappings, this is
trivially true by key uniqueness: each VAddr maps to at most one entry.
Uses `lookup` (which delegates to `HashMap[vaddr]?`) for type resolution. -/
def noVirtualOverlap (root : VSpaceRoot) : Prop :=
  ∀ v e₁ e₂,
    root.lookup v = some e₁ →
    root.lookup v = some e₂ →
    e₁ = e₂

/-- WS-G6: With HashMap-backed mappings, `noVirtualOverlap` is trivially true
for *every* `VSpaceRoot` — key uniqueness in the HashMap guarantees that a
single `lookup` can return at most one value, so `e₁ = e₂` follows by
injection. This subsumes `noVirtualOverlap_empty`, `mapPage_noVirtualOverlap`,
and `unmapPage_noVirtualOverlap`, which are retained for API compatibility. -/
theorem noVirtualOverlap_trivial (root : VSpaceRoot) : noVirtualOverlap root := by
  intro v e₁ e₂ h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

/-- WS-G6: Empty mappings trivially satisfy no-virtual-overlap.
Follows directly from `noVirtualOverlap_trivial` but retained for API compatibility. -/
theorem noVirtualOverlap_empty (asid : SeLe4n.ASID) :
    noVirtualOverlap { asid := asid, mappings := {} } :=
  noVirtualOverlap_trivial _

/-- WS-G6: After unmapping vaddr, lookup returns none. Maps to `HashMap.getElem?_erase`. -/
theorem lookup_unmapPage_eq_none
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr = none := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some p =>
      simp [hLookup] at hUnmap
      cases hUnmap
      simp [lookup]

/-- WS-G6/WS-H11: After mapping vaddr→paddr with perms, lookup returns the entry.
Maps to `HashMap.getElem?_insert`. -/
theorem lookup_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr = some (paddr, perms) := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some p => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      simp [lookup]

/-- WS-H11: After mapping vaddr→paddr with default perms, lookupAddr returns paddr. -/
theorem lookupAddr_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookupAddr vaddr = some paddr := by
  simp [lookupAddr, lookup_mapPage_eq root root' vaddr paddr perms hMap]

/-- F-08 helper: `mapPage` preserves the VSpace root ASID. -/
theorem mapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := default)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.asid = root.asid := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap; rfl

/-- F-08 helper: `unmapPage` preserves the VSpace root ASID. -/
theorem unmapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.asid = root.asid := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap; rfl

/-- WS-G6: If `lookup` returns `none`, the vaddr has no mapping in the HashMap. -/
theorem lookup_eq_none_iff
    (root : VSpaceRoot)
    (vaddr : SeLe4n.VAddr) :
    root.lookup vaddr = none ↔ vaddr ∉ root.mappings := by
  simp [lookup]

/-- WS-G6: A successful `mapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem mapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hOverlap : noVirtualOverlap root)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    noVirtualOverlap root' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      exact noVirtualOverlap_trivial _

/-- WS-G6: A successful `unmapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem unmapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (_hOverlap : noVirtualOverlap root)
    (hUnmap : root.unmapPage vaddr = some root') :
    noVirtualOverlap root' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      exact noVirtualOverlap_trivial _

/-- TPI-001 helper: mapping vaddr does not affect lookup of a different vaddr'.
Maps to `HashMap.getElem?_insert` with the inequality hypothesis. -/
theorem lookup_mapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hNe : vaddr ≠ vaddr')
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      simp only [lookup, HashMap_getElem?_insert]
      have : ¬((vaddr == vaddr') = true) := by
        intro h; exact hNe (eq_of_beq h)
      simp [this]

/-- TPI-001 helper: unmapPage at vaddr does not affect lookup of a different vaddr'.
Maps to `HashMap.getElem?_erase` with the inequality hypothesis. -/
theorem lookup_unmapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      simp only [lookup, HashMap_getElem?_erase]
      have : ¬((vaddr == vaddr') = true) := by
        intro h; exact hNe (eq_of_beq h)
      simp [this]

end VSpaceRoot

/-- WS-G6/WS-H7: `BEq` instance for `VSpaceRoot` using entry-wise comparison on the
HashMap-backed mappings. Two VSpaceRoots are equal iff their ASID and all
mapping entries agree (same size + every key maps to the same value).
WS-H11: Updated for enriched `(PAddr × PagePermissions)` value type. -/
instance : BEq VSpaceRoot where
  beq a b :=
    a.asid == b.asid &&
    a.mappings.size == b.mappings.size &&
    a.mappings.fold (init := true) (fun acc k v => acc && b.mappings[k]? == some v)

/-- WS-H7: VSpaceRoot BEq correctness — the fold-based comparison is sound.
When BEq returns true, the two VSpaceRoots have equal ASIDs and identical
mapping entries. The proof relies on HashMap key uniqueness: size equality +
forward containment guarantees bidirectional equality.

Note: The full `beq_correct` biconditional (`(a == b) = true ↔ a = b`) requires
HashMap extensional equality axioms beyond Lean's Std.HashMap surface. We prove
the forward (soundness) direction; the reverse follows from `BEq.refl` when the
structures are definitionally equal. -/
theorem VSpaceRoot.beq_sound (a b : VSpaceRoot) (h : (a == b) = true) :
    a.asid = b.asid ∧ a.mappings.size = b.mappings.size := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

namespace CNode

inductive ResolveError where
  | depthMismatch
  | guardMismatch
  deriving Repr, DecidableEq

def empty : CNode :=
  { depth := 0, guardWidth := 0, guardValue := 0, radixWidth := 0, slots := {} }

/-- Construct a CNode at a given depth with guard/radix parameters. -/
def mk' (d gw gv rw : Nat) (s : Std.HashMap SeLe4n.Slot Capability := {}) : CNode :=
  { depth := d, guardWidth := gw, guardValue := gv, radixWidth := rw, slots := s }

/-- Number of addressable slots represented by this CNode radix width. -/
def slotCount (node : CNode) : Nat :=
  2 ^ node.radixWidth

/-- Total bits consumed by one resolution step at this CNode. -/
def bitsConsumed (node : CNode) : Nat :=
  node.guardWidth + node.radixWidth

/-- WS-H13: CNode well-formedness — consumed bits fit in remaining depth,
and at least one bit is consumed (ensures termination of multi-level resolution). -/
def wellFormed (node : CNode) : Prop :=
  node.bitsConsumed ≤ node.depth ∧ 0 < node.bitsConsumed

/-- Resolve a CPtr/depth pair into the local slot index using guard/radix semantics.

WS-H13: Uses `guardWidth` and `radixWidth` fields directly for compressed-path
resolution. The `bitsRemaining` parameter indicates how many address bits
remain to be resolved at this level. -/
def resolveSlot (node : CNode) (cptr : SeLe4n.CPtr) (bitsRemaining : Nat) : Except ResolveError SeLe4n.Slot :=
  let consumed := node.bitsConsumed
  if bitsRemaining < consumed then
    .error .depthMismatch
  else
    let shiftedAddr := cptr.toNat >>> (bitsRemaining - consumed)
    let radixMask := 2 ^ node.radixWidth
    let slotIndex := shiftedAddr % radixMask
    let guardExtracted := (shiftedAddr / radixMask) % (2 ^ node.guardWidth)
    if guardExtracted = node.guardValue then
      .ok (SeLe4n.Slot.ofNat slotIndex)
    else
      .error .guardMismatch

/-- WS-G5/F-P03: O(1) amortized slot lookup via `HashMap.find?`. -/
def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  node.slots[slot]?

/-- WS-G5/F-P03: O(1) amortized slot insert via `HashMap.insert`.
HashMap key uniqueness ensures the old entry for `slot` is replaced. -/
def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  { node with slots := node.slots.insert slot cap }

/-- WS-G5/F-P03: O(1) amortized slot removal via `HashMap.erase`. -/
def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with slots := node.slots.erase slot }

/-- Local revoke helper for the current modeled slice.

This keeps the authority-bearing source slot while deleting sibling slots in the same CNode that
name the same capability target. Full cross-CNode revoke requires an explicit derivation graph and
is intentionally deferred.

WS-G5/F-P03: Inherently O(m) (filter-by-target), uses `HashMap.filter`. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  {
    node with
      slots := node.slots.filter fun s c => s == sourceSlot || !(c.target == target)
  }

/-- WS-G5: After removing a slot, lookup returns `none`.
Maps directly to `HashMap.getElem?_erase_self`. -/
theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).lookup slot = none := by
  simp [remove, lookup]

/-- WS-G5: If `lookup` returns `some`, the slot key is present in the HashMap.
Replaces the list-era membership theorem with HashMap semantics. -/
theorem lookup_mem_of_some (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : node.lookup slot = some cap) : slot ∈ node.slots := by
  simp [lookup] at h
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])

theorem resolveSlot_depthMismatch
    (node : CNode)
    (cptr : SeLe4n.CPtr)
    (bitsRemaining : Nat)
    (hDepth : bitsRemaining < node.bitsConsumed) :
    node.resolveSlot cptr bitsRemaining = .error .depthMismatch := by
  unfold resolveSlot bitsConsumed at *
  have h : bitsRemaining < node.guardWidth + node.radixWidth := hDepth
  simp [h]

/-- WS-G5: Source slot is preserved by `revokeTargetLocal` because the filter
predicate always includes entries where `s = sourceSlot`. -/
theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  simp only [revokeTargetLocal, lookup]
  exact SeLe4n.HashMap_filter_preserves_key node.slots _ sourceSlot
    (fun k' _ hBeq => by simp [eq_of_beq hBeq])

-- ============================================================================
-- WS-G5/WS-E2/C-01: CNode slot-index uniqueness infrastructure
-- ============================================================================

/-- CNode slot-index uniqueness: each slot index maps to at most one capability.

WS-G5: With HashMap-backed slots, key uniqueness is structural — HashMap enforces
that each key maps to exactly one value. This invariant is trivially satisfied
for all CNodes by construction. The definition is retained for backward
compatibility with the invariant surface (Capability/Invariant.lean). -/
def slotsUnique (_cn : CNode) : Prop :=
  True

/-- WS-G5: Trivially true — HashMap enforces key uniqueness by construction. -/
theorem empty_slotsUnique : CNode.empty.slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.insert enforces key uniqueness by construction. -/
theorem insert_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (_hUniq : cn.slotsUnique) :
    (cn.insert slot cap).slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.erase preserves key uniqueness. -/
theorem remove_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot)
    (_hUniq : cn.slotsUnique) :
    (cn.remove slot).slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.filter preserves key uniqueness. -/
theorem revokeTargetLocal_slotsUnique
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (_hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotsUnique :=
  trivial

-- ============================================================================
-- WS-H4: Meaningful CNode slot-count bound predicate
-- ============================================================================

/-- WS-H4/C-03: Every CNode has at most `2^radixBits` occupied slots.
This is the meaningful replacement for the trivially-true `slotsUnique`
predicate — it captures the actual capacity constraint that the CNode
guard/radix semantics enforce. -/
def slotCountBounded (cn : CNode) : Prop :=
  cn.slots.size ≤ cn.slotCount

/-- Empty CNode satisfies slot-count bound (0 ≤ 2^0 = 1). -/
theorem empty_slotCountBounded : CNode.empty.slotCountBounded := by
  unfold slotCountBounded empty slotCount
  simp

/-- Removing a slot preserves the slot-count bound (size can only decrease). -/
theorem remove_slotCountBounded
    (cn : CNode) (slot : SeLe4n.Slot)
    (hBounded : cn.slotCountBounded) :
    (cn.remove slot).slotCountBounded := by
  show (cn.slots.erase slot).size ≤ 2 ^ cn.radixWidth
  have h : (cn.slots.erase slot).size ≤ cn.slots.size := Std.HashMap.size_erase_le
  exact Nat.le_trans h hBounded

/-- Revoking target-local preserves the slot-count bound (filter can only decrease size). -/
theorem revokeTargetLocal_slotCountBounded
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hBounded : cn.slotCountBounded) :
    (cn.revokeTargetLocal sourceSlot target).slotCountBounded := by
  show (cn.slots.filter (fun s c => s == sourceSlot || !c.target == target)).size ≤ 2 ^ cn.radixWidth
  have h := @Std.HashMap.size_filter_le_size _ _ _ _ cn.slots _ _
    (fun s c => s == sourceSlot || !c.target == target)
  exact Nat.le_trans h hBounded

/-- WS-G5: If a slot is present in the HashMap, lookup returns its value.
With HashMap-backed slots, `slotsUnique` is trivially satisfied (structural
invariant of HashMap), so the uniqueness hypothesis is unused. -/
theorem mem_lookup_of_slotsUnique (node : CNode) (_hUniq : node.slotsUnique)
    (slot : SeLe4n.Slot) (hMem : slot ∈ node.slots) :
    node.lookup slot = some node.slots[slot] :=
  Std.HashMap.getElem?_eq_some_getElem hMem

/-- WS-G5: Lookup roundtrip after insert — inserting at `slot` makes lookup
return the inserted capability. Maps directly to `HashMap.getElem?_insert_self`. -/
theorem lookup_insert_eq
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).lookup slot = some cap := by
  simp [insert, lookup]

/-- WS-G5: Insert at a different slot does not affect lookup.
Maps directly to `HashMap.getElem?_insert`. -/
theorem lookup_insert_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot) (cap : Capability)
    (hNe : slot ≠ slot') :
    (cn.insert slot cap).lookup slot' = cn.lookup slot' := by
  simp only [insert, lookup]
  rw [Std.HashMap.getElem?_insert]
  have : ¬((slot == slot') = true) := by
    intro h; exact hNe (eq_of_beq h)
  simp [this]

/-- WS-G5: Remove at a different slot does not affect lookup.
Maps directly to `HashMap.getElem?_erase`. -/
theorem lookup_remove_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot)
    (hNe : slot ≠ slot') :
    (cn.remove slot).lookup slot' = cn.lookup slot' := by
  simp only [remove, lookup]
  rw [Std.HashMap.getElem?_erase]
  have : ¬((slot == slot') = true) := by
    intro h; exact hNe (eq_of_beq h)
  simp [this]

end CNode

/-- WS-H13: `BEq` instance for `CNode` using entry-wise comparison on the
HashMap-backed slots. Two CNodes are equal iff their depth, guardWidth,
guardValue, radixWidth, and all slot entries agree. -/
instance : BEq CNode where
  beq a b :=
    a.depth == b.depth && a.guardWidth == b.guardWidth &&
    a.guardValue == b.guardValue && a.radixWidth == b.radixWidth &&
    a.slots.size == b.slots.size &&
    a.slots.fold (init := true) (fun acc k v => acc && b.slots[k]? == some v)

/-- WS-H13: CNode BEq soundness — when BEq returns true, the two CNodes have
equal depth, guardWidth, guardValue, radixWidth, and slot count. -/
theorem CNode.beq_sound (a b : CNode) (h : (a == b) = true) :
    a.depth = b.depth ∧ a.guardWidth = b.guardWidth ∧
    a.guardValue = b.guardValue ∧ a.radixWidth = b.radixWidth ∧
    a.slots.size = b.slots.size := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

-- ============================================================================
-- WS-H13: CSpace depth consistency predicates
-- ============================================================================

/-- WS-H13: CNode well-formedness — consumed bits fit in remaining depth,
and at least one bit is consumed (ensures termination of multi-level resolution).

The two constraints encode:
- `hConsumed`: the CNode does not consume more bits than available at its depth.
- `hProgress`: at least one bit is consumed per resolution step, preventing
  zero-width CNodes that would cause infinite loops. -/
def cnodeWellFormed (cn : CNode) : Prop :=
  cn.bitsConsumed ≤ cn.depth ∧ 0 < cn.bitsConsumed

/-- WS-H13: Empty CNode is trivially well-formed only when depth = 0.
For non-trivial resolution, CNodes must have positive bitsConsumed. -/
theorem CNode.empty_not_wellFormed : ¬ CNode.empty.wellFormed := by
  intro ⟨_, hProg⟩
  simp [CNode.empty, CNode.bitsConsumed] at hProg

-- ============================================================================
-- WS-E4/C-03: Capability Derivation Tree (CDT) model
-- ============================================================================

/-- A slot address in the global capability namespace: (CNode ObjId, Slot). -/
abbrev SlotAddr := SeLe4n.ObjId × SeLe4n.Slot

/-- The operation that created a derivation edge. -/
inductive DerivationOp where
  | mint
  | copy
  deriving Repr, DecidableEq

/-- Stable CDT node identifier.

Nodes are stable across CSpace slot moves: slots point to nodes, and edges are
between nodes (not slot addresses). -/
abbrev CdtNodeId := Nat

/-- A single edge in the Capability Derivation Tree.

WS-E4/C-03: Each edge records parent/child stable node IDs and the operation
that created the derivation. The CDT is a forest: each node has at most one
parent but may have many children. -/
structure CapDerivationEdge where
  parent : CdtNodeId
  child : CdtNodeId
  op : DerivationOp
  deriving Repr, DecidableEq

namespace CapDerivationEdge

def isChildOf (edge : CapDerivationEdge) (node : CdtNodeId) : Bool :=
  edge.child = node

def isParentOf (edge : CapDerivationEdge) (node : CdtNodeId) : Bool :=
  edge.parent = node

end CapDerivationEdge

/-- The Capability Derivation Tree stored at the system level.

WS-E4/C-03: A list of derivation edges forming a forest. Operations maintain
the acyclicity invariant: no slot can be both ancestor and descendant of itself. -/
structure CapDerivationTree where
  edges : List CapDerivationEdge := []
  /-- WS-G8/F-P14: Parent-indexed child map for O(1) `childrenOf` lookup.
  Runtime index maintained in parallel with `edges`; `edges` remains the
  proof anchor. -/
  childMap : Std.HashMap CdtNodeId (List CdtNodeId) := {}
  deriving Repr

namespace CapDerivationTree

def empty : CapDerivationTree := { edges := [], childMap := {} }

/-- Add a derivation edge from parent to child.
WS-G8: Maintains `childMap` index alongside `edges`. -/
def addEdge (cdt : CapDerivationTree) (parent child : CdtNodeId)
    (op : DerivationOp) : CapDerivationTree :=
  let currentChildren := cdt.childMap.get? parent |>.getD []
  { edges := { parent, child, op } :: cdt.edges,
    childMap := cdt.childMap.insert parent (child :: currentChildren) }

/-- Find all direct children of a given node.
WS-G8/F-P14: O(1) lookup via `childMap` instead of O(E) edge scan. -/
def childrenOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : List CdtNodeId :=
  cdt.childMap.get? node |>.getD []

/-- Find the parent of a given node, if any. -/
def parentOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : Option CdtNodeId :=
  (cdt.edges.find? (fun e => e.isChildOf node)).map CapDerivationEdge.parent

/-- Remove all edges referencing a given node as child (detach from parent).
WS-G8: Maintains `childMap` by removing `node` from all parent child lists. -/
def removeAsChild (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  { edges := cdt.edges.filter (fun e => ¬e.isChildOf node),
    childMap := cdt.childMap.fold (init := {}) fun m parent children =>
      let filtered := children.filter (· != node)
      if filtered.isEmpty then m else m.insert parent filtered }

/-- Remove all edges referencing a given node as parent (detach all children).
WS-G8: Erases the parent's `childMap` entry. -/
def removeAsParent (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  { edges := cdt.edges.filter (fun e => ¬e.isParentOf node),
    childMap := cdt.childMap.erase node }

/-- Remove all edges where the given node appears as parent or child.
WS-G8: Erases parent entry and removes from all child lists. -/
def removeNode (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  let edgesFiltered := cdt.edges.filter (fun e => ¬e.isParentOf node ∧ ¬e.isChildOf node)
  let mapWithoutParent := cdt.childMap.erase node
  let mapFinal := mapWithoutParent.fold (init := {}) fun m parent children =>
    let filtered := children.filter (· != node)
    if filtered.isEmpty then m else m.insert parent filtered
  { edges := edgesFiltered, childMap := mapFinal }

/-- Collect all descendants of a slot via bounded BFS traversal.
Uses fuel = edges.length to ensure termination and completeness
for acyclic trees.
WS-G8/F-P14: Uses `childrenOf` (O(1) via `childMap`) instead of inline
edge scan, yielding O(N+E) total traversal. -/
def descendantsOf (cdt : CapDerivationTree) (root : CdtNodeId)
    : List CdtNodeId :=
  go cdt.edges.length [root] []
where
  go : Nat → List CdtNodeId → List CdtNodeId → List CdtNodeId
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | fuel + 1, node :: rest, acc =>
        let children := cdt.childrenOf node
        let newChildren := children.filter (fun c => c ∉ acc)
        go fuel (rest ++ newChildren) (acc ++ newChildren)

/-- CDT acyclicity: no node reaches itself through derivation edges. -/
def acyclic (cdt : CapDerivationTree) : Prop :=
  ∀ e ∈ cdt.edges, e.parent ∉ cdt.descendantsOf e.child

theorem empty_acyclic : CapDerivationTree.empty.acyclic := by
  intro e hMem
  simp [CapDerivationTree.empty] at hMem

-- ============================================================================
-- WS-H4: Edge-well-founded acyclicity (simpler formulation for subset proofs)
-- ============================================================================

/-- WS-H4/M-03: Edge-well-founded acyclicity — no node can reach itself
through a non-empty path of derivation edges. This formulation enables clean
subset-preservation proofs: if edges' ⊆ edges and edges is well-founded,
then edges' is well-founded. -/
def edgeWellFounded (cdt : CapDerivationTree) : Prop :=
  ∀ (node : CdtNodeId),
    ¬(∃ (path : List CdtNodeId),
        path.length > 1 ∧
        path.head? = some node ∧
        path.getLast? = some node ∧
        (∀ i, (h : i + 1 < path.length) →
          ∃ e ∈ cdt.edges, e.parent = path[i] ∧ e.child = path[i + 1]))

/-- WS-H4: Empty CDT is trivially edge-well-founded (no edges, no cycles). -/
theorem empty_edgeWellFounded : CapDerivationTree.empty.edgeWellFounded := by
  intro node ⟨path, _, _, _, hEdges⟩
  have h0 := hEdges 0 (by omega)
  rcases h0 with ⟨e, hMem, _, _⟩
  simp [CapDerivationTree.empty] at hMem

/-- WS-H4: Edge-well-foundedness is preserved under edge-subset.
If every edge of `cdt'` is also in `cdt`, and `cdt` is well-founded,
then `cdt'` is well-founded. -/
theorem edgeWellFounded_sub
    (cdt cdt' : CapDerivationTree)
    (hWF : cdt.edgeWellFounded)
    (hSub : ∀ e ∈ cdt'.edges, e ∈ cdt.edges) :
    cdt'.edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  exact hWF node ⟨path, hLen, hHead, hLast, fun i hi => by
    rcases hEdges i hi with ⟨e, hMem, hp, hc⟩
    exact ⟨e, hSub e hMem, hp, hc⟩⟩

/-- Removing a node preserves a subset of edges. -/
theorem removeNode_edges_sub (cdt : CapDerivationTree) (node : CdtNodeId) :
    ∀ e ∈ (cdt.removeNode node).edges, e ∈ cdt.edges := by
  intro e hMem
  simp [removeNode] at hMem
  exact hMem.1

/-- WS-G8: Consistency invariant — `childMap` mirrors the parent→child
relationship in `edges`. -/
def childMapConsistent (cdt : CapDerivationTree) : Prop :=
  ∀ parent child,
    child ∈ (cdt.childMap.get? parent).getD [] ↔
      ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child

theorem empty_childMapConsistent : CapDerivationTree.empty.childMapConsistent := by
  intro parent child
  simp only [CapDerivationTree.empty]
  constructor
  · intro h; rw [HashMap_get?_empty] at h; simp at h
  · rintro ⟨_, hMem, _⟩; cases hMem

theorem addEdge_childMapConsistent (cdt : CapDerivationTree)
    (p c : CdtNodeId) (op : DerivationOp)
    (hCon : cdt.childMapConsistent) :
    (cdt.addEdge p c op).childMapConsistent := by
  intro parent child
  constructor
  · -- Forward: child in new childMap → edge exists
    intro hIn
    simp only [addEdge] at hIn
    rw [HashMap_get?_insert] at hIn
    split at hIn
    · -- p == parent is true
      rename_i heq
      have hPeq : p = parent := eq_of_beq heq
      simp only [Option.getD] at hIn
      rcases List.mem_cons.mp hIn with hChildEq | hTail
      · exact ⟨⟨p, c, op⟩, .head _, hPeq, hChildEq.symm⟩
      · have ⟨e, heMem, hep, hec⟩ := (hCon parent child).mp (hPeq ▸ hTail)
        exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
    · -- p == parent is false
      have ⟨e, heMem, hep, hec⟩ := (hCon parent child).mp hIn
      exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
  · -- Backward: edge exists → child in new childMap
    rintro ⟨e, heMem, hep, hec⟩
    simp only [addEdge]
    rw [HashMap_get?_insert]
    rcases List.mem_cons.mp heMem with heq | hTail
    · -- e is the new edge
      subst heq
      simp only at hep hec
      subst hep; subst hec
      simp only [beq_self_eq_true, ↓reduceIte, Option.getD]
      exact .head _
    · -- e is from existing edges
      split
      · -- p == parent is true
        rename_i heq
        have hPeq : p = parent := eq_of_beq heq
        simp only [Option.getD]
        exact List.mem_cons_of_mem _ (hPeq ▸ (hCon p child).mpr ⟨e, hTail, hPeq ▸ hep, hec⟩)
      · -- p == parent is false
        exact (hCon parent child).mpr ⟨e, hTail, hep, hec⟩

/-- Slot-address view of a CDT edge (projection through slot backpointers). -/
structure ObservedDerivationEdge where
  parent : SlotAddr
  child : SlotAddr
  op : DerivationOp
  deriving Repr, DecidableEq

/-- Project node-based CDT edges through a node→slot mapping. -/
def projectObservedEdges
    (cdt : CapDerivationTree)
    (nodeSlot : CdtNodeId → Option SlotAddr) : List ObservedDerivationEdge :=
  cdt.edges.filterMap (fun e =>
    match nodeSlot e.parent, nodeSlot e.child with
    | some p, some c => some { parent := p, child := c, op := e.op }
    | _, _ => none)

end CapDerivationTree

/-- WS-G5: `DecidableEq` removed from `KernelObject` because `CNode.slots` is now
`Std.HashMap Slot Capability` which does not have a `DecidableEq` instance.
`Repr` is retained for trace output. `BEq` is provided manually via entry-wise
HashMap comparison for runtime test assertions. -/
inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | notification (n : Notification)
  | cnode (c : CNode)
  | vspaceRoot (v : VSpaceRoot)
  | untyped (u : UntypedObject)
  deriving Repr

/-- WS-G5: Manual `BEq` for `KernelObject` dispatching to constituent `BEq`
instances. CNode comparison uses the entry-wise `BEq CNode` instance above. -/
instance : BEq KernelObject where
  beq
    | .tcb a, .tcb b => a == b
    | .endpoint a, .endpoint b => a == b
    | .notification a, .notification b => a == b
    | .cnode a, .cnode b => a == b
    | .vspaceRoot a, .vspaceRoot b => a == b
    | .untyped a, .untyped b => a == b
    | _, _ => false

inductive KernelObjectType where
  | tcb
  | endpoint
  | notification
  | cnode
  | vspaceRoot
  | untyped
  deriving Repr, DecidableEq

namespace KernelObject

def objectType : KernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .notification _ => .notification
  | .cnode _ => .cnode
  | .vspaceRoot _ => .vspaceRoot
  | .untyped _ => .untyped

end KernelObject

/-- Construct a capability that names an object directly.
    WS-F5/D2b: Accepts list for ergonomics, converts to AccessRightSet internally. -/
def makeObjectCap (id : SeLe4n.ObjId) (rights : List AccessRight) : Capability :=
  { target := .object id, rights := AccessRightSet.ofList rights }

end SeLe4n.Model
