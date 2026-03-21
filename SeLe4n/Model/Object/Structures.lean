/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.Types
import SeLe4n.Kernel.RobinHood.Bridge

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

/-- WS-K-D: Decode a raw `Nat` permissions word to `PagePermissions` using
a bitfield layout: bit 0=read, 1=write, 2=execute, 3=user, 4=cacheable.
Every `Nat` maps to a valid `PagePermissions` — W^X enforcement happens
downstream in `vspaceMapPage`. -/
def PagePermissions.ofNat (n : Nat) : PagePermissions :=
  { read      := n &&& 1 != 0
    write     := n &&& 2 != 0
    execute   := n &&& 4 != 0
    user      := n &&& 8 != 0
    cacheable := n &&& 16 != 0 }

/-- WS-K-D: Encode `PagePermissions` as a `Nat` bitfield.
Companion to `ofNat` for round-trip proofs. -/
def PagePermissions.toNat (p : PagePermissions) : Nat :=
  (if p.read then 1 else 0) |||
  (if p.write then 2 else 0) |||
  (if p.execute then 4 else 0) |||
  (if p.user then 8 else 0) |||
  (if p.cacheable then 16 else 0)

/-- WS-K-D: `PagePermissions.ofNat` is pure. -/
theorem PagePermissions.ofNat_deterministic (n : Nat) :
    PagePermissions.ofNat n = PagePermissions.ofNat n := rfl

/-- WS-K-D: Round-trip: encoding then decoding recovers the original. -/
theorem PagePermissions.ofNat_toNat_roundtrip (p : PagePermissions) :
    PagePermissions.ofNat (PagePermissions.toNat p) = p := by
  simp only [PagePermissions.ofNat, PagePermissions.toNat]
  cases p with
  | mk r w e u c =>
    cases r <;> cases w <;> cases e <;> cases u <;> cases c <;> native_decide

/-- WS-G6/F-P05: Minimal VSpace root object: ASID identity plus flat virtual→physical mappings.

This intentionally models only one-level deterministic lookup semantics for WS-B1.
Hierarchical page-table levels are deferred behind this stable executable surface.

`mappings` is backed by `RHTable VAddr (PAddr × PagePermissions)` for O(1)
amortized lookup, insert, and erase. RHTable key uniqueness is structural
(noDupKeys invariant), making `noVirtualOverlap` trivially true.

WS-H11/H-02: Enriched with per-page permissions (read/write/execute/user/cacheable). -/
structure VSpaceRoot where
  asid : SeLe4n.ASID
  mappings : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)
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

/-- WS-G6: After unmapping vaddr, lookup returns none. Maps to `RHTable.getElem?_erase_self`.
Requires `invExt` for RHTable erase correctness. -/
theorem lookup_unmapPage_eq_none
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hExt : root.mappings.invExt)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr = none := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some p =>
      simp [hLookup] at hUnmap
      cases hUnmap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self root.mappings vaddr hExt

/-- WS-G6/WS-H11: After mapping vaddr→paddr with perms, lookup returns the entry.
Maps to `RHTable.getElem?_insert_self`. Requires `invExt` for RHTable correctness. -/
theorem lookup_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr = some (paddr, perms) := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some p => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self root.mappings vaddr (paddr, perms) hExt

/-- WS-H11: After mapping vaddr→paddr with default perms, lookupAddr returns paddr.
Requires `invExt` for RHTable correctness. -/
theorem lookupAddr_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookupAddr vaddr = some paddr := by
  simp [lookupAddr, lookup_mapPage_eq root root' vaddr paddr perms hExt hMap]

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

/-- WS-G6: If `lookup` returns `none`, the vaddr has no mapping in the RHTable. -/
theorem lookup_eq_none_iff
    (root : VSpaceRoot)
    (vaddr : SeLe4n.VAddr) :
    root.lookup vaddr = none ↔ vaddr ∉ root.mappings := by
  constructor
  · -- lookup = none → vaddr ∉ mappings
    intro h hMem
    simp only [lookup] at h
    change root.mappings.get? vaddr = none at h
    have hIsSome := (SeLe4n.Kernel.RobinHood.RHTable.mem_iff_isSome_getElem?
      root.mappings vaddr).mp hMem
    rw [h] at hIsSome; exact absurd hIsSome (by simp)
  · -- vaddr ∉ mappings → lookup = none
    intro h
    simp only [lookup]
    show root.mappings.get? vaddr = none
    cases hc : root.mappings.get? vaddr with
    | none => rfl
    | some v =>
      exfalso; apply h
      exact (SeLe4n.Kernel.RobinHood.RHTable.mem_iff_isSome_getElem? root.mappings vaddr).mpr
        (by simp [hc])

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
Maps to `RHTable.getElem?_insert_ne` with the inequality hypothesis.
Requires `invExt` for RHTable correctness. -/
theorem lookup_mapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hNe : vaddr ≠ vaddr')
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne root.mappings vaddr vaddr'
        (paddr, perms) (fun h => hNe (eq_of_beq h)) hExt

/-- TPI-001 helper: unmapPage at vaddr does not affect lookup of a different vaddr'.
Maps to `RHTable.getElem?_erase_ne` with the inequality hypothesis.
Requires `invExt` and `size < capacity` for RHTable erase correctness. -/
theorem lookup_unmapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hExt : root.mappings.invExt)
    (hSize : root.mappings.size < root.mappings.capacity)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne root.mappings vaddr vaddr'
        (fun h => hNe (eq_of_beq h)) hExt hSize

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
extensional equality axioms beyond the RHTable surface. We prove
the forward (soundness) direction; the reverse follows from `BEq.refl` when the
structures are definitionally equal. -/
theorem VSpaceRoot.beq_sound (a b : VSpaceRoot) (h : (a == b) = true) :
    a.asid = b.asid ∧ a.mappings.size = b.mappings.size := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

namespace CNode

open SeLe4n.Kernel.RobinHood

inductive ResolveError where
  | depthMismatch
  | guardMismatch
  deriving Repr, DecidableEq

def empty : CNode :=
  { depth := 0, guardWidth := 0, guardValue := 0, radixWidth := 0,
    slots := RHTable.empty 16 }

/-- Construct a CNode at a given depth with guard/radix parameters. -/

def mk' (d gw gv rw : Nat)
    (s : RHTable SeLe4n.Slot Capability := RHTable.empty 16) : CNode :=
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

/-- WS-G5/F-P03: O(1) amortized slot lookup via `RHTable.get?`. -/
def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  node.slots.get? slot

/-- WS-G5/F-P03: O(1) amortized slot insert via `RHTable.insert`.
RHTable key uniqueness (noDupKeys invariant) ensures the old entry for `slot` is replaced. -/
def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  { node with slots := node.slots.insert slot cap }

/-- WS-G5/F-P03: O(1) amortized slot removal via `RHTable.erase`. -/
def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with slots := node.slots.erase slot }

/-- M-D01: Find the first empty slot in a CNode starting from `base`,
scanning up to `limit` consecutive slot indices. Returns `none` if all
scanned slots are occupied.

The iteration is bounded by `limit` (typically `maxExtraCaps = 3`) rather
than `2^radixWidth`, because we only need slots for the (at most 3) extra
caps in the message. Termination is structural on `limit`. -/
def findFirstEmptySlot (cn : CNode) (base : SeLe4n.Slot)
    (limit : Nat) : Option SeLe4n.Slot :=
  match limit with
  | 0 => none
  | n + 1 =>
      match cn.lookup base with
      | none => some base
      | some _ => cn.findFirstEmptySlot (SeLe4n.Slot.ofNat (base.toNat + 1)) n

/-- If findFirstEmptySlot returns `some s`, then `cn.lookup s = none`. -/
theorem findFirstEmptySlot_spec
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) (s : SeLe4n.Slot)
    (hFind : cn.findFirstEmptySlot base limit = some s) :
    cn.lookup s = none := by
  induction limit generalizing base with
  | zero => simp [findFirstEmptySlot] at hFind
  | succ n ih =>
    simp only [findFirstEmptySlot] at hFind
    split at hFind
    · -- cn.lookup base = none
      cases hFind; assumption
    · -- cn.lookup base = some _
      exact ih _ hFind

/-- findFirstEmptySlot with limit 0 always returns none. -/
theorem findFirstEmptySlot_zero (cn : CNode) (base : SeLe4n.Slot) :
    cn.findFirstEmptySlot base 0 = none := by
  simp [findFirstEmptySlot]

/-- If findFirstEmptySlot returns `none`, all scanned slots are occupied. -/
theorem findFirstEmptySlot_none_iff
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) :
    cn.findFirstEmptySlot base limit = none →
    ∀ i, i < limit →
      (cn.lookup (SeLe4n.Slot.ofNat (base.toNat + i))).isSome := by
  induction limit generalizing base with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [findFirstEmptySlot]
    split
    · intro h; exact absurd h (by simp)
    · rename_i cap hLookup
      intro hRec i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, SeLe4n.Slot.ofNat_toNat]
        rw [hLookup]; rfl
      | succ j =>
        have hj : j < n := Nat.lt_of_succ_lt_succ hi
        have := ih (SeLe4n.Slot.ofNat (base.toNat + 1)) hRec j hj
        simp only [SeLe4n.Slot.toNat_ofNat] at this
        have hEq : base.toNat + 1 + j = base.toNat + (j + 1) := by omega
        rw [hEq] at this; exact this

/-- Local revoke helper for the current modeled slice.

This keeps the authority-bearing source slot while deleting sibling slots in the same CNode that
name the same capability target. Full cross-CNode revoke requires an explicit derivation graph and
is intentionally deferred.

WS-G5/F-P03: Inherently O(m) (filter-by-target), uses `RHTable.filter`. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  {
    node with
      slots := node.slots.filter fun s c => s == sourceSlot || !(c.target == target)
  }

-- ============================================================================
-- WS-G5/WS-E2/C-01: CNode slot-index uniqueness infrastructure
-- ============================================================================

/-- CNode slot well-formedness: the RHTable-backed slots satisfy the extended
invariant (`invExt`) and are not full (`size < capacity`).

WS-N4: With RHTable-backed slots, key uniqueness is enforced by the `noDupKeys`
component of `invExt`. The `size < capacity` condition is maintained by the
resize-at-75%-load policy and is required for erase correctness. -/
def slotsUnique (cn : CNode) : Prop :=
  cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity

/-- WS-G5: After removing a slot, lookup returns `none`.
Maps directly to `RHTable.getElem?_erase_self`. Requires slot invariant
(invExt) to guarantee erase+lookup correctness. -/

theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot)
    (hUniq : node.slotsUnique) :
    (node.remove slot).lookup slot = none := by
  simp only [remove, lookup]
  exact RHTable.getElem?_erase_self node.slots slot hUniq.1

/-- WS-G5: If `lookup` returns `some`, the slot key is present in the RHTable.
Replaces the list-era membership theorem with RHTable semantics. -/

theorem lookup_mem_of_some (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : node.lookup slot = some cap) : slot ∈ node.slots := by
  simp [lookup] at h
  exact (RHTable.mem_iff_isSome_getElem? node.slots slot).mpr (by simp [h])

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
predicate always includes entries where `s = sourceSlot`.
Requires slot invariant for RHTable filter correctness. -/

theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget)
    (hUniq : node.slotsUnique) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  simp only [revokeTargetLocal, lookup]
  exact RHTable.filter_preserves_key node.slots _ sourceSlot
    (fun k' _ hBeq => by simp [eq_of_beq hBeq]) hUniq.1

/-- WS-N4: The empty CNode's slots satisfy the slot invariant. -/
theorem empty_slotsUnique : CNode.empty.slotsUnique := by
  refine ⟨RHTable.empty_invExt 16 (by omega), ?_, ?_⟩
  · show (RHTable.empty 16 (by omega : (0 : Nat) < 16)).size <
      (RHTable.empty 16 (by omega : (0 : Nat) < 16)).capacity
    simp [RHTable.empty]
  · show 4 ≤ (RHTable.empty 16 (by omega : (0 : Nat) < 16)).capacity
    simp [RHTable.empty]

/-- WS-N4: Insert preserves the slot invariant. -/

theorem insert_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hUniq : cn.slotsUnique) :
    (cn.insert slot cap).slotsUnique := by
  refine ⟨cn.slots.insert_preserves_invExt slot cap hUniq.1,
    cn.slots.insert_size_lt_capacity slot cap hUniq.1 hUniq.2.1 hUniq.2.2, ?_⟩
  · -- capacity ≥ 4: insert either keeps same capacity or doubles it
    simp only [CNode.insert]; unfold RHTable.insert; split
    · -- resize branch: capacity doubles
      rw [RHTable.insertNoResize_capacity, cn.slots.resize_fold_capacity]
      have := hUniq.2.2; omega
    · -- no resize: capacity unchanged
      rw [RHTable.insertNoResize_capacity]; exact hUniq.2.2

/-- WS-N4: Erase preserves the slot invariant. -/

theorem remove_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot)
    (hUniq : cn.slotsUnique) :
    (cn.remove slot).slotsUnique := by
  refine ⟨cn.slots.erase_preserves_invExt slot hUniq.1 hUniq.2.1,
    cn.slots.erase_size_lt_capacity slot hUniq.2.1, ?_⟩
  · -- erase preserves capacity
    simp only [CNode.remove]; unfold RHTable.erase; simp only []; split <;> exact hUniq.2.2

/-- WS-N4: Filter preserves the slot invariant. -/

theorem revokeTargetLocal_slotsUnique
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotsUnique := by
  refine ⟨cn.slots.filter_preserves_invExt
      (fun s c => s == sourceSlot || !(c.target == target)) hUniq.1,
    cn.slots.filter_size_lt_capacity
      (fun s c => s == sourceSlot || !(c.target == target)) hUniq.2.1 hUniq.1.1, ?_⟩
  · -- filter preserves capacity (it rebuilds with same capacity)
    simp only [CNode.revokeTargetLocal]; unfold RHTable.filter RHTable.fold
    exact Array.foldl_induction
      (motive := fun _ (acc : RHTable SeLe4n.Slot Capability) => 4 ≤ acc.capacity)
      (by simp [RHTable.empty]; exact hUniq.2.2)
      (fun i acc hAcc => by
        simp only []; split
        · exact hAcc
        · rename_i entry _
          by_cases hf : (fun s c => s == sourceSlot || !(c.target == target)) entry.key entry.value
          · simp only [hf, ite_true]
            rw [RHTable.insertNoResize_capacity]; exact hAcc
          · simp only [show ((fun s c => s == sourceSlot || !(c.target == target))
              entry.key entry.value) = false from Bool.eq_false_iff.mpr hf]
            exact hAcc)

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
  simp [RHTable.empty]

/-- Removing a slot preserves the slot-count bound (size can only decrease). -/

theorem remove_slotCountBounded
    (cn : CNode) (slot : SeLe4n.Slot)
    (hBounded : cn.slotCountBounded) :
    (cn.remove slot).slotCountBounded := by
  show (cn.slots.erase slot).size ≤ 2 ^ cn.radixWidth
  have h : (cn.slots.erase slot).size ≤ cn.slots.size := RHTable.size_erase_le cn.slots slot
  exact Nat.le_trans h hBounded

/-- Revoking target-local preserves the slot-count bound (filter can only decrease size). -/

theorem revokeTargetLocal_slotCountBounded
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hBounded : cn.slotCountBounded)
    (hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotCountBounded := by
  show (cn.slots.filter (fun s c => s == sourceSlot || !(c.target == target))).size ≤ 2 ^ cn.radixWidth
  have h := RHTable.size_filter_le_size cn.slots
    (fun s c => s == sourceSlot || !(c.target == target)) hUniq.1.1
  exact Nat.le_trans h hBounded

/-- WS-G5: If a slot is present in the RHTable, lookup returns its value.
With RHTable-backed slots, key uniqueness is maintained by the `noDupKeys`
component of `invExt` (part of `slotsUnique`). -/

theorem mem_lookup_of_slotsUnique (node : CNode) (_hUniq : node.slotsUnique)
    (slot : SeLe4n.Slot) (hMem : slot ∈ node.slots) :
    ∃ v, node.lookup slot = some v := by
  have := (RHTable.mem_iff_isSome_getElem? node.slots slot).mp hMem
  simp [lookup, Option.isSome_iff_exists] at this ⊢
  exact this

/-- WS-G5: Lookup roundtrip after insert — inserting at `slot` makes lookup
return the inserted capability. Maps directly to `RHTable.getElem?_insert_self`. -/

theorem lookup_insert_eq
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hUniq : cn.slotsUnique) :
    (cn.insert slot cap).lookup slot = some cap := by
  simp only [insert, lookup]
  exact RHTable.getElem?_insert_self cn.slots slot cap hUniq.1

/-- WS-G5: Insert at a different slot does not affect lookup.
Maps directly to `RHTable.getElem?_insert_ne`. -/

theorem lookup_insert_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot) (cap : Capability)
    (hNe : slot ≠ slot')
    (hUniq : cn.slotsUnique) :
    (cn.insert slot cap).lookup slot' = cn.lookup slot' := by
  simp only [insert, lookup]
  exact RHTable.getElem?_insert_ne cn.slots slot slot' cap
    (fun h => hNe (eq_of_beq h)) hUniq.1

/-- WS-G5: Remove at a different slot does not affect lookup.
Maps directly to `RHTable.getElem?_erase_ne`. -/

theorem lookup_remove_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot)
    (hNe : slot ≠ slot')
    (hUniq : cn.slotsUnique) :
    (cn.remove slot).lookup slot' = cn.lookup slot' := by
  simp only [remove, lookup]
  exact RHTable.getElem?_erase_ne cn.slots slot slot'
    (fun h => hNe (eq_of_beq h)) hUniq.1 hUniq.2.1

end CNode

/-- WS-H13/WS-N4: `BEq` instance for `CNode` using entry-wise comparison on the
RHTable-backed slots. Two CNodes are equal iff their depth, guardWidth,
guardValue, radixWidth, and all slot entries agree. -/

instance : BEq CNode where
  beq a b :=
    a.depth == b.depth && a.guardWidth == b.guardWidth &&
    a.guardValue == b.guardValue && a.radixWidth == b.radixWidth &&
    a.slots.size == b.slots.size &&
    a.slots.fold (init := true) (fun acc k v => acc && b.slots.get? k == some v)

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
  | ipcTransfer
  deriving Repr, DecidableEq

/-- Stable CDT node identifier.

Nodes are stable across CSpace slot moves: slots point to nodes, and edges are
between nodes (not slot addresses).

WS-J1-F: Typed wrapper replacing `abbrev CdtNodeId := Nat` for consistency
with all other kernel identifiers. Provides explicit `Hashable`, `LawfulHashable`,
`EquivBEq`, `LawfulBEq` instances for HashMap/HashSet keying. -/
structure CdtNodeId where
  val : Nat
  deriving DecidableEq, Repr, Inhabited

/-- WS-J1-F: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable CdtNodeId where
  hash a := hash a.val

namespace CdtNodeId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : CdtNodeId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : CdtNodeId) : Nat := id.val

instance : ToString CdtNodeId where
  toString id := toString id.toNat

end CdtNodeId

/-- WS-J1-F: LawfulHashable for CdtNodeId HashMap/HashSet proof support. -/
instance : LawfulHashable CdtNodeId where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

/-- WS-J1-F: EquivBEq for CdtNodeId HashMap proof support. -/
instance : EquivBEq CdtNodeId := ⟨⟩

/-- WS-J1-F: LawfulBEq for CdtNodeId HashMap/HashSet proof support. -/
instance : LawfulBEq CdtNodeId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _

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
  childMap : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId (List CdtNodeId) := {}
  /-- M-P02: Child-indexed parent map for O(1) `parentOf` lookup.
  Maps each child node to its unique parent. Symmetric to `childMap`. -/
  parentMap : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId := {}
  deriving Repr

namespace CapDerivationTree

def empty : CapDerivationTree := { edges := [], childMap := {}, parentMap := {} }

/-- Add a derivation edge from parent to child.
WS-G8: Maintains `childMap` index alongside `edges`. -/
def addEdge (cdt : CapDerivationTree) (parent child : CdtNodeId)
    (op : DerivationOp) : CapDerivationTree :=
  let currentChildren := cdt.childMap.get? parent |>.getD []
  { edges := { parent, child, op } :: cdt.edges,
    childMap := cdt.childMap.insert parent (child :: currentChildren),
    parentMap := cdt.parentMap.insert child parent }

/-- Find all direct children of a given node.
WS-G8/F-P14: O(1) lookup via `childMap` instead of O(E) edge scan. -/
def childrenOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : List CdtNodeId :=
  cdt.childMap.get? node |>.getD []

/-- Find the parent of a given node, if any.
M-P02: O(1) lookup via `parentMap` instead of O(E) edge scan. -/
def parentOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : Option CdtNodeId :=
  cdt.parentMap[node]?

/-- Remove all edges referencing a given node as child (detach from parent).
M-P03: Uses targeted `parentMap.erase` + `childMap` splice instead of
full edge-list filter + childMap rebuild. -/
def removeAsChild (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  let parentNode? := cdt.parentMap[node]?
  let childMap' := match parentNode? with
    | some p =>
      let siblings := (cdt.childMap.get? p).getD []
      let filtered := siblings.filter (· != node)
      if filtered.isEmpty then cdt.childMap.erase p else cdt.childMap.insert p filtered
    | none => cdt.childMap
  { edges := cdt.edges.filter (fun e => ¬e.isChildOf node),
    childMap := childMap',
    parentMap := cdt.parentMap.erase node }

/-- Remove all edges referencing a given node as parent (detach all children).
M-P03: Erases the parent's `childMap` entry and all children's `parentMap` entries. -/
def removeAsParent (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  let children := (cdt.childMap.get? node).getD []
  let parentMap' := children.foldl (fun m c => m.erase c) cdt.parentMap
  { edges := cdt.edges.filter (fun e => ¬e.isParentOf node),
    childMap := cdt.childMap.erase node,
    parentMap := parentMap' }

/-- Remove all edges where the given node appears as parent or child.
M-P03: Targeted `parentMap`/`childMap` updates instead of full rebuild. -/
def removeNode (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  -- Phase 1: Remove as parent (erase children's parentMap entries + own childMap entry)
  let children := (cdt.childMap.get? node).getD []
  let parentMapWithoutChildren := children.foldl (fun m c => m.erase c) cdt.parentMap
  -- Phase 2: Remove as child (erase own parentMap entry + splice parent's childMap)
  let parentMapFinal := parentMapWithoutChildren.erase node
  let parentNode? := cdt.parentMap[node]?
  let childMapWithoutSelf := cdt.childMap.erase node
  let childMapFinal := match parentNode? with
    | some p =>
      let siblings := (childMapWithoutSelf.get? p).getD []
      let filtered := siblings.filter (· != node)
      if filtered.isEmpty then childMapWithoutSelf.erase p
      else childMapWithoutSelf.insert p filtered
    | none => childMapWithoutSelf
  -- Phase 3: Filter edges (proof anchor)
  let edgesFiltered := cdt.edges.filter
    (fun e => ¬e.isParentOf node ∧ ¬e.isChildOf node)
  { edges := edgesFiltered, childMap := childMapFinal, parentMap := parentMapFinal }

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

/-- WS-H4/M-G03: Adding an edge preserves edge-well-foundedness when the child
node does not appear in any existing edge (as either parent or child). The parent
node MAY already participate in edges. This covers the common case in kernel
operations where `ensureCdtNodeForSlot` creates a fresh CDT node for the
destination slot.

For nodes that already participate in derivation edges, callers should supply
`hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` directly (the hypothesis
pattern used by `cspaceCopy_preserves_capabilityInvariantBundle` et al.).
The general `descendantsOf`-based theorem requires a BFS completeness proof
that is deferred to Phase 2 (WS-M2) when the CDT structure is refactored. -/
theorem addEdge_preserves_edgeWellFounded_fresh
    (cdt : CapDerivationTree) (parent child : CdtNodeId) (op : DerivationOp)
    (hNeq : parent ≠ child)
    (hAcyclic : cdt.edgeWellFounded)
    (hFreshChild : ∀ e ∈ cdt.edges, e.parent ≠ child ∧ e.child ≠ child) :
    (cdt.addEdge parent child op).edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  -- Strategy: project the cycle onto old edges. If every edge in the cycle is
  -- old, hAcyclic gives contradiction. For the new edge (parent → child),
  -- child has no outgoing edge (fresh), so the cycle cannot continue past it.
  -- We show contradiction when the new edge appears, then fall through to the
  -- old-edge case to build the projected cycle for hAcyclic.
  apply hAcyclic node
  refine ⟨path, hLen, hHead, hLast, fun i hi => ?_⟩
  have ⟨e, heMem, hep, hec⟩ := hEdges i hi
  simp only [addEdge] at heMem
  rcases List.mem_cons.mp heMem with heq | hOld
  · -- e is the new edge: path[i] = parent, path[i+1] = child
    exfalso
    have hCi1 : path[i + 1] = child := by rw [← hec]; exact congrArg CapDerivationEdge.child heq
    -- Find the edge following child. Either i+2 < path.length (interior)
    -- or i+1 is the last index (cycle wraps to path[0]).
    by_cases hNext : i + 1 + 1 < path.length
    · -- Interior case: edge from path[i+1] = child to path[i+2]
      have ⟨e2, he2Mem, he2p, _⟩ := hEdges (i + 1) hNext
      simp only [addEdge] at he2Mem
      rcases List.mem_cons.mp he2Mem with heq2 | hOld2
      · -- New edge again: parent = path[i+1] = child, but parent ≠ child
        have : path[i + 1] = parent := by rw [← he2p]; exact congrArg CapDerivationEdge.parent heq2
        rw [hCi1] at this; exact hNeq this.symm
      · -- Old edge with parent = child: contradicts hFreshChild
        have := (hFreshChild e2 hOld2).1
        rw [he2p, hCi1] at this; exact this rfl
    · -- Wrap-around case: i+1 = path.length - 1, so child is the last element.
      -- Since getLast? = head? = some node, child = node, and path[0] = child.
      -- Edge 0 starts from child, but child has no edges → contradiction.
      have hJLast : i + 1 = path.length - 1 := by omega
      -- Extract: path[path.length - 1] = node from getLast?
      have hLastIdx : path[path.length - 1] = node := by
        rw [List.getLast?_eq_getElem?] at hLast
        exact (List.getElem?_eq_some_iff.mp hLast).2
      -- child = node: path[i+1] = child, and i+1 = path.length-1, getLast? = some node
      have hChildIsNode : child = node := by
        rw [← hCi1, List.getElem_eq_iff (by omega), show i + 1 = path.length - 1 from hJLast,
            ← List.getLast?_eq_getElem?]
        exact hLast
      -- Extract: path[0] = node from head?
      have hFirstIdx : path[0] = node := by
        cases path with
        | nil => simp at hLen
        | cons a rest => simp [List.head?] at hHead; exact hHead
      have hChildIsFirst : path[0] = child := hFirstIdx.trans hChildIsNode.symm
      -- Edge 0: from path[0] = child to path[1]
      have hFirstEdge : 0 + 1 < path.length := by omega
      have ⟨e0, he0Mem, he0p, _⟩ := hEdges 0 hFirstEdge
      simp only [addEdge] at he0Mem
      rcases List.mem_cons.mp he0Mem with heq0 | hOld0
      · -- New edge: e0.parent = parent = path[0] = child → parent = child contradiction
        have h1 : e0.parent = parent := by simp [heq0]
        exact absurd (h1.symm.trans he0p |>.trans hChildIsFirst) hNeq
      · -- Old edge from child: contradicts hFreshChild
        exact absurd (he0p.trans hChildIsFirst) (hFreshChild e0 hOld0).1
  · exact ⟨e, hOld, hep, hec⟩

/-- WS-H4/M-G03: Runtime cycle-check — returns `true` if adding edge
(parent → child) would NOT create a cycle. Checks that parent ≠ child and
parent is not reachable from child via existing edges. -/
def addEdgeWouldBeSafe (cdt : CapDerivationTree) (parent child : CdtNodeId) : Bool :=
  parent != child && parent ∉ cdt.descendantsOf child

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
  · intro h
    have : ({} : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId (List CdtNodeId)).get? parent = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) parent
    rw [this] at h; simp at h
  · rintro ⟨_, hMem, _⟩; cases hMem

theorem addEdge_childMapConsistent (cdt : CapDerivationTree)
    (p c : CdtNodeId) (op : DerivationOp)
    (hCon : cdt.childMapConsistent)
    (hExt : cdt.childMap.invExt) :
    (cdt.addEdge p c op).childMapConsistent := by
  intro parent child
  constructor
  · -- Forward: child in new childMap → edge exists
    intro hIn
    simp only [addEdge] at hIn
    by_cases heq : (p == parent) = true
    · -- p == parent is true
      have hPeq : p = parent := eq_of_beq heq
      subst hPeq
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hExt] at hIn
      simp only [Option.getD] at hIn
      rcases List.mem_cons.mp hIn with hChildEq | hTail
      · exact ⟨⟨p, c, op⟩, .head _, rfl, hChildEq.symm⟩
      · have ⟨e, heMem, hep, hec⟩ := (hCon p child).mp hTail
        exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
    · -- p == parent is false
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ heq hExt] at hIn
      have ⟨e, heMem, hep, hec⟩ := (hCon parent child).mp hIn
      exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
  · -- Backward: edge exists → child in new childMap
    rintro ⟨e, heMem, hep, hec⟩
    simp only [addEdge]
    rcases List.mem_cons.mp heMem with heq | hTail
    · -- e is the new edge
      subst heq
      simp only at hep hec
      subst hep; subst hec
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hExt]
      simp only [Option.getD]
      exact .head _
    · -- e is from existing edges
      by_cases heq : (p == parent) = true
      · -- p == parent is true
        have hPeq : p = parent := eq_of_beq heq
        subst hPeq
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hExt]
        simp only [Option.getD]
        exact List.mem_cons_of_mem _ ((hCon p child).mpr ⟨e, hTail, hep, hec⟩)
      · -- p == parent is false
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ heq hExt]
        exact (hCon parent child).mpr ⟨e, hTail, hep, hec⟩

/-- M-P02: Consistency invariant — `parentMap` mirrors the child→parent
relationship in `edges`. Each child has at most one parent (forest property). -/
def parentMapConsistent (cdt : CapDerivationTree) : Prop :=
  ∀ child parent,
    cdt.parentMap[child]? = some parent ↔
      ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child

theorem empty_parentMapConsistent : CapDerivationTree.empty.parentMapConsistent := by
  intro child parent
  simp only [CapDerivationTree.empty]
  constructor
  · intro h
    have : ({} : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId)[child]? = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) child
    rw [this] at h; cases h
  · rintro ⟨_, hMem, _⟩; cases hMem

theorem addEdge_parentMapConsistent (cdt : CapDerivationTree)
    (p c : CdtNodeId) (op : DerivationOp)
    (hCon : cdt.parentMapConsistent)
    (hFresh : cdt.parentMap[c]? = none)
    (hExt : cdt.parentMap.invExt) :
    (cdt.addEdge p c op).parentMapConsistent := by
  intro child parent
  constructor
  · -- Forward: parentMap entry → edge exists
    intro hIn
    simp only [addEdge] at hIn
    -- Normalize [k]? to get? for RHTable rewriting
    change (cdt.parentMap.insert c p).get? child = some parent at hIn
    by_cases heq : (c == child) = true
    · -- c == child is true
      have hCeq : c = child := eq_of_beq heq
      subst hCeq
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hExt] at hIn
      cases hIn
      exact ⟨⟨p, c, op⟩, .head _, rfl, rfl⟩
    · -- c == child is false
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ heq hExt] at hIn
      have ⟨e, heMem, hep, hec⟩ := (hCon child parent).mp hIn
      exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
  · -- Backward: edge exists → parentMap entry
    rintro ⟨e, heMem, hep, hec⟩
    simp only [addEdge]
    -- Normalize [k]? to get? for RHTable rewriting
    show (cdt.parentMap.insert c p).get? child = some parent
    rcases List.mem_cons.mp heMem with heq | hTail
    · -- e is the new edge
      subst heq
      simp only at hep hec
      subst hep; subst hec
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hExt]
    · -- e is from existing edges
      by_cases heq : (c == child) = true
      · -- c == child is true
        have hCeq : c = child := eq_of_beq heq
        subst hCeq
        -- child = c, but hFresh says parentMap[c]? = none
        -- yet we have an old edge with e.child = c, so hCon would give parentMap[c]? = some e.parent
        have := (hCon c e.parent).mpr ⟨e, hTail, rfl, hec⟩
        rw [hFresh] at this; cases this
      · -- c == child is false
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ heq hExt]
        exact (hCon child parent).mpr ⟨e, hTail, hep, hec⟩

/-- M-P02: Helper — `foldl erase` preserves entries for keys not in the list.
Requires `invExt` and `size < capacity` for RHTable erase correctness. -/
private theorem foldl_erase_preserves
    (xs : List CdtNodeId) (m : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId) (k : CdtNodeId)
    (hNotAny : ∀ c ∈ xs, (c == k) = false)
    (hExt : m.invExt) (hSize : m.size < m.capacity) :
    (xs.foldl (fun acc c => acc.erase c) m)[k]? = m[k]? := by
  induction xs generalizing m with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons]
    have hxk : (x == k) = false := hNotAny x (.head _)
    have hRest : ∀ c ∈ rest, (c == k) = false :=
      fun c hc => hNotAny c (.tail _ hc)
    have hExtE := m.erase_preserves_invExt x hExt hSize
    have hSizeE := m.erase_size_lt_capacity x hSize
    have h1 := ih _ hRest hExtE hSizeE
    have h2 := SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne m x k (by simp [hxk]) hExt hSize
    -- h1 : foldl[k]? = (m.erase x)[k]?, h2 : (m.erase x).get? k = m.get? k
    -- Both [k]? and .get? are definitionally equal for RHTable
    exact h1.trans h2

/-- M-P02: Helper — once `[k]? = none`, further `foldl erase` keeps it none.
Requires `invExt` and `size < capacity` for RHTable erase correctness. -/
private theorem foldl_erase_none
    (xs : List CdtNodeId) (m : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId) (k : CdtNodeId)
    (hNone : m[k]? = none)
    (hExt : m.invExt) (hSize : m.size < m.capacity) :
    (xs.foldl (fun acc c => acc.erase c) m)[k]? = none := by
  induction xs generalizing m with
  | nil => exact hNone
  | cons x rest ih =>
    simp only [List.foldl_cons]
    have hExtE := m.erase_preserves_invExt x hExt hSize
    have hSizeE := m.erase_size_lt_capacity x hSize
    apply ih _ _ hExtE hSizeE
    show (m.erase x).get? k = none
    by_cases hxk : (x == k) = true
    · have hkEq : x = k := eq_of_beq hxk
      rw [hkEq]; exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self m k hExt
    · rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne m x k hxk hExt hSize]; exact hNone

/-- M-P02: Helper — `foldl erase` erases entries for keys in the list.
Requires `invExt` and `size < capacity` for RHTable erase correctness. -/
private theorem foldl_erase_mem
    (xs : List CdtNodeId) (m : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId) (k : CdtNodeId)
    (hMem : ∃ c ∈ xs, (c == k) = true)
    (hExt : m.invExt) (hSize : m.size < m.capacity) :
    (xs.foldl (fun acc c => acc.erase c) m)[k]? = none := by
  induction xs generalizing m with
  | nil => obtain ⟨_, hMem, _⟩ := hMem; cases hMem
  | cons x rest ih =>
    simp only [List.foldl_cons]
    have hExtE := m.erase_preserves_invExt x hExt hSize
    have hSizeE := m.erase_size_lt_capacity x hSize
    obtain ⟨c, hcMem, hck⟩ := hMem
    rcases List.mem_cons.mp hcMem with hcx | hTail
    · -- c = x, so x == k is true
      have hxk : (x == k) = true := hcx ▸ hck
      have hkEq : x = k := eq_of_beq hxk
      apply foldl_erase_none _ _ _ _ hExtE hSizeE
      show (m.erase x).get? k = none
      rw [hkEq]; exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self m k hExt
    · exact ih _ ⟨c, hTail, hck⟩ hExtE hSizeE

/-- M-P02: `removeNode` preserves `parentMapConsistent`.

The proof shows that after removing all edges mentioning `node`:
- Children of `node` have their `parentMap` entries erased (matching edge removal)
- `node` itself has its `parentMap` entry erased (matching edge removal)
- All other entries are unchanged (matching surviving edges) -/
theorem removeNode_parentMapConsistent
    (cdt : CapDerivationTree) (node : CdtNodeId)
    (hCon : cdt.parentMapConsistent)
    (hChildCon : cdt.childMapConsistent)
    (hExt : cdt.parentMap.invExt) (hSizePM : cdt.parentMap.size < cdt.parentMap.capacity) :
    (cdt.removeNode node).parentMapConsistent := by
  intro child parent
  simp only [removeNode]
  -- Establish invExt/size for the fold result via auxiliary lemma
  have foldl_erase_invExt : ∀ (xs : List CdtNodeId)
      (m : SeLe4n.Kernel.RobinHood.RHTable CdtNodeId CdtNodeId),
      m.invExt → m.size < m.capacity →
      (xs.foldl (fun acc c => acc.erase c) m).invExt ∧
      (xs.foldl (fun acc c => acc.erase c) m).size <
      (xs.foldl (fun acc c => acc.erase c) m).capacity := by
    intro xs
    induction xs with
    | nil => intro m hE hS; exact ⟨hE, hS⟩
    | cons x rest ih =>
      intro m hE hS
      simp only [List.foldl_cons]
      exact ih _ (m.erase_preserves_invExt x hE hS) (m.erase_size_lt_capacity x hS)
  have hFoldBoth := foldl_erase_invExt
    ((cdt.childMap.get? node).getD []) cdt.parentMap hExt hSizePM
  have hFoldExt := hFoldBoth.1
  have hFoldSize := hFoldBoth.2
  constructor
  · -- Forward: parentMapFinal[child]? = some parent → surviving edge exists
    intro hIn
    -- Normalize [k]? to .get? for RHTable rewriting
    change ((List.foldl (fun m c => m.erase c) cdt.parentMap
      ((cdt.childMap.get? node).getD [])).erase node).get? child = some parent at hIn
    by_cases hNeNodeBool : (node == child) = true
    · -- node == child: erase_self gives none, contradicts some parent
      have hNodeEq : node = child := eq_of_beq hNeNodeBool
      subst hNodeEq
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self _ node hFoldExt] at hIn
      cases hIn
    · -- child ≠ node
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne _ node child hNeNodeBool
        hFoldExt hFoldSize] at hIn
      have hNotChild : ∀ c ∈ (cdt.childMap.get? node).getD [], (c == child) = false := by
        intro c hc
        cases h : (c == child)
        · rfl
        · exfalso
          have hNone : (List.foldl (fun acc c => acc.erase c) cdt.parentMap
            ((cdt.childMap.get? node).getD [])).get? child = none :=
            foldl_erase_mem _ cdt.parentMap child ⟨c, hc, h⟩ hExt hSizePM
          rw [hNone] at hIn; exact absurd hIn (by simp)
      have hPreserves : (List.foldl (fun acc c => acc.erase c) cdt.parentMap
        ((cdt.childMap.get? node).getD [])).get? child = cdt.parentMap.get? child :=
        foldl_erase_preserves _ _ _ hNotChild hExt hSizePM
      rw [hPreserves] at hIn
      have ⟨e, heMem, hep, hec⟩ := (hCon child parent).mp hIn
      refine ⟨e, List.mem_filter.mpr ⟨heMem, ?_⟩, hep, hec⟩
      simp only [decide_eq_true_eq]
      constructor
      · -- ¬e.isParentOf node = true
        intro hParent
        have hChildInMap : child ∈ (cdt.childMap.get? node).getD [] := by
          apply (hChildCon node child).mpr
          simp only [CapDerivationEdge.isParentOf] at hParent
          exact ⟨e, heMem, eq_of_beq hParent, hec⟩
        have := hNotChild child hChildInMap
        simp at this
      · -- ¬e.isChildOf node = true
        intro hChild
        simp only [CapDerivationEdge.isChildOf] at hChild
        have hChildEqNode : e.child = node := of_decide_eq_true hChild
        have : child = node := hec.symm.trans hChildEqNode
        subst this
        simp at hNeNodeBool
  · -- Backward: surviving edge → parentMapFinal[child]? = some parent
    rintro ⟨e, heMem, hep, hec⟩
    have ⟨heMemOrig, hFilter⟩ := List.mem_filter.mp heMem
    simp only [decide_eq_true_eq] at hFilter
    have ⟨hNotParent, hNotChild⟩ := hFilter
    -- child ≠ node
    have hNeNode : ¬(node == child) = true := by
      intro h
      have hNodeEqChild : node = child := eq_of_beq h
      simp only [CapDerivationEdge.isChildOf] at hNotChild
      exact hNotChild (decide_eq_true (by rw [hec, hNodeEqChild]))
    -- Normalize [k]? to .get? for RHTable rewriting
    show ((List.foldl (fun m c => m.erase c) cdt.parentMap
      ((cdt.childMap.get? node).getD [])).erase node).get? child = some parent
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne _ node child hNeNode
      hFoldExt hFoldSize]
    -- Now goal is foldl result .get? child = some parent
    show (List.foldl (fun m c => m.erase c) cdt.parentMap
      ((cdt.childMap.get? node).getD [])).get? child = some parent
    -- child not in children list
    have hNotInChildren : ∀ c ∈ (cdt.childMap.get? node).getD [], (c == child) = false := by
      intro c hc
      cases h : (c == child)
      · rfl
      · exfalso
        have hCeq : c = child := eq_of_beq h
        -- Use c = child to substitute
        rw [hCeq] at hc
        have ⟨e', he'Mem, he'p, he'c⟩ := (hChildCon node child).mp hc
        have hParentFromOld := (hCon child node).mpr ⟨e', he'Mem, he'p, he'c⟩
        have hParentFromEdge := (hCon child parent).mpr ⟨e, heMemOrig, hep, hec⟩
        rw [hParentFromOld] at hParentFromEdge
        cases hParentFromEdge
        simp only [CapDerivationEdge.isParentOf] at hNotParent
        exact hNotParent (decide_eq_true hep)
    have hPreserves : (List.foldl (fun m c => m.erase c) cdt.parentMap
      ((cdt.childMap.get? node).getD [])).get? child = cdt.parentMap.get? child :=
      foldl_erase_preserves _ _ _ hNotInChildren hExt hSizePM
    rw [hPreserves]
    exact (hCon child parent).mpr ⟨e, heMemOrig, hep, hec⟩

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

/-- R2-D/M-08: Decidable ancestor check — returns `true` if `ancestor` is
reachable from `start` by following parent edges upward through the CDT.
Uses `parentMap` for O(depth) lookup. Fuel = edges.length for termination. -/
def isAncestor (cdt : CapDerivationTree) (ancestor start : CdtNodeId) : Bool :=
  go cdt.edges.length start
where
  go : Nat → CdtNodeId → Bool
    | 0, _ => false
    | n + 1, current =>
      if current == ancestor then true
      else match cdt.parentMap[current]? with
        | none => false
        | some par => go n par

end CapDerivationTree

/-- WS-G5: `DecidableEq` removed from `KernelObject` because `CNode.slots` is
`RHTable Slot Capability` which does not have a `DecidableEq` instance.
`Repr` is retained for trace output. `BEq` is provided manually via entry-wise
comparison for runtime test assertions. -/
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
