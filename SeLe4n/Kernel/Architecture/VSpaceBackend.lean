import SeLe4n.Model.State

/-!
# VSpace Backend Abstraction (H3 preparation)

This module defines the `VSpaceBackend` typeclass — a forward-looking
abstraction over VSpace implementations. The current HashMap model
(`VSpaceRoot.mappings : Std.HashMap VAddr PAddr`) satisfies this interface
naturally. When H3 introduces ARMv8 hierarchical page tables, a new
backend can be instantiated without changing the abstract kernel proofs.

## Design

The typeclass mirrors the existing VSpace operations in
`SeLe4n.Kernel.Architecture.VSpace` but makes the implementation
strategy abstract:

- `mapPage`: Insert a virtual-to-physical mapping.
- `unmapPage`: Remove a virtual-to-physical mapping.
- `lookupPage`: Translate a virtual address to a physical address.

Each operation returns an `Option` to signal failure (conflict, not-found).
The backend is responsible for maintaining its internal consistency.

## Per-operation invariant obligations

A backend must satisfy:
1. **ASID preservation**: `mapPage` and `unmapPage` do not change the root's ASID.
2. **Round-trip correctness**: `lookupPage` after `mapPage` returns the mapped
   physical address. `lookupPage` after `unmapPage` returns `none`.
3. **Non-interference**: Map/unmap at one vaddr does not affect lookup at another.

System-level invariants (e.g., cross-root ASID uniqueness, within-root
no-virtual-overlap) are enforced by `SeLe4n/Kernel/Architecture/VSpace.lean`
and `VSpaceInvariant.lean`, not by the backend itself.

The current `hashMapVSpaceBackend` instance inherits all obligations from
the existing `VSpaceRoot` lemmas in `SeLe4n/Model/Object.lean`.

## Status

H3-prep forward declaration. The existing VSpace operations continue to
work as before. This interface will be consumed during H3 when the RPi5
platform provides an ARMv8 page-table backend.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n

/-- Abstract VSpace backend interface.

    A backend provides page-level map/unmap/lookup operations over an
    opaque root representation. The abstract kernel calls these through
    the existing `vspaceMapPage`/`vspaceUnmapPage`/`vspaceLookup`
    functions; the backend determines the internal data structure.

    **Type parameter `Root`:** The backing representation for a single
    address space (e.g., `VSpaceRoot` for the current HashMap-based model,
    or a hierarchical page table for ARM64). -/
class VSpaceBackend (Root : Type) where
  /-- Insert a virtual-to-physical mapping into the root.
      Returns `none` if the mapping conflicts with an existing entry. -/
  mapPage : Root → VAddr → PAddr → Option Root
  /-- Remove the mapping for a virtual address from the root.
      Returns `none` if no mapping exists for the given vaddr. -/
  unmapPage : Root → VAddr → Option Root
  /-- Translate a virtual address to a physical address.
      Returns `none` if the vaddr is not mapped. -/
  lookupPage : Root → VAddr → Option PAddr
  /-- The ASID bound to this root. -/
  rootAsid : Root → ASID
  /-- Mapping a page preserves the root's ASID. -/
  mapPage_preserves_asid :
    ∀ root root' vaddr paddr,
      mapPage root vaddr paddr = some root' → rootAsid root' = rootAsid root
  /-- Unmapping a page preserves the root's ASID. -/
  unmapPage_preserves_asid :
    ∀ root root' vaddr,
      unmapPage root vaddr = some root' → rootAsid root' = rootAsid root
  /-- Round-trip: lookup after successful map returns the mapped address. -/
  lookup_after_map :
    ∀ root root' vaddr paddr,
      mapPage root vaddr paddr = some root' →
      lookupPage root' vaddr = some paddr
  /-- Non-interference: map at one vaddr does not affect lookup at another. -/
  lookup_map_other :
    ∀ root root' vaddr vaddr' paddr,
      vaddr ≠ vaddr' →
      mapPage root vaddr paddr = some root' →
      lookupPage root' vaddr' = lookupPage root vaddr'
  /-- Round-trip: lookup after successful unmap returns none. -/
  lookup_after_unmap :
    ∀ root root' vaddr,
      unmapPage root vaddr = some root' →
      lookupPage root' vaddr = none
  /-- Non-interference: unmap at one vaddr does not affect lookup at another. -/
  lookup_unmap_other :
    ∀ root root' vaddr vaddr',
      vaddr ≠ vaddr' →
      unmapPage root vaddr = some root' →
      lookupPage root' vaddr' = lookupPage root vaddr'

-- ============================================================================
-- HashMap-based VSpaceBackend instance (current model) — WS-G6/F-P05
-- ============================================================================

open SeLe4n.Model in
/-- WS-G6/F-P05: The HashMap-backed `VSpaceRoot` satisfies the `VSpaceBackend` interface.

    This instance delegates to the O(1) operations and lemmas defined in
    `SeLe4n.Model.Object` (`VSpaceRoot.mapPage`, `.unmapPage`, `.lookup`)
    and proved in `VSpaceRoot.mapPage_asid_eq`, `lookup_mapPage_eq`, etc.

    No new proofs are required — all obligations are discharged by existing
    theorems. -/
instance hashMapVSpaceBackend : VSpaceBackend VSpaceRoot where
  mapPage root vaddr paddr := root.mapPage vaddr paddr
  unmapPage root vaddr := root.unmapPage vaddr
  lookupPage root vaddr := root.lookup vaddr
  rootAsid root := root.asid
  mapPage_preserves_asid := VSpaceRoot.mapPage_asid_eq
  unmapPage_preserves_asid := VSpaceRoot.unmapPage_asid_eq
  lookup_after_map := VSpaceRoot.lookup_mapPage_eq
  lookup_map_other := fun root root' vaddr vaddr' paddr hNe hMap =>
    VSpaceRoot.lookup_mapPage_ne root root' vaddr vaddr' paddr hNe hMap
  lookup_after_unmap := VSpaceRoot.lookup_unmapPage_eq_none
  lookup_unmap_other := fun root root' vaddr vaddr' hNe hUnmap =>
    VSpaceRoot.lookup_unmapPage_ne root root' vaddr vaddr' hNe hUnmap

end SeLe4n.Kernel.Architecture
