/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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
open SeLe4n.Model

/-- Abstract VSpace backend interface.

    WS-H11: Enriched with `PagePermissions`. `mapPage` accepts permissions,
    `lookupPage` returns the full `(PAddr × PagePermissions)` entry.

    **Type parameter `Root`:** The backing representation for a single
    address space (e.g., `VSpaceRoot` for the current HashMap-based model,
    or a hierarchical page table for ARM64).

    **H3 preparation:** This typeclass is currently unused — `VSpace.lean`
    operates on the concrete `VSpaceRoot` directly. When hierarchical page
    tables are implemented for ARM64, this typeclass will be instantiated
    with the hardware-specific representation. The `hashMapVSpaceBackend`
    instance below demonstrates that the current model satisfies all
    obligations. -/
class VSpaceBackend (Root : Type) where
  /-- Insert a virtual-to-physical mapping with permissions into the root.
      Returns `none` if the mapping conflicts with an existing entry. -/
  mapPage : Root → VAddr → PAddr → PagePermissions → Option Root
  /-- Remove the mapping for a virtual address from the root.
      Returns `none` if no mapping exists for the given vaddr. -/
  unmapPage : Root → VAddr → Option Root
  /-- Translate a virtual address to a physical address and permissions.
      Returns `none` if the vaddr is not mapped. -/
  lookupPage : Root → VAddr → Option (PAddr × PagePermissions)
  /-- Physical-address-only lookup for backward compatibility. -/
  lookupAddr : Root → VAddr → Option PAddr
  /-- The ASID bound to this root. -/
  rootAsid : Root → ASID
  /-- Mapping a page preserves the root's ASID. -/
  mapPage_preserves_asid :
    ∀ root root' vaddr paddr perms,
      mapPage root vaddr paddr perms = some root' → rootAsid root' = rootAsid root
  /-- Unmapping a page preserves the root's ASID. -/
  unmapPage_preserves_asid :
    ∀ root root' vaddr,
      unmapPage root vaddr = some root' → rootAsid root' = rootAsid root
  /-- Round-trip: lookup after successful map returns the mapped entry. -/
  lookup_after_map :
    ∀ root root' vaddr paddr perms,
      mapPage root vaddr paddr perms = some root' →
      lookupPage root' vaddr = some (paddr, perms)
  /-- Non-interference: map at one vaddr does not affect lookup at another. -/
  lookup_map_other :
    ∀ root root' vaddr vaddr' paddr perms,
      vaddr ≠ vaddr' →
      mapPage root vaddr paddr perms = some root' →
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

/-- WS-G6/F-P05/WS-H11: The HashMap-backed `VSpaceRoot` satisfies the `VSpaceBackend` interface.

    This instance delegates to the O(1) operations and lemmas defined in
    `SeLe4n.Model.Object` (`VSpaceRoot.mapPage`, `.unmapPage`, `.lookup`)
    and proved in `VSpaceRoot.mapPage_asid_eq`, `lookup_mapPage_eq`, etc.

    WS-H11: Updated for enriched `(PAddr × PagePermissions)` value type. -/
instance hashMapVSpaceBackend : VSpaceBackend VSpaceRoot where
  mapPage root vaddr paddr perms := root.mapPage vaddr paddr perms
  unmapPage root vaddr := root.unmapPage vaddr
  lookupPage root vaddr := root.lookup vaddr
  lookupAddr root vaddr := root.lookupAddr vaddr
  rootAsid root := root.asid
  mapPage_preserves_asid := fun root root' vaddr paddr perms hMap =>
    VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMap
  unmapPage_preserves_asid := VSpaceRoot.unmapPage_asid_eq
  lookup_after_map := VSpaceRoot.lookup_mapPage_eq
  lookup_map_other := fun root root' vaddr vaddr' paddr perms hNe hMap =>
    VSpaceRoot.lookup_mapPage_ne root root' vaddr vaddr' paddr perms hNe hMap
  lookup_after_unmap := VSpaceRoot.lookup_unmapPage_eq_none
  lookup_unmap_other := fun root root' vaddr vaddr' hNe hUnmap =>
    VSpaceRoot.lookup_unmapPage_ne root root' vaddr vaddr' hNe hUnmap

end SeLe4n.Kernel.Architecture
