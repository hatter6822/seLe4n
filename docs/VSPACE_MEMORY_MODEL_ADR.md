# ADR: WS-B1 VSpace + Bounded Memory Model Foundation

## Status

Accepted — 2026-02-17 (amended 2026-02-19 by WS-C7)

## Context

The 2026-02 comprehensive audit identified a core architecture gap: the model had
`TCB.vspaceRoot` but no executable VSpace object semantics, and memory remained an
unbounded functional map without a bounded translation contract.

WS-B1 closes this by introducing a minimal, deterministic VSpace foundation that is
proof-friendly and explicitly extensible.

## Decision

1. Add a first-class `VSpaceRoot` kernel object with:
   - `asid`,
   - flat `mappings : List (VAddr × PAddr)`.
2. Add deterministic VSpace transitions:
   - `vspaceMapPage` (fails with `.asidNotBound` or `.mappingConflict`),
   - `vspaceUnmapPage` (fails with `.asidNotBound` or `.translationFault`),
   - `vspaceLookup` (fails with `.asidNotBound` or `.translationFault`).
3. Add WS-B1 invariant surface:
   - ASID-root uniqueness,
   - virtual non-overlap,
   - bounded-translation predicate (`boundedAddressTranslation`).
4. Keep page-table hierarchy abstract for now; this ADR commits only to a stable
   map/unmap/lookup interface and explicit failure taxonomy.
5. (Historical WS-B1 baseline) Use a bounded ASID-discovery window while object storage remains
   function-encoded.
6. (WS-C7 amendment) Replace bounded numeric scanning with explicit object-index traversal
   (`SystemState.objectIndex`) for ASID-root discovery (`resolveAsidRoot`).

## Evolution through subsequent workstreams

| Workstream | Change |
|------------|--------|
| WS-C7 | Replaced bounded numeric scanning with explicit object-index traversal for ASID discovery. |
| WS-G6 | Migrated `VSpaceRoot.mappings` from `List (VAddr × PAddr)` to `Std.HashMap VAddr PAddr` for O(1) operations. |
| WS-G3 | Added `asidTable : Std.HashMap ASID ObjId` for O(1) ASID resolution; `asidTableConsistent` invariant; `vspaceInvariantBundle` extended to 3 conjuncts. |
| WS-H11 | Enriched mappings to `HashMap VAddr (PAddr × PagePermissions)` with W^X enforcement; `vspaceInvariantBundle` extended to 5 conjuncts (+ `wxExclusiveInvariant` + `boundedAddressTranslation`); `VSpaceBackend` enriched with permissions; `MachineConfig.wellFormed` enforces `endAddr ≤ 2^physicalAddressWidth`; abstract TLB model (`TlbState`, `adapterFlushTlb`, `tlbConsistent`). |

## Consequences

### Positive

- Removes VSpace placeholder status from the executable model.
- Enables deterministic map→lookup→unmap trace evidence.
- Provides a stable proof and API surface for WS-B5/WS-B6/WS-B7 follow-on work.
- (WS-H11) Per-page permissions with W^X enforcement at insertion time.
- (WS-H11) Abstract TLB model enables reasoning about cache maintenance sequences.

### Deferred

- Multi-level page-table walk semantics.
- ~~Hardware-precise MMU/TLB invalidation behavior.~~ Partially addressed: abstract `TlbState` model added (WS-H11); hardware-specific TLB ISB/DSB barrier integration deferred to H3 platform bring-up.
- Tight coupling to physical memory frame allocator semantics.

These remain tracked as post-WS-B1 expansions; WS-C7 has already removed the bounded
discovery-window hack in favor of explicit object indexing, while full finite-map ASID indexing
remains future work.

## Verification evidence

- `SeLe4n/Model/Object.lean` (PagePermissions, VSpaceRoot)
- `SeLe4n/Machine.lean` (MachineConfig.wellFormed, MemoryRegion.wellFormed)
- `SeLe4n/Kernel/Architecture/VSpace.lean`
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
- `SeLe4n/Kernel/Architecture/VSpaceBackend.lean`
- `SeLe4n/Kernel/Architecture/TlbModel.lean`
- `docs/FINITE_OBJECT_STORE_ADR.md` (WS-C7 object-index staging ADR)
- `Main.lean` VSpace trace steps
- `tests/fixtures/main_trace_smoke.expected`
