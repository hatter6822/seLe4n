# ADR: WS-B1 VSpace + Bounded Memory Model Foundation

## Status

Accepted — 2026-02-17

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
5. Use a bounded ASID-discovery window (`vspaceDiscoveryWindow = 4096`) while
   object storage remains function-encoded; replace this with a direct finite-map
   ASID index in follow-on state-model work.

## Consequences

### Positive

- Removes VSpace placeholder status from the executable model.
- Enables deterministic map→lookup→unmap trace evidence.
- Provides a stable proof and API surface for WS-B5/WS-B6/WS-B7 follow-on work.

### Deferred

- Multi-level page-table walk semantics.
- Hardware-precise MMU/TLB invalidation behavior.
- Tight coupling to physical memory frame allocator semantics.

These remain tracked as post-WS-B1 expansions, including finite-map ASID indexing.

## Verification evidence

- `SeLe4n/Kernel/Architecture/VSpace.lean`
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
- `Main.lean` VSpace trace steps
- `tests/fixtures/main_trace_smoke.expected`
