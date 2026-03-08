# VSpace + Bounded Memory Model (ADR)

Canonical ADR: [`docs/VSPACE_MEMORY_MODEL_ADR.md`](../VSPACE_MEMORY_MODEL_ADR.md).

**Status:** Accepted — 2026-02-17 (amended by WS-C7, WS-G3, WS-G6)

## Problem

The 2026-02 audit identified a core architecture gap: the model had `TCB.vspaceRoot` but no executable VSpace object semantics. Memory was an unbounded functional map without a bounded translation contract. VSpace was effectively a placeholder.

## Decision

Introduce a first-class `VSpaceRoot` kernel object with deterministic transitions:

| Operation | Behavior | Error cases |
|-----------|----------|------------|
| `vspaceMapPage` | Add virtual-to-physical mapping | `asidNotBound`, `mappingConflict` |
| `vspaceUnmapPage` | Remove mapping | `asidNotBound`, `translationFault` |
| `vspaceLookup` | Resolve virtual address | `asidNotBound`, `translationFault` |

All operations are total functions with typed errors — no undefined behavior.

## Invariant surface

The VSpace invariant bundle enforces three properties:

1. **ASID-root uniqueness** — each ASID maps to at most one VSpaceRoot object.
2. **Virtual non-overlap** — no two mappings in a VSpaceRoot share a virtual address.
3. **Bounded address translation** — `boundedAddressTranslation` constrains valid address ranges.

## Evolution through subsequent workstreams

| Workstream | Change |
|-----------|--------|
| **WS-C7** | `resolveAsidRoot` rewritten from bounded numeric scanning to `objectIndex` traversal |
| **WS-G3** | ASID table migrated to `HashMap ASID ObjId` for O(1) resolution; bidirectional `asidTableConsistent` invariant; `vspaceInvariantBundle` extended to 3-conjunct |
| **WS-G6** | `VSpaceRoot.mappings` migrated to `HashMap VAddr PAddr` for O(1) page lookup; `noVirtualOverlap` trivially true (HashMap key uniqueness); round-trip theorems re-proved |
| **WS-H11** | Mappings enriched to `HashMap VAddr (PAddr × PagePermissions)` with W^X enforcement; `vspaceInvariantBundle` extended to 5-conjunct (+ `wxExclusiveInvariant` + `boundedAddressTranslation`); `VSpaceBackend` enriched with permissions; `MachineConfig.wellFormed` enforces `endAddr ≤ 2^physicalAddressWidth`; abstract TLB model (`TlbState`, `adapterFlushTlb`, `tlbConsistent`) |

## What remains abstract

Intentionally deferred to the RPi5 hardware binding (H3):

- Multi-level page-table walk semantics
- ~~Hardware MMU/TLB invalidation behavior~~ — partially addressed: abstract `TlbState` model added (WS-H11); hardware-specific ISB/DSB barrier integration deferred
- Physical memory frame allocator coupling

The `VSpaceBackend` typeclass provides the platform-agnostic abstraction point for these.

## Verification evidence

- `SeLe4n/Kernel/Architecture/VSpace.lean` — transitions
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — invariants and preservation
- `SeLe4n/Kernel/Architecture/VSpaceBackend.lean` — backend typeclass
- `Main.lean` — VSpace trace steps (fixture-locked)

## Related

- [Finite Object Store ADR](../FINITE_OBJECT_STORE_ADR.md) (WS-C7)
- [Path to Real Hardware](10-path-to-real-hardware-mobile-first.md) — RPi5 VSpaceBackend binding
- [Architecture & Module Map](03-architecture-and-module-map.md) — module overview
