# Model Structure and Maintainability (ADR)

Canonical ADR: [`docs/FINITE_OBJECT_STORE_ADR.md`](../FINITE_OBJECT_STORE_ADR.md).

**Status:** Accepted (WS-C7, completed)

## Problem

`SystemState` historically stored objects as a total function `ObjId -> Option KernelObject`. VSpace ASID resolution scanned a hard-coded synthetic range (`0..4095`). `ServiceId` was an `abbrev` to `Nat`, violating the typed-identifier discipline used everywhere else in the model.

These three issues hurt maintainability: architecture behavior depended on magic numbers, identifier confusion was possible, and the functional object store made future finite-map migration difficult.

## Decisions

| # | Decision | Rationale |
|---|----------|-----------|
| 1 | Introduce typed `ServiceId` wrapper in `Prelude.lean` | Consistent with `ThreadId`, `ObjId`, `CPtr`, etc. |
| 2 | Add finite `objectIndex : List ObjId` to `SystemState` | Tracks materialized object identities explicitly |
| 3 | Update `storeObject` to maintain `objectIndex` deterministically | Insert-once behavior; no duplicates |
| 4 | Replace `resolveAsidRoot` bounded-range scanning with `objectIndex` traversal | Removes magic-number dependency |
| 5 | Keep function-based object lookup during this stage | Minimizes proof churn; staged migration endpoint |

## Consequences

**Positive:**
- Removes linear-scan hack tied to arbitrary numeric windows.
- Provides finite object-store frontier for architecture lookup.
- Preserves existing proofs that reason over `objects : ObjId -> Option KernelObject`.
- Enables future `Std.HashMap` migration (completed in WS-G2) with lower proof churn.

**Compatibility:**
- `BootstrapBuilder.build` seeds `objectIndex` from declared object entries.
- Existing `ServiceId` literals continue to work via `OfNat`.
- Tier 3 anchors assert `resolveAsidRoot` + `objectIndex` usage.

## Evolution

WS-C7 was a staging point. Subsequent workstreams completed the migration:

| Workstream | What changed |
|-----------|-------------|
| **WS-G1** | `Hashable` instances for all typed identifiers, enabling HashMap usage |
| **WS-G2** | Object store migrated to `Std.HashMap ObjId KernelObject` |
| **WS-H7** | Closure-backed fields (`services`, `irqHandlers`, `cdtSlotNode`, `cdtNodeSlot`) migrated to `Std.HashMap` |

The functional object store that WS-C7 preserved has now been fully replaced by hash-based structures.

## Verification evidence

- `SeLe4n/Prelude.lean` — `ServiceId` wrapper
- `SeLe4n/Model/State.lean` — `objectIndex`, `storeObject` maintenance
- `SeLe4n/Kernel/Architecture/VSpace.lean` — `resolveAsidRoot` using `objectIndex`

## Related

- [VSpace + Bounded Memory Model](26-ws-b1-vspace-memory-adr.md) — WS-B1 foundation
- [Kernel Performance Optimization](08-kernel-performance-optimization.md) — WS-G migration
- [Architecture & Module Map](03-architecture-and-module-map.md) — module structure
