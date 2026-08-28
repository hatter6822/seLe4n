# ADR: WS-C7 Finite Object Store and ServiceId Wrapper

## Status
Accepted (WS-C7)

## Context
`SystemState` historically stored objects as a total function `ObjId → Option KernelObject` and VSpace ASID resolution scanned a fixed synthetic range (`0..4095`). This hurt maintainability and made architecture behavior depend on a hard-coded discovery window. In parallel, `ServiceId` was an `abbrev` to `Nat`, violating the typed-identifier discipline used across the rest of the model.

## Decision
1. Introduce a typed `ServiceId` wrapper in `SeLe4n/Prelude.lean` with `ofNat`, `toNat`, and `OfNat` support.
2. Extend `SystemState` with a finite `objectIndex : List ObjId` that tracks materialized object identities.
3. Update `storeObject` to maintain `objectIndex` deterministically (insert-once behavior).
4. Replace `resolveAsidRoot` bounded-range scanning with `objectIndex` traversal.
5. Keep function-based object lookup during this stage for proof compatibility; this is a staged migration endpoint, not a full finite-map replacement.

## Consequences
- Removes the linear-scan architecture hack tied to arbitrary numeric windows.
- Provides a finite object-store frontier used by architecture lookup logic.
- Preserves compatibility with existing proofs that reason over `objects : ObjId → Option KernelObject`.
- Enables future migration to a concrete finite map with lower proof churn because identifiers are now consistently typed and object discovery is explicit.

## Compatibility notes (as of WS-C7)
- `BootstrapBuilder.build` now seeds `objectIndex` from declared object entries.
- Existing `ServiceId` literals continue to work via `OfNat`.
- Invariant-surface script anchors were updated to assert `resolveAsidRoot` + `objectIndex` usage.

## Evolution through subsequent workstreams

This ADR's staged endpoint was reached and passed:

- **WS-G3**: `resolveAsidRoot` moved from `objectIndex` traversal to the
  O(1) `asidTable` lookup (`Kernel/Architecture/VSpace.lean`); Tier 3 now
  *forbids* objectIndex scanning in `VSpace.lean` — the inverse of the
  anchor this ADR installed.
- **WS-Q2**: the function-based lookup kept in Decision item 5 was
  replaced by the verified finite map — `objects : RHTable ObjId
  KernelObject` (`Model/State.lean`) — completing the migration this ADR
  staged.
- **WS-H14e**: the `OfNat` instances were removed project-wide in favor of
  explicit `.ofNat` constructors, superseding the second compatibility
  note.
