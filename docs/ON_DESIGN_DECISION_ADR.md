# ADR: O(n) Data Structure Design Decision (F-17/WS-E6)

**Status:** Accepted
**Date:** 2026-02-26
**Workstream:** WS-E6 (Model completeness and documentation)
**Finding:** F-17 (carry-forward from WS-D6)

## Context

The seLe4n kernel model uses `List`-based data structures throughout:

| Structure | Location | Access pattern |
|---|---|---|
| Object store | `SystemState.objects : ObjId → Option KernelObject` | Function (O(1) abstract) |
| Object index | `SystemState.objectIndex : List ObjId` | Linear scan via `find?` |
| Runnable queue | `SchedulerState.runnable : List ThreadId` | Linear scan, append, erase |
| CNode slots | `CNode.slots : List (Slot × Capability)` | Linear scan via `find?` |
| Endpoint queues | `Endpoint.queue/sendQueue/receiveQueue : List ThreadId` | Append, head removal |
| VSpace mappings | `VSpaceRoot.mappings : List (VAddr × PAddr)` | Linear scan via `find?` |
| Service dependencies | `ServiceGraphEntry.dependencies : List ServiceId` | Membership check |
| CDT edges | `CapDerivationTree.edges : List (SlotRef × SlotRef)` | BFS traversal |
| Notification waiters | `Notification.waitingThreads : List ThreadId` | Append, head removal |

All list-based operations are O(n) in the number of elements.

## Decision

**O(n) list-based data structures are intentional** for this stage of the
formalization. The model prioritizes proof clarity and deterministic semantics
over execution efficiency.

## Rationale

1. **Proof simplicity.** List operations (`find?`, `filter`, `map`, `any`,
   `erase`, `append`) have well-understood Lean 4 library lemmas. Switching to
   `RBMap` or `HashMap` would require either axiomatizing map properties or
   importing Mathlib, adding proof complexity without improving assurance.

2. **Deterministic semantics.** Lists provide a canonical iteration order that
   makes tie-breaking, queue ordering, and traversal deterministic by
   construction. The scheduler's three-level selection (priority > deadline >
   FIFO) exploits list position as the final stable tie-break. Hash-based
   structures would require explicit ordering contracts.

3. **Bounded model scope.** The abstract model operates on small, finite state
   spaces (tens of objects, not millions). O(n) is functionally equivalent to
   O(1) at this scale. The model is not intended for execution at real-kernel
   scale.

4. **Monotonic index compatibility.** The `objectIndex` design (L-05) exploits
   list append semantics for monotonicity: once an ID appears in the list, it
   remains permanently. This property would need explicit maintenance with a
   map-based structure.

## Scope note

This decision applies to the **abstract formal model** only. It does not
constrain any concrete implementation that might be extracted or inspired by
this model. A production kernel implementation would use appropriate data
structures (arrays, hash tables, balanced trees) for each use case.

## Future migration path

When model scale or execution requirements change, the migration strategy is:

1. **Phase 1: Type alias.** Replace `List`-based fields with type aliases
   (`ObjectIndex := List ObjId`) to centralize the abstraction boundary.

2. **Phase 2: Interface extraction.** Define typeclass-based interfaces
   (`Lookup`, `Insert`, `Membership`) that both `List` and `RBMap`
   implementations satisfy.

3. **Phase 3: Gradual replacement.** Swap individual structures from `List` to
   `RBMap`/`Array` behind the interface, updating proofs module-by-module.
   The invariant surfaces (preservation theorems) should remain stable if
   proofs depend on interface properties rather than `List`-specific lemmas.

Estimated effort: Medium (several workstream slices). Not planned for the
current WS-E portfolio.
