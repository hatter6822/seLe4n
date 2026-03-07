# ADR: F-17 O(n) List-Based Data Structure Design Decision

## Status
Accepted (WS-E6 / F-17) — **Superseded by WS-G (v0.12.6–v0.12.15)**

> **Note:** WS-G completed the migration from List-based to `Std.HashMap`/`Std.HashSet`-based data structures for all kernel hot paths. The "Migration path" section below describes the strategy that was executed. See [Kernel Performance Optimization](gitbook/08-kernel-performance-optimization.md) and [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) for the completed execution record.

## Context

The seLe4n kernel model uses `List`-based data structures for several core
collections:

| Collection | Type | Location |
|---|---|---|
| Runnable queue | `List ThreadId` | `SchedulerState.runnable` |
| Object index | `List ObjId` | `SystemState.objectIndex` |
| CNode slots | `List (Slot × Capability)` | `CNode.slots` |
| VSpace mappings | `List PageTableEntry` | `VSpaceRoot.mappings` |
| Endpoint queues | intrusive queue boundaries + TCB links | `Endpoint.queue/sendQ/receiveQ` + `TCB.queuePrev/queueNext` |
| Service dependencies | `List ServiceId` | `ServiceGraphEntry.dependencies` |
| Domain schedule | `List DomainScheduleEntry` | `SchedulerState.domainSchedule` |

Operations that scan these lists — `chooseBestRunnable`, `filterByDomain`,
`resolveAsidRoot`, capability revocation — are O(n) in the number of elements.
The seL4 C implementation uses red-black trees, hash tables, and CDT structures
with O(log n) or O(1) amortized complexity for the corresponding operations.

Finding F-17 from the v0.11.6 audit asks that this design decision be explicitly
documented with rationale, scope note, and a future migration path.

## Decision

We retain `List`-based structures for the current formalization stage, for the
following reasons:

### 1. Proof tractability

Lean 4's `List` type has a mature library of lemmas (`List.mem_cons`,
`List.filter_map`, `List.foldl_assoc`, etc.) that make inductive proofs over
collection operations straightforward. Switching to balanced trees (e.g.,
`Batteries.RBMap`) would require re-proving every invariant in terms of the
tree's internal balancing logic, substantially increasing proof burden without
improving the semantic fidelity of the model.

### 2. Current stage: proof-first, optimize later

seLe4n is evolving toward a production kernel targeting Raspberry Pi 5. In the
current stage, the priority is closing proof gaps (WS-F) with machine-checked
invariant preservation. The O(n) cost is paid only in the trace harness and
test execution, where n is typically < 20. Once the proof surface is complete,
the migration path below enables swapping to efficient backends without
re-proving kernel invariants.

### 3. Semantic equivalence

The functional behavior of `List.filter`, `List.foldl`, and `List.find?` is
identical to the corresponding tree operations for the purposes of our
specification. The invariants we prove (e.g., "the scheduled thread has the
highest priority in the runnable set") hold regardless of the backing data
structure.

### 4. Deterministic ordering

Lists provide a natural FIFO ordering that models queue semantics (runnable
queue, IPC send/receive queues, domain schedule table) without requiring an
explicit sequence number or insertion timestamp. This simplifies both the model
and the proofs.

## Scope note

This decision covers the current proof-completion phase. O(n) data structures
are **not** appropriate for the production kernel under hard real-time
constraints. The migration path (below) is a planned part of the production
roadmap — it will be executed after the WS-F proof gaps are closed and before
Raspberry Pi 5 hardware binding (H3).

## Affected operations and their complexity

| Operation | Current complexity | seL4 complexity | Notes |
|---|---|---|---|
| `chooseBestRunnable` | O(n) scan | O(log n) RB-tree | Priority queue |
| `filterByDomain` | O(n) filter | O(1) per-domain list | Domain partitioning |
| `resolveAsidRoot` | O(n) index scan | O(1) ASID table | ASID lookup |
| `cspaceRevokeCap` | O(n) slot scan | O(n) CDT walk | Both linear in worst case |
| `objectIndex` membership | O(n) scan | O(1) hash lookup | Object store |

## Migration path

If future work requires performance-sensitive execution (e.g., large-scale
simulation, model-based testing with thousands of objects), the migration
strategy is:

1. **Define an abstract interface** (`FiniteMap α β`) with the operations used
   by the kernel model (`lookup`, `insert`, `delete`, `fold`, `filter`).
2. **Prove the interface lemmas** once, parameterized over the interface.
3. **Instantiate with `List`** for the current proof-friendly implementation.
4. **Instantiate with `Batteries.RBMap`** (or `Batteries.HashMap`) for the
   performance-sensitive backend, proving the interface contract holds for the
   efficient implementation.
5. **Swap backends** without changing any kernel-level proofs, since they depend
   only on the interface lemmas.

This staged approach is standard in verified systems (see Cogent, CakeML, and
seL4's own abstract/concrete refinement layers).

## References

- F-17 finding: `docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`
- Finite object store ADR: `docs/FINITE_OBJECT_STORE_ADR.md` (related: WS-C7)
- seL4 kernel data structures: `docs/spec/SEL4_SPEC.md` §5 (scheduling)
