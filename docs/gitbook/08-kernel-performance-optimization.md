# Kernel Performance Optimization (WS-G)

The WS-G portfolio (v0.12.6–v0.12.15) systematically eliminated every
algorithmic bottleneck identified by the
[v0.12.5 kernel performance audit](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All 14 findings (F-P01 through F-P14) across 6 subsystems are resolved.
Every invariant proof was re-verified — zero `sorry`, zero `axiom`.

## 1. Motivation

A production microkernel targeting Raspberry Pi 5 cannot afford O(n) hot-path
operations. The v0.12.5 audit found 3 critical, 6 high, and 5 medium
algorithmic complexity issues:

- Object lookup used closure-chain accumulation (O(n) per access)
- Scheduler insert/remove scanned flat thread lists (O(t))
- CNode and VSpace operations did linear scans (O(m))
- IPC endpoint queues used O(n) append
- Service dependency checking was O(n^2) BFS
- Information-flow projection re-evaluated observability per object

The WS-G portfolio replaced all of these with O(1) hash-based structures while
preserving every machine-checked proof.

## 2. Approach

**Three principles guided the migration:**

1. **Performance without sacrifice.** No security invariant was weakened. Every
   theorem was re-proved, not removed.
2. **Proof-first migration.** Bridge lemmas were written before data structure
   changes, ensuring proofs stayed green throughout.
3. **Foundation-first ordering.** WS-G1 (Hashable infrastructure) enabled all
   subsequent workstreams. Dependencies were strictly ordered.

## 3. Workstream summary

| ID | Focus | Findings closed | Version |
|----|-------|----------------|---------|
| **WS-G1** | Hashable/BEq infrastructure | (prerequisite) | v0.12.6 |
| **WS-G2** | Object store HashMap | F-P01, F-P10, F-P13 | v0.12.7 |
| **WS-G3** | ASID resolution table | F-P06 | v0.12.8 |
| **WS-G4** | Run queue restructure | F-P02, F-P07, F-P12 | v0.12.9 |
| **WS-G5** | CNode slot HashMap | F-P03 | v0.12.10 |
| **WS-G6** | VSpace mapping HashMap | F-P05 | v0.12.11 |
| **WS-G7** | IPC queue + notification | F-P04, F-P11 | v0.12.12 |
| **WS-G8** | Graph traversal optimization | F-P08, F-P14 | v0.12.13 |
| **WS-G9** | Info-flow projection | F-P09 | v0.12.14 |
| — | Refinement pass | (quality) | v0.12.15 |

## 4. Technical detail by workstream

### WS-G1: Hashable/BEq infrastructure (v0.12.6)

Added `Hashable` and `BEq` instances for all 13 typed identifiers (`ThreadId`,
`ObjId`, `CPtr`, `Slot`, `DomainId`, `ASID`, `VAddr`, `PAddr`, `Priority`,
`CdtNodeId`, `ServiceId`, `Deadline`, `Badge`) plus the composite `SlotRef`
key. All instances are `@[inline]` for zero overhead. Imported
`Std.Data.HashMap` and `Std.Data.HashSet` in `Prelude.lean`.

**Why this matters:** Without `Hashable`, no hash-based data structure could be
instantiated. This was the prerequisite for all other WS-G workstreams.

### WS-G2: Object store HashMap (v0.12.7)

Replaced the closure-chain object store with `Std.HashMap ObjId KernelObject`.
Added `objectIndexSet : Std.HashSet ObjId` for O(1) membership and
`objectTypes : Std.HashMap ObjId KernelObjectType` for lifecycle metadata.

| Before | After |
|--------|-------|
| `objects` via closure chain | `objects : Std.HashMap ObjId KernelObject` |
| O(n) lookup accumulation | O(1) amortized lookup |
| O(n) membership check | O(1) via `objectIndexSet` |

9 bridge lemmas, `objectIndexSetSync` invariant, 599 theorems re-verified.
Closes F-P01 (critical), F-P10, F-P13.

### WS-G3: ASID resolution table (v0.12.8)

Added `asidTable : Std.HashMap ASID ObjId` to `SystemState`. Rewrote
`resolveAsidRoot` from O(n) `objectIndex.findSome?` traversal to O(1)
HashMap lookup with object-store validation.

Bidirectional `asidTableConsistent` invariant ensures soundness (every ASID
table entry points to a valid VSpaceRoot) and completeness (every VSpaceRoot
with an ASID is in the table). `vspaceInvariantBundle` extended from 2 to 3
conjuncts. Closes F-P06 (critical).

### WS-G4: Run queue restructure (v0.12.9)

Replaced the flat `runnable : List ThreadId` with a priority-bucketed
`RunQueue` structure:

```
RunQueue {
  byPriority : Std.HashMap Priority (List ThreadId)
  members    : Std.HashSet ThreadId
  maxPriority : Option Priority
  flat_wf    : structural invariant
}
```

Operations `insert`/`remove`/`contains`/`rotateHead` are all O(1).
`chooseBestInBucket` reduces best-candidate selection from O(t) to O(k)
(number of priority buckets). Eliminated `withRunnableQueue`, `runnableHead`,
`runnableTail`. 13 bridge lemmas, 30+ IPC proofs migrated. Closes F-P02
(critical), F-P07, F-P12.

### WS-G5: CNode slot HashMap (v0.12.10)

Migrated `CNode.slots` from `List (Slot × Capability)` to
`Std.HashMap Slot Capability`. Slot `lookup`/`insert`/`remove` all O(1).
`slotsUnique` is now trivially true (HashMap key uniqueness is structural).

`cspaceRevoke` computes `revokedRefs` via a single `HashMap.fold` pass
instead of repeated list scans. Manual `BEq CNode`/`BEq KernelObject`
instances added for runtime test support. Closes F-P03.

### WS-G6: VSpace mapping HashMap (v0.12.11)

Migrated `VSpaceRoot.mappings` from `List (VAddr × PAddr)` to
`Std.HashMap VAddr PAddr` (subsequently enriched to `Std.HashMap VAddr (PAddr × PagePermissions)` by WS-H11). Page `lookup`/`mapPage`/`unmapPage` all O(1).

The `noVirtualOverlap` property is now trivially true for all VSpaceRoots
(HashMap key uniqueness guarantees no duplicate virtual addresses).
`hashMapVSpaceBackend` replaces `listVSpaceBackend` as the canonical backend
instance. Round-trip theorems re-proved with HashMap bridge lemmas.
Closes F-P05.

### WS-G7: IPC queue + notification optimization (v0.12.12)

Deprecated legacy endpoint operations (`endpointSend`/`endpointReceive`/
`endpointAwaitReceive`) in favor of O(1) dual-queue operations (fully removed
in WS-H12a v0.13.8).

`notificationWait` O(n) duplicate check replaced with O(1) TCB `ipcState`
inspection. O(n) append replaced with O(1) prepend. New
`notificationWaiterConsistent` invariant bridges TCB state to queue
membership. `endpointSendDualChecked` enforcement wrapper added.
Closes F-P04, F-P11.

### WS-G8: Graph traversal optimization (v0.12.13)

Rewrote `serviceHasPathTo` from O(n^2) BFS with `List ServiceId` visited
set to O(n+e) DFS with `Std.HashSet ServiceId`.

Extended `CapDerivationTree` with `childMap : Std.HashMap CdtNodeId
(List CdtNodeId)` — a parent-indexed edge index enabling O(1)
`childrenOf` lookup. `descendantsOf` drops from O(N*E) to O(N+E).
`childMapConsistent` invariant with `empty`/`addEdge` preservation proofs.
Closes F-P08, F-P14.

### WS-G9: Information-flow projection optimization (v0.12.14)

`computeObservableSet` precomputes `Std.HashSet ObjId` via a single `foldl`
pass over the observable objects. `projectStateFast` uses O(1) `contains`
lookups instead of per-object `objectObservable` re-evaluation.

`projectStateFast_eq` proves semantic equivalence with the original
`projectState` and is `@[csimp]`-ready for compiler substitution. Zero
downstream proof breakage — all 15 NI theorems unchanged. Closes F-P09.

### Refinement pass (v0.12.15)

Post-completion quality sweep:

- `RunQueue.remove` bucket precomputation (eliminated redundant `List.filter`)
- `MachineConfig.wellFormed` page-size validation via `isPowerOfTwo` (bitwise)
- Dead code removal (`filterByDomain`)
- Phantom object cleanup (ID 200 from `bootstrapInvariantObjectIds`)
- Runtime invariant checks: `runQueueThreadPriorityConsistentB`, `cdtChildMapConsistentCheck`
- `StateBuilder` TCB priority integration for correct RunQueue bucketing
- `NegativeStateSuite` expansion: `endpointReplyRecv` and `cspaceMutate` coverage

## 5. Complexity improvements

| Hot path | Before | After |
|----------|--------|-------|
| Object lookup | O(n) closure chain | O(1) HashMap |
| Object membership | O(n) index scan | O(1) HashSet |
| ASID resolution | O(n) linear scan | O(1) HashMap |
| Scheduler insert/remove | O(t) list scan | O(1) bucket |
| Best-candidate selection | O(t) full scan | O(k) bucket-first |
| CNode slot lookup | O(m) list scan | O(1) HashMap |
| VSpace page lookup | O(m) list scan | O(1) HashMap |
| Endpoint queue append | O(n) list append | O(1) prepend |
| Notification duplicate check | O(n) list scan | O(1) TCB state |
| Service reachability | O(n^2) BFS | O(n+e) DFS |
| CDT children lookup | O(E) edge scan | O(1) childMap |
| CDT descendant traversal | O(N*E) | O(N+E) |
| Info-flow observability | O(n) per object | O(1) HashSet |

## 6. Proof impact

All theorem/invariant declarations were re-verified after each workstream. Key proof artifacts:

- **60+ bridge lemmas** connecting HashMap/HashSet operations to prior list-based reasoning
- **`objectIndexSetSync`** invariant (WS-G2): HashSet mirrors HashMap key set
- **`asidTableConsistent`** invariant (WS-G3): bidirectional ASID ↔ VSpaceRoot
- **`flat_wf`** structural invariant (WS-G4): RunQueue bucket consistency
- **`slotsUnique` triviality** (WS-G5): HashMap key uniqueness replaces explicit proof
- **`noVirtualOverlap` triviality** (WS-G6): same pattern for VSpace
- **`notificationWaiterConsistent`** (WS-G7): TCB state ↔ queue membership
- **`childMapConsistent`** (WS-G8): CDT childMap ↔ edges bidirectional
- **`projectStateFast_eq`** (WS-G9): fast ↔ original projection equivalence

## 7. Files modified

The WS-G portfolio touched 15 production files across all kernel subsystems.
Major structural changes concentrated in:

- `SeLe4n/Prelude.lean` — Hashable instances, HashSet bridge lemmas
- `SeLe4n/Model/Object.lean` — CNode, VSpaceRoot, CDT data structures
- `SeLe4n/Model/State.lean` — SystemState fields (objects, asidTable, objectTypes)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` — priority-bucketed RunQueue
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — fast projection path

## 8. Canonical references

- Audit: [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md)
- Workstream plan: [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md)
- Changelog: [`CHANGELOG.md`](../../CHANGELOG.md) (v0.12.6–v0.12.15)

