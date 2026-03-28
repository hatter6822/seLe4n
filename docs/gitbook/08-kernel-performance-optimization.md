# Kernel Performance Optimization (WS-G)

The WS-G portfolio (v0.12.6–v0.12.15) systematically eliminated every
algorithmic bottleneck identified by the
[v0.12.5 kernel performance audit](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
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

## 4b. WS-M capability performance optimizations (v0.16.14–v0.17.0)

The WS-M audit identified 5 performance findings (M-P01–M-P05) in the capability
subsystem. All resolved across Phases 2 and 5.

| Finding | Issue | Resolution | Version |
|---------|-------|------------|---------|
| **M-P01** | `cspaceRevokeCdt` double-pass revoke fold | `revokeAndClearRefsState` fuses revoke and clear-refs into single-pass fold | v0.16.15 |
| **M-P02** | CDT parent lookup O(E) edge scan | `parentMap : HashMap CdtNodeId CdtNodeId` index for O(1) `parentOf` | v0.16.15 |
| **M-P03** | Reply lemma duplication across preservation proofs | Extracted shared infrastructure; new field preservation lemmas | v0.16.15 |
| **M-P04** | `descendantsOf` materializes full O(N+E) set upfront | `processRevokeNode` shared step + `streamingRevokeBFS` BFS loop; `cspaceRevokeCdtStreaming` avoids full materialization | v0.16.19–v0.17.0 |
| **M-P05** | `endpointReply_preserves_capabilityInvariantBundle` duplication | Unified via extracted lemmas from M-P03 | v0.16.15 |

### M-P04: Streaming BFS revocation (v0.16.19, optimized v0.17.0)

`cspaceRevokeCdtStreaming` performs level-by-level BFS revocation via
`streamingRevokeBFS`, processing one CDT node at a time without materializing
the full `descendantsOf` set. Each BFS step discovers only the immediate children
of the current node, avoiding O(N+E) upfront computation for deep derivation
trees. The per-node transition is factored into `processRevokeNode`, shared by
both the materialized fold (`cspaceRevokeCdt`) and the streaming BFS path.

Preservation is proved in two layers:
- `processRevokeNode_preserves_capabilityInvariantBundle` — shared per-node proof
- `streamingRevokeBFS_preserves` — composed multi-level preservation
- `cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` — top-level bundle preservation

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
| CDT revoke (descendant materialization) | O(N+E) upfront | Streaming BFS (per-level) |

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

## 8. WS-V Phase V7: Data Structure & Proof Optimization (v0.22.8)

V7 addresses performance and correctness findings from the v0.21.7 pre-release
audit:

- **LawfulBEq enforcement** (V7-C): All `RHTable` public operations now require
  `[LawfulBEq α]`, ensuring propositional soundness of equality checks. Ripple
  fixes across 18 files including FrozenState, FreezeProofs, and FrozenOps.
- **Heartbeat reduction** (V7-A/B): `filter_fold_present` reduced from 3.2M to
  400K heartbeats via `filter_fold_present_step` extraction. `insertLoop`
  preservation proofs reduced from 800K to 420K via `noDupKeys_after_set` and
  `distCorrect_after_set` helpers.
- **Algorithmic improvements** (V7-G/I): `CNodeRadix.toList` from O(n²) to O(n).
  Boot-time key uniqueness checks from O(n²) to O(n) via `Std.HashSet`.
- **`native_decide` elimination** (V7-E): `RegisterFile.not_lawfulBEq` now uses
  kernel-reducible `decide` instead of `native_decide`.

## 9. Canonical references

- Audit: [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md)
- Workstream plan: [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md)
- V7 workstream plan: [`AUDIT_v0.21.7_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.21.7_WORKSTREAM_PLAN.md)
- Changelog: [`CHANGELOG.md`](../../CHANGELOG.md) (v0.12.6–v0.12.15, v0.22.8)

