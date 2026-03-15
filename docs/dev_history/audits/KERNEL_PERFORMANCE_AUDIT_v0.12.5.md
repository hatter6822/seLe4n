# Kernel Performance Audit — seLe4n v0.12.5

**Date:** 2026-03-01
**Scope:** End-to-end codebase audit targeting runtime performance
**Constraint:** No security sacrifices — all recommendations preserve invariant proofs

---

## Executive Summary

This audit examines every kernel subsystem in seLe4n v0.12.5 for performance
characteristics, identifying 14 actionable findings across 6 subsystems. The
findings fall into three tiers:

- **Critical (3 findings):** Algorithmic complexity on the IPC/scheduling hot
  path, closure-chain accumulation in the object store, and linear ASID
  resolution on every VSpace operation.
- **High (6 findings):** Flat-list data structures in CNode slots, endpoint
  queues, runnable queue, VSpace mappings, service dependency BFS, and
  information-flow projection overhead.
- **Medium (5 findings):** Redundant object lookups in lifecycle transitions,
  `objectIndex` membership scans in `storeObject`, notification duplicate
  checks, CDT BFS traversal cost, and `withRunnableQueue` tail recomputation.

None of the recommendations require weakening any invariant, removing any
theorem, or introducing `sorry`/`axiom`. Every optimization targets the
executable model's data structure representation while preserving the proof
surface.

---

## Table of Contents

1. [Methodology](#1-methodology)
2. [Architecture & Hot-Path Analysis](#2-architecture--hot-path-analysis)
3. [Finding F-P01: Object Store Closure-Chain Accumulation](#3-finding-f-p01)
4. [Finding F-P02: Runnable Queue — O(n) Insert/Remove/Membership](#4-finding-f-p02)
5. [Finding F-P03: CNode Slot List — O(m) Lookup/Insert/Delete](#5-finding-f-p03)
6. [Finding F-P04: Legacy Endpoint Queue — O(n) Append](#6-finding-f-p04)
7. [Finding F-P05: VSpace Mapping List — O(m) Lookup](#7-finding-f-p05)
8. [Finding F-P06: ASID Resolution — O(n) Linear Scan](#8-finding-f-p06)
9. [Finding F-P07: Scheduler Best-Candidate Selection — O(n) Scan](#9-finding-f-p07)
10. [Finding F-P08: Service Dependency BFS — O(n²) Worst Case](#10-finding-f-p08)
11. [Finding F-P09: Information-Flow Projection CNode Filtering](#11-finding-f-p09)
12. [Finding F-P10: storeObject objectIndex Membership Check](#12-finding-f-p10)
13. [Finding F-P11: Notification Duplicate Wait Check](#13-finding-f-p11)
14. [Finding F-P12: withRunnableQueue Tail Recomputation](#14-finding-f-p12)
15. [Finding F-P13: Lifecycle Triple-Lookup Pattern](#15-finding-f-p13)
16. [Finding F-P14: CDT descendantsOf BFS Traversal](#16-finding-f-p14)
17. [Positive Findings — Already Optimized](#17-positive-findings)
18. [Prioritized Recommendation Matrix](#18-prioritized-recommendation-matrix)
19. [Implementation Roadmap](#19-implementation-roadmap)

---

## 1. Methodology

**Files audited:** All 42 `.lean` source files (excluding `.lake/` packages).

**Approach:**
- Read every Operations file in full, tracking function signatures and
  algorithmic complexity
- Traced critical paths end-to-end (IPC send, schedule, capability lookup,
  VSpace translate) through the call chain
- Identified data structure choices driving asymptotic behavior
- Cross-referenced with the invariant proof surface to verify that each
  recommendation preserves existing theorems

**Complexity model:** The audit uses standard big-O notation against the
following size parameters:
- *n* = number of kernel objects in the system
- *m* = number of slots in a CNode (or mappings in a VSpaceRoot)
- *t* = number of threads in the runnable queue
- *k* = number of edges in the CDT or service dependency graph

---

## 2. Architecture & Hot-Path Analysis

### Kernel hot paths (frequency order)

| Hot path                  | Typical frequency     | Current E2E complexity |
|---------------------------|-----------------------|------------------------|
| IPC endpoint send/receive | Every syscall          | O(1) dual-queue, O(t) legacy |
| Timer tick / preemption   | Every timer interrupt  | O(t) chooseBestRunnable |
| Capability lookup         | Every syscall          | O(m) slot scan         |
| VSpace translation        | Every page fault       | O(n + m)               |
| Schedule / yield          | On preemption/yield    | O(t) chooseBestRunnable |
| Capability mint/copy      | Object setup           | O(m) insert + lookup   |
| Service start/restart     | Lifecycle events       | O(n²) BFS cycle check  |

### Data structure summary

| Structure          | Representation             | Hot-path role           |
|--------------------|----------------------------|-------------------------|
| Object store       | `ObjId → Option KernelObject` (closure) | Every operation   |
| Runnable queue     | `List ThreadId`            | Schedule, IPC, preempt  |
| CNode slots        | `List (Slot × Capability)` | Cap lookup/insert       |
| Endpoint queue     | `List ThreadId` (legacy)   | IPC send/receive        |
| Intrusive queue    | TCB-embedded links         | Dual-queue IPC          |
| VSpace mappings    | `List (VAddr × PAddr)`     | Page fault path         |
| Service graph      | `ServiceId → Option Entry` | Lifecycle events        |
| CDT edges          | `List CapDerivationEdge`   | Revoke                  |
| Object index       | `List ObjId`               | ASID resolve, store     |

---

## 3. Finding F-P01: Object Store Closure-Chain Accumulation {#3-finding-f-p01}

**Severity:** CRITICAL
**Location:** `SeLe4n/Model/State.lean:156–173`
**Affected paths:** Every kernel transition that calls `storeObject`

### Description

The object store is represented as a pure function `ObjId → Option KernelObject`.
Each `storeObject` call wraps the previous function in a new closure:

```lean
let objects' : ObjId → Option KernelObject :=
  fun oid => if oid = id then some obj else st.objects oid
```

After *k* successive `storeObject` calls (common in IPC where sender TCB, receiver
TCB, and endpoint are all updated), every subsequent object lookup traverses a
chain of *k* nested `if` comparisons before reaching the base function. This is
O(k) per lookup where k = number of stores since the last structural
compaction.

The same pattern applies to `lifecycle.objectTypes` (line 163) and
`lifecycle.capabilityRefs` (lines 164–170), which are also function-typed.

### Impact

- A single `endpointSendDual` operation updates 2–3 objects (sender TCB, receiver
  TCB, endpoint). Subsequent lookups in the same syscall pay O(3) overhead.
- Over a long-running trace without compaction, *k* grows unboundedly.
- `timerTick` adds one closure per tick (line 209). After 1000 ticks, every
  object lookup traverses 1000 `if` branches.

### Recommendation

**Replace function-typed stores with `Lean.HashMap` (or `Std.HashMap`).**

```lean
-- Before:
objects : ObjId → Option KernelObject

-- After:
objects : Std.HashMap ObjId KernelObject
```

This gives O(1) amortized lookup and O(1) insert. The `DecidableEq` and
`Hashable` instances required for `ObjId` are trivially derivable from the
inner `Nat`. All existing theorems about `storeObject_objects_eq` and
`storeObject_objects_ne` can be re-proved against `HashMap.find?`/`HashMap.insert`
semantics. No invariant content changes — only the data structure representation.

**Alternative (less invasive):** Periodically compact the closure chain into
a `RBMap` at fixed intervals (e.g., every N stores). This is a runtime
optimization that preserves the existing proof structure entirely.

---

## 4. Finding F-P02: Runnable Queue — O(n) Insert/Remove/Membership {#4-finding-f-p02}

**Severity:** CRITICAL
**Location:** `SeLe4n/Kernel/IPC/Operations.lean:7–24`
**Affected paths:** Every IPC block/unblock, every preemption, every yield

### Description

Three operations on the runnable queue are O(t) where t = queue length:

| Operation         | Code                                       | Complexity |
|-------------------|--------------------------------------------|------------|
| `removeRunnable`  | `runnable.filter (· ≠ tid)` (line 8)       | O(t)       |
| `ensureRunnable`  | `tid ∈ runnable` membership (line 17)      | O(t)       |
| `rotateCurrentToBack` | `runnable.erase tid ++ [tid]` (line 122) | O(t)     |

Every IPC send that blocks the sender calls `removeRunnable`. Every IPC receive
that unblocks a sender calls `ensureRunnable`. Every timer preemption calls
`rotateCurrentToBack`. These are the three hottest scheduler operations.

Additionally, `chooseBestRunnableBy` (line 82) iterates the entire runnable list
for best-candidate selection — this is inherently O(t) and unavoidable for
a priority scan, but the data structure choice makes the constant factor worse.

### Recommendation

**Replace `List ThreadId` with a per-domain, per-priority run queue structure:**

```lean
structure RunQueue where
  byPriority : Std.HashMap Priority (Std.Queue ThreadId)
  membership : Std.HashSet ThreadId
  size : Nat
```

Benefits:
- `removeRunnable`: O(1) hash lookup + O(1) dequeue
- `ensureRunnable`: O(1) membership check
- `chooseBestRunnable`: O(1) — take from highest non-empty priority bucket
- `rotateCurrentToBack`: O(1) — dequeue head, enqueue tail of same bucket

The `runQueueUnique` invariant (`List.Nodup`) translates to the `HashSet`
membership invariant. The `queueCurrentConsistent` invariant translates to
`current ∈ membership`. All preservation theorems can be re-proved.

**Proof-compatible interim step:** Keep `List ThreadId` but add a shadow
`HashSet ThreadId` for O(1) membership checks. The list remains the proof
anchor; the hash set is the runtime fast path. Prove they agree via a
consistency invariant.

---

## 5. Finding F-P03: CNode Slot List — O(m) Lookup/Insert/Delete {#5-finding-f-p03}

**Severity:** HIGH
**Location:** `SeLe4n/Model/Object.lean:169–173, 622–799`
**Affected paths:** Every capability lookup, insert, delete, mint, copy, revoke

### Description

CNode slots are stored as `List (Slot × Capability)`. All operations are linear:

| Operation              | Implementation                      | Complexity |
|------------------------|-------------------------------------|------------|
| `CNode.lookup`         | `slots.find? (fst = slot)`          | O(m)       |
| `CNode.insert`         | filter old + prepend new            | O(m)       |
| `CNode.remove`         | `slots.filter (fst ≠ slot)`         | O(m)       |
| `CNode.revokeTargetLocal` | filter by target                 | O(m)       |
| `CNode.resolveSlot`    | bit arithmetic                      | O(1)       |

The slot-resolution step (`resolveSlot`) is already O(1), but the slot-to-capability
lookup that follows is O(m). In seL4, CNodes can have up to 2^(guardBits+radix)
slots. Even in the abstract model, a root CNode with 256 capabilities makes
every `cspaceLookupSlot` call traverse up to 256 list entries.

### Recommendation

**Replace `List (Slot × Capability)` with `Std.HashMap Slot Capability`:**

```lean
structure CNode where
  guard : Nat
  radix : Nat
  slots : Std.HashMap Slot Capability
```

- Lookup: O(1) amortized
- Insert: O(1) amortized
- Delete: O(1) amortized
- Revoke (by target): O(m) — inherently linear, but only occurs on revoke

The `slotsUnique` invariant becomes trivially satisfied (hash maps enforce
key uniqueness by construction). All 8 CNode theorems in `Object.lean:676–798`
can be simplified or become trivially true.

---

## 6. Finding F-P04: Legacy Endpoint Queue — O(n) Append {#6-finding-f-p04}

**Severity:** HIGH
**Location:** `SeLe4n/Kernel/IPC/Operations.lean:85–118`
**Affected paths:** `endpointSend` legacy path

### Description

The legacy IPC path uses `ep.queue ++ [sender]` (line 99) for FIFO enqueue,
which is O(n) list append.

### Current state

The dual-queue module (`DualQueue.lean`) already provides O(1) intrusive
queue operations (`endpointQueueEnqueue`, `endpointQueuePopHead`,
`endpointQueueRemoveDual`). The `endpointSendDual` function is the optimized
replacement.

### Recommendation

**Migrate all call sites from legacy `endpointSend`/`endpointReceive` to
`endpointSendDual`/`endpointReceiveDual`.** Then deprecate the legacy path.

The dual-queue design is already proven correct with O(1) enqueue, O(1)
dequeue, and O(1) arbitrary-element removal via `queuePPrev` metadata.
This finding is about completing the migration, not designing new data
structures.

---

## 7. Finding F-P05: VSpace Mapping List — O(m) Lookup {#7-finding-f-p05}

**Severity:** HIGH
**Location:** `SeLe4n/Model/Object.lean:430–620`
**Affected paths:** `vspaceLookup`, `vspaceMapPage`, `vspaceUnmapPage`

### Description

`VSpaceRoot.mappings` is `List (VAddr × PAddr)`. Every `lookup` calls
`mappings.find? (fst = vaddr)` — O(m) where m = number of page mappings.

On a real system with hundreds or thousands of page mappings per address space,
this is a significant bottleneck on the page-fault path.

Additionally, `mapPage` internally calls `lookup` to check for conflicts (line
441 of Object.lean), then the caller may call `lookup` again to verify — a
hidden redundancy.

### Recommendation

**Replace `List (VAddr × PAddr)` with `Std.HashMap VAddr PAddr`:**

```lean
structure VSpaceRoot where
  asid : ASID
  mappings : Std.HashMap VAddr PAddr
```

- `lookup`: O(1) amortized
- `mapPage`: O(1) amortized (conflict check + insert in one operation)
- `unmapPage`: O(1) amortized

All 9 VSpace theorems in `Object.lean:458–619` can be re-proved against
`HashMap` semantics. The round-trip theorems (`lookup_after_map`, etc.) map
directly to `HashMap.find?_insert` lemmas.

**H3 preparation:** When hierarchical page tables are implemented via
`VSpaceBackend`, the backend implementation should use a tree/trie structure
matching the real ARM64 4-level page table. The abstract `VSpaceRoot` can
remain `HashMap`-based for proof simplicity, with the backend providing the
hardware-faithful walk.

---

## 8. Finding F-P06: ASID Resolution — O(n) Linear Scan {#8-finding-f-p06}

**Severity:** CRITICAL
**Location:** `SeLe4n/Kernel/Architecture/VSpace.lean:21–25`
**Affected paths:** Every VSpace operation (`vspaceLookup`, `vspaceMapPage`, `vspaceUnmapPage`)

### Description

```lean
def resolveAsidRoot (st : SystemState) (asid : ASID) : Option (ObjId × VSpaceRoot) :=
  st.objectIndex.findSome? (fun oid =>
    match st.objects oid with
    | some (.vspaceRoot root) => if root.asid = asid then some (oid, root) else none
    | _ => none)
```

Every VSpace operation starts by scanning the entire `objectIndex` list to find
the VSpaceRoot with the matching ASID. This is O(n) where n = total number of
kernel objects ever stored (the index is append-only, never pruned).

On a system with 500+ objects, every page-fault-path VSpace lookup pays 500+
iterations just to locate the right VSpaceRoot — before the actual page lookup
even begins.

### Recommendation

**Add an ASID→ObjId index to `SystemState`:**

```lean
structure SystemState where
  ...
  asidTable : Std.HashMap ASID ObjId  -- NEW: O(1) ASID resolution
```

Maintain this table alongside `storeObject`: when a `.vspaceRoot` is stored,
update the ASID→ObjId mapping. When a VSpaceRoot is deleted, remove the entry.

`resolveAsidRoot` becomes:

```lean
def resolveAsidRoot (st : SystemState) (asid : ASID) : Option (ObjId × VSpaceRoot) :=
  match st.asidTable.find? asid with
  | some oid =>
    match st.objects oid with
    | some (.vspaceRoot root) => some (oid, root)
    | _ => none
  | none => none
```

Complexity drops from O(n) to O(1). The `vspaceAsidRootsUnique` invariant
(VSpaceInvariant.lean) is maintained by the table update logic. No existing
theorems need weakening.

---

## 9. Finding F-P07: Scheduler Best-Candidate Selection — O(t) Scan {#9-finding-f-p07}

**Severity:** HIGH
**Location:** `SeLe4n/Kernel/Scheduler/Operations.lean:82–106`
**Affected paths:** `schedule`, `handleYield`, `timerTick` (on preemption)

### Description

`chooseBestRunnableBy` iterates the entire runnable list to find the
highest-priority, earliest-deadline thread in the active domain:

```lean
private def chooseBestRunnableBy objects eligible runnable best :=
  match runnable with
  | [] => .ok best
  | tid :: rest => ... chooseBestRunnableBy objects eligible rest best'
```

This is O(t) on every schedule call. Additionally, `filterByDomain` (line 127)
is a separate O(t) pass that is not currently used by `chooseThread` but exists
as an alternate API.

### Recommendation

**Adopt per-priority bucket queues** (same recommendation as F-P02). With a
priority-indexed run queue, `chooseBestRunnable` becomes O(1): pick the head
of the highest non-empty priority bucket. EDF tie-breaking within a priority
band remains O(k) where k = threads at that priority, but k is typically 1–3
in real systems.

**Proof impact:** The `isBetterCandidate_irrefl` and `isBetterCandidate_asymm`
theorems remain valid. The `schedule_preserves_kernelInvariant` theorem chain
needs re-proof against the new data structure, but the invariant definitions
themselves do not change.

---

## 10. Finding F-P08: Service Dependency BFS — O(n²) Worst Case {#10-finding-f-p08}

**Severity:** HIGH
**Location:** `SeLe4n/Kernel/Service/Operations.lean:120–135`
**Affected paths:** `serviceRegisterDependency`, `serviceHasPathTo`

### Description

Cycle detection in the service graph uses BFS with two O(n) operations per
iteration:

```lean
let newFrontier := rest ++ deps.filter (· ∉ visited)  -- O(n) append + O(n²) membership
go newFrontier (node :: visited) fuel
```

- `· ∉ visited` is O(|visited|) per element, O(|deps| × |visited|) per iteration
- `rest ++ ...` is O(|rest|) list concatenation
- Total: O(n²) for a graph with n services

### Recommendation

**Replace `visited : List ServiceId` with `Std.HashSet ServiceId`:**

```lean
go frontier (visited : Std.HashSet ServiceId) fuel :=
  match frontier with
  | [] => ...
  | node :: rest =>
    if visited.contains node then go rest visited (fuel + 1)
    else
      let deps := lookupDeps st node
      let newDeps := deps.filter (fun d => !visited.contains d)
      go (newDeps ++ rest) (visited.insert node) fuel  -- DFS-order for cache locality
```

This reduces cycle detection from O(n²) to O(n + e) where e = dependency edges.

Also: prepend new deps to `rest` instead of appending (`newDeps ++ rest`
instead of `rest ++ newDeps`). This changes traversal order from BFS to DFS
but preserves the cycle-detection property and reduces append cost from O(|rest|)
to O(|newDeps|).

---

## 11. Finding F-P09: Information-Flow Projection CNode Filtering {#11-finding-f-p09}

**Severity:** HIGH
**Location:** `SeLe4n/Kernel/InformationFlow/Projection.lean:78–83`
**Affected paths:** `projectState`, `projectKernelObject`

### Description

Every state projection filters all CNode slots for observability:

```lean
| .cnode cn =>
    .cnode { cn with slots := cn.slots.filter (fun (_, cap) =>
      capTargetObservable ctx observer cap.target) }
```

For a system with 50 CNodes × 256 slots each, a single `projectState` call
performs ~12,800 label comparisons just for CNode filtering. Additionally,
`objectObservable` is evaluated redundantly across `projectObjects`,
`projectIrqHandlers`, `projectObjectIndex`, and `projectServiceStatus`.

### Recommendation

1. **Precompute an observable-object set** at the start of `projectState`:
   ```lean
   let observableOids : Std.HashSet ObjId :=
     st.objectIndex.foldl (fun acc oid =>
       if objectObservable ctx observer oid then acc.insert oid else acc) {}
   ```
   Then use `observableOids.contains` instead of re-evaluating `objectObservable`
   at every access point. This eliminates redundant label lookups.

2. **Lazy CNode projection:** Only project CNode slots when the CNode is
   actually accessed by a consumer, not eagerly during `projectState`. This
   amortizes the filtering cost.

3. **Cache projected objects:** Since `projectKernelObject` is proven idempotent
   (theorem at line 87), cache results to avoid re-filtering the same CNode
   multiple times.

---

## 12. Finding F-P10: storeObject objectIndex Membership Check {#12-finding-f-p10}

**Severity:** MEDIUM
**Location:** `SeLe4n/Model/State.lean:172`
**Affected paths:** Every `storeObject` call

### Description

```lean
let objectIndex' := if id ∈ st.objectIndex then st.objectIndex else id :: st.objectIndex
```

The `id ∈ st.objectIndex` check is O(n) where n = index length. This runs on
every `storeObject` call, including the 2–3 stores per IPC operation.

### Recommendation

**Add a companion `HashSet ObjId` to `objectIndex`** for O(1) membership
checks:

```lean
structure SystemState where
  ...
  objectIndex : List ObjId              -- proof anchor (monotonic, append-only)
  objectIndexSet : Std.HashSet ObjId    -- runtime O(1) membership
```

Maintain the invariant `∀ id, id ∈ objectIndex ↔ objectIndexSet.contains id`.
Use `objectIndexSet` for the membership check; prepend to `objectIndex` only
when the set reports absence.

---

## 13. Finding F-P11: Notification Duplicate Wait Check {#13-finding-f-p11}

**Severity:** MEDIUM
**Location:** `SeLe4n/Kernel/IPC/Operations.lean:225, 230`
**Affected paths:** `notificationWait`

### Description

```lean
if waiter ∈ ntfn.waitingThreads then .error .alreadyWaiting  -- O(n) membership
...
let ntfn' := { ntfn with waitingThreads := ntfn.waitingThreads ++ [waiter] }  -- O(n) append
```

Both operations are O(n) where n = number of waiting threads.

### Recommendation

The notification wait queue is smaller than endpoint queues (typically 1–5
threads), so this is lower priority. However, the same intrusive-queue
pattern from `DualQueue.lean` could be applied to notification objects.
Alternatively, the TCB's `ipcState` already tracks `blockedOnNotification`,
so the duplicate check could be replaced by checking `tcb.ipcState` directly
(O(1) lookup) rather than scanning the wait list.

---

## 14. Finding F-P12: withRunnableQueue Tail Recomputation {#14-finding-f-p12}

**Severity:** MEDIUM
**Location:** `SeLe4n/Model/State.lean:62–70`
**Affected paths:** Every runnable queue mutation

### Description

```lean
def SchedulerState.withRunnableQueue (sched : SchedulerState) (queue : List ThreadId) :=
  { sched with
    runnable := queue
    runnableHead := queue.head?     -- O(1)
    runnableTail := queue.getLast?   -- O(n) ← traverses entire list
  }
```

`queue.getLast?` is O(n). This runs after every `removeRunnable`,
`ensureRunnable`, and `rotateCurrentToBack`. The `runnableHead` and
`runnableTail` cache fields (WS-E7) are intended for O(1) access, but
they are recomputed from scratch on every queue mutation.

### Recommendation

If the runnable queue moves to a proper queue/deque structure (per F-P02),
`head` and `tail` become O(1) structural accesses and `withRunnableQueue` is
eliminated. In the interim, maintain `runnableTail` incrementally:
- On append: set tail to the appended element
- On remove: only recompute tail if the removed element was the tail

---

## 15. Finding F-P13: Lifecycle Triple-Lookup Pattern {#15-finding-f-p13}

**Severity:** MEDIUM
**Location:** `SeLe4n/Kernel/Lifecycle/Operations.lean:21–38`
**Affected paths:** `lifecycleRetypeObject`

### Description

```lean
match st.objects target with                              -- lookup 1
| some currentObj =>
    if st.lifecycle.objectTypes target = ... then          -- lookup 2
      match cspaceLookupSlot authority st with             -- lookup 3
      | .ok (authCap, st') =>
          if lifecycleRetypeAuthority authCap target then
            storeObject target newObj st'
```

Three separate state accesses for one operation. In the closure-chain model
(F-P01), each lookup may traverse the same chain.

### Recommendation

If F-P01 is addressed (HashMap-backed stores), this becomes three O(1) lookups
and is acceptable. No separate fix needed beyond F-P01.

---

## 16. Finding F-P14: CDT descendantsOf BFS Traversal {#16-finding-f-p14}

**Severity:** MEDIUM
**Location:** `SeLe4n/Model/Object.lean:888–896`
**Affected paths:** `cspaceRevokeCdt`, `cspaceRevokeCdtStrict`

### Description

CDT descendant collection uses BFS with `fuel = edges.length`:

```lean
def descendantsOf (cdt : CapDerivationTree) (root : CdtNodeId) : List CdtNodeId :=
  let fuel := cdt.edges.length
  go cdt [root] [] fuel
```

Each BFS step calls `childrenOf` which scans the full edge list — O(E) per
node. Total: O(N × E) where N = nodes, E = edges. For CDTs with many
derivations (e.g., after hundreds of mint/copy operations), this compounds.

### Recommendation

**Index the edge list by parent node** with a `HashMap CdtNodeId (List CdtNodeId)`.
`childrenOf` becomes O(1) lookup. BFS becomes O(N + E) total.

---

## 17. Positive Findings — Already Optimized {#17-positive-findings}

Several subsystems are well-optimized and deserve recognition:

### Dual-Queue IPC (DualQueue.lean) — OPTIMAL

The intrusive dual-queue design achieves O(1) for:
- `endpointQueuePopHead` — head dequeue via direct pointer
- `endpointQueueEnqueue` — tail enqueue + O(1) predecessor link
- `endpointQueueRemoveDual` — arbitrary-element removal via `queuePPrev`
- `endpointSendDual` — end-to-end O(1) fast path

The `queuePPrev` (pointer-to-previous-link) metadata eliminates the O(n)
predecessor scan that intrusive lists normally require. This is the most
performance-critical design decision in the codebase and it is correct.

### Architecture Adapters (Adapter.lean) — OPTIMAL

All three adapter operations (`adapterAdvanceTimer`, `adapterWriteRegister`,
`adapterReadMemory`) are O(1) in kernel state. Contract checks are deferred
to platform bindings.

### Information-Flow Policy (Policy.lean) — OPTIMAL

`securityFlowsTo` is O(1) pattern match on a 2-level
`Confidentiality × Integrity` lattice. Lattice properties (reflexive,
transitive, antisymmetric) are proven. No runtime overhead from the security
model itself — overhead comes from where/how often it is called (see F-P09).

### KernelM Monad (Prelude.lean) — OPTIMAL

The `KernelM` state monad is a direct `σ → Except ε (α × σ)` function with
no boxing, no heap allocation, and no indirection. `bind` is a single match.
This is the ideal representation for a formal kernel monad.

### `@[inline]` Annotations (Prelude.lean) — GOOD

All identifier conversion functions (`ofNat`, `toNat`, `toObjId`, `isReserved`,
`sentinel`) are `@[inline]`. This ensures zero overhead for typed identifier
wrappers at compile time.

---

## 18. Prioritized Recommendation Matrix {#18-prioritized-recommendation-matrix}

| Priority | Finding | Change                                  | Proof impact | Estimated effort |
|----------|---------|-----------------------------------------|--------------|------------------|
| P0       | F-P01   | HashMap-backed object store             | Re-prove storeObject lemmas | Medium |
| P0       | F-P02   | Priority-bucketed run queue + HashSet   | Re-prove scheduler invariants | High |
| P0       | F-P06   | ASID→ObjId table in SystemState         | Add consistency invariant | Low |
| P1       | F-P03   | HashMap-backed CNode slots              | Simplify slotsUnique proofs | Medium |
| P1       | F-P04   | Complete dual-queue migration           | Remove legacy proofs | Low |
| P1       | F-P05   | HashMap-backed VSpace mappings          | Re-prove VSpace round-trips | Medium |
| P1       | F-P07   | Priority buckets (shared with F-P02)    | Included in F-P02 | — |
| P1       | F-P08   | HashSet visited in service BFS          | Minimal proof impact | Low |
| P1       | F-P09   | Precompute observable set; lazy CNode proj | Re-prove projection lemmas | Medium |
| P2       | F-P10   | Shadow HashSet for objectIndex          | Add consistency invariant | Low |
| P2       | F-P11   | Check ipcState instead of wait-list scan| Adjust notificationWait proofs | Low |
| P2       | F-P12   | Incremental tail maintenance            | Trivial proof update | Low |
| P2       | F-P13   | Resolved by F-P01                       | — | — |
| P2       | F-P14   | Parent-indexed CDT edge map             | Re-prove CDT BFS termination | Medium |

---

## 19. Implementation Roadmap {#19-implementation-roadmap}

### Phase 1: Foundation (P0 items)

**Goal:** Eliminate O(n) from the three hottest paths.

1. **F-P06 (ASID table)** — Lowest effort, highest impact on page-fault path.
   Add `asidTable : Std.HashMap ASID ObjId` to `SystemState`. Update
   `storeObject` to maintain it. Rewrite `resolveAsidRoot`. Add consistency
   invariant + preservation theorem.

2. **F-P01 (Object store HashMap)** — Replace `objects : ObjId → Option
   KernelObject` with `Std.HashMap ObjId KernelObject`. This changes the
   representation but not the interface. All `storeObject_*` and `lookupObject`
   theorems need re-proof. Simultaneously replace `lifecycle.objectTypes` and
   `lifecycle.capabilityRefs` with HashMap representations.

3. **F-P02 (Run queue)** — Replace `runnable : List ThreadId` with a structured
   run queue. This is the largest change and should be done after F-P01 to
   avoid double-refactoring.

### Phase 2: Data Structures (P1 items)

**Goal:** Eliminate O(m) from capability and VSpace paths.

4. **F-P03 (CNode HashMap)** — Replace `slots : List (Slot × Capability)`.
5. **F-P05 (VSpace HashMap)** — Replace `mappings : List (VAddr × PAddr)`.
6. **F-P04 (Dual-queue migration)** — Deprecate legacy endpoint operations.
7. **F-P08 (Service BFS)** — HashSet visited set.
8. **F-P09 (Projection cache)** — Precomputed observable set.

### Phase 3: Polish (P2 items)

**Goal:** Remove remaining constant-factor overhead.

9. **F-P10** through **F-P14** — minor optimizations, individually low effort.

### Proof strategy for HashMap migration

The transition from function-typed stores to `HashMap` can be done
incrementally using a **bisimulation wrapper**:

1. Define `objects_fn (hm : HashMap ObjId KernelObject) : ObjId → Option KernelObject := hm.find?`
2. Prove `objects_fn (hm.insert id obj) = fun oid => if oid = id then some obj else objects_fn hm oid`
3. This one-time bisimulation lemma bridges all existing `storeObject_*` theorems
4. Once the bridge is established, downstream proofs use `HashMap` lemmas directly

This approach preserves the entire existing proof surface during transition
and allows incremental migration of theorems from closure-based reasoning to
HashMap-based reasoning.
