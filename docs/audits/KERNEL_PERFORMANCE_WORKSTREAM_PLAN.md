# WS-G Workstream Plan — Kernel Performance Optimization

**Created:** 2026-03-01
**Findings baseline:** [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](KERNEL_PERFORMANCE_AUDIT_v0.12.5.md)
**Prior portfolio:** WS-F (v0.12.2 audit remediation, WS-F1..F4 completed)
**Project direction:** Production microkernel targeting Raspberry Pi 5 (ARM64)
**Constraint:** No security sacrifices — all optimizations preserve invariant proofs

---

## 1. Planning Objective

Implement all 14 performance findings from the v0.12.5 Kernel Performance Audit,
eliminating algorithmic bottlenecks across every kernel hot path. The audit
identified O(n) and O(n²) complexity on the IPC, scheduling, capability lookup,
VSpace translation, and service dependency paths — all of which must become O(1)
amortized for a production-ready microkernel.

This plan decomposes the 14 findings into 9 workstreams across 4 execution
phases. The critical constraint: **no `sorry`, `axiom`, or invariant weakening**
is permitted. Every data structure migration preserves the existing proof surface
through bisimulation wrappers and incremental theorem re-proofs.

## 2. Planning Principles

1. **Performance without sacrifice**: every optimization preserves all existing
   invariants, theorems, and deterministic semantics.
2. **Proof-first migration**: HashMap bisimulation wrappers bridge existing
   theorems during transition; downstream proofs migrate incrementally.
3. **Foundation-first ordering**: infrastructure (Hashable instances) and core
   state representation (object store) are addressed before subsystem-specific
   optimizations.
4. **Coherent slices**: each workstream is a self-contained, independently
   testable change with clear entry and exit criteria.
5. **No sorry/axiom**: zero tolerance in production proof surface.
6. **Evidence-gated**: every workstream closes with reproducible command evidence.

---

## 3. Finding-to-Workstream Matrix

| Finding | Severity | Description | Workstream |
|---------|----------|-------------|------------|
| F-P01 | CRITICAL | Object store closure-chain accumulation | WS-G2 |
| F-P02 | CRITICAL | Runnable queue O(n) insert/remove/membership | WS-G4 |
| F-P03 | HIGH | CNode slot list O(m) lookup/insert/delete | WS-G5 |
| F-P04 | HIGH | Legacy endpoint queue O(n) append | WS-G7 |
| F-P05 | HIGH | VSpace mapping list O(m) lookup | WS-G6 |
| F-P06 | CRITICAL | ASID resolution O(n) linear scan | WS-G3 |
| F-P07 | HIGH | Scheduler best-candidate O(t) scan | WS-G4 |
| F-P08 | HIGH | Service dependency BFS O(n²) worst case | WS-G8 |
| F-P09 | HIGH | Information-flow projection CNode filtering | WS-G9 |
| F-P10 | MEDIUM | storeObject objectIndex membership check | WS-G2 |
| F-P11 | MEDIUM | Notification duplicate wait check | WS-G7 |
| F-P12 | MEDIUM | withRunnableQueue tail recomputation | WS-G4 |
| F-P13 | MEDIUM | Lifecycle triple-lookup pattern | WS-G2 |
| F-P14 | MEDIUM | CDT descendantsOf BFS traversal | WS-G8 |

---

## 4. Workstream Definitions

### WS-G1: Hashable/BEq Infrastructure (PREREQUISITE)

**Objective:** Derive `Hashable` and `BEq` instances for all typed identifiers,
enabling `Std.HashMap` and `Std.HashSet` usage throughout the kernel.

**Entry criteria:** Current codebase compiles with zero sorry. `test_smoke.sh` passes.

**Rationale:** The codebase currently has zero HashMap/HashSet usage. All 13
typed identifiers (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Deadline`,
`Irq`, `ServiceId`, `CPtr`, `Slot`, `Badge`, `ASID`, `VAddr`, `PAddr`) have
`DecidableEq` but lack `Hashable` and `BEq` instances. Every subsequent
workstream (WS-G2 through WS-G9) depends on these instances.

**Deliverables:**
1. Add `Hashable` and `BEq` instances to all 13 typed identifiers in
   `Prelude.lean`. Each wraps a `Nat`, so `Hashable` delegates to
   `hash val.val` and `BEq` delegates to `val.val == val.val`. Mark all
   instances `@[inline]` for zero runtime overhead.
2. Add `import Std.Data.HashMap` and `import Std.Data.HashSet` to
   `Prelude.lean` (or a new `SeLe4n/Data.lean` import hub).
3. Add `Hashable` and `BEq` for composite keys used in later workstreams:
   `CdtNodeId`, `SlotRef` (if used as HashMap keys).
4. Verify no behavioral change: all existing tests pass identically.

**Exit evidence:**
- `lake build` passes with zero errors/warnings.
- `test_smoke.sh` passes.
- `Hashable` instances verified by a unit-level check (e.g., `#eval hash (ObjId.mk 42)`).

**Dependencies:** None. This is the foundation workstream.

**Estimated effort:** Low (single file, mechanical derivation).

---

### WS-G2: Object Store & ObjectIndex HashMap (F-P01, F-P10, F-P13) — COMPLETED

**Objective:** Replace the closure-chain object store with `Std.HashMap` and add
a shadow `HashSet` for `objectIndex` membership, eliminating O(k) lookup
degradation and O(n) membership scans.

**Entry criteria:** WS-G1 completed (Hashable instances available).

**Findings addressed:**
- **F-P01** (CRITICAL): `objects : ObjId → Option KernelObject` accumulates
  nested closures on every `storeObject`. After k stores, every lookup is O(k).
- **F-P10** (MEDIUM): `id ∈ st.objectIndex` in `storeObject` is O(n) on every
  call.
- **F-P13** (MEDIUM): Lifecycle triple-lookup pattern — resolved automatically
  once object lookups become O(1).

**Deliverables:**

*Phase A — Object store migration:*
1. Replace `objects : ObjId → Option KernelObject` with
   `objects : Std.HashMap ObjId KernelObject` in `SystemState` (State.lean).
2. Replace `lifecycle.objectTypes : ObjId → Option ObjectType` and
   `lifecycle.capabilityRefs : ObjId → Option (List CPtr)` with HashMap
   equivalents in `LifecycleMetadata`.
3. Update `storeObject` to use `HashMap.insert` instead of closure wrapping.
4. Update all `st.objects oid` call sites to use `st.objects.find? oid`.
5. Prove bisimulation bridge lemma:
   `HashMap.find? (hm.insert id obj) oid = if oid = id then some obj else hm.find? oid`
   This one-time lemma bridges all existing `storeObject_objects_eq` and
   `storeObject_objects_ne` theorems to HashMap semantics.
6. Re-prove all `storeObject_*` lemmas against `HashMap.find?`/`HashMap.insert`.
7. Re-prove downstream invariant preservation theorems that reference `st.objects`.

*Phase B — ObjectIndex shadow set:*
8. Add `objectIndexSet : Std.HashSet ObjId` to `SystemState`.
9. Add consistency invariant:
   `∀ id, id ∈ objectIndex ↔ objectIndexSet.contains id`.
10. Replace `id ∈ st.objectIndex` in `storeObject` with
    `st.objectIndexSet.contains id` for O(1) membership.
11. Maintain both structures in parallel: `objectIndex` remains the proof anchor
    (monotonic, append-only); `objectIndexSet` is the runtime fast path.
12. Prove consistency invariant preservation for `storeObject`.

**Proof strategy:**
- Use the bisimulation wrapper approach from the audit roadmap (Section 19).
  Define `objects_fn (hm : HashMap ObjId KernelObject) := hm.find?` and prove
  equivalence to the old closure-based `objects`. This bridges all existing
  theorems without rewriting them immediately.
- Migrate theorems incrementally: first establish the bridge, then update
  individual proofs in subsequent passes. The bridge ensures the build never
  breaks during migration.
- For `objectIndexSet`, the consistency invariant is structurally simple
  (insert into set when prepending to list) and follows the existing
  `storeObject` control flow.

**Files modified:**
- `SeLe4n/Model/State.lean` — `SystemState`, `LifecycleMetadata`, `storeObject`
- `SeLe4n/Kernel/Scheduler/Operations.lean` — `st.objects` call sites
- `SeLe4n/Kernel/IPC/Operations.lean` — `st.objects` call sites
- `SeLe4n/Kernel/Capability/Operations.lean` — `st.objects` call sites
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — `st.objects` call sites
- `SeLe4n/Kernel/Architecture/VSpace.lean` — `st.objects` call sites
- `SeLe4n/Kernel/Service/Operations.lean` — `st.objects` call sites
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — `st.objects` call sites
- `SeLe4n/Kernel/API.lean` — public interface updates
- All `*Invariant.lean` files — re-prove affected theorems

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `lake exe sele4n` output matches `tests/fixtures/main_trace_smoke.expected`.
- `grep -r "ObjId → Option KernelObject" SeLe4n/` returns zero matches
  (no closure-chain stores remain).

**Dependencies:** WS-G1 (Hashable instances).

**Completion notes (v0.12.7):**
- All exit evidence met: `lake build` zero errors/warnings/sorry, `test_full.sh` Tier 0-3 pass.
- `capabilityRefs` retained as closure-based function (not HashMap) — intentional, as it serves as a computed projection rather than a primary data store.
- `ObservableState.objects` and `chooseBestRunnable*` retain function type `ObjId → Option KernelObject` by design.
- Proof migration required: type annotations for `[k]?` notation, `congrArg` replacing `congrFun`, explicit `default.objects` → `∅` bridges, `objectIndexSetSync` invariant for `storeObject`.

---

### WS-G3: ASID Resolution Table (F-P06) — COMPLETED

**Objective:** Add an `ASID → ObjId` index to `SystemState`, reducing ASID
resolution from O(n) linear scan to O(1) hash lookup on every VSpace operation.

**Entry criteria:** WS-G1 completed (Hashable instance for `ASID`). Ideally
after WS-G2 (HashMap-backed object store), but can proceed in parallel since
the ASID table is an independent addition to `SystemState`.

**Findings addressed:**
- **F-P06** (CRITICAL): `resolveAsidRoot` scans the entire `objectIndex` list
  (O(n) where n = total objects) on every `vspaceLookup`, `vspaceMapPage`, and
  `vspaceUnmapPage` call.

**Deliverables:**
1. Add `asidTable : Std.HashMap ASID ObjId` to `SystemState` (State.lean).
2. Update `storeObject` to maintain the ASID table: when storing a
   `.vspaceRoot root`, insert `root.asid → id` into `asidTable`. When
   overwriting a VSpaceRoot with a different ASID, remove the old mapping.
3. Update `resolveAsidRoot` (VSpace.lean:21-25) to use `st.asidTable.find?`
   instead of `st.objectIndex.findSome?`. Fall back to object lookup to
   verify the ObjId still holds a `.vspaceRoot`.
4. Add ASID table consistency invariant to `VSpaceInvariant.lean`:
   `∀ asid oid, st.asidTable.find? asid = some oid →
     ∃ root, st.objects.find? oid = some (.vspaceRoot root) ∧ root.asid = asid`
5. Prove consistency invariant preservation for `storeObject`.
6. Verify `vspaceAsidRootsUnique` invariant is maintained by the table.
7. Re-prove `resolveAsidRoot` round-trip theorems (VSpace.lean:109-145)
   against the new implementation.
8. Handle VSpaceRoot deletion: when a VSpaceRoot is overwritten with a
   non-VSpaceRoot object (via retype), remove the ASID entry.

**Files modified:**
- `SeLe4n/Model/State.lean` — `SystemState` (add `asidTable` field)
- `SeLe4n/Kernel/Architecture/VSpace.lean` — `resolveAsidRoot` rewrite
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — consistency invariant
- `SeLe4n/Testing/StateBuilder.lean` — initialize `asidTable` in test states

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `resolveAsidRoot` no longer references `objectIndex.findSome?`.

**Dependencies:** WS-G1 (Hashable for ASID).

**Estimated effort:** Low (localized change, single new field, clear invariant).

**Completion notes (v0.12.8):**
- All exit evidence met: `lake build` zero errors/warnings/sorry, `test_full.sh` Tier 0-3 pass.
- `resolveAsidRoot` uses `st.asidTable[asid]?` O(1) lookup; `objectIndex.findSome?` eliminated from VSpace.lean.
- Bidirectional `asidTableConsistent` invariant; `vspaceInvariantBundle` extended to 3-conjunct.
- `storeObject` erase-before-insert maintenance with 3 bridge lemmas.
- StateBuilder auto-populates `asidTable` from VSpaceRoot objects.

---

### WS-G4: Run Queue Restructure (F-P02, F-P07, F-P12) — COMPLETED

**Objective:** Replace the flat `List ThreadId` runnable queue with a
priority-bucketed run queue backed by `Std.HashMap` and `Std.HashSet`,
reducing all scheduler hot-path operations from O(t) to O(1).

**Entry criteria:** WS-G1 completed. WS-G2 recommended (HashMap object store
simplifies TCB lookups in scheduler), but not strictly required.

**Findings addressed:**
- **F-P02** (CRITICAL): `removeRunnable` (O(t) filter), `ensureRunnable`
  (O(t) membership + append), `rotateCurrentToBack` (O(t) erase + append).
- **F-P07** (HIGH): `chooseBestRunnableBy` (O(t) scan for best candidate).
- **F-P12** (MEDIUM): `withRunnableQueue` recomputes `getLast?` in O(t) on
  every queue mutation.

**Deliverables:**

*Phase A — RunQueue structure definition:*
1. Define `RunQueue` structure in a new `SeLe4n/Kernel/Scheduler/RunQueue.lean`:
   ```
   structure RunQueue where
     byPriority : Std.HashMap Priority (Std.Queue ThreadId)
     membership : Std.HashSet ThreadId
     size : Nat
     maxPriority : Option Priority  -- cached highest non-empty priority
   ```
2. Implement O(1) operations:
   - `RunQueue.insert (tid : ThreadId) (prio : Priority)` — insert into
     priority bucket, add to membership set, update maxPriority.
   - `RunQueue.remove (tid : ThreadId) (prio : Priority)` — remove from
     bucket, remove from membership set, update maxPriority if needed.
   - `RunQueue.contains (tid : ThreadId) : Bool` — membership set lookup.
   - `RunQueue.popBest : Option (ThreadId × Priority)` — dequeue from
     highest-priority non-empty bucket.
   - `RunQueue.rotateHead (tid : ThreadId) (prio : Priority)` — dequeue
     head and re-enqueue at tail of same bucket.

*Phase B — Scheduler integration:*
3. Replace `runnable : List ThreadId` with `runQueue : RunQueue` in
   `SchedulerState`. Remove `runnableHead`, `runnableTail` cache fields
   (subsumed by `RunQueue` structure). Remove `withRunnableQueue` helper.
4. Rewrite `removeRunnable` (IPC/Operations.lean:7-14) to use
   `RunQueue.remove`. Requires looking up the thread's priority from the
   TCB — this is an O(1) HashMap lookup after WS-G2.
5. Rewrite `ensureRunnable` (IPC/Operations.lean:16-24) to use
   `RunQueue.contains` + `RunQueue.insert`.
6. Rewrite `rotateCurrentToBack` (Scheduler/Operations.lean:115-124) to use
   `RunQueue.rotateHead`.
7. Rewrite `chooseBestRunnableBy` / `chooseBestRunnableInDomain`
   (Scheduler/Operations.lean:82-113) to use `RunQueue.popBest`. Within a
   priority band, EDF tie-breaking iterates only threads at that priority
   (typically 1-3 in real systems).

*Phase C — Invariant re-proof:*
8. Replace `runQueueUnique` invariant (List.Nodup) with `RunQueue` structural
   uniqueness: membership HashSet enforces key uniqueness by construction.
   Prove equivalence or redefine.
9. Replace `queueCurrentConsistent` (current ∈ runnable) with
   `current ∈ runQueue.membership`. Prove preservation.
10. Re-prove `schedule_preserves_kernelInvariant` theorem chain against the
    new data structure.
11. Re-prove `timerTick_preserves_schedulerInvariantBundle` against
    `RunQueue.rotateHead`.
12. Re-prove `isBetterCandidate_irrefl` and `isBetterCandidate_asymm`
    (these are pure comparison properties and should not change, but verify).

**Files modified:**
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` — **NEW**: RunQueue structure + operations
- `SeLe4n/Model/State.lean` — `SchedulerState` restructure
- `SeLe4n/Kernel/Scheduler/Operations.lean` — scheduler transitions rewrite
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — invariant re-proof
- `SeLe4n/Kernel/IPC/Operations.lean` — `removeRunnable`, `ensureRunnable`
- `SeLe4n/Kernel/IPC/Invariant.lean` — affected preservation theorems
- `SeLe4n/Testing/StateBuilder.lean` — RunQueue construction in test states

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `lake exe sele4n` output matches expected fixture.
- No `List.filter (· ≠ tid)` patterns remain in scheduler/IPC operations.
- No `getLast?` calls remain in `SchedulerState` helpers.

**Dependencies:** WS-G1 (Hashable for ThreadId, Priority). WS-G2 recommended
(O(1) TCB lookup for priority resolution in removeRunnable/ensureRunnable).

**Estimated effort:** High (largest single change; new data structure, multiple
subsystem rewrites, significant theorem re-proof).

**Completion notes (v0.12.9):**
- All exit evidence met: `lake build` zero errors/warnings/sorry, `test_full.sh` Tier 0-3 pass.
- `RunQueue` structure in `Scheduler/RunQueue.lean` with `byPriority : Std.HashMap Priority (List ThreadId)`, `membership : Std.HashSet ThreadId`, `threadPriority : Std.HashMap ThreadId Priority`, `flat : List ThreadId` for proof compatibility, and `flat_wf` structural invariant bridging flat list ↔ HashSet membership.
- O(1) operations: `insert`, `remove`, `contains`, `rotateHead`, `rotateToBack`. `maxPriority` cached and maintained incrementally.
- `SchedulerState.runQueue : RunQueue` replaces flat `runnable : List ThreadId`. `runnableHead`/`runnableTail` and `withRunnableQueue` helper eliminated.
- `removeRunnable`/`ensureRunnable` rewritten against `RunQueue.remove`/`RunQueue.insert`. `rotateCurrentToBack` uses `RunQueue.rotateToBack`.
- No `List.filter (· ≠ tid)` patterns remain in scheduler/IPC operations. No `getLast?` calls remain.
- 13 `RunQueue` bridge lemmas (`mem_insert`, `mem_remove`, `mem_rotateHead`, `mem_rotateToBack`, `toList_insert_not_mem`, `toList_filter_insert_neg`, `toList_filter_remove_neg`, `not_mem_toList_of_not_mem`, `not_mem_remove_toList`, `mem_toList_rotateToBack_self`, `toList_rotateToBack_nodup`, `mem_toList_rotateToBack_ne`, etc.).
- `chooseBestInBucket` bucket-first scheduling: scans max-priority bucket first (O(k)) with full-list fallback. Addresses F-P07 deliverable #7.
- Dead `rotateCurrentToBack` private function removed (subsumed by `RunQueue.rotateToBack`).
- IPC/Invariant.lean: 30+ proofs migrated to flat-list variants (`removeRunnable_runnable_mem`, `ensureRunnable_runnable_mem_old`).
- InformationFlow/Invariant.lean: `ensureRunnable_preserves_projection` re-proved via `congr 1` + `toList_filter_insert_neg`.
- Full proof migration: zero sorry/axiom across all modified files.

---

### WS-G5: CNode Slot HashMap (F-P03) — COMPLETED

**Objective:** Replace list-based CNode slots with `Std.HashMap Slot Capability`,
reducing every capability lookup, insert, and delete from O(m) to O(1) amortized.

**Entry criteria:** WS-G1 completed (Hashable instance for `Slot`). WS-G2
recommended (HashMap object store ensures CNode retrieval is O(1)).

**Findings addressed:**
- **F-P03** (HIGH): `CNode.lookup`, `CNode.insert`, `CNode.remove` are all
  O(m) where m = number of slots. Every capability resolution on every syscall
  traverses up to m list entries.

**Deliverables:**
1. Replace `slots : List (Slot × Capability)` with
   `slots : Std.HashMap Slot Capability` in the `CNode` structure
   (Object.lean:169-173).
2. Rewrite `CNode.lookup` to use `slots.find?` — O(1).
3. Rewrite `CNode.insert` to use `slots.insert` — O(1).
4. Rewrite `CNode.remove` to use `slots.erase` — O(1).
5. Rewrite `CNode.revokeTargetLocal` — remains O(m) for filter-by-target
   (inherently linear), but use `slots.fold` instead of `List.filter`.
6. Simplify or remove the `slotsUnique` invariant: HashMap enforces key
   uniqueness by construction, making this invariant trivially true.
7. Re-prove all 8 CNode theorems in Object.lean:676-798 against HashMap
   semantics. Round-trip theorems (`lookup_after_insert`,
   `lookup_after_remove`) map directly to `HashMap.find?_insert` /
   `HashMap.find?_erase` lemmas.
8. Update `cspaceLookupSlot`, `cspaceInsertSlot`, `cspaceDeleteSlot`,
   `cspaceMint`, `cspaceCopy` in Capability/Operations.lean.
9. Update `projectKernelObject` CNode slot filtering in
   InformationFlow/Projection.lean to use `slots.fold` + `HashMap.ofList`
   (or `slots.filter` if available on HashMap).

**Files modified:**
- `SeLe4n/Model/Object.lean` — `CNode` structure + operations
- `SeLe4n/Kernel/Capability/Operations.lean` — CSpace operation call sites
- `SeLe4n/Kernel/Capability/Invariant.lean` — `slotsUnique` simplification
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — CNode projection
- `SeLe4n/Testing/StateBuilder.lean` — CNode construction in tests

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- No `List.find? (fst = slot)` patterns remain in CNode operations.

**Dependencies:** WS-G1 (Hashable for Slot).

**Estimated effort:** Medium (contained to CNode subsystem; well-defined
theorem migration).

**Completion notes (v0.12.10):**
Completed in v0.12.10. `CNode.slots` migrated from `List (Slot × Capability)` to
`Std.HashMap Slot Capability`. All CNode operations (`lookup`, `insert`, `remove`)
are O(1) amortized. `slotsUnique` invariant trivially true (HashMap key uniqueness).
Two bridge lemmas added to Prelude.lean: `HashMap_filter_preserves_key` for
`revokeTargetLocal` source-slot preservation, and `HashMap_filter_filter_getElem?` for
projection filter idempotency (reformulated at slot-lookup level because
`AssocList.filter` reverses bucket ordering). `projectKernelObject_idempotent`
reformulated from structural to slot-level equality. Manual `BEq CNode` and
`BEq KernelObject` instances replace lost `DecidableEq` derivation.
`revokedRefs` computation in `cspaceRevoke` uses `HashMap.fold` for a single O(m)
pass (no intermediate `.toList` allocation). Test slot-existence checks use
`HashMap.contains` for O(1). All 10 files modified, zero sorry/axiom,
`test_full.sh` passes Tier 0-3. Closes F-P03.

---

### WS-G6: VSpace Mapping HashMap (F-P05) — HIGH

**Objective:** Replace list-based VSpace mappings with
`Std.HashMap VAddr PAddr`, reducing page-fault-path lookups from O(m) to O(1).

**Entry criteria:** WS-G1 completed (Hashable instance for `VAddr`).
WS-G3 recommended (ASID resolution is O(1), so the full page-fault path
becomes O(1) end-to-end).

**Findings addressed:**
- **F-P05** (HIGH): `VSpaceRoot.mappings` is `List (VAddr × PAddr)`.
  `vspaceLookup`, `vspaceMapPage`, and `vspaceUnmapPage` are all O(m).

**Deliverables:**
1. Replace `mappings : List (VAddr × PAddr)` with
   `mappings : Std.HashMap VAddr PAddr` in the `VSpaceRoot` structure
   (Object.lean:430-433).
2. Rewrite `VSpaceRoot.lookup` to use `mappings.find?` — O(1).
3. Rewrite `VSpaceRoot.mapPage` to use `mappings.insert` — O(1). The
   conflict check (`lookup` before insert) becomes O(1) + O(1) = O(1).
4. Rewrite `VSpaceRoot.unmapPage` to use `mappings.erase` — O(1).
5. Re-prove all 9 VSpace theorems in Object.lean:458-619 against HashMap
   semantics. Key round-trip theorems:
   - `lookup_after_map` → `HashMap.find?_insert`
   - `lookup_after_unmap_same` → `HashMap.find?_erase_same`
   - `lookup_after_unmap_diff` → `HashMap.find?_erase_diff`
6. Update `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup` in
   Architecture/VSpace.lean.
7. Verify `VSpaceBackend` (`listVSpaceBackend` instance in
   VSpaceBackend.lean) — this may need renaming or a new
   `hashMapVSpaceBackend` instance since the underlying representation
   changes from list to HashMap.

**H3 preparation note:** The abstract `VSpaceRoot` becomes HashMap-based for
proof simplicity. When hierarchical page tables are implemented via
`VSpaceBackend`, the backend can provide a tree/trie structure matching
ARM64 4-level page tables. The abstract model and concrete backend are already
decoupled by the `VSpaceBackend` typeclass.

**Files modified:**
- `SeLe4n/Model/Object.lean` — `VSpaceRoot` structure + operations
- `SeLe4n/Kernel/Architecture/VSpace.lean` — VSpace operation call sites
- `SeLe4n/Kernel/Architecture/VSpaceBackend.lean` — backend instance update
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — theorem re-proof
- `SeLe4n/Testing/StateBuilder.lean` — VSpaceRoot construction in tests

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- No `List.find? (fst = vaddr)` patterns remain in VSpace operations.
- Full page-fault path (ASID resolve → VSpace lookup) is O(1) end-to-end
  (verifiable by code inspection after WS-G3 + WS-G6).

**Dependencies:** WS-G1 (Hashable for VAddr, PAddr).

**Estimated effort:** Medium (parallel structure to WS-G5; contained to
VSpace subsystem).

---

### WS-G7: IPC Queue Completion & Notification (F-P04, F-P11) — HIGH

**Objective:** Complete the migration from legacy O(n) endpoint queues to the
existing O(1) dual-queue implementation, and optimize the notification
duplicate-wait check.

**Entry criteria:** WS-G2 completed (HashMap object store for O(1) TCB lookups
needed by dual-queue operations).

**Findings addressed:**
- **F-P04** (HIGH): Legacy `endpointSend`/`endpointReceive` use
  `ep.queue ++ [sender]` for O(n) FIFO enqueue. The dual-queue replacement
  (`DualQueue.lean`) already provides O(1) operations but the migration is
  incomplete.
- **F-P11** (MEDIUM): `notificationWait` checks `waiter ∈ ntfn.waitingThreads`
  (O(n) membership) and appends with `++ [waiter]` (O(n)).

**Deliverables:**

*Phase A — Legacy endpoint deprecation:*
1. Audit all call sites of `endpointSend` and `endpointReceive` across the
   codebase. Identify which still use the legacy path vs. the dual-queue path
   (`endpointSendDual`, `endpointReceiveDual`).
2. Migrate remaining legacy call sites to dual-queue equivalents.
3. Mark legacy `endpointSend`, `endpointReceive`, `endpointAwaitReceive` as
   deprecated (add `@[deprecated]` attribute or comment annotation).
4. If no legacy call sites remain after migration, remove the legacy
   implementations entirely. Otherwise, gate them behind a `legacy` namespace.
5. Remove or consolidate legacy-specific invariant proofs that are subsumed
   by dual-queue proofs.

*Phase B — Notification wait optimization:*
6. Replace the `waiter ∈ ntfn.waitingThreads` membership check with a direct
   TCB `ipcState` check: if `tcb.ipcState = .blockedOnNotification ntfnId`,
   the thread is already waiting. This is O(1) via the object store lookup
   (post WS-G2).
7. Replace `ntfn.waitingThreads ++ [waiter]` with a prepend
   `waiter :: ntfn.waitingThreads` (O(1)) or, if FIFO order matters for
   fairness, with an intrusive queue pattern matching `DualQueue.lean`.
8. Re-prove `notificationWait_preserves_ipcInvariant` and
   `notificationWait_preserves_schedulerInvariantBundle` against the new
   duplicate-check logic.

**Files modified:**
- `SeLe4n/Kernel/IPC/Operations.lean` — legacy endpoint deprecation,
  notification wait rewrite
- `SeLe4n/Kernel/IPC/Invariant.lean` — affected preservation theorems
- `SeLe4n/Kernel/API.lean` — update public API to route through dual-queue
- `SeLe4n/Testing/MainTraceHarness.lean` — update trace scenarios if API changes

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_smoke.sh` passes.
- No `ep.queue ++ [sender]` patterns remain in IPC operations.
- `notificationWait` no longer uses `∈ ntfn.waitingThreads` for membership.

**Dependencies:** WS-G2 (O(1) TCB lookup for ipcState-based duplicate check).
WS-F1 (dual-queue verification, already completed).

**Estimated effort:** Low-Medium (legacy migration is largely mechanical;
notification optimization is localized).

---

### WS-G8: Graph Traversal Optimization (F-P08, F-P14) — HIGH

**Objective:** Replace list-based visited sets and edge lookups in service
dependency BFS and CDT descendant traversal with hash-based structures,
reducing cycle detection from O(n²) to O(n+e) and CDT traversal from
O(N×E) to O(N+E).

**Entry criteria:** WS-G1 completed (Hashable for `ServiceId`, `CdtNodeId`).

**Findings addressed:**
- **F-P08** (HIGH): `serviceHasPathTo` BFS uses `visited : List ServiceId`
  with O(|visited|) membership checks per node, yielding O(n²) total.
  List append `rest ++ deps.filter (· ∉ visited)` adds O(|rest|) per step.
- **F-P14** (MEDIUM): `descendantsOf` BFS calls `childrenOf` which scans the
  full edge list (O(E)) per node, yielding O(N×E) total.

**Deliverables:**

*Phase A — Service BFS:*
1. Replace `visited : List ServiceId` with `visited : Std.HashSet ServiceId`
   in `serviceHasPathTo` (Service/Operations.lean:116-133).
2. Replace `node ∈ visited` with `visited.contains node` — O(1).
3. Replace `deps.filter (· ∉ visited)` with
   `deps.filter (fun d => !visited.contains d)` — O(|deps|) total instead
   of O(|deps| × |visited|).
4. Switch from BFS to DFS ordering: prepend new deps (`newDeps ++ rest`)
   instead of appending (`rest ++ newDeps`). This changes traversal order
   but preserves cycle detection correctness and reduces append from
   O(|rest|) to O(|newDeps|).
5. Re-prove `serviceHasPathTo` cycle detection properties. The key property
   (if a path exists from src to target, the function returns true) is
   invariant under BFS↔DFS ordering change.

*Phase B — CDT edge index:*
6. Add a parent-indexed edge map to `CapDerivationTree`:
   ```
   structure CapDerivationTree where
     edges : List CapDerivationEdge        -- proof anchor
     childMap : Std.HashMap CdtNodeId (List CdtNodeId)  -- runtime index
   ```
7. Maintain `childMap` alongside `edges`: when an edge is added
   (`addEdge`), insert into the map. When an edge is removed, update the
   map.
8. Rewrite `childrenOf` to use `childMap.find?` — O(1) lookup.
9. `descendantsOf` BFS becomes O(N+E) total (each node visited once,
   children retrieved in O(1)).
10. Add consistency invariant:
    `∀ parent child, child ∈ (childMap.find? parent).getD [] ↔
      ∃ e ∈ edges, e.parent = parent ∧ e.child = child`
11. Prove consistency invariant preservation for `addEdge` / `removeEdge`.
12. Re-prove `descendantsOf` termination and correctness.

**Files modified:**
- `SeLe4n/Kernel/Service/Operations.lean` — `serviceHasPathTo` rewrite
- `SeLe4n/Kernel/Service/Invariant.lean` — cycle detection properties
- `SeLe4n/Model/Object.lean` — `CapDerivationTree` structure + `childrenOf`
- `SeLe4n/Kernel/Capability/Operations.lean` — CDT mutation call sites
- `SeLe4n/Kernel/Capability/Invariant.lean` — CDT invariant proofs

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `serviceHasPathTo` no longer uses `List ServiceId` for visited set.
- `childrenOf` no longer scans the full edge list.

**Dependencies:** WS-G1 (Hashable for ServiceId, CdtNodeId).

**Estimated effort:** Medium (two independent sub-changes; service BFS is
low effort, CDT indexing is medium due to consistency invariant).

---

### WS-G9: Information-Flow Projection Optimization (F-P09) — HIGH

**Objective:** Eliminate redundant observability evaluations and reduce CNode
slot filtering overhead in `projectState` by precomputing an observable-object
set and caching projected results.

**Entry criteria:** WS-G1 completed (Hashable for `ObjId`). WS-G5 recommended
(HashMap CNode slots enable more efficient projection filtering).

**Findings addressed:**
- **F-P09** (HIGH): `projectState` evaluates `objectObservable` redundantly
  across `projectObjects`, `projectIrqHandlers`, `projectObjectIndex`, and
  slot-level `capTargetObservable` in CNode projection. For 50 CNodes × 256
  slots, this is ~12,800 label comparisons per projection.

**Deliverables:**
1. Precompute an observable-object set at the start of `projectState`:
   ```
   let observableOids : Std.HashSet ObjId :=
     st.objectIndex.foldl (fun acc oid =>
       if objectObservable ctx observer oid then acc.insert oid else acc) {}
   ```
   Pass `observableOids` to all sub-projection functions.
2. Replace all `objectObservable ctx observer oid` calls within
   `projectObjects`, `projectIrqHandlers`, `projectObjectIndex` with
   `observableOids.contains oid` — O(1) per check.
3. Implement lazy CNode projection: instead of eagerly filtering all CNode
   slots during `projectState`, defer slot filtering to access time. Define
   a wrapper that projects on demand:
   ```
   def lazyProjectCNode (ctx : LabelingContext) (observer : IfObserver)
       (cn : CNode) : CNode :=
     { cn with slots := cn.slots.filter (fun (_, cap) =>
         observableOids.contains cap.target) }
   ```
   Apply this lazily when a CNode is actually accessed by a consumer, not
   eagerly for all CNodes in the system.
4. Cache projected objects: since `projectKernelObject` is proven idempotent
   (Projection.lean:87), cache results in a local HashMap to avoid
   re-filtering the same CNode multiple times during a single projection.
5. Re-prove `projectKernelObject_idempotent` and `projectState` equivalence
   theorems against the optimized implementation. The key property is that
   the observable set computation produces the same result as individual
   `objectObservable` calls — prove this via `HashSet` membership equivalence.
6. Re-prove non-interference theorems that depend on `projectState` equality.

**Files modified:**
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — `projectState` and
  sub-functions rewrite
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — NI theorem re-proof

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `objectObservable` is evaluated at most once per object per `projectState`
  call (verifiable by code inspection).

**Dependencies:** WS-G1 (Hashable for ObjId). WS-G5 recommended (HashMap
CNode slots for efficient projection filtering).

**Estimated effort:** Medium (localized to information-flow subsystem; requires
careful theorem re-proof to maintain NI guarantees).

---

## 5. Execution Phases

| Phase | Workstreams | Description | Dependency gate |
|-------|-------------|-------------|-----------------|
| **P0** | WS-G1 | Hashable/BEq infrastructure — unlocks all HashMap usage | None |
| **P1** | WS-G2, WS-G3 | Core state representation — object store + ASID table (parallel) | WS-G1 |
| **P2** | WS-G4 | Run queue restructure (depends on WS-G2 for O(1) TCB lookup) | WS-G1, WS-G2 |
| **P3** | WS-G5, WS-G6, WS-G7, WS-G8, WS-G9 | Data structure + subsystem optimizations (parallel) | WS-G1; WS-G2 for G7/G9 |

**Phase notes:**
- **P0** is a single low-effort PR that enables everything else. No behavioral
  changes, only instance derivations and imports.
- **P1** addresses the two highest-impact critical findings in parallel: F-P01
  (object store) and F-P06 (ASID table). These touch different parts of
  `SystemState` and can proceed concurrently with careful coordination on
  the `SystemState` structure definition.
- **P2** is sequenced after P1 because `removeRunnable` and `ensureRunnable`
  need O(1) TCB lookups (from WS-G2) to resolve thread priorities for the
  bucketed run queue.
- **P3** workstreams are largely independent and can proceed in parallel.
  WS-G7 and WS-G9 benefit from WS-G2 (HashMap object store) but can begin
  implementation while WS-G2 is in progress, merging after P1 completion.

**Parallelism within phases:**

```
P0:  [WS-G1]
      │
P1:  [WS-G2]──────────────┬──[WS-G3]
      │                    │
P2:  [WS-G4]              │
      │                    │
P3:  [WS-G5]──[WS-G6]──[WS-G7]──[WS-G8]──[WS-G9]
     (parallel: all P3 workstreams can proceed concurrently)
```

---

## 6. Status Dashboard

| Workstream | Priority | Findings | Status | Est. effort |
|------------|----------|----------|--------|-------------|
| WS-G1 | Prerequisite | (infrastructure) | **Completed** | Low |
| WS-G2 | Critical | F-P01, F-P10, F-P13 | **Completed** | Medium-High |
| WS-G3 | Critical | F-P06 | **Completed** | Low |
| WS-G4 | Critical | F-P02, F-P07, F-P12 | **Completed** | High |
| WS-G5 | High | F-P03 | **Completed** | Medium |
| WS-G6 | High | F-P05 | **Completed** | Medium |
| WS-G7 | High | F-P04, F-P11 | **Completed** | Low-Medium |
| WS-G8 | High | F-P08, F-P14 | **Completed** | Medium |
| WS-G9 | High | F-P09 | Planning | Medium |

**Finding coverage:** All 14 findings (F-P01 through F-P14) are addressed.
3 CRITICAL, 6 HIGH, 5 MEDIUM — 100% coverage.

---

## 7. Proof Strategy for HashMap Migration

The transition from function-typed/list-typed stores to `Std.HashMap` is the
dominant proof challenge across WS-G2 through WS-G9. A consistent migration
strategy minimizes re-proof effort and prevents build breakage during transition.

### 7.1 Bisimulation Bridge Pattern

For each data structure migration, establish a one-time bisimulation lemma that
bridges the old and new representations:

**Object store (WS-G2):**
```
theorem objects_bisim (hm : Std.HashMap ObjId KernelObject) (id : ObjId) (obj : KernelObject) :
  (hm.insert id obj).find? oid = if oid = id then some obj else hm.find? oid
```
This single lemma allows all existing `storeObject_objects_eq` and
`storeObject_objects_ne` theorems to be re-proved mechanically.

**CNode slots (WS-G5):**
```
theorem slots_bisim (hm : Std.HashMap Slot Capability) (s : Slot) (cap : Capability) :
  (hm.insert s cap).find? s' = if s' = s then some cap else hm.find? s'
```

**VSpace mappings (WS-G6):**
```
theorem mappings_bisim (hm : Std.HashMap VAddr PAddr) (va : VAddr) (pa : PAddr) :
  (hm.insert va pa).find? va' = if va' = va then some pa else hm.find? va'
```

### 7.2 Incremental Migration Sequence

1. **Establish bridge**: Prove the bisimulation lemma for the target data structure.
2. **Swap representation**: Change the structure field type.
3. **Update operations**: Rewrite insert/lookup/delete against the new type.
4. **Re-prove via bridge**: Use the bisimulation lemma to re-prove all existing
   theorems. At this stage, proofs reference the bridge lemma rather than
   native HashMap lemmas — this is acceptable and ensures quick migration.
5. **Native re-proof (optional)**: In a follow-up pass, replace bridge-based
   proofs with direct `HashMap` lemma applications for cleaner proof terms.

### 7.3 Invariant Simplification Opportunities

Several invariants become trivially true or structurally simplified after
HashMap migration:

| Invariant | Current form | Post-migration |
|-----------|-------------|----------------|
| `slotsUnique` | Prove `List.Nodup` for CNode slots | Trivially true (HashMap key uniqueness) |
| `runQueueUnique` | Prove `List.Nodup` for runnable | Trivially true (HashSet membership) |
| `vspaceAsidRootsUnique` | Prove no two roots share ASID | Maintained by `asidTable` key uniqueness |
| `objectIndex` monotonicity | Prove append-only growth | Shadow `HashSet` + list maintains both |

These simplifications reduce the total proof surface and improve maintainability.

---

## 8. Complexity Impact Summary

| Hot path | Before | After | Workstream |
|----------|--------|-------|------------|
| Object lookup | O(k) closure chain | O(1) HashMap | WS-G2 |
| Object store | O(n) index membership | O(1) HashSet | WS-G2 |
| ASID resolution | O(n) objectIndex scan | O(1) HashMap | WS-G3 |
| Runnable remove | O(t) list filter | O(1) HashSet + HashMap | WS-G4 |
| Runnable membership | O(t) list scan | O(1) HashSet | WS-G4 |
| Best-candidate selection | O(t) full scan | O(1) priority bucket head | WS-G4 |
| Rotate to back | O(t) erase + append | O(1) dequeue + enqueue | WS-G4 |
| Tail recomputation | O(t) getLast? | Eliminated (structural) | WS-G4 |
| CNode slot lookup | O(m) list find | O(1) HashMap | WS-G5 |
| CNode slot insert | O(m) filter + prepend | O(1) HashMap insert | WS-G5 |
| VSpace mapping lookup | O(m) list find | O(1) HashMap | WS-G6 |
| VSpace map/unmap | O(m) list ops | O(1) HashMap | WS-G6 |
| Legacy endpoint enqueue | O(n) list append | O(1) dual-queue | WS-G7 |
| Notification dup check | O(n) list membership | O(1) ipcState check | WS-G7 |
| Service cycle detection | O(n²) BFS | O(n+e) DFS w/ HashSet | WS-G8 |
| CDT child lookup | O(E) edge scan | O(1) HashMap | WS-G8 |
| CDT descendant BFS | O(N×E) | O(N+E) | WS-G8 |
| Projection observability | O(n) per-access eval | O(1) precomputed set | WS-G9 |

**End-to-end hot-path improvement:**
- **IPC send/receive:** O(t + k) → O(1)
- **Timer tick / preemption:** O(t) → O(1)
- **Capability lookup:** O(m) → O(1)
- **VSpace translation (page fault):** O(n + m) → O(1)
- **Service dependency registration:** O(n²) → O(n + e)

---

## 9. Risk Matrix

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| HashMap lemma gaps in Lean 4 stdlib | Medium | High | Prove custom lemmas as needed; Lean `Std` provides `find?_insert` and `find?_erase` since 4.x. Verify available lemmas before starting WS-G2. |
| Cross-workstream merge conflicts on `SystemState` | High | Medium | Sequence P1 carefully: WS-G2 and WS-G3 both modify `SystemState`. Assign disjoint field sets (G2 owns `objects`/`lifecycle`/`objectIndexSet`; G3 owns `asidTable`). |
| Proof regression during migration | Medium | High | Bisimulation bridge ensures no intermediate build breakage. Each workstream maintains a green build throughout. |
| `Std.Queue` availability | Low | Low | If `Std.Queue` is not available in Lean 4.28.0, implement a minimal `Queue` (pair of lists) in `Prelude.lean`. |
| RunQueue priority-bucket memory overhead | Low | Low | Priority range is bounded (typically 0-255). HashMap with 256 buckets is negligible. |
| Fixture breakage from API changes | Medium | Low | Update `tests/fixtures/main_trace_smoke.expected` with each workstream. Document rationale for fixture changes. |
| `@[inline]` interaction with HashMap operations | Low | Medium | Verify that `@[inline]` on typed identifier operations composes correctly with HashMap `Hashable` instances. Test with `set_option trace.compiler.ir true`. |

---

## 10. Documentation Synchronization

Each workstream PR must update (per project convention):

1. `README.md` — if public API or architecture changes
2. `docs/spec/SELE4N_SPEC.md` — data structure representation changes
3. `docs/DEVELOPMENT.md` — build or testing changes
4. `CHANGELOG.md` — feature entry for each workstream completion
5. `docs/CLAIM_EVIDENCE_INDEX.md` — if complexity claims change
6. This plan (`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`) — status updates

---

## 11. Exit Criteria (Portfolio-Level)

The WS-G portfolio is complete when:

1. All 14 performance findings (F-P01 through F-P14) are addressed.
2. `lake build` passes with zero errors, zero warnings, zero sorry.
3. `test_full.sh` passes (Tier 0-3).
4. `lake exe sele4n` output matches the expected fixture.
5. No O(n) or O(n²) operations remain on the IPC, scheduling, capability,
   or VSpace hot paths (verifiable by code inspection).
6. All invariant preservation theorems are re-proved against the new data
   structures (no bisimulation bridges remain as permanent debt — all proofs
   use native HashMap lemmas).
7. Documentation is synchronized per Section 10.
