# WS-L Workstream Plan — IPC Subsystem Audit & Remediation (v0.16.8)

**Created**: 2026-03-15
**Baseline version**: 0.16.8
**Baseline audit**: End-to-end IPC subsystem audit (all 12 IPC files, 9,195 LoC)
**Prior portfolios**: WS-K (v0.16.8, complete), WS-I (I1–I4 complete, I5 pending)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Audit Summary

A comprehensive end-to-end audit of the IPC subsystem was conducted covering:

- **Operations**: `Endpoint.lean` (545 lines), `SchedulerLemmas.lean` (510 lines)
- **DualQueue**: `Core.lean` (248 lines), `Transport.lean` (1,504 lines)
- **Invariants**: `Defs.lean` (593 lines), `EndpointPreservation.lean` (1,467 lines),
  `CallReplyRecv.lean` (868 lines), `NotificationPreservation.lean` (738 lines),
  `Structural.lean` (2,345 lines)
- **Re-export hubs**: `Operations.lean`, `DualQueue.lean`, `Invariant.lean`
- **API integration**: `API.lean` syscall wrappers, `SyscallArgDecode.lean`
- **Model types**: `Object/Types.lean` (IpcMessage, ThreadIpcState, IntrusiveQueue)

**Overall verdict**: Zero `sorry`/`axiom`. All proofs machine-checked. Zero
critical vulnerabilities. Three performance optimization opportunities. Five
proof strengthening opportunities. Five test coverage gaps. One deferred
workstream (WS-I5) to resolve.

---

## 2. Finding Registry

### Performance Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| L-P01 | MEDIUM | `Transport.lean:1355` | `endpointReceiveDual` redundantly re-lookups sender TCB after `endpointQueuePopHead` already retrieved it internally |
| L-P02 | LOW | `Transport.lean:1451,1461` | `endpointReply` lookups target TCB for validation then `storeTcbIpcStateAndMessage` re-lookups same TCB |
| L-P03 | LOW | `Endpoint.lean:155,169` | `notificationWait` lookups waiter TCB for duplicate-check then `storeTcbIpcState` re-lookups same TCB |

### Proof Strengthening Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| L-G01 | MEDIUM | `DualQueue/Core.lean` | No enqueue-dequeue round-trip theorem: no proof that successfully enqueued thread can be dequeued without error |
| L-G02 | MEDIUM | `DualQueue/Core.lean` | Queue structural correctness (doubly-linked list integrity from enqueue through dequeue) not proven end-to-end |
| L-G03 | MEDIUM | `Invariant/Defs.lean` | No ipcState-queue membership consistency invariant: no proof that `blockedOnSend epId` ↔ thread on `epId.sendQ` |
| L-G04 | LOW | `DualQueue/Core.lean:616-622` | Tail consistency during `endpointQueueRemoveDual` is implicit, not explicitly proven |
| L-G05 | LOW | `Invariant/EndpointPreservation.lean` | Missing `endpointReply_preserves_ipcSchedulerContractPredicates` theorem |

### Test Coverage Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| L-T01 | MEDIUM | `MainTraceHarness.lean` | `endpointReplyRecv` positive-path behavior (message transfer + state transitions) not tested |
| L-T02 | MEDIUM | `NegativeStateSuite.lean` | Endpoint deletion while senders/receivers queued not tested |
| L-T03 | LOW | `MainTraceHarness.lean` | Capability transfer during IPC (actual cap rights propagation) not tested |
| L-T04 | LOW | `NegativeStateSuite.lean` | Blocked thread rejection for repeated IPC operations not explicitly tested |
| L-T05 | LOW | `MainTraceHarness.lean` | Complex multi-endpoint interleaving (3+ endpoints) not tested |

### Deferred Items Resolved

| ID | Origin | Description | Resolution |
|----|--------|-------------|------------|
| L-D01 | WS-I5/R-12 | Document RegName/RegValue design decision | Superseded by WS-J1 (typed wrappers implemented) |
| L-D02 | WS-I5/R-13 | Add readers' guide for 3-layer IF architecture | Resolved in WS-L Phase E |
| L-D03 | WS-I5/R-14 | Document test fixture update process | Resolved in WS-L Phase E |
| L-D04 | WS-I5/R-17 | HashMap.fold migration for detachCNodeSlots | Resolved in WS-L Phase B |
| L-D05 | WS-I5/R-18 | Metrics regeneration automation | Resolved in WS-L Phase E |

---

## 3. Planning Principles

1. **Performance-first**: Address redundant lookups that affect IPC hot paths.
2. **Proof completeness**: Add missing round-trip and consistency theorems.
3. **Test coverage**: Fill gaps in ReplyRecv, lifecycle, and interleaving scenarios.
4. **Deferred resolution**: Close all WS-I5 pending items within this portfolio.
5. **Zero sorry/axiom**: Every new theorem must be fully machine-checked.
6. **Coherent slices**: Each phase independently deliverable and testable.
7. **Minimal disruption**: Preserve existing API signatures where possible.

---

## 4. Phase Overview

### Phase 1: IPC Performance Optimization (WS-L1)

**Focus**: Eliminate redundant object lookups on IPC hot paths.
**Priority**: HIGH — directly impacts IPC throughput.
**Estimated effort**: 4–6 hours.

### Phase 2: Code Quality & Deferred Cleanup (WS-L2)

**Focus**: HashMap.fold migration, code hygiene.
**Priority**: MEDIUM — closes deferred WS-I5/R-17.
**Estimated effort**: 2–3 hours.

### Phase 3: Proof Strengthening (WS-L3)

**Focus**: Add missing round-trip, consistency, and preservation theorems.
**Priority**: MEDIUM — strengthens formal assurance.
**Estimated effort**: 8–12 hours.

### Phase 4: Test Coverage Expansion (WS-L4)

**Focus**: Fill coverage gaps for ReplyRecv, lifecycle, interleaving.
**Priority**: MEDIUM — broadens runtime validation.
**Estimated effort**: 6–8 hours.

### Phase 5: Documentation & Workstream Closeout (WS-L5)

**Focus**: Resolve all deferred WS-I5 documentation items, update all docs.
**Priority**: LOW — polish and completeness.
**Estimated effort**: 4–6 hours.

### Dependency Graph

```
Phase 1: WS-L1 (Performance)
           │
           ▼
Phase 2: WS-L2 (Code Quality)     [parallel-safe with Phase 1]
           │
           ▼
Phase 3: WS-L3 (Proof Strengthening) [depends on L1 API changes]
           │
           ▼
Phase 4: WS-L4 (Test Coverage)    [depends on L1 changes; parallel with L3]
           │
           ▼
Phase 5: WS-L5 (Documentation)    [after all implementation phases]
```

---

## 5. Workstream Definitions

### WS-L1: IPC Performance Optimization

**Objective**: Eliminate 4 redundant TCB lookups on IPC hot paths (3 on the
endpoint receive/reply critical path, 1 on the notification wait path),
reducing per-operation overhead by ~15–20% on critical paths.

**Priority**: HIGH — Phase 1
**Dependencies**: None
**Findings addressed**: L-P01, L-P02, L-P03

**Key design decisions**:

1. **Equivalence-theorem strategy**: Instead of duplicating preservation lemmas
   for `_fromTcb` variants, each variant ships with an equivalence theorem
   proving `_fromTcb st tid tcb ... = original st tid ...` when
   `lookupTcb st tid = some tcb`. All existing preservation proofs apply via
   `simp`/`rw` rewriting. Zero new preservation lemmas needed.

2. **Pre-dequeue TCB semantics**: `endpointQueuePopHead` returns the TCB as
   captured at the internal `lookupTcb` (Core.lean:182), before queue links are
   cleared. Non-queue fields (`ipcState`, `pendingMessage`, `priority`,
   `domain`) are unchanged by PopHead and safe to read. Queue link fields
   (`queuePrev`, `queuePPrev`, `queueNext`) are stale and must not be written
   back. Callers that need to write to the TCB (via `storeTcbIpcStateAndMessage`)
   must still use the state-based lookup since the post-state TCB has cleared
   queue links.

3. **Cascade minimization**: Transport lemma and preservation theorem updates
   for PopHead are purely mechanical pattern-match changes (`(tid, st')` →
   `(tid, _tcb, st')`). Proof bodies are unchanged because `unfold
   endpointQueuePopHead` produces the same case structure with an additional
   binding.

---

#### L1-A: Return dequeued TCB from `endpointQueuePopHead` (L-P01)

**Problem**: `endpointQueuePopHead` (Core.lean:172–208) internally looks up the
head TCB at line 182 to read `queueNext`, but returns only `(ThreadId, SystemState)`.
The most impacted caller, `endpointReceiveDual` (Transport.lean:1355), must
re-lookup the same TCB to read `pendingMessage` and `ipcState` — fields that
PopHead did not modify. This is a redundant O(log n) HashMap lookup on every
endpoint receive rendezvous.

**Sub-tasks**:

##### L1-A.1: Change PopHead signature and implementation (Core.lean)

**Scope**: `SeLe4n/Kernel/IPC/DualQueue/Core.lean`, lines 172–208

1. Change return type from `Except KernelError (SeLe4n.ThreadId × SystemState)`
   to `Except KernelError (SeLe4n.ThreadId × TCB × SystemState)`.
2. At line 206, change `.ok (tid, st3)` to `.ok (tid, headTcb, st3)` where
   `headTcb` is the TCB captured at line 182–184. This is the pre-dequeue TCB;
   non-queue fields are accurate, queue link fields are stale (cleared in `st3`).
3. No other changes to Core.lean.

**Exit**: `Core.lean` compiles (callers will temporarily break).

##### L1-A.2: Update PopHead transport lemmas (Transport.lean:19–299)

**Scope**: 5 transport lemmas that pattern-match on PopHead result

Each lemma's hypothesis changes mechanically:
```
hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st')
  →
hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st')
```

Affected lemmas (all in `Transport.lean`):
- `endpointQueuePopHead_scheduler_eq` (lines 20–69)
- `endpointQueuePopHead_endpoint_backward_ne` (lines 72–123)
- `endpointQueuePopHead_notification_backward` (lines 126–180)
- `endpointQueuePopHead_tcb_forward` (lines 184–237)
- `endpointQueuePopHead_tcb_ipcState_backward` (lines 241–299)

Proof bodies unchanged — `unfold endpointQueuePopHead at hStep` still produces
the same case tree; the additional `headTcb` binding is consumed by existing
`simp`/`cases` tactics.

**Exit**: All transport lemmas compile.

##### L1-A.3: Update `endpointReceiveDual` — eliminate redundant lookup

**Scope**: `Transport.lean`, lines 1342–1388

Change destructuring at line 1351 from `(sender, st')` to
`(sender, senderTcb, st')`. Replace the redundant `lookupTcb st' sender`
block (lines 1355–1359) with direct field access:
```lean
let (senderMsg, senderWasCall) :=
  (senderTcb.pendingMessage, match senderTcb.ipcState with
    | .blockedOnCall _ => true
    | _ => false)
```

This eliminates 1 redundant lookup. The `senderTcb` fields `pendingMessage`
and `ipcState` are unchanged by PopHead (only queue links are modified).

**Exit**: `endpointReceiveDual` compiles with zero `lookupTcb` after PopHead.

##### L1-A.4: Update `endpointSendDual` and `endpointCall` — mechanical

**Scope**: `Transport.lean`, lines 1297–1324 and 1401–1433

- `endpointSendDual` line 1311: `(receiver, st')` → `(receiver, _tcb, st')`
- `endpointCall` line 1415: `(receiver, st')` → `(receiver, _tcb, st')`

These callers don't use the returned TCB (they operate on the receiver, not the
dequeued thread's TCB data). Change is purely mechanical.

**Exit**: Both functions compile.

##### L1-A.5: Update preservation theorems — mechanical cascade

**Scope**: Preservation theorems across 3 invariant files

All theorems that destructure PopHead results need the same mechanical update:
`(tid, st')` → `(tid, _tcb, st')` in hypothesis patterns. The proof bodies
are unchanged because `unfold endpointQueuePopHead` still works identically.

Files and estimated theorem counts:
- `EndpointPreservation.lean`: ~6 theorems referencing PopHead
- `CallReplyRecv.lean`: ~4 theorems referencing PopHead
- `Structural.lean`: ~8 theorems referencing PopHead

**Exit**: `lake build` succeeds with zero warnings.

**Files modified (L1-A total)**:
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` — signature + return value
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — lemmas + callers
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` — mechanical
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` — mechanical
- `SeLe4n/Kernel/IPC/Invariant/Structural.lean` — mechanical

**L1-A exit evidence**:
- `lake build` succeeds with zero warnings
- `test_smoke.sh` passes
- `rg "lookupTcb.*sender" Transport.lean` returns zero hits in receive path

---

#### L1-B: Cache validated TCB in `endpointReply`/`endpointReplyRecv` (L-P02)

**Problem**: `endpointReply` (Transport.lean:1451) calls `lookupTcb st target`
to validate `ipcState = .blockedOnReply`, then `storeTcbIpcStateAndMessage`
(line 1461) internally calls `lookupTcb st target` again on the **same state**
`st`. Similarly, `endpointReplyRecv` (line 1481/1492) has the same pattern.
Each redundant lookup is an O(log n) HashMap operation on every reply.

**Sub-tasks**:

##### L1-B.1: Add `storeTcbIpcStateAndMessage_fromTcb` with equivalence theorem

**Scope**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, after line 91

1. Add the `_fromTcb` variant:
   ```lean
   def storeTcbIpcStateAndMessage_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
       (tcb : TCB) (ipcState : ThreadIpcState) (msg : Option IpcMessage)
       : Except KernelError SystemState :=
     match storeObject tid.toObjId
       (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
     | .error e => .error e
     | .ok ((), st') => .ok st'
   ```

2. Add equivalence theorem (immediately after):
   ```lean
   theorem storeTcbIpcStateAndMessage_fromTcb_eq
       (hLookup : lookupTcb st tid = some tcb) :
       storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg =
       storeTcbIpcStateAndMessage st tid ipcState msg
   ```
   Proof: unfold both, rewrite with `hLookup`, `rfl`.

This equivalence theorem means **zero new preservation lemmas** are needed.
Any existing theorem about `storeTcbIpcStateAndMessage` applies to the
`_fromTcb` variant via `rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup]`.

**Exit**: New function and theorem compile with zero sorry.

##### L1-B.2: Update `endpointReply` to use `_fromTcb`

**Scope**: `Transport.lean`, lines 1444–1465

At line 1461, replace:
```lean
match storeTcbIpcStateAndMessage st target .ready (some msg) with
```
with:
```lean
match storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
```
where `tcb` is the TCB already bound at line 1453. Both lookups operate on the
same state `st`, so the TCB is guaranteed to match.

**Exit**: `endpointReply` compiles. 1 redundant lookup eliminated.

##### L1-B.3: Update `endpointReplyRecv` to use `_fromTcb`

**Scope**: `Transport.lean`, lines 1471–1501

At line 1492, replace:
```lean
match storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
```
with:
```lean
match storeTcbIpcStateAndMessage_fromTcb st replyTarget tcb .ready (some msg) with
```
where `tcb` is bound at line 1483. Same-state guarantee applies.

**Exit**: `endpointReplyRecv` compiles. 1 redundant lookup eliminated.

**Files modified (L1-B total)**:
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` — new function + theorem
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — 2 caller updates

**L1-B exit evidence**:
- `lake build` succeeds with zero warnings
- `test_smoke.sh` passes
- Zero new preservation lemmas needed (equivalence theorem covers all cases)

---

#### L1-C: Cache validated TCB in `notificationWait` (L-P03)

**Problem**: `notificationWait` (Endpoint.lean:155) calls `lookupTcb st waiter`
for the O(1) duplicate-wait check, then `storeTcbIpcState` (line 169) re-lookups
the same TCB. The intermediate `storeObject` (line 165) modifies only the
notification object at `notificationId`, not the waiter's TCB, so the looked-up
TCB is still valid in the post-store state.

**Sub-tasks**:

##### L1-C.1: Add `storeTcbIpcState_fromTcb` with equivalence theorem

**Scope**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, after `storeTcbIpcState`

1. Add the `_fromTcb` variant:
   ```lean
   def storeTcbIpcState_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
       (tcb : TCB) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
     match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
     | .error e => .error e
     | .ok ((), st') => .ok st'
   ```

2. Add equivalence theorem:
   ```lean
   theorem storeTcbIpcState_fromTcb_eq
       (hLookup : lookupTcb st tid = some tcb) :
       storeTcbIpcState_fromTcb st tid tcb ipcState =
       storeTcbIpcState st tid ipcState
   ```

3. Add TCB cross-store stability lemma (used to justify `_fromTcb` usage
   after an intervening `storeObject` at a different ObjId):
   ```lean
   theorem lookupTcb_preserved_by_storeObject_ne
       (hLookup : lookupTcb st tid = some tcb)
       (hNe : oid ≠ tid.toObjId)
       (hStore : storeObject oid obj st = .ok ((), st')) :
       lookupTcb st' tid = some tcb
   ```
   This lemma proves the TCB is unchanged when `storeObject` targets a
   different ObjId — which is exactly the case in `notificationWait` where
   the notification is stored at `notificationId` but the TCB is at
   `waiter.toObjId`.

**Exit**: New function, equivalence theorem, and stability lemma compile.

##### L1-C.2: Update `notificationWait` to use `_fromTcb`

**Scope**: `Endpoint.lean`, lines 138–173

In the no-pending-badge branch, after `lookupTcb st waiter` succeeds with
`tcb` at line 155, and after `storeObject notificationId (.notification ntfn')
st` produces `st'` at line 165, replace:
```lean
match storeTcbIpcState st' waiter (.blockedOnNotification notificationId) with
```
with:
```lean
match storeTcbIpcState_fromTcb st' waiter tcb (.blockedOnNotification notificationId) with
```
**Correctness justification**: `storeObject` at `notificationId` does not modify
the TCB at `waiter.toObjId` (different ObjId), so `lookupTcb st' waiter =
some tcb` holds. The equivalence theorem then guarantees identical behavior.

**Exit**: `notificationWait` compiles. 1 redundant lookup eliminated.

**Files modified (L1-C total)**:
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` — new function + theorems + caller

**L1-C exit evidence**:
- `lake build` succeeds with zero warnings
- `test_smoke.sh` passes

---

#### WS-L1 Aggregate Summary

| Sub-task | Lookups eliminated | Cascade scope | Risk |
|----------|-------------------|---------------|------|
| L1-A (PopHead TCB) | 1 (endpointReceiveDual) | ~18 theorem pattern-match updates | Medium: wide cascade but mechanical |
| L1-B (reply _fromTcb) | 2 (endpointReply + ReplyRecv) | 2 caller updates, 0 new lemmas | Low: additive, equivalence theorem |
| L1-C (notification _fromTcb) | 1 (notificationWait) | 1 caller update, 0 new lemmas | Low: additive, single file |
| **Total** | **4 redundant lookups** | | |

**Recommended execution order**: L1-B → L1-C → L1-A. Start with additive
changes (new `_fromTcb` functions) that don't cascade, then tackle the
signature change (L1-A) which has the widest impact but is mechanically safe.

**WS-L1 aggregate exit evidence**:
- `lake build` succeeds with zero warnings
- `test_smoke.sh` passes
- Zero `sorry` in any new theorem or function
- 4 redundant `lookupTcb` calls eliminated across IPC hot paths

---

### WS-L2: Code Quality & Deferred Cleanup

**Objective**: Eliminate all `Std.HashMap.toList.foldl/foldr` anti-patterns across
the codebase, replacing them with direct `Std.HashMap.fold` calls that avoid
intermediate list allocation. Close WS-I5/R-17 and address all related code
hygiene items discovered during the IPC subsystem audit.

**Priority**: MEDIUM — Phase 2
**Dependencies**: None (parallel-safe with L1)
**Findings addressed**: L-D04

**Audit scope**: A codebase-wide search for `.toList.foldl` and `.toList.foldr`
on `Std.HashMap` values identified **4 sites** requiring migration:

| Site | File | Line | Pattern | HashMap type |
|------|------|------|---------|-------------|
| S1 | `Kernel/Lifecycle/Operations.lean` | 83 | `.toList.foldl` | `Std.HashMap Slot Capability` |
| S2 | `Testing/InvariantChecks.lean` | 96 | `.toList.foldr` | `Std.HashMap Slot Capability` |
| S3 | `Testing/InvariantChecks.lean` | 112 | `.toList.foldr` | `Std.HashMap Slot Capability` |
| S4 | `Testing/InvariantChecks.lean` | 271 | `.toList.foldr` | `Std.HashMap CdtNodeId (List CdtNodeId)` |

Note: The original L-D04 description incorrectly referenced `Object/Structures.lean`.
The actual `detachCNodeSlots` definition is at `Kernel/Lifecycle/Operations.lean:82`.

**Key design decisions**:

1. **Proof update strategy for S1**: `detachCNodeSlots` has 3 preservation
   theorems (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`) that prove
   through `List.foldl` induction over `cn.slots.toList`. Switching to
   `HashMap.fold` changes the proof structure — the `List.foldl` / `List.cons`
   case split must be replaced with `HashMap.fold` reasoning. Since
   `HashMap.fold` internally iterates over key-value pairs in an unspecified
   order but applies the same function, and all three theorems prove that the
   fold body preserves the property unconditionally (for any pair), the proofs
   generalize cleanly. Strategy: rewrite proofs using a generic fold invariant
   helper that lifts per-step preservation to full-fold preservation.
2. **Test code (S2–S4)**: These are decidable runtime checks in
   `InvariantChecks.lean`. No proofs reference them. Migration is mechanical:
   replace `.toList.foldr f init` with `.fold init (fun acc k v => f (k, v) acc)`.
3. **Execution order**: S2–S4 first (zero proof cascade, fast validation),
   then S1 (requires proof updates, higher risk).

---

#### L2-A: Migrate `InvariantChecks.lean` fold patterns (S2, S3, S4)

**Problem**: Three runtime invariant check functions in `Testing/InvariantChecks.lean`
use `.toList.foldr` on `Std.HashMap` values, creating unnecessary intermediate
`List` allocations on every invariant check invocation. While these are test-only
functions, they execute on every trace run and should follow the same code quality
standards as production code.

**Sub-tasks**:

##### L2-A.1: Migrate `cspaceSlotCoherencyChecks` (S2)

**Scope**: `SeLe4n/Testing/InvariantChecks.lean`, line 96

Replace:
```lean
cn.slots.toList.foldr (fun (slot, cap) inner => ... ) acc
```
with:
```lean
cn.slots.fold acc (fun inner slot cap => ... )
```

Note: `HashMap.fold` passes `(acc, key, value)` as separate arguments, not as
a tuple `(key, value)`. The lambda signature changes from `(slot, cap)` tuple
destructuring to `inner slot cap` positional arguments. The fold direction
difference (`foldr` → `fold`) does not affect correctness because each check
element is independent (list concatenation is order-insensitive for check
validation).

**Exit**: `lake build` succeeds.

##### L2-A.2: Migrate `capabilityRightsStructuralChecks` (S3)

**Scope**: `SeLe4n/Testing/InvariantChecks.lean`, line 112

Same mechanical pattern as L2-A.1. Replace `.toList.foldr` with `.fold`.

**Exit**: `lake build` succeeds.

##### L2-A.3: Migrate `cdtChildMapConsistentCheck` (S4)

**Scope**: `SeLe4n/Testing/InvariantChecks.lean`, line 271

Replace:
```lean
cdt.childMap.toList.foldr (fun (parent, children) acc => ... ) []
```
with:
```lean
cdt.childMap.fold [] (fun acc parent children => ... )
```

Note: The inner `children.foldr` on `List CdtNodeId` is correct and does NOT
need migration — `children` is already a `List`, not a `HashMap`.

**Exit**: `lake build` succeeds.

**Files modified (L2-A total)**:
- `SeLe4n/Testing/InvariantChecks.lean` — 3 fold migrations

**L2-A exit evidence**:
- `lake build` succeeds with zero warnings
- `test_smoke.sh` passes (invariant checks execute correctly)
- Zero `sorry` (no proofs involved)

---

#### L2-B: Migrate `detachCNodeSlots` and update preservation proofs (S1, L-D04)

**Problem**: `detachCNodeSlots` (Lifecycle/Operations.lean:82) uses
`cn.slots.toList.foldl` instead of `cn.slots.fold`, creating an unnecessary
intermediate list allocation on every CNode slot detachment during lifecycle
retype operations. Three preservation theorems prove through `List.foldl`
induction and must be updated.

**Sub-tasks**:

##### L2-B.1: Replace `.toList.foldl` with `.fold` in `detachCNodeSlots`

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 82–85

Replace:
```lean
def detachCNodeSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) : SystemState :=
  cn.slots.toList.foldl (fun acc pair =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := pair.1 }
  ) st
```
with:
```lean
def detachCNodeSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) : SystemState :=
  cn.slots.fold st (fun acc slot _cap =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }
  )
```

This eliminates the intermediate `List (Slot × Capability)` allocation.

**Exit**: Definition compiles (proofs will temporarily break).

##### L2-B.2: Update `detachCNodeSlots_objects_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 87–103

The current proof uses `List.foldl` induction:
```lean
have key : ∀ (l : List ...) (acc : SystemState),
  (l.foldl ...).objects = acc.objects := by
  intro l; induction l with ...
```

This must be replaced with a proof that works over `HashMap.fold`. Strategy:
use `Std.HashMap.fold_induction` or equivalent fold reasoning, proving that
the fold body `(fun acc slot _cap => detachSlotFromCdt acc ...)` preserves
`.objects` at each step (which is already established by
`detachSlotFromCdt_objects_eq`).

**Exit**: Theorem compiles with zero `sorry`.

##### L2-B.3: Update `detachCNodeSlots_lifecycle_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 105–121

Same proof update pattern as L2-B.2, using `detachSlotFromCdt_lifecycle_eq`
as the per-step preservation lemma.

**Exit**: Theorem compiles with zero `sorry`.

##### L2-B.4: Update `detachCNodeSlots_scheduler_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 176–193

Same proof update pattern as L2-B.2. The per-step preservation fact is proven
inline: `(SystemState.detachSlotFromCdt acc ref).scheduler = acc.scheduler`
by `unfold SystemState.detachSlotFromCdt; split <;> rfl`.

**Exit**: Theorem compiles with zero `sorry`.

**Files modified (L2-B total)**:
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — definition + 3 proof updates

**L2-B exit evidence**:
- `lake build` succeeds with zero warnings
- `test_full.sh` passes (lifecycle theorems are Tier 3 anchors)
- Zero `sorry` in any updated proof

---

#### WS-L2 Aggregate Summary

| Sub-task | Sites migrated | Proof updates | Risk |
|----------|---------------|---------------|------|
| L2-A (InvariantChecks) | 3 (S2, S3, S4) | 0 (test code only) | Low: mechanical, no proof cascade |
| L2-B (detachCNodeSlots) | 1 (S1) | 3 theorems | Medium: proof structure changes |
| **Total** | **4 `.toList` fold patterns** | **3 proof updates** | |

**Recommended execution order**: L2-A (test code, zero risk) → L2-B (production
code + proofs, medium risk). This allows validating the build after each step.

**WS-L2 aggregate exit evidence**:
- `lake build` succeeds with zero warnings
- `test_full.sh` passes
- Zero `sorry` in any new or updated code
- Zero remaining `.toList.foldl` or `.toList.foldr` on `Std.HashMap` values
- Verification: `rg '\.toList\.(foldl|foldr)' --type lean` returns zero hits

---

### WS-L3: Proof Strengthening

**Objective**: Add 5 missing theorems that strengthen the formal assurance of the
IPC dual-queue subsystem.

**Priority**: MEDIUM — Phase 3
**Dependencies**: WS-L1 (API changes may affect theorem statements)
**Findings addressed**: L-G01, L-G02, L-G03, L-G04, L-G05

#### L3-A: Enqueue-dequeue round-trip theorem (L-G01)

**Problem**: No theorem proves that a successfully enqueued thread can be
subsequently dequeued without error from the same queue.

**Deliverables**:

1. Add theorem `endpointQueueEnqueue_then_popHead_succeeds`:
   If `endpointQueueEnqueue epId isRecvQ tid st = .ok st'` and the thread was
   enqueued into an empty queue, then
   `endpointQueuePopHead epId isRecvQ st' = .ok (tid, tcb, st'')`.
2. Prove by unfolding both operations and showing head = tid after enqueue into
   empty queue.

**Files modified**:
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — new theorem

**Exit evidence**:
- `lake build` succeeds
- Zero sorry in new theorem

#### L3-B: Queue structural end-to-end integrity (L-G02)

**Problem**: Queue doubly-linked list integrity is proven at the `tcbQueueLinkIntegrity`
level (global system invariant) but not end-to-end through enqueue→dequeue sequences.

**Deliverables**:

1. Add theorem `endpointQueueEnqueue_maintains_linkIntegrity`:
   If `tcbQueueLinkIntegrity st` and `endpointQueueEnqueue` succeeds producing
   `st'`, then `tcbQueueLinkIntegrity st'`.
   (Note: The frame lemma version exists in Structural.lean; this theorem
   composes it with the freshness preconditions to provide a usable form.)
2. Add similar theorem for `endpointQueuePopHead`.

**Files modified**:
- `SeLe4n/Kernel/IPC/Invariant/Structural.lean` — composed theorems

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-C: ipcState-queue membership consistency invariant (L-G03)

**Problem**: No invariant proves that `tcb.ipcState = .blockedOnSend epId` if and
only if the thread is on `epId.sendQ`. The invariant exists implicitly (operations
always set both atomically) but is not stated.

**Deliverables**:

1. Define `ipcStateQueueConsistent (st : SystemState) : Prop` asserting:
   - `tcb.ipcState = .blockedOnSend epId` → thread is on `epId.sendQ`
   - `tcb.ipcState = .blockedOnReceive epId` → thread is on `epId.receiveQ`
   - `tcb.ipcState = .blockedOnCall epId` → thread is on `epId.sendQ`
   - `tcb.ipcState = .ready` → thread is not on any endpoint queue
2. Add to `Invariant/Defs.lean`.
3. Add preservation theorems for `endpointSendDual`, `endpointReceiveDual`,
   `endpointCall`, `endpointReply`, `endpointReplyRecv` in appropriate
   preservation files.

**Files modified**:
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — invariant definition
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` — preservation
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` — preservation

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-D: Tail consistency theorem for `endpointQueueRemoveDual` (L-G04)

**Problem**: When removing a non-tail thread from a multi-element queue,
`endpointQueueRemoveDual` preserves the tail. This is correct but implicit.

**Deliverables**:

1. Add theorem `endpointQueueRemoveDual_preserves_tail`:
   If the removed thread has `queueNext = some _` (not the tail), then
   the post-state queue tail equals the pre-state queue tail.

**Files modified**:
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — new theorem

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-E: endpointReply contract preservation (L-G05)

**Problem**: `endpointReply_preserves_ipcSchedulerContractPredicates` is missing
from EndpointPreservation.lean. The reply operation modifies TCB ipcState
(blockedOnReply → ready) and adds the thread to the run queue, which affects
contract predicates.

**Deliverables**:

1. Add theorem `endpointReply_preserves_ipcSchedulerContractPredicates`.
2. Proof strategy: decompose into storeTcbIpcStateAndMessage → ensureRunnable,
   show each predicate preserved using `contracts_of_same_scheduler_ipcState`
   for the store step, then per-predicate analysis for ensureRunnable.

**Files modified**:
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` — new theorem

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

---

### WS-L4: Test Coverage Expansion

**Objective**: Fill 5 test coverage gaps discovered during the IPC audit,
adding runtime validation for ReplyRecv, lifecycle, capability transfer,
blocked-thread rejection, and multi-endpoint interleaving.

**Priority**: MEDIUM — Phase 4
**Dependencies**: WS-L1 (performance changes may affect operation signatures)
**Findings addressed**: L-T01, L-T02, L-T03, L-T04, L-T05

#### L4-A: ReplyRecv positive-path test (L-T01)

**Problem**: `endpointReplyRecv` is only tested for bounds-checking rejection
(NegativeStateSuite:572–589). No test exercises the positive path: server
replies to caller, then immediately receives next sender's message.

**Deliverables**:

1. Add `runReplyRecvRoundtripTrace` test function in `MainTraceHarness.lean`:
   - Thread A calls endpoint (blockedOnCall → blockedOnReply)
   - Thread B calls endpoint (queued on sendQ)
   - Server thread uses ReplyRecv: replies to A, receives B's message
   - Verify: A unblocked with reply message, server has B's message
   - Verify: state transitions (A: blockedOnReply → ready, B: blockedOnCall → blockedOnReply)
2. Add scenario IDs: `RRC-001` through `RRC-006`.
3. Update fixture file with expected output.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — new test function
- `tests/fixtures/main_trace_smoke.expected` — fixture update

**Exit evidence**:
- `test_smoke.sh` passes
- RRC scenario IDs visible in trace output

#### L4-B: Endpoint lifecycle with queued threads test (L-T02)

**Problem**: No test exercises deletion of an endpoint while threads are blocked
on its send/receive queues. This is a critical edge case for lifecycle safety.

**Deliverables**:

1. Add `runEndpointLifecycleTrace` test function in `MainTraceHarness.lean`:
   - Enqueue 2 senders on endpoint
   - Delete endpoint via lifecycle operation
   - Verify: senders' ipcState transitions (blocked → ready or error)
   - Verify: queue links cleared
2. Add scenario IDs: `ELC-001` through `ELC-004`.
3. Update fixture file.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — new test function
- `tests/fixtures/main_trace_smoke.expected` — fixture update

**Exit evidence**:
- `test_smoke.sh` passes

#### L4-C: Blocked thread IPC rejection test (L-T04)

**Problem**: No explicit test verifies that a thread already blocked on IPC
is rejected when attempting another IPC operation.

**Deliverables**:

1. Add negative test cases in `NegativeStateSuite.lean`:
   - Thread blocked on send attempts another send → error
   - Thread blocked on receive attempts send → error
   - Thread blocked on notification wait attempts endpoint receive → error
2. Verify error type is `alreadyWaiting` or `illegalState`.

**Files modified**:
- `tests/NegativeStateSuite.lean` — new negative cases

**Exit evidence**:
- `test_smoke.sh` passes

#### L4-D: Multi-endpoint interleaving test (L-T05)

**Problem**: Existing tests use at most 2 endpoints. Complex interleaving
across 3+ endpoints is not tested.

**Deliverables**:

1. Add `runMultiEndpointInterleavingTrace` in `MainTraceHarness.lean`:
   - Create 3 endpoints
   - Thread A sends to EP1, Thread B sends to EP2, Thread C sends to EP3
   - Receiver receives from EP2 first, then EP1, then EP3
   - Verify FIFO per-endpoint, cross-endpoint independence
2. Add scenario IDs: `MEI-001` through `MEI-006`.
3. Update fixture file.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — new test function
- `tests/fixtures/main_trace_smoke.expected` — fixture update

**Exit evidence**:
- `test_smoke.sh` passes

---

### WS-L5: Documentation & Workstream Closeout

**Objective**: Resolve all deferred WS-I5 documentation items, update all
project documentation to reflect WS-L changes, regenerate metrics.

**Priority**: LOW — Phase 5 (after all implementation phases)
**Dependencies**: WS-L1 through WS-L4
**Findings addressed**: L-D01, L-D02, L-D03, L-D05

#### L5-A: Information-flow architecture readers' guide (L-D02)

**Problem**: WS-I5/R-13 identified a missing readers' guide for the 3-layer
information-flow architecture (Policy → Enforcement → Invariant).

**Deliverables**:

1. Add section to `docs/gitbook/12-proof-and-invariant-map.md` explaining:
   - Layer 1: `Policy.lean` — security label lattice, flow rules
   - Layer 2: `Enforcement/Wrappers.lean` — policy-gated operation wrappers
   - Layer 3: `Invariant/*.lean` — per-operation NI proofs + composition
2. Include cross-references to canonical source files.

**Files modified**:
- `docs/gitbook/12-proof-and-invariant-map.md` — new section

#### L5-B: Test fixture update process documentation (L-D03)

**Problem**: WS-I5/R-14 identified that the process for updating test fixtures
is undocumented.

**Deliverables**:

1. Add section to `docs/DEVELOPMENT.md` documenting:
   - When fixtures need updating (new trace scenarios, changed output format)
   - How to regenerate: `lake exe sele4n > tests/fixtures/main_trace_smoke.expected`
   - How to verify: `diff` against prior version, inspect changes
   - CI enforcement: Tier 2 smoke test validates fixture match

**Files modified**:
- `docs/DEVELOPMENT.md` — new section

#### L5-C: Metrics regeneration documentation (L-D05)

**Problem**: WS-I5/R-18 identified that metrics regeneration is manual and
undocumented.

**Deliverables**:

1. Document the metrics regeneration process in `docs/DEVELOPMENT.md`:
   - Run `./scripts/report_current_state.py`
   - Update `README.md` metrics from `readme_sync` key in `codebase_map.json`
   - Update `docs/spec/SELE4N_SPEC.md` current state snapshot
   - Update `docs/gitbook/05-specification-and-roadmap.md` version
2. Add reminder to PR checklist.

**Files modified**:
- `docs/DEVELOPMENT.md` — metrics section

#### L5-D: Documentation sync across all canonical sources

**Problem**: WS-L implementation changes require documentation updates.

**Deliverables**:

1. Update `README.md` — metrics sync from `codebase_map.json`
2. Update `docs/spec/SELE4N_SPEC.md` — version, metrics, IPC subsystem status
3. Update `docs/DEVELOPMENT.md` — active workstream reference
4. Update `docs/CLAIM_EVIDENCE_INDEX.md` — add WS-L claim row
5. Update `docs/WORKSTREAM_HISTORY.md` — add WS-L portfolio entry
6. Update affected GitBook chapters:
   - `docs/gitbook/03-architecture-and-module-map.md` — IPC module updates
   - `docs/gitbook/04-project-design-deep-dive.md` — performance optimizations
   - `docs/gitbook/05-specification-and-roadmap.md` — version and roadmap
   - `docs/gitbook/12-proof-and-invariant-map.md` — new theorems
7. Regenerate `docs/codebase_map.json`
8. Bump `lakefile.toml` version

**Files modified**: All documentation files listed above

**Exit evidence**:
- `test_full.sh` passes (includes Tier 3 documentation anchor checks)
- All metrics consistent across README, spec, GitBook

---

## 6. Finding-to-Phase Traceability Matrix

| Finding | Phase | Task | Status |
|---------|-------|------|--------|
| L-P01 | WS-L1 | L1-A | **COMPLETED** (v0.16.9) |
| L-P02 | WS-L1 | L1-B | **COMPLETED** (v0.16.9) |
| L-P03 | WS-L1 | L1-C | **COMPLETED** (v0.16.9) |
| L-D04 | WS-L2 | L2-A (S2–S4), L2-B (S1) | **COMPLETED** (v0.16.10) |
| L-G01 | WS-L3 | L3-A | Planned |
| L-G02 | WS-L3 | L3-B | Planned |
| L-G03 | WS-L3 | L3-C | Planned |
| L-G04 | WS-L3 | L3-D | Planned |
| L-G05 | WS-L3 | L3-E | Planned |
| L-T01 | WS-L4 | L4-A | Planned |
| L-T02 | WS-L4 | L4-B | Planned |
| L-T04 | WS-L4 | L4-C | Planned |
| L-T05 | WS-L4 | L4-D | Planned |
| L-D01 | — | — | Superseded (WS-J1) |
| L-D02 | WS-L5 | L5-A | Planned |
| L-D03 | WS-L5 | L5-B | Planned |
| L-D05 | WS-L5 | L5-C | Planned |
| L-T03 | — | — | Deferred (cap transfer requires CSpace IPC integration not yet modeled) |

---

## 7. Completion Evidence Checklist

- [ ] `lake build` succeeds with zero warnings
- [ ] `test_smoke.sh` passes
- [ ] `test_full.sh` passes
- [ ] Zero `sorry`/`axiom` in production proof surface
- [ ] All 13 findings addressed (12 resolved, 1 intentionally deferred with rationale)
- [ ] All 4 WS-I5 deferred items resolved
- [ ] Documentation synchronized across all canonical sources
- [ ] `codebase_map.json` regenerated
- [ ] WS-L portfolio entry added to `WORKSTREAM_HISTORY.md`
- [ ] WS-L claim row added to `CLAIM_EVIDENCE_INDEX.md`

---

## 8. Risk Assessment

| Risk | Mitigation |
|------|------------|
| L1-A signature change cascades to many theorems | Incremental: change signature first, fix compilation, then update proofs |
| L2-B `HashMap.fold` proof structure differs from `List.foldl` induction | Use generic fold invariant helper; per-step preservation already proven |
| L3-C consistency invariant too strong (blocks legitimate states) | Define as implication (blocked → queued), not biconditional initially |
| L4-B endpoint deletion may not be implemented yet | Verify lifecycle subsystem supports endpoint deletion; adjust test if not |
| Proof explosion in L3 theorems | Use existing compositional infrastructure (`contracts_of_same_scheduler_ipcState`) |

---

## 9. Supersession Notice

This workstream plan **supersedes WS-I5** (pending). All WS-I5 items are either:
- **Resolved within WS-L**: R-13 (L5-A), R-14 (L5-B), R-17 (L2-A), R-18 (L5-C)
- **Superseded by prior work**: R-12 (resolved by WS-J1 typed wrappers)
