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
**Status**: **COMPLETED** (v0.16.13).
**Sub-tasks**: L5-A (IF readers' guide), L5-B (fixture docs — early delivery v0.16.12),
L5-C (metrics docs — early delivery v0.16.12), L5-D1 (version bump), L5-D2 (README/spec
sync), L5-D3 (DEVELOPMENT.md update), L5-D4 (history/claims), L5-D5 (GitBook sync),
L5-D6 (test validation).

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
   `HashMap.fold` changes the proof goal but the underlying proof structure
   can be preserved. Strategy: use `Std.HashMap.fold_eq_foldl_toList` (from
   Lean 4.28.0 stdlib) to rewrite the `HashMap.fold` back to `List.foldl`
   on `m.toList`, then apply the existing `List.foldl` induction proof. The
   lambda shape changes from `(fun acc' pair => ... pair.1)` to
   `(fun a b => ... b.fst)` but these are definitionally equal since
   `Prod.fst = Prod.1`.
2. **Test code (S2–S4)**: These are decidable runtime checks in
   `InvariantChecks.lean`. No proofs reference them. Migration is mechanical:
   replace `.toList.foldr f init` with `.fold (fun acc k v => f (k, v) acc) init`.
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
cn.slots.fold (fun inner slot cap => ... ) acc
```

Note: `HashMap.fold` signature is `fold (f : γ → α → β → γ) (init : γ) (m)`,
so in dot notation `m.fold f init`. The lambda receives `(acc, key, value)` as
separate arguments, not as a tuple `(key, value)`. The fold direction difference
(`foldr` → `fold`) does not affect correctness because each check element is
independent (list concatenation is order-insensitive for check validation).

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
cdt.childMap.fold (fun acc parent children => ... ) []
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

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 82–85 (definition only)

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
  cn.slots.fold (fun acc slot _cap =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }
  ) st
```

This eliminates the intermediate `List (Slot × Capability)` allocation.

**Exit**: Definition compiles (proofs will temporarily break).

##### L2-B.2: Update `detachCNodeSlots_objects_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 88–104

The current proof uses `List.foldl` induction:
```lean
have key : ∀ (l : List ...) (acc : SystemState),
  (l.foldl ...).objects = acc.objects := by
  intro l; induction l with ...
```

This must be replaced with a proof that works over `HashMap.fold`. Strategy:
use `Std.HashMap.fold_eq_foldl_toList` to rewrite `HashMap.fold f init m` to
`m.toList.foldl (fun a b => f a b.fst b.snd) init`, then apply the existing
`List.foldl` induction proof which proves the fold body preserves `.objects`
at each step (already established by `detachSlotFromCdt_objects_eq`).

**Exit**: Theorem compiles with zero `sorry`.

##### L2-B.3: Update `detachCNodeSlots_lifecycle_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 107–123

Same proof update pattern as L2-B.2, using `detachSlotFromCdt_lifecycle_eq`
as the per-step preservation lemma.

**Exit**: Theorem compiles with zero `sorry`.

##### L2-B.4: Update `detachCNodeSlots_scheduler_eq` proof

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 178–196

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

### WS-L3: Proof Strengthening — **COMPLETED**

**Objective**: Add 4 missing theorems and 1 new invariant definition that
strengthen the formal assurance of the IPC dual-queue subsystem. L-G05 was
found to be already resolved during pre-implementation audit (theorem exists
in `CallReplyRecv.lean:797`).

**Priority**: MEDIUM — Phase 3
**Dependencies**: WS-L1 (API changes may affect theorem statements)
**Findings addressed**: L-G01, L-G02, L-G03, L-G04
**Finding already resolved**: L-G05 (`endpointReply_preserves_ipcSchedulerContractPredicates`
exists in `CallReplyRecv.lean:797`, proven via handshake-path decomposition)

#### L3-A: Enqueue-dequeue round-trip theorem (L-G01)

**Problem**: No theorem proves that a successfully enqueued thread can be
subsequently dequeued without error from the same queue.

**Subtasks** (3 units of work):

**L3-A1: Enqueue-into-empty-queue postcondition lemma**

Add `endpointQueueEnqueue_empty_sets_head` to `Transport.lean`:
If `endpointQueueEnqueue epId isRecvQ tid st = .ok st'` and the pre-state
queue tail is `none` (empty queue), then in `st'` the endpoint's queue
`head = some tid ∧ tail = some tid`. Proof strategy: unfold `endpointQueueEnqueue`,
take the `q.tail = none` branch, show `storeObject` writes the expected
endpoint. Then extract the TCB state from `storeTcbQueueLinks` to confirm
the thread's `queuePPrev = some .endpointHead`.

**L3-A2: PopHead-after-single-element postcondition lemma**

Add `endpointQueuePopHead_single_returns_thread` to `Transport.lean`:
If an endpoint queue has `head = some tid ∧ tail = some tid` (single-element)
and the thread's `queueNext = none`, then `endpointQueuePopHead` returns
`(tid, tcb, st'')`. Proof: unfold `endpointQueuePopHead`, take the
`headTcb.queueNext = none` branch, confirm head match.

**L3-A3: Composed round-trip theorem**

Add `endpointQueueEnqueue_then_popHead_succeeds` to `Transport.lean`:
Compose L3-A1 and L3-A2: if enqueue into an empty queue succeeds producing
`st'`, then `endpointQueuePopHead` on `st'` succeeds returning the same
`tid`. Requires showing TCB lookup succeeds in the post-enqueue state
(via `endpointQueueEnqueue_tcb_forward`) and that `queueNext = none` for a
single-element queue (from L3-A1 postcondition).

**Files modified**:
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — 3 new theorems

**Exit evidence**:
- `lake build` succeeds
- Zero sorry in new theorems

#### L3-B: Standalone link integrity preservation (L-G02)

**Problem**: `tcbQueueLinkIntegrity` preservation for enqueue/popHead is
bundled inside `dualQueueSystemInvariant` preservation. No standalone
theorems extract just the link integrity component, making compositional
reasoning harder for downstream consumers.

**Subtasks** (2 units of work):

**L3-B1: PopHead standalone link integrity**

Add `endpointQueuePopHead_preserves_tcbQueueLinkIntegrity` to `Structural.lean`:
If `tcbQueueLinkIntegrity st` and `dualQueueEndpointWellFormed epId st` and
`endpointQueuePopHead epId isRecvQ st = .ok (tid, tcb, st')`, then
`tcbQueueLinkIntegrity st'`. Proof: extract from existing
`endpointQueuePopHead_preserves_dualQueueSystemInvariant` by constructing
a minimal `dualQueueSystemInvariant` and projecting `.2`.

**L3-B2: Enqueue standalone link integrity**

Add `endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity` to `Structural.lean`:
If `tcbQueueLinkIntegrity st` and `dualQueueEndpointWellFormed epId st` and
freshness preconditions hold and `endpointQueueEnqueue` succeeds, then
`tcbQueueLinkIntegrity st'`. Same extraction strategy as L3-B1.

**Files modified**:
- `SeLe4n/Kernel/IPC/Invariant/Structural.lean` — 2 new theorems

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-C: ipcState-queue membership consistency invariant (L-G03)

**Problem**: No invariant proves that `tcb.ipcState = .blockedOnSend epId`
implies the thread is on `epId.sendQ`. The invariant exists implicitly
(operations always set both atomically) but is not stated as a formal
property.

**Design decision**: Define as forward implication only (blockedState →
queued), not biconditional. Biconditional would be too strong: after
`endpointQueuePopHead` the thread is dequeued but its ipcState is not yet
updated (the caller sets it). The forward direction captures the safety-
relevant property (no orphaned blocked threads).

**Subtasks** (3 units of work):

**L3-C1: Invariant definition**

Add `ipcStateQueueConsistent (st : SystemState) : Prop` to `Invariant/Defs.lean`:
- `blockedOnSend epId` → `∃ ep, st.objects[epId]? = some (.endpoint ep) ∧
  threadReachableFromHead ep.sendQ tid st` (thread is reachable from sendQ head)
- `blockedOnReceive epId` → thread reachable from receiveQ head
- `blockedOnCall epId` → thread reachable from sendQ head (Call uses sendQ)

Where `threadReachableFromHead q tid st` is a helper predicate: either
`q.head = some tid`, or there exists a chain of `queueNext` links from
`q.head` to `tid`. This avoids requiring full list membership tracking.

Note: We use the simpler forward-implication form. A thread with
`blockedOnReply` is NOT on any queue (it was popped and transitioned), so
blockedOnReply is excluded. A thread with `.ready` being NOT on any queue
is already enforced by `endpointQueueEnqueue`'s precondition check.

**L3-C2: Preservation for queue-only operations**

Add preservation theorems to `Invariant/Structural.lean`:
- `endpointQueuePopHead_preserves_ipcStateQueueConsistent`: PopHead
  removes the head thread but does NOT change any ipcState, so all
  remaining threads' forward implications still hold. The popped thread
  retains its blockedOn* state in the returned TCB but is no longer on
  the queue — this is the expected transient state before the caller
  updates ipcState.
- `endpointQueueEnqueue_preserves_ipcStateQueueConsistent`: Enqueue
  requires `ipcState = .ready`, so the newly-enqueued thread has no
  forward obligation. Existing threads are unaffected.

**L3-C3: Preservation for high-level IPC operations**

Add preservation theorems to `Structural.lean` (required by import
dependency chain — these theorems depend on helpers from both
`EndpointPreservation.lean` and `CallReplyRecv.lean`):
- `endpointSendDual_preserves_ipcStateQueueConsistent`
- `endpointReceiveDual_preserves_ipcStateQueueConsistent`
- `endpointReply_preserves_ipcStateQueueConsistent`

Proof strategy: each operation either (a) enqueues a thread and sets its
ipcState atomically (blockedOn* + enqueue), or (b) dequeues a thread and
sets it to `.ready` (removing the forward obligation). Case (a) adds a
new entry that trivially satisfies the forward implication. Case (b)
removes the obligation by setting `.ready`. Sub-operation helpers
(`storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent`,
`storeTcbIpcState_preserves_ipcStateQueueConsistent`,
`storeTcbPendingMessage_preserves_ipcStateQueueConsistent`,
`ensureRunnable_preserves_ipcStateQueueConsistent`,
`removeRunnable_preserves_ipcStateQueueConsistent`) compose to cover
all intermediate state transitions.

**Files modified**:
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — invariant definition + helper
- `SeLe4n/Kernel/IPC/Invariant/Structural.lean` — queue-op + high-level preservation

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-D: Tail consistency for `endpointQueueRemoveDual` (L-G04)

**Problem**: When removing a non-tail thread from a multi-element queue,
`endpointQueueRemoveDual` preserves the queue tail. This is correct by
inspection but not explicitly proven.

**Subtasks** (2 units of work):

**L3-D1: Tail preservation for non-tail removal**

Add `endpointQueueRemoveDual_preserves_tail_of_nonTail` to `Transport.lean`:
If the removed thread has `queueNext = some _` (i.e., it is not the tail),
then the post-state endpoint queue tail equals the pre-state tail. Proof:
unfold `endpointQueueRemoveDual`, observe that when `tcb.queueNext = some _`
the `newTail` computation returns `q.tail` unchanged, and the final
`storeObject` writes this same tail.

**L3-D2: Tail update characterization for tail removal**

Add `endpointQueueRemoveDual_tail_update` to `Transport.lean`:
Full characterization of tail behavior: when the removed thread IS the
tail (`queueNext = none`), the new tail is either `none` (was sole element,
pprev = endpointHead) or `some prevTid` (pprev = tcbNext prevTid). This
complements L3-D1 by covering the remaining case.

**Files modified**:
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — 2 new theorems

**Exit evidence**:
- `lake build` succeeds
- Zero sorry

#### L3-E: endpointReply contract preservation (L-G05) — ALREADY RESOLVED

**Status**: Pre-implementation audit found that
`endpointReply_preserves_ipcSchedulerContractPredicates` already exists in
`CallReplyRecv.lean:797`. The theorem was added during WS-F1/TPI-D09 work.
No action required.

**Evidence**: `CallReplyRecv.lean:797` — fully machine-checked, zero sorry

---

### WS-L4: Test Coverage Expansion

**Objective**: Fill test coverage gaps discovered during the IPC audit, adding
runtime validation for ReplyRecv multi-sender paths, endpoint lifecycle with
queued threads, blocked-thread rejection, and multi-endpoint interleaving with
3+ endpoints. L-T03 (capability transfer during IPC) is intentionally deferred
because CSpace-IPC integration is not yet modeled.

**Priority**: MEDIUM — Phase 4
**Dependencies**: WS-L1 (performance changes may affect operation signatures)
**Findings addressed**: L-T01, L-T02, L-T04, L-T05
**Finding deferred**: L-T03 (cap transfer requires CSpace IPC integration not yet modeled)

**Implementation status** (partial — items marked ✓ already implemented):

| Task | Sub-step | Status | Version |
|------|----------|--------|---------|
| L4-A | A1 (base roundtrip) | ✓ Complete | v0.16.11 |
| L4-A | A2 (second sender queued) | ✓ Complete | v0.16.12 |
| L4-A | A3 (fixture + registry) | ✓ Complete | v0.16.12 |
| L4-B | B1 (lifecycle fixture) | ✓ Complete | v0.16.12 |
| L4-B | B2 (delete-with-senders) | ✓ Complete | v0.16.12 |
| L4-B | B3 (stale-IPC guard) | ✓ Complete | v0.16.12 |
| L4-B | B4 (fixture + registry) | ✓ Complete | v0.16.12 |
| L4-C | C1 (send-while-blocked) | ✓ Complete | v0.16.11 |
| L4-C | C2 (recv-while-blocked) | ✓ Complete | v0.16.11 |
| L4-C | C3 (ntfn-while-blocked) | ✓ Complete | v0.16.11 |
| L4-C | C4 (cross: recv→send diff ep) | ✓ Complete | v0.16.12 |
| L4-C | C5 (cross: send→recv diff ep) | ✓ Complete | v0.16.12 |
| L4-D | D1 (base 2-endpoint) | ✓ Complete | v0.16.11 |
| L4-D | D2 (3rd endpoint + FIFO) | ✓ Complete | v0.16.12 |
| L4-D | D3 (out-of-order recv) | ✓ Complete | v0.16.12 |
| L4-D | D4 (fixture + registry) | ✓ Complete | v0.16.12 |

#### L4-A: ReplyRecv positive-path test (L-T01)

**Problem**: `endpointReplyRecv` is only tested for bounds-checking rejection
(NegativeStateSuite:572–589). No test exercises the positive path: server
replies to caller, then immediately receives next sender's message.

**Current state**: Base roundtrip implemented in `runReplyRecvRoundtripTrace`
(MainTraceHarness.lean:1548–1598) with scenario IDs RRC-001, RRC-003, RRC-004,
RRC-005. The test covers: caller calls → server receives → server ReplyRecv →
verify caller unblocked with reply message → verify server blocked on receiveQ.

**Remaining gap**: The plan originally called for a second sender (Thread B)
queued on the endpoint before ReplyRecv, so ReplyRecv both replies to Thread A
AND immediately receives Thread B's message (the rendezvous-after-reply path).
This is the more interesting positive-path scenario and exercises the dual
reply+receive semantics of `endpointReplyRecv` more thoroughly.

**Sub-steps**:

- **A2: Add second-sender rendezvous to `runReplyRecvRoundtripTrace`**
  1. After server receives caller A's message, have caller B call the same
     endpoint (B enqueues on sendQ with `.blockedOnCall`).
  2. Server issues `endpointReplyRecv`: replies to A with result message,
     simultaneously receives B's message (rendezvous from sendQ).
  3. Verify: A transitions `.blockedOnReply` → `.ready` with reply message.
  4. Verify: B transitions `.blockedOnCall` → `.blockedOnReply` (server
     received B's message, so B awaits reply).
  5. Verify: server has B's pending message registers.
  6. Emit scenario IDs: `RRC-002` (B's blockedOnReply state), `RRC-006`
     (server received B's message registers).
  7. Update `tests/fixtures/main_trace_smoke.expected` with RRC-002, RRC-006.
  8. Update `tests/fixtures/scenario_registry.yaml` with RRC-002, RRC-006.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — extend `runReplyRecvRoundtripTrace`
- `tests/fixtures/main_trace_smoke.expected` — add RRC-002, RRC-006 fixture lines
- `tests/fixtures/scenario_registry.yaml` — register RRC-002, RRC-006

**Exit evidence**:
- `test_smoke.sh` passes
- All 6 RRC scenario IDs (RRC-001 through RRC-006) visible in trace output
- ITR-001 check count incremented to reflect new invariant checks

#### L4-B: Endpoint lifecycle with queued threads test (L-T02)

**Problem**: No test exercises deletion of an endpoint while threads are blocked
on its send queue. This is a critical edge case for lifecycle safety.

**Design note**: Per `Lifecycle/Operations.lean:33–37`, endpoint queue cleanup
during deletion is intentionally deferred. Blocked threads retain stale
`ipcState` references after endpoint retype. Safety is maintained by
`lookupTcb` guards on all subsequent IPC operations. The test validates this
graceful-failure-by-guard model, not automatic thread unblocking.

**Sub-steps**:

- **B1: Build lifecycle-aware endpoint fixture**
  1. Create a helper state with: endpoint, 2 TCBs (senders), lifecycle
     metadata (`.withLifecycleObjectType`, `.withLifecycleCapabilityRef`),
     a CNode with authority cap for the endpoint.
  2. Block both senders on the endpoint's sendQ via `endpointSendDual`.
  3. Emit `ELC-001`: confirm senders are `blockedOnSend`.

- **B2: Execute retype-as-delete and verify graceful handling**
  1. Use `lifecycleRevokeDeleteRetype` to delete (retype) the endpoint.
  2. Verify: operation succeeds (`.ok`).
  3. Verify: senders' `ipcState` still references the old endpoint ID
     (stale but safe — no automatic cleanup).
  4. Emit `ELC-002`: confirm retype succeeded.
  5. Emit `ELC-003`: confirm senders retain stale `blockedOnSend` state.

- **B3: Validate stale-IPC guard rejection**
  1. Attempt `endpointSendDual` on the now-retyped object ID.
  2. Verify: operation returns error (`.objectNotFound` or type mismatch)
     because the endpoint object no longer exists under that ID.
  3. Emit `ELC-004`: confirm stale endpoint operations are rejected.

- **B4: Update fixtures and registry**
  1. Add ELC-001 through ELC-004 to `main_trace_smoke.expected`.
  2. Add ELC-001 through ELC-004 to `scenario_registry.yaml`.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — new `runEndpointLifecycleTrace`
- `tests/fixtures/main_trace_smoke.expected` — ELC fixture lines
- `tests/fixtures/scenario_registry.yaml` — ELC registry entries

**Exit evidence**:
- `test_smoke.sh` passes
- ELC-001 through ELC-004 visible in trace output
- ITR-001 check count incremented

#### L4-C: Blocked thread IPC rejection test (L-T04) — COMPLETED (v0.16.11, extended v0.16.12)

**Problem**: No explicit test verifies that a thread already blocked on IPC
is rejected when attempting another IPC operation.

**Resolution**: Implemented as `runWSL4BlockedThreadChecks` in
`NegativeStateSuite.lean:2200–2275`. Five rejection scenarios validated:

Same-type rejection (v0.16.11):
1. Thread blocked on send → second send rejected with `.alreadyWaiting`
2. Thread blocked on receive → second receive rejected with `.alreadyWaiting`
3. Thread blocked on notification wait → send rejected with `.alreadyWaiting`

Cross-state rejection (v0.16.12):
4. Thread blocked on receive → send to *different* endpoint rejected with `.alreadyWaiting`
5. Thread blocked on send → receive from *different* endpoint rejected with `.alreadyWaiting`

All five use `expectError` with `.alreadyWaiting` error variant. Cross-state
tests use a separate endpoint (ObjId 41) to ensure the enqueue path is taken
(not the rendezvous path). Invoked from `main` at NegativeStateSuite.lean.

#### L4-D: Multi-endpoint interleaving test (L-T05)

**Problem**: Existing tests use at most 2 endpoints. Complex interleaving
across 3+ endpoints is not tested.

**Current state**: Base 2-endpoint test implemented in
`runMultiEndpointInterleavingTrace` (MainTraceHarness.lean:1604–1646) with
scenario IDs MEI-001, MEI-002, MEI-003. Covers: send on EP1 → receive EP1 →
send on EP2 → receive EP2 → verify cross-endpoint independence.

**Remaining gaps**:
1. Only 2 endpoints used (plan specified 3+).
2. No FIFO ordering verification within a single endpoint.
3. No out-of-order receive verification (receive from EP2 before EP1).

**Sub-steps**:

- **D2: Add 3rd endpoint and FIFO verification**
  1. Add EP3 (`ObjId ⟨201⟩`) to the endpoint set.
  2. Send two messages to EP1 from different threads (or same thread
     re-readied between sends) to create a 2-deep sendQ.
  3. Receive both from EP1 and verify FIFO order (first-sent received first).
  4. Emit `MEI-004`: confirm FIFO ordering on EP1.

- **D3: Add out-of-order cross-endpoint receive**
  1. Send on EP3, then send on EP1 (reversed creation order).
  2. Receive from EP3 first, then EP1 — verify correct message isolation.
  3. Emit `MEI-005`: confirm EP3 message received correctly.
  4. Emit `MEI-006`: confirm all 3 endpoints' queues are empty after draining.

- **D4: Update fixtures and registry**
  1. Add MEI-004, MEI-005, MEI-006 to `main_trace_smoke.expected`.
  2. Add MEI-004, MEI-005, MEI-006 to `scenario_registry.yaml`.

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — extend `runMultiEndpointInterleavingTrace`
- `tests/fixtures/main_trace_smoke.expected` — add MEI-004/005/006 fixture lines
- `tests/fixtures/scenario_registry.yaml` — register MEI-004/005/006

**Exit evidence**:
- `test_smoke.sh` passes
- All 6 MEI scenario IDs (MEI-001 through MEI-006) visible in trace output
- ITR-001 check count incremented

---

### WS-L5: Documentation & Workstream Closeout

**Objective**: Resolve all deferred WS-I5 documentation items, update all
project documentation to reflect WS-L changes, regenerate metrics, and close
the WS-L portfolio with full evidence.

**Priority**: LOW — Phase 5 (after all implementation phases)
**Dependencies**: WS-L1 through WS-L4
**Findings addressed**: L-D01, L-D02, L-D03, L-D05

#### L5-A: Information-flow architecture readers' guide (L-D02)

**Problem**: WS-I5/R-13 identified a missing readers' guide for the 3-layer
information-flow architecture (Policy → Enforcement → Invariant).

**Deliverables**:

1. Add a new section to `docs/gitbook/12-proof-and-invariant-map.md` titled
   "Information-flow architecture readers' guide" explaining:
   - **Layer 1 — Policy** (`InformationFlow/Policy.lean`): `SecurityLabel`
     product structure (`Confidentiality × Integrity`), `securityFlowsTo`
     decidable predicate, `LabelingContext` for assigning labels to objects,
     threads, endpoints, and services. Pure declarative specification with no
     state mutation.
   - **Layer 2 — Enforcement** (`InformationFlow/Enforcement/Wrappers.lean`,
     `Enforcement/Soundness.lean`): thin policy-gated wrappers that embed
     a single `securityFlowsTo` check before delegating to the underlying
     unchecked operation. 7 wrapped operations (`endpointSendDualChecked`,
     `notificationSignalChecked`, `cspaceMintChecked`, `cspaceCopyChecked`,
     `cspaceMoveChecked`, `endpointReceiveDualChecked`, `serviceRestartChecked`).
     Soundness theorems prove transparency on allowed flows and safe denial
     on policy violations.
   - **Layer 3 — Invariant** (`InformationFlow/Projection.lean`,
     `Invariant/Helpers.lean`, `Invariant/Operations.lean`,
     `Invariant/Composition.lean`): `ObservableState` projection defines what
     each security-cleared observer can see. Per-operation NI theorems in
     `Operations.lean` prove each kernel primitive preserves `lowEquivalent`
     for non-observable targets. `Composition.lean` provides the multi-step
     `composedNonInterference_trace` theorem (IF-M4). `Helpers.lean` provides
     shared frame lemmas (`storeObject_at_unobservable_preserves_lowEquivalent`).
   - **Cross-layer connections**: Policy feeds Enforcement (wrapper embeds
     `securityFlowsTo` check); Enforcement's soundness guarantees only safe
     calls reach the kernel; Invariant proves those calls preserve NI.
2. Include cross-references to all canonical source files with relative paths.

**Files modified**:
- `docs/gitbook/12-proof-and-invariant-map.md` — new section (§22)

**Exit evidence**:
- New section present in GitBook chapter 12
- All source file references resolve to existing paths

#### L5-B: Test fixture update process documentation (L-D03)

**Problem**: WS-I5/R-14 identified that the process for updating test fixtures
is undocumented.

**Status**: **COMPLETED** (v0.16.12) — documentation added to `docs/DEVELOPMENT.md`
§7 "Test fixture update process (WS-L5-B)" as part of WS-L4 delivery.

**Delivered content** (in `docs/DEVELOPMENT.md` §7):
- When fixtures need updating (new trace scenarios, changed output format)
- Step-by-step regeneration: add scenario IDs, rebuild, run `lake exe sele4n`,
  update `tests/fixtures/main_trace_smoke.expected` and `scenario_registry.yaml`
- ITR-001 count update procedure
- CI enforcement: Tier 0 registry validation + Tier 2 fixture comparison

**Files modified**: `docs/DEVELOPMENT.md` — section already present

#### L5-C: Metrics regeneration documentation (L-D05)

**Problem**: WS-I5/R-18 identified that metrics regeneration is manual and
undocumented.

**Status**: **COMPLETED** (v0.16.12) — documentation added to `docs/DEVELOPMENT.md`
§7 "Metrics regeneration process (WS-L5-C)" as part of WS-L4 delivery.

**Delivered content** (in `docs/DEVELOPMENT.md` §7):
- Run `./scripts/report_current_state.py` for updated metrics
- Update `README.md`, `docs/spec/SELE4N_SPEC.md`, and
  `docs/gitbook/05-specification-and-roadmap.md` — all three must match
- Regenerate `docs/codebase_map.json` via `generate_codebase_map.py`
- Validate with `./scripts/test_docs_sync.sh`

**Files modified**: `docs/DEVELOPMENT.md` — section already present

#### L5-D1: Version bump and metrics regeneration

**Problem**: WS-L implementation changes (L1–L4) added new theorems, test
scenarios, and LoC that are not yet reflected in the canonical version string
or metrics surfaces.

**Deliverables**:

1. Bump `lakefile.toml` version from `0.16.12` to `0.16.13`.
2. Run `./scripts/report_current_state.py` to capture updated metrics.
3. Run `./scripts/generate_codebase_map.py --pretty --output docs/codebase_map.json`
   to regenerate the machine-readable codebase map.
4. Validate with `./scripts/generate_codebase_map.py --pretty --check`.

**Files modified**:
- `lakefile.toml` — version bump
- `docs/codebase_map.json` — regenerated

**Exit evidence**:
- `lakefile.toml` contains `version = "0.16.13"`
- `generate_codebase_map.py --pretty --check` passes

#### L5-D2: README and specification metrics sync

**Problem**: `README.md` and `docs/spec/SELE4N_SPEC.md` metrics (version, LoC,
theorem count) must match the regenerated codebase map.

**Deliverables**:

1. Update `README.md` — version badge, production/test LoC, proved declaration
   count, latest audit reference, and active workstream status (WS-L5 complete).
2. Update `docs/spec/SELE4N_SPEC.md` — version, metrics, IPC subsystem status,
   and workstream phase completions (L1–L5 all COMPLETED).

**Files modified**:
- `README.md` — metrics section
- `docs/spec/SELE4N_SPEC.md` — current state snapshot

**Exit evidence**:
- Version `0.16.13` in both files
- LoC and theorem counts match `report_current_state.py` output

#### L5-D3: DEVELOPMENT.md workstream reference update

**Problem**: `docs/DEVELOPMENT.md` §3 "Next workstreams" references WS-L5 as
"in progress" and needs to reflect WS-L completion.

**Deliverables**:

1. Update §3 to mark WS-L5 as **COMPLETED** (v0.16.13).
2. Update the "active workstream" reference to reflect the next milestone
   (Raspberry Pi 5 hardware binding).
3. Add WS-L to the completed workstream list in §1.

**Files modified**:
- `docs/DEVELOPMENT.md` — §1 and §3

**Exit evidence**:
- WS-L5 marked COMPLETED in §3
- WS-L listed in §1 completed workstream section

#### L5-D4: Workstream history and claim evidence update

**Problem**: `docs/WORKSTREAM_HISTORY.md` and `docs/CLAIM_EVIDENCE_INDEX.md`
must reflect WS-L portfolio completion.

**Deliverables**:

1. Update `docs/WORKSTREAM_HISTORY.md`:
   - Mark WS-L5 as **COMPLETED** (v0.16.13) in the WS-L phase table.
   - Update WS-L portfolio status from "IN PROGRESS" to "COMPLETED".
   - Add WS-L5 summary (documentation sync, readers' guide, version bump).
2. Update `docs/CLAIM_EVIDENCE_INDEX.md`:
   - Update WS-L portfolio claim row to reflect L5 completion.
   - Add WS-L5 documentation claim with evidence commands.

**Files modified**:
- `docs/WORKSTREAM_HISTORY.md` — WS-L phase table and portfolio status
- `docs/CLAIM_EVIDENCE_INDEX.md` — WS-L claim rows

**Exit evidence**:
- WS-L portfolio shows 5/5 phases COMPLETED
- Claim evidence index includes L5 deliverables

#### L5-D5: GitBook chapter synchronization

**Problem**: GitBook mirrors must reflect WS-L implementation changes and
new documentation.

**Deliverables**:

1. Update `docs/gitbook/03-architecture-and-module-map.md`:
   - Note WS-L1 IPC hot-path optimizations (TCB lookup elimination).
2. Update `docs/gitbook/04-project-design-deep-dive.md`:
   - Add subsection on IPC hot-path optimization design (pass-through TCB
     pattern from `endpointQueuePopHead` to avoid re-lookup).
3. Update `docs/gitbook/05-specification-and-roadmap.md`:
   - Version bump to `0.16.13`.
   - Update LoC/theorem metrics.
   - Mark WS-L as COMPLETED in roadmap table.
4. Update `docs/gitbook/12-proof-and-invariant-map.md`:
   - Add WS-L3 theorems (enqueue-dequeue round-trip, queue link integrity
     preservation, `ipcStateQueueConsistent` invariant + preservation,
     tail consistency).
   - Add information-flow readers' guide (L5-A deliverable, see above).

**Files modified**:
- `docs/gitbook/03-architecture-and-module-map.md` — IPC optimization note
- `docs/gitbook/04-project-design-deep-dive.md` — hot-path design subsection
- `docs/gitbook/05-specification-and-roadmap.md` — version and metrics
- `docs/gitbook/12-proof-and-invariant-map.md` — new theorems + readers' guide

**Exit evidence**:
- All 4 GitBook chapters updated
- Version and metrics consistent with README and spec

#### L5-D6: Test suite validation and CI readiness

**Problem**: All test tiers must pass after documentation and version changes.

**Deliverables**:

1. Run `./scripts/test_full.sh` (Tier 0–3).
2. Fix any Tier 0 hygiene failures (website link manifest, forbidden markers).
3. Fix any Tier 3 invariant surface anchor mismatches from new theorems or
   documentation changes.
4. Verify zero `sorry`/`axiom` in production proof surface.
5. Verify zero warnings from `lake build`.

**Files modified**: Test scripts and anchors only if failures require fixes.

**Exit evidence**:
- `test_full.sh` passes with zero failures
- `lake build` completes with zero warnings
- All metrics consistent across README, spec, GitBook

---

## 6. Finding-to-Phase Traceability Matrix

| Finding | Phase | Task | Status |
|---------|-------|------|--------|
| L-P01 | WS-L1 | L1-A | **COMPLETED** (v0.16.9) |
| L-P02 | WS-L1 | L1-B | **COMPLETED** (v0.16.9) |
| L-P03 | WS-L1 | L1-C | **COMPLETED** (v0.16.9) |
| L-D04 | WS-L2 | L2-A (S2–S4), L2-B (S1) | **COMPLETED** (v0.16.10) |
| L-G01 | WS-L3 | L3-A | **COMPLETED** (v0.16.11) |
| L-G02 | WS-L3 | L3-B | **COMPLETED** (v0.16.11) |
| L-G03 | WS-L3 | L3-C | **COMPLETED** (v0.16.11) — C1 definition + C2 queue-op preservation + C3 high-level preservation (all 3 theorems) |
| L-G04 | WS-L3 | L3-D | **COMPLETED** (v0.16.11) |
| L-G05 | WS-L3 | L3-E | **ALREADY RESOLVED** (pre-existing in `CallReplyRecv.lean:797`) |
| L-T01 | WS-L4 | L4-A (A1–A2) | **COMPLETED** (v0.16.12) — base roundtrip + A2 second-sender rendezvous |
| L-T02 | WS-L4 | L4-B (B1–B4) | **COMPLETED** (v0.16.12) — lifecycle retype with queued senders + stale guard |
| L-T04 | WS-L4 | L4-C (C1–C5) | **COMPLETED** (v0.16.11, extended v0.16.12) — 3 same-type + 2 cross-state rejection |
| L-T05 | WS-L4 | L4-D (D1–D4) | **COMPLETED** (v0.16.12) — 3-endpoint out-of-order + FIFO verification |
| L-D01 | — | — | Superseded (WS-J1) |
| L-D02 | WS-L5 | L5-A | **COMPLETED** (v0.16.13) |
| L-D03 | WS-L5 | L5-B | **COMPLETED** (v0.16.12, early delivery) |
| L-D05 | WS-L5 | L5-C | **COMPLETED** (v0.16.12, early delivery) |
| L-T03 | — | — | Deferred (cap transfer requires CSpace IPC integration not yet modeled) |

---

## 7. Completion Evidence Checklist

- [x] `lake build` succeeds with zero warnings
- [x] `test_smoke.sh` passes
- [x] `test_full.sh` passes
- [x] Zero `sorry`/`axiom` in production proof surface
- [x] All 13 findings addressed (12 resolved, 1 intentionally deferred with rationale)
- [x] All 4 WS-I5 deferred items resolved (L-D01 superseded, L-D02/L5-A, L-D03/L5-B, L-D05/L5-C)
- [x] Documentation synchronized across all canonical sources (L5-D1 through L5-D6)
- [x] `codebase_map.json` regenerated (L5-D1)
- [x] WS-L portfolio entry added to `WORKSTREAM_HISTORY.md` (L5-D4)
- [x] WS-L claim row added to `CLAIM_EVIDENCE_INDEX.md` (L5-D4)
- [x] Information-flow readers' guide added to GitBook ch.12 (L5-A)
- [x] Version bumped to 0.16.13 (L5-D1)
- [x] Metrics synchronized across README, spec, GitBook (L5-D2, L5-D5)

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
