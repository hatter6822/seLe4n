# V3-J/K: Preservation Proofs for Queue Membership & No-Duplicate Invariants

**Workstream**: WS-V Phase V3+ — Proof Chain Hardening (Preservation Extension)
**Scope**: V3-J (ipcStateQueueMembershipConsistent preservation) + V3-K (endpointQueueNoDup preservation)
**Source Findings**: L-IPC-3 (V3-J), L-LIFE-1 (V3-K)
**Prerequisites**: V3 Phase complete (v0.22.2) — predicate definitions machine-checked
**Dependencies**: `dualQueueSystemInvariant` preservation (complete), `tcbQueueChainAcyclic` (complete)
**Gate Conditions**: `lake build` succeeds; zero `sorry`; `test_full.sh` green
**Estimated Scope**: ~1200-1600 lines Lean (proofs), ~30-50 lines modified, ~0 lines runtime code

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Current State Analysis](#2-current-state-analysis)
3. [V3-K: endpointQueueNoDup Preservation Proofs](#3-v3-k-endpointqueuenodup-preservation-proofs)
4. [V3-J: ipcStateQueueMembershipConsistent Preservation Proofs](#4-v3-j-ipcstatequeuemembershipconsistent-preservation-proofs)
5. [Bundle Integration Plan](#5-bundle-integration-plan)
6. [Execution Order & Dependency Graph](#6-execution-order--dependency-graph)
7. [Cross-Cutting Concerns](#7-cross-cutting-concerns)
8. [Risk Assessment & Mitigations](#8-risk-assessment--mitigations)
9. [Testing & Validation Strategy](#9-testing--validation-strategy)
10. [Documentation Synchronization](#10-documentation-synchronization)

---

## 1. Executive Summary

Phase V3 (Proof Chain Hardening) delivered predicate definitions for two critical
queue invariants — `ipcStateQueueMembershipConsistent` (V3-J) and
`endpointQueueNoDup` (V3-K) — as machine-checked definitions in
`IPC/Invariant/Defs.lean`. However, **no preservation proofs** exist for either
predicate. Without preservation proofs, these invariants cannot be composed into
the kernel's invariant bundle, and the machine-checked guarantee that they hold
across all state transitions is absent.

This plan details the complete implementation of preservation proofs for both
predicates across all IPC operations that modify endpoint queues, TCB ipcState,
or TCB queueNext links. The work is structured as two parallel proof chains
(V3-K and V3-J) that converge at a bundle integration phase.

**V3-K (`endpointQueueNoDup`)** enforces two properties:
1. No TCB self-loops: `queueNext tcb ≠ some tid` for all threads
2. Send/receive queue head disjointness: no thread heads both queues simultaneously

**V3-J (`ipcStateQueueMembershipConsistent`)** enforces bidirectional consistency:
- Every thread with `ipcState = .blockedOnSend epId` is reachable from
  `ep.sendQ.head` via `queueNext` links
- Every thread with `ipcState = .blockedOnReceive epId` or `.blockedOnCall epId`
  is reachable from `ep.receiveQ.head` via `queueNext` links

Together, these predicates close the formal gap between the kernel's queue
structure and the IPC blocking state machine, ensuring that blocked threads are
always located in the correct queue and that queue traversal is guaranteed to
terminate without revisiting nodes.

---

## 2. Current State Analysis

### 2.1. Predicate Definitions (Complete — v0.22.2)

Both predicates are defined in `SeLe4n/Kernel/IPC/Invariant/Defs.lean`:

**V3-K: `endpointQueueNoDup`** (Defs.lean:821-829)
```lean
def endpointQueueNoDup (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[oid]? = some (.endpoint ep) →
    (∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      TCB.queueNext tcb ≠ some tid) ∧
    (ep.sendQ.head = none ∨ ep.receiveQ.head = none ∨
     ep.sendQ.head ≠ ep.receiveQ.head)
```

**V3-J: `ipcStateQueueMembershipConsistent`** (Defs.lean:790-812)
```lean
def ipcStateQueueMembershipConsistent (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (KernelObject.tcb tcb) →
    match tcb.ipcState with
    | .blockedOnSend epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnReceive epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨ ...)
    | .blockedOnCall epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨ ...)
    | _ => True
```

### 2.2. Existing Proof Infrastructure

The V3-G6 work (complete) established the pattern for adding invariant
predicates to the IPC subsystem. The template involves:

1. **Primitive frame lemmas** in `Structural.lean` — showing storage operations
   that don't touch the relevant fields preserve the invariant
2. **Per-operation preservation** in the appropriate preservation file
3. **Bundle integration** — adding the predicate to `ipcInvariantFull` and
   updating extractor theorems

**Existing related infrastructure**:

| Infrastructure | Location | Status | Relevance |
|---------------|----------|--------|-----------|
| `tcbQueueChainAcyclic` preservation | `Structural.lean` | Complete | V3-K self-loop property is implied by acyclicity |
| `tcbQueueLinkIntegrity` preservation | `Structural.lean` | Complete | V3-J reachability depends on link integrity |
| `dualQueueSystemInvariant` preservation | `Structural.lean` | Complete | Contains `tcbQueueChainAcyclic` as conjunct |
| `intrusiveQueueWellFormed` preservation | `Structural.lean` | Complete | Queue structure needed for V3-J head reasoning |
| `QueueNextPath` inductive type | `Defs.lean:135-141` | Complete | V3-J reachability encoding |
| `QueueNextPath_trans` | `Defs.lean:148-154` | Complete | Path composition for V3-J |
| `tcbQueueChainAcyclic_no_self_loop` | `Defs.lean:157-163` | Complete | Directly proves V3-K component 1 |
| `storeTcbQueueLinks_preserves_*` | `DualQueue/Core.lean` | Complete | Primitive for queue link operations |

### 2.3. Critical Observation: V3-K Self-Loop Redundancy

The V3-K predicate's first component (no self-loops) states:
```lean
∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
  st.objects[tid.toObjId]? = some (.tcb tcb) →
  TCB.queueNext tcb ≠ some tid
```

This is **already implied** by `tcbQueueChainAcyclic` (which is part of
`dualQueueSystemInvariant`, which is part of `ipcInvariantFull`). The existing
theorem `tcbQueueChainAcyclic_no_self_loop` (Defs.lean:157-163) proves exactly
this. Therefore, V3-K's first component preservation is **already done** — it
follows from the existing `dualQueueSystemInvariant` preservation proofs.

The only new proof work for V3-K is the **second component**: send/receive
queue head disjointness.

### 2.4. Current `ipcInvariantFull` (5 conjuncts)

```lean
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧
  dualQueueSystemInvariant st ∧
  allPendingMessagesBounded st ∧
  badgeWellFormed st ∧
  waitingThreadsPendingMessageNone st
```

After V3-J/K integration, this will become 7 conjuncts:
```lean
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧
  dualQueueSystemInvariant st ∧
  allPendingMessagesBounded st ∧
  badgeWellFormed st ∧
  waitingThreadsPendingMessageNone st ∧
  endpointQueueNoDup st ∧
  ipcStateQueueMembershipConsistent st
```

### 2.5. Operations Requiring Preservation Proofs

Every operation that modifies endpoint queues, TCB `ipcState`, or TCB
`queueNext` fields must preserve both predicates. The complete list:

| Operation | Modifies Queues | Modifies ipcState | Modifies queueNext | File |
|-----------|:-:|:-:|:-:|------|
| `endpointQueueEnqueue` | head/tail | — | prev.queueNext, new.queuePrev | `DualQueue/Core.lean` |
| `endpointQueuePopHead` | head | — | next.queuePrev, head.queueNext/Prev | `DualQueue/Core.lean` |
| `endpointQueueRemoveDual` | head/tail | — | prev.queueNext, next.queuePrev | `DualQueue/Transport.lean` |
| `storeTcbIpcState` | — | target | — | `Operations/Endpoint.lean` |
| `storeTcbIpcStateAndMessage` | — | target | — | `Operations/Endpoint.lean` |
| `storeTcbQueueLinks` | — | — | target | `DualQueue/Core.lean` |
| `endpointSendDual` | yes (enqueue or popHead) | sender + receiver | yes (via queue ops) | `DualQueue/Transport.lean` |
| `endpointReceiveDual` | yes (enqueue or popHead) | receiver + sender | yes (via queue ops) | `DualQueue/Transport.lean` |
| `endpointCall` | yes (enqueue or popHead) | caller + receiver | yes (via queue ops) | `DualQueue/Transport.lean` |
| `endpointReply` | — | target | — | `DualQueue/Transport.lean` |
| `endpointReplyRecv` | yes (reply + receive) | replier + target | yes (via receive) | `DualQueue/Transport.lean` |
| `notificationSignal` | — | waiter | — | `Operations/Endpoint.lean` |
| `notificationWait` | — | waiter | — | `Operations/Endpoint.lean` |
| `lifecycleRetypeObject` | — | — | — | `Lifecycle/Operations.lean` |
| `storeObject` (non-TCB) | varies | — | — | (generic) |

**Operations that do NOT need proofs** (only modify scheduler, capabilities,
or unrelated fields):
- `ensureRunnable` / `removeRunnable` — scheduler only, no object modification
- `ipcUnwrapCaps` / `ipcTransferSingleCap` — CNode only, no TCB/endpoint modification
- `cspaceMint` / `cspaceDelete` — CNode + CDT only

---

## 3. V3-K: endpointQueueNoDup Preservation Proofs

### 3.1. Predicate Decomposition

`endpointQueueNoDup` is a universally-quantified conjunction over all endpoints.
For each endpoint, two properties must hold:

**Component K-1**: No self-loops in `queueNext` (global over all TCBs)
```lean
∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
  st.objects[tid.toObjId]? = some (.tcb tcb) →
  TCB.queueNext tcb ≠ some tid
```

**Component K-2**: Send/receive queue head disjointness
```lean
ep.sendQ.head = none ∨ ep.receiveQ.head = none ∨
ep.sendQ.head ≠ ep.receiveQ.head
```

As noted in Section 2.3, K-1 is **already proven** via `tcbQueueChainAcyclic`
(part of `dualQueueSystemInvariant`). The theorem
`tcbQueueChainAcyclic_no_self_loop` (Defs.lean:157-163) provides exactly this.
Therefore, K-1 preservation follows from existing `dualQueueSystemInvariant`
preservation proofs — no new work needed.

**All new proof work for V3-K targets K-2 exclusively.**

### 3.2. K-2 Analysis: Queue Head Disjointness

The disjointness property states that for every endpoint, no thread ID
appears as the head of both `sendQ` and `receiveQ` simultaneously.

**Why this holds structurally**: `endpointQueueEnqueue` guards against
double-enqueue via the `ipcState ≠ .ready` check (DualQueue/Core.lean:294).
A thread must be `.ready` to enqueue. After enqueue, its `ipcState` changes
to a blocking state. Since a thread can only be in one blocking state at a
time, it can only be in one queue at a time. Queue heads are drawn from
their respective queues, so they must be different threads.

**Operations that can change queue heads**:

| Operation | sendQ.head change | receiveQ.head change |
|-----------|------------------|---------------------|
| `endpointQueueEnqueue(_, false, tid)` | `none → some tid` (empty) or unchanged (non-empty) | unchanged |
| `endpointQueueEnqueue(_, true, tid)` | unchanged | `none → some tid` (empty) or unchanged |
| `endpointQueuePopHead(_, false)` | `some h → some h.next` or `none` | unchanged |
| `endpointQueuePopHead(_, true)` | unchanged | `some h → some h.next` or `none` |
| `endpointQueueRemoveDual` (at head) | may change | may change |
| `storeObject` (replacing endpoint) | arbitrary | arbitrary |

### 3.3. V3-K Sub-Task Breakdown

#### V3-K-prim-1: Primitive `storeObject` Frame Lemma

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Small (~20-30 lines)

When `storeObject` stores a non-endpoint, non-TCB object, `endpointQueueNoDup`
is trivially preserved because neither endpoint queues nor TCB `queueNext`
fields change.

```lean
/-- Storing a non-endpoint, non-TCB object preserves endpointQueueNoDup. -/
theorem storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    endpointQueueNoDup st'
```

**Proof strategy**: For K-1, TCBs at `tid ≠ oid` are unchanged
(`storeObject_objects_ne`), and `oid` is not a TCB (`hNotTcb`). For K-2,
endpoints at `epId ≠ oid` are unchanged, and `oid` is not an endpoint
(`hNotEp`).

#### V3-K-prim-2: `storeTcbQueueLinks` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Small (~25-40 lines)

`storeTcbQueueLinks` modifies one TCB's queue links. K-1 is already handled
by `dualQueueSystemInvariant`. For K-2, endpoint queue heads are NOT changed
by TCB stores (endpoints are different objects), so the disjointness property
transfers directly.

```lean
theorem storeTcbQueueLinks_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    endpointQueueNoDup st'
```

**Proof strategy**: Storing a TCB does not modify any endpoint object.
For any endpoint `ep` at `oid`, `st'.objects[oid]? = st.objects[oid]?` (since
`oid` is an endpoint key, not a TCB key, and `objects.invExt` ensures type
safety). Therefore `ep.sendQ.head` and `ep.receiveQ.head` are unchanged.
K-1 follows from `hAcyclic` (post-state acyclicity). K-2 follows from
endpoint object stability.

#### V3-K-prim-3: Endpoint Store with Known Queue Heads

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~40-60 lines)

When `storeObject` replaces an endpoint, we need to verify that the new
endpoint's queue heads satisfy disjointness. This requires a precondition
about the new endpoint's queue structure.

```lean
theorem storeObject_endpoint_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep' : Endpoint)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep') st = .ok ((), st'))
    (hDisjoint : ep'.sendQ.head = none ∨ ep'.receiveQ.head = none ∨
                 ep'.sendQ.head ≠ ep'.receiveQ.head) :
    endpointQueueNoDup st'
```

**Proof strategy**: For the stored endpoint at `oid`, K-2 follows from
`hDisjoint`. For other endpoints at `oid' ≠ oid`, their objects are unchanged
(`storeObject_objects_ne`). K-1 follows from `hAcyclic`.

#### V3-K-op-1: `endpointQueueEnqueue` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~60-80 lines)

This is the **most important** V3-K proof. `endpointQueueEnqueue` modifies
one endpoint's queue and one or two TCBs' queue links.

**Two sub-cases**:

**Case A: Empty queue** (no existing tail)
- Queue becomes `{ head := some tid, tail := some tid }`
- The other queue is unchanged
- If the enqueue targets sendQ: `receiveQ.head` unchanged. The new
  `sendQ.head = some tid`. Must show `tid ≠ receiveQ.head` (if receiveQ
  is non-empty). This follows from the enqueue guard: `ipcState = .ready`
  means the thread is not blocked on receive, so it cannot be in the
  receive queue head.

**Case B: Non-empty queue** (existing tail)
- Queue head is unchanged (only tail is updated)
- New thread is appended at tail, not head
- K-2 is trivially preserved (heads unchanged)

**Key precondition**: The thread being enqueued has `ipcState = .ready` and
no existing queue links. This means it's not currently in any queue, which
implies it cannot be any queue's head. Combined with the pre-state K-2
disjointness, the post-state disjointness follows.

**Proof sketch** (Case A, send-side enqueue):
```
-- Pre: hInv gives (for all eps) sendQ.head = none ∨ ...
-- Post: sendQ.head = some tid
-- Need: some tid ≠ receiveQ.head
-- From: tid has ipcState = .ready (enqueue guard)
-- From: ipcSchedulerCoherence (or separate precondition) implies tid not in any queue
-- Therefore: tid ≠ receiveQ.head
```

**Important**: This proof may need `ipcStateQueueMembershipConsistent` or a
weaker precondition (thread not in any queue head) as a hypothesis. If so,
this creates a **dependency from V3-K to V3-J** for the receive-side case.
See Section 7.1 for analysis.

**Alternative approach**: Use the `endpointQueueEnqueue` guard check
(`tcb.ipcState ≠ .ready` returns error) plus the observation that the
queue head TCB must have a non-ready ipcState. Since the enqueue guard
ensures `ipcState = .ready`, and queue-head threads have non-ready ipcState,
the enqueuing thread cannot equal any queue head. This avoids the V3-J
dependency and is self-contained.

#### V3-K-op-2: `endpointQueuePopHead` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~50-70 lines)

PopHead removes the head of one queue and advances to the next element.

**Analysis**: PopHead on sendQ changes `sendQ.head` from `some h` to
`h.queueNext` (or `none`). The `receiveQ.head` is unchanged. If the new
`sendQ.head` (= `h.queueNext`) equals `receiveQ.head`, that would violate
K-2. But this cannot happen because:

1. `h.queueNext` points to the next thread in the send queue
2. That thread has `ipcState = .blockedOnSend` (it's in the send queue)
3. If it were also `receiveQ.head`, it would need to be in the receive queue
4. But a thread can only be in one queue (by `ipcState` exclusivity)
5. Therefore `h.queueNext ≠ receiveQ.head`

**Precondition needed**: A weaker form of V3-J — that threads reachable via
sendQ have `ipcState = .blockedOnSend`, not `.blockedOnReceive`. OR we can
use `tcbQueueLinkIntegrity` + `intrusiveQueueWellFormed` to argue that
queue-internal threads cannot be queue heads of the opposite queue.

**Alternative self-contained approach**: Use the existing
`dualQueueEndpointWellFormed` (receiveQ head has `queuePrev = none`) and
`tcbQueueLinkIntegrity` (if `h.queueNext = some n`, then `n.queuePrev = some h`,
so `n.queuePrev ≠ none`). Since `receiveQ.head` has `queuePrev = none` and
`h.queueNext` has `queuePrev = some h ≠ none`, they cannot be the same thread.

This is the **cleanest approach** — it uses only existing infrastructure from
`dualQueueSystemInvariant` without needing V3-J.

#### V3-K-op-3: `endpointQueueRemoveDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~60-80 lines)

`endpointQueueRemoveDual` removes an arbitrary thread from a queue (not just
the head). It handles head removal, tail removal, and middle removal.

**Head removal case**: Similar to PopHead — the new head is the removed
thread's `queueNext`. By the same `queuePrev` argument as V3-K-op-2, the
new head cannot be the opposite queue's head.

**Tail/middle removal**: Queue heads are unchanged. K-2 trivially preserved.

#### V3-K-op-4: `endpointSendDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` or `Structural.lean`
**Scope**: Medium (~40-60 lines)

Composes primitive preservation:
- **Rendezvous path**: `endpointQueuePopHead` (receive queue) + `storeTcbIpcStateAndMessage` + `ensureRunnable`
- **Block path**: `endpointQueueEnqueue` (send queue) + `storeTcbIpcStateAndMessage` + `removeRunnable`

Each step's preservation chains to the next.

#### V3-K-op-5: `endpointReceiveDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` or `Structural.lean`
**Scope**: Medium (~50-70 lines)

- **Rendezvous path**: `endpointQueuePopHead` (send queue) + `storeTcbIpcStateAndMessage` × 2 + `ensureRunnable` + `storeTcbPendingMessage`
- **Block path**: `endpointQueueEnqueue` (receive queue) + `storeTcbIpcState` + `removeRunnable`

More complex than send due to the Call/Send split in the rendezvous path.

#### V3-K-op-6: `endpointCall` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` or `Structural.lean`
**Scope**: Medium (~40-60 lines)

- **Rendezvous path**: PopHead + wake receiver + block caller as `.blockedOnReply`
- **Block path**: Enqueue caller on send queue + block as `.blockedOnCall`

Neither path creates new queue heads that violate disjointness.

#### V3-K-op-7: `endpointReply` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` or `Structural.lean`
**Scope**: Small (~20-30 lines)

Reply does not touch any endpoint queue. It only modifies TCB `ipcState`
(`.blockedOnReply` → `.ready`) and `pendingMessage`. No queue heads change.
K-2 trivially preserved. K-1 follows from `tcbQueueChainAcyclic` preservation.

#### V3-K-op-8: `endpointReplyRecv` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` or `Structural.lean`
**Scope**: Medium (~40-60 lines)

Compound: Reply + ReceiveDual. Chains V3-K-op-7 with V3-K-op-5.

#### V3-K-op-9: `notificationSignal` / `notificationWait` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`
**Scope**: Small (~25-35 lines)

Neither notification operation modifies endpoint queues or TCB `queueNext`
fields. `notificationSignal` stores a notification object and a TCB
(`storeTcbIpcStateAndMessage`). `notificationWait` stores a notification
and calls `storeTcbIpcState`. Neither touches endpoint objects.

K-1 follows from `tcbQueueChainAcyclic` preservation (existing). K-2 follows
from endpoint object stability under notification stores.

### 3.4. V3-K File Change Summary

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Invariant/Structural.lean` | ~350-450 | 0 | Primitive + operation proofs |
| `IPC/Invariant/EndpointPreservation.lean` | ~40-60 | 0 | Operation proofs (optional, may go in Structural) |
| `IPC/Invariant/CallReplyRecv.lean` | ~30-50 | 0 | Operation proofs (optional, may go in Structural) |
| `IPC/Invariant/NotificationPreservation.lean` | ~25-35 | 0 | Frame proofs |
| **Total** | **~445-595** | **0** | |

---

## 4. V3-J: ipcStateQueueMembershipConsistent Preservation Proofs

### 4.1. Predicate Structure Analysis

`ipcStateQueueMembershipConsistent` asserts a **bidirectional binding** between
a thread's `ipcState` and the endpoint queue structure. For every thread:

- `blockedOnSend epId` → reachable from `ep.sendQ.head` via `queueNext`
- `blockedOnReceive epId` → reachable from `ep.receiveQ.head` via `queueNext`
- `blockedOnCall epId` → reachable from `ep.receiveQ.head` via `queueNext`
- Other states → `True` (unconstrained)

"Reachable" means either:
1. The thread IS the queue head: `ep.sendQ.head = some tid` (or receiveQ)
2. There exists a predecessor: `∃ prev prevTcb, prev.objects = some (.tcb prevTcb) ∧ prevTcb.queueNext = some tid`

This is a **one-hop reachability** check — the thread is either the head or
has a direct predecessor in the queue chain. This is weaker than full transitive
`QueueNextPath` reachability but sufficient to guarantee presence in the queue
(combined with `tcbQueueLinkIntegrity`, one-hop backward reachability implies
full forward reachability from the head).

### 4.2. Proof Complexity Assessment

V3-J is **significantly harder** than V3-K because:

1. **Three ipcState variants** must be tracked (send, receive, call) across
   every operation, with each variant having its own queue (sendQ vs receiveQ).

2. **Queue operations modify both the endpoint and TCBs**. After
   `endpointQueueEnqueue`, the new thread must be shown reachable (it's the
   new tail, linked by the old tail's `queueNext`). After
   `endpointQueuePopHead`, the removed thread exits scope (ipcState changes)
   and the remaining threads must remain reachable (head advances to next).

3. **ipcState transitions and queue membership must stay synchronized**. When
   `storeTcbIpcState` changes a thread from `.ready` to `.blockedOnSend epId`,
   the thread must already be in `ep.sendQ` (via prior enqueue). When changing
   from `.blockedOnSend` to `.ready` (dequeue + wake), the thread must no
   longer appear in the queue.

4. **Cross-thread reasoning**: Modifying one TCB's `queueNext` affects the
   reachability of the thread it previously pointed to.

### 4.3. V3-J Sub-Task Breakdown

#### V3-J-prim-1: `storeObject` Non-TCB, Non-Endpoint Frame Lemma

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Small (~20-30 lines)

Non-TCB, non-endpoint stores do not affect TCB `ipcState`, `queueNext`, or
endpoint queue heads. The predicate is trivially preserved via
`storeObject_objects_ne`.

#### V3-J-prim-2: `storeTcbIpcState` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~50-70 lines)

`storeTcbIpcState` modifies one thread's `ipcState` without changing
`queueNext` or any endpoint object. Two proof obligations:

**For the target thread `tid`**:
- If the new `ipcState` is a blocking state (`blockedOnSend epId`, etc.),
  the thread must be reachable from the corresponding queue head. This
  requires a **precondition**: the caller must ensure the thread is already
  enqueued before setting its blocking state.
- If the new `ipcState` is `.ready` or another non-blocking state, the
  obligation is `True` — trivially satisfied.

**For all other threads**:
- Their TCBs are unchanged (`storeObject_objects_ne`)
- Their `ipcState` and reachability are unaffected

**Key precondition pattern**:
```lean
theorem storeTcbIpcState_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (newState : ThreadIpcState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid newState = .ok ((), st'))
    -- When transitioning INTO a blocking state, the thread must be reachable
    (hReachable : match newState with
      | .blockedOnSend epId =>
          ∃ ep, st.objects[epId]? = some (.endpoint ep) ∧
            (ep.sendQ.head = some tid ∨ ∃ prev prevTcb, ...)
      | .blockedOnReceive epId => ...
      | .blockedOnCall epId => ...
      | _ => True) :
    ipcStateQueueMembershipConsistent st'
```

This precondition can be discharged at each call site from the operation
context (e.g., `endpointSendDual` calls `endpointQueueEnqueue` before
`storeTcbIpcState`, establishing the reachability).

#### V3-J-prim-3: `storeTcbIpcStateAndMessage` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~50-70 lines)

Same structure as V3-J-prim-2 but for the combined ipcState + message store.
Identical precondition pattern.

#### V3-J-prim-4: `storeTcbQueueLinks` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium-Hard (~60-90 lines)

`storeTcbQueueLinks` modifies one TCB's `queuePrev`, `queuePPrev`, and
`queueNext` fields. This **directly affects reachability**:

- If `tid`'s `queueNext` changes from `some x` to `some y`, then `x` loses
  its predecessor (affecting `x`'s reachability) and `y` gains a predecessor
- If `tid`'s `queueNext` changes from `some x` to `none`, `x` loses its
  predecessor

**Proof strategy**: This primitive is always called as part of a larger
queue operation (`endpointQueueEnqueue`, `endpointQueuePopHead`,
`endpointQueueRemoveDual`). The invariant may not hold at intermediate states
within these multi-step operations. Therefore, it may be more practical to
prove preservation at the **operation level** (enqueue, popHead, removeDual)
rather than at the primitive `storeTcbQueueLinks` level.

**Decision**: Prove V3-J at the operation level, not the primitive level.
The primitive `storeTcbQueueLinks` will be handled implicitly within each
operation proof.

#### V3-J-op-1: `endpointQueueEnqueue` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~100-140 lines)

**This is the hardest proof in the entire plan.**

`endpointQueueEnqueue(endpointId, isReceiveQ, tid)` modifies:
1. The endpoint's queue (head/tail)
2. The old tail's `queueNext` (to point to `tid`)
3. The new thread's `queuePrev` (to point to old tail)

**Proof obligations**:

*For the newly enqueued thread `tid`*:
- After enqueue, `tid` is NOT yet in a blocking state — its `ipcState` is
  still `.ready` (the enqueue guard checks this). So the predicate evaluates
  to `True` for `tid` in the post-state. The `storeTcbIpcState` call that
  follows (in the parent operation) is what transitions `tid` into a blocking
  state, and V3-J-prim-2 handles that.

*For previously blocked threads*:
- Empty-queue case: Queue was empty. No threads were blocked on this endpoint
  (because the queue was empty, no thread could have been the head). After
  enqueue, head = tid. Other threads' reachability is unaffected since no
  `queueNext` pointers changed (except the new thread's).
- Non-empty case: Queue had existing members. Old head is unchanged. Old
  tail's `queueNext` now points to `tid`. For threads that were reachable
  before, they remain reachable because:
  - The head hasn't changed
  - No existing thread's `queueNext` was changed to point away from its
    successor (only the old tail gained a new `queueNext`)
  - The old tail's successor chain is extended, not broken

*For threads blocked on OTHER endpoints*:
- Other endpoints' queue heads are unchanged
- `queueNext` changes only affect `tid` and the old tail, not threads in
  other queues
- But we must be careful: changing the old tail's `queueNext` from `none`
  to `some tid` means `tid` now has a predecessor. If `tid` happened to be
  blocked on a different endpoint (impossible by the enqueue guard, since
  `ipcState = .ready`), this would incorrectly establish reachability. The
  enqueue guard prevents this.

**Helper lemma needed**:
```lean
/-- After endpointQueueEnqueue, threads previously reachable remain reachable. -/
private theorem endpointQueueEnqueue_preserves_existing_reachability ...
```

#### V3-J-op-2: `endpointQueuePopHead` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~80-120 lines)

PopHead removes the head thread and clears its queue links. The new head
is the old head's `queueNext`.

**Proof obligations**:

*For the popped thread (old head)*:
- Its `ipcState` is NOT changed by PopHead itself. The caller (`endpointSendDual`,
  etc.) will change it to `.ready` or another state via `storeTcbIpcState(AndMessage)`.
- In the intermediate state after PopHead but before ipcState change, the
  popped thread still has its old `ipcState` (e.g., `.blockedOnReceive epId`)
  but is no longer reachable (queue head has advanced). **The invariant
  temporarily breaks here.**
- This means the invariant must be proven at the **full operation level**, not
  at the PopHead level alone.

**Strategy**: Like V3-J-prim-4, this confirms that V3-J preservation should
be proven at the **composite operation level** (`endpointSendDual`,
`endpointReceiveDual`, etc.) rather than at the primitive level. The primitive
PopHead may temporarily violate the invariant, but the full operation
(PopHead + ipcState change) restores it.

**Alternative**: Add a **weaker lemma** that tracks what PopHead does to
reachability and ipcState, then compose it at the operation level:

```lean
/-- After PopHead, all previously reachable threads (except the popped head)
remain reachable via the new head's queueNext chain. -/
private theorem endpointQueuePopHead_reachability_transfer ...

/-- After PopHead, the popped thread's queueNext is cleared. -/
private theorem endpointQueuePopHead_clears_head_links ...
```

#### V3-J-op-3: `endpointSendDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~80-120 lines)

Two paths:

**Rendezvous path** (receiver waiting):
1. `endpointQueuePopHead(ep, true)` — removes receiver from receiveQ
2. `storeTcbIpcStateAndMessage(receiver, .ready, msg)` — receiver exits scope
3. `ensureRunnable(receiver)` — scheduler only

After step 1, the popped receiver still has `ipcState = .blockedOnReceive` but
is no longer in the queue. After step 2, the receiver has `ipcState = .ready`,
exiting the predicate's scope. For all other threads in the receiveQ, the new
head (old head's `queueNext`) maintains reachability via the same chain with
one link removed from the front. Threads in other queues are unaffected.

The sender's ipcState remains `.ready` throughout — trivially `True`.

**Block path** (no receiver):
1. `endpointQueueEnqueue(ep, false, sender)` — adds sender to sendQ
2. `storeTcbIpcStateAndMessage(sender, .blockedOnSend epId, msg)` — sender enters scope
3. `removeRunnable(sender)` — scheduler only

After step 1, sender has `ipcState = .ready` (trivially `True`). After step 2,
sender has `ipcState = .blockedOnSend epId` and must be reachable from
`sendQ.head`. If the queue was empty, sender IS the head. If non-empty,
sender is the tail, reachable via the old tail's `queueNext` (set by enqueue).

**Precondition satisfaction**: Step 2's precondition (V3-J-prim-3) — that the
sender is reachable — is discharged by step 1's enqueue result. The enqueue
either made the sender the head (empty case) or linked the old tail to the
sender (non-empty case).

#### V3-J-op-4: `endpointReceiveDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~100-140 lines)

**Rendezvous path** (sender waiting):
1. `endpointQueuePopHead(ep, false)` — removes sender from sendQ
2. Split on `senderWasCall`:
   - Call: `storeTcbIpcStateAndMessage(sender, .blockedOnReply, none)` — sender enters reply scope (not in send/receive/call, so `True`)
   - Send: `storeTcbIpcStateAndMessage(sender, .ready, none)` + `ensureRunnable` — sender exits scope
3. `storeTcbPendingMessage(receiver, senderMsg)` — receiver's message only, no ipcState change

The receiver's ipcState is never changed by this path (stays `.ready`).
Sender transitions out of `.blockedOnSend`/`.blockedOnCall` scope.

**Block path** (no sender):
1. `endpointQueueEnqueue(ep, true, receiver)` — adds receiver to receiveQ
2. `storeTcbIpcState(receiver, .blockedOnReceive epId)` — receiver enters scope
3. `removeRunnable(receiver)` — scheduler only

Same reachability discharge pattern as V3-J-op-3 block path.

#### V3-J-op-5: `endpointCall` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium-Hard (~70-100 lines)

**Rendezvous path**: PopHead(receiveQ) + wake receiver + block caller as `.blockedOnReply`
- Caller never enters a send/receive/call queue — only transitions to `.blockedOnReply`, which evaluates to `True`
- Receiver transitions to `.ready` — exits scope

**Block path**: Enqueue(sendQ, caller) + `storeTcbIpcStateAndMessage(caller, .blockedOnCall epId, msg)`
- Caller is enqueued on sendQ, then enters `.blockedOnCall epId`
- `.blockedOnCall epId` requires reachability from `ep.receiveQ.head`
- **Wait** — the definition says `.blockedOnCall epId` should be reachable from **receiveQ**, but the caller is enqueued on **sendQ**.

**Critical check of V3-J definition** (Defs.lean:806-811):
```lean
| .blockedOnCall epId =>
    ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
      (ep.receiveQ.head = some tid ∨ ...)
```

The definition says `blockedOnCall` threads should be reachable from
**`receiveQ.head`**. But `endpointCall` enqueues on the **sendQ** (not receiveQ).
When a receiver later calls `endpointReceiveDual`, it pops from sendQ and
the caller transitions from `.blockedOnCall` to `.blockedOnReply`.

**Issue**: The `blockedOnCall` case in V3-J checks `receiveQ.head`, but Call
callers are enqueued on sendQ. This appears to be a **definition error** in
the V3-J predicate.

**Analysis**: Looking at `endpointReceiveDual` (Transport.lean:1640-1650),
when a sender is popped from `sendQ` and `senderTcb.ipcState = .blockedOnCall _`,
the sender transitions to `.blockedOnReply`. The sender was in `sendQ`, not
`receiveQ`. The V3-J definition's use of `receiveQ` for `blockedOnCall` is
incorrect — it should be `sendQ`.

**However**: Let's check if `endpointCall`'s block path actually enqueues on
sendQ. Yes — `endpointQueueEnqueue endpointId false caller` where `false`
means sendQ (Transport.lean:1735). So `blockedOnCall` callers are in `sendQ`.

**Conclusion**: The V3-J predicate definition may need a **fix** for the
`blockedOnCall` case: `ep.sendQ.head` instead of `ep.receiveQ.head`. This
is a **definition-level issue** that must be resolved before preservation
proofs can proceed.

**Alternative reading**: Perhaps `blockedOnCall` was intentionally mapped to
`receiveQ` because in seL4's model, Call senders eventually become receivers.
But in seLe4n's implementation, Call callers sit on `sendQ` until a receiver
pops them. The definition should match the implementation.

**Resolution sub-task** (V3-J-fix): Fix `ipcStateQueueMembershipConsistent`
definition for `blockedOnCall` to use `sendQ` instead of `receiveQ`. This is
a ~2-line change in `Defs.lean`.

#### V3-J-op-6: `endpointReply` / `endpointReplyRecv` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~60-80 lines combined)

`endpointReply` wakes a `.blockedOnReply` thread (to `.ready`). Since
`.blockedOnReply` evaluates to `True` in V3-J, and `.ready` also evaluates
to `True`, the predicate is trivially preserved for the target thread. No
queue operations occur.

`endpointReplyRecv` = Reply + ReceiveDual. Chains V3-J-op-6 (Reply) with
V3-J-op-4 (ReceiveDual).

#### V3-J-op-7: `notificationSignal` / `notificationWait` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`
**Scope**: Small (~30-40 lines combined)

Neither notification operation modifies endpoint queues or TCB `queueNext`.
`notificationSignal` changes a waiter's `ipcState` from `.blockedOnNotification`
to `.ready` — both evaluate to `True` in V3-J. `notificationWait` changes
`ipcState` to `.blockedOnNotification` — also `True`. Endpoint objects are
untouched.

### 4.4. V3-J File Change Summary

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Invariant/Defs.lean` | 0 | ~2 (blockedOnCall fix if needed) | Definition fix |
| `IPC/Invariant/Structural.lean` | ~550-750 | 0 | Operation-level proofs |
| `IPC/Invariant/NotificationPreservation.lean` | ~30-40 | 0 | Frame proofs |
| **Total** | **~580-790** | **~2** | |

---

## 5. Bundle Integration Plan

### 5.1. Phase 1: Add Predicates to `ipcInvariantFull`

**File**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (line 287-289)

```lean
-- Before (5 conjuncts):
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st

-- After (7 conjuncts):
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st
```

### 5.2. Phase 2: Update Extractor Theorems

**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~lines 1358-1382)

Current extractors and their conjunction paths:
```
coreIpcInvariantBundle_to_ipcInvariant              → h.2.2.1
coreIpcInvariantBundle_to_dualQueueSystemInvariant   → h.2.2.2.1
coreIpcInvariantBundle_to_allPendingMessagesBounded  → h.2.2.2.2.1
coreIpcInvariantBundle_to_badgeWellFormed            → h.2.2.2.2.2.1
coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone → h.2.2.2.2.2.2
```

After adding 2 conjuncts, the last extractor path changes, and 2 new
extractors are needed:

```
coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone → h.2.2.2.2.2.1  (was .2)
coreIpcInvariantBundle_to_endpointQueueNoDup               → h.2.2.2.2.2.2.1 (NEW)
coreIpcInvariantBundle_to_ipcStateQueueMembershipConsistent → h.2.2.2.2.2.2.2 (NEW)
```

**Breaking change**: `coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone`
path changes from `.2.2.2.2.2.2` to `.2.2.2.2.2.1`. All call sites must be
audited and updated.

### 5.3. Phase 3: Update Bundle Reconstruction Theorems

Every theorem in `Structural.lean` that reconstructs `ipcInvariantFull` from
its components must be extended to include `endpointQueueNoDup` and
`ipcStateQueueMembershipConsistent` preservation.

Similarly, `lifecycleRetypeObject_preserves_coreIpcInvariantBundle` in
`Preservation.lean` must thread the two new components. Lifecycle retype
creates new objects — both predicates are trivially preserved because retype
does not modify existing endpoint queues or TCB `ipcState`/`queueNext` fields.

### 5.4. Bundle Integration File Changes

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Invariant/Defs.lean` | 2 | 2 | Definition extension |
| `Capability/Invariant/Preservation.lean` | ~15 | ~10 | Extractors + lifecycle |
| `IPC/Invariant/Structural.lean` | ~30-50 | ~20-30 | Bundle reconstruction |
| `Architecture/Invariant.lean` | 0 | ~5 | Path fixes if needed |
| **Total** | **~47-67** | **~37-47** | |

---

## 6. Execution Order & Dependency Graph

### 6.1. Dependency DAG

```
V3-J-fix (blockedOnCall sendQ fix, if needed)
  │
  ├───────────────────────────────────────────────┐
  │                                               │
  V3-K primitives                           V3-J primitives
  (prim-1, prim-2, prim-3)                 (prim-1, prim-2, prim-3)
  │                                               │
  V3-K queue ops                            V3-J queue ops
  (op-1: enqueue, op-2: popHead,            (op-1: enqueue, op-2: popHead)
   op-3: removeDual)                              │
  │                                               │
  V3-K IPC ops                              V3-J IPC ops
  (op-4: send, op-5: recv,                 (op-3: send, op-4: recv,
   op-6: call, op-7: reply,                 op-5: call, op-6: reply/replyRecv,
   op-8: replyRecv, op-9: ntfn)             op-7: ntfn)
  │                                               │
  └───────────────────────────────────────────────┘
                          │
                  Bundle Integration
                  (Defs + Preservation + Structural + Architecture)
```

### 6.2. Recommended Execution Phases

**Phase 0: Definition Fix (if needed)**
- Verify V3-J `blockedOnCall` → `sendQ` vs `receiveQ` correctness
- If fix needed: update `ipcStateQueueMembershipConsistent` definition
- ~5 minutes
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Defs`

**Phase 1: V3-K Primitive + Queue Operation Proofs**
- V3-K-prim-1: Non-TCB/non-endpoint frame lemma (~20 min)
- V3-K-prim-2: `storeTcbQueueLinks` preservation (~30 min)
- V3-K-prim-3: Endpoint store with known heads (~40 min)
- V3-K-op-1: `endpointQueueEnqueue` preservation (~1-1.5 hours)
- V3-K-op-2: `endpointQueuePopHead` preservation (~1 hour)
- V3-K-op-3: `endpointQueueRemoveDual` preservation (~1 hour)
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 2: V3-K IPC Operation Proofs (parallelizable)**
- V3-K-op-4 through V3-K-op-9: Compose primitive proofs
- ~3-4 hours total
- **Gate**: Individual module builds

**Phase 3: V3-J Queue Operation Proofs** (can run in parallel with Phase 2)
- V3-J-prim-1 through V3-J-prim-3: Frame/primitive lemmas (~1.5 hours)
- V3-J-op-1: `endpointQueueEnqueue` preservation (~2-3 hours — hardest proof)
- V3-J-op-2: `endpointQueuePopHead` helper lemmas (~1.5 hours)
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 4: V3-J IPC Operation Proofs**
- V3-J-op-3 through V3-J-op-7: Compose queue + primitive proofs
- ~4-5 hours total
- **Gate**: Individual module builds

**Phase 5: Bundle Integration**
- Update `ipcInvariantFull` definition
- Add extractor theorems, fix paths
- Update bundle reconstruction theorems
- ~2-3 hours
- **Gate**: Full `lake build` succeeds

**Phase 6: Validation & Documentation**
- `test_full.sh`
- Documentation sync (see Section 10)
- **Gate**: All tests pass; zero `sorry`

### 6.3. Parallelization Opportunities

| Can Parallelize | Cannot Parallelize |
|-----------------|-------------------|
| V3-K primitives ∥ V3-J primitives (different predicates, same file — separate regions) | V3-K ops depend on V3-K primitives |
| V3-K IPC ops ∥ V3-J queue ops (different proof chains) | V3-J IPC ops depend on V3-J queue ops |
| V3-K notification proofs ∥ V3-K endpoint proofs (different files) | Bundle integration depends on ALL proofs |

---

## 7. Cross-Cutting Concerns

### 7.1. V3-K / V3-J Interaction at `endpointQueueEnqueue`

V3-K-op-1 (enqueue preserves queue head disjointness) needs to show that a
newly enqueued thread on sendQ is not the receiveQ head. The cleanest approach
uses the **well-formedness** infrastructure:

The enqueued thread has `ipcState = .ready` (guard check). The receiveQ head
(if it exists) has `queuePrev = none` (from `intrusiveQueueWellFormed`). By
`tcbQueueLinkIntegrity`, a thread with `queuePrev = none` can only be a queue
head. The enqueued thread, having `queuePrev = none` AND `queueNext = none`
AND `queuePPrev = none` (from enqueue guard checks on links at
DualQueue/Core.lean:296), could potentially match these properties.

**Better argument**: After enqueue in the empty-queue case, the new thread
becomes head of sendQ. If it were ALSO head of receiveQ, that would mean the
same endpoint has the same thread as head of both queues simultaneously. But
the pre-state had `sendQ.head = none` (queue was empty), and the receiveQ was
untouched by the sendQ enqueue. If receiveQ.head was `some x`, then `x ≠ tid`
because the pre-state `endpointQueueNoDup` held (K-2 disjointness was trivially
satisfied since sendQ.head was `none`). After enqueue, sendQ.head = `some tid`.
The receiveQ.head is still `some x` with `x ≠ tid` because:
- `tid` had `ipcState = .ready` (enqueue guard)
- If `tid` were the receiveQ head, it would need `ipcState = .blockedOnReceive _`
  (by V3-J or the operational semantics). Contradiction with `.ready`.

**This reasoning uses V3-J semantically but not formally.** The proof can be
made self-contained by requiring a weaker precondition: "the enqueuing thread
is not the head of any queue." This can be derived from the enqueue guard's
link check (`queuePPrev = none ∧ queuePrev = none ∧ queueNext = none`).
A thread that is a queue head has `queuePPrev = some .endpointHead`
(DualQueue/Core.lean:306), so a thread with `queuePPrev = none` cannot be
any queue head. This is the **self-contained approach** — no V3-J dependency.

### 7.2. V3-J `blockedOnCall` Queue Assignment Issue

As identified in Section 4.3 (V3-J-op-5), the V3-J definition maps
`blockedOnCall epId` to `receiveQ.head`, but the implementation enqueues
Call callers on `sendQ`. This must be investigated before V3-J proofs begin.

**Three possible resolutions**:

1. **Fix the definition** (recommended): Change `blockedOnCall` to use `sendQ`
   instead of `receiveQ`. This matches the implementation.

2. **Leave as-is if intentional**: If the definition deliberately models a
   different semantics (e.g., post-dequeue state), document the rationale.
   But this would make the invariant unprovable for the current implementation.

3. **Change the implementation**: Enqueue Call callers on receiveQ instead of
   sendQ. This would be a significant behavioral change and is not recommended.

**Action item**: Verify the intended semantics by examining how `endpointCall`
and `endpointReceiveDual` interact. The implementation clearly shows Call
callers enter `sendQ` (Transport.lean:1735), are popped by
`endpointReceiveDual` from `sendQ` (Transport.lean:1640), and then transition
to `.blockedOnReply`. The definition should use `sendQ`.

### 7.3. Structural.lean Size Management

`Structural.lean` is already ~6934 lines (the largest file in the project).
Adding ~900-1200 lines of V3-J/K proofs will push it to ~8000+ lines.

**Mitigation options**:
1. **Accept the growth**: The file is already chunked by section headers and
   read in offset/limit chunks per CLAUDE.md guidelines.
2. **Split into sub-modules**: Create `IPC/Invariant/QueueMembership.lean`
   and `IPC/Invariant/QueueNoDup.lean` for the new proofs, re-exporting
   through `Structural.lean`.
3. **Hybrid**: Put primitive frame lemmas in `Structural.lean` (close to
   existing primitives) and operation-level proofs in new files.

**Recommended**: Option 2 — create new sub-modules. This keeps files
manageable and follows the existing pattern where `Structural.lean` is
a re-export hub for structural invariant proofs.

---

## 8. Risk Assessment & Mitigations

### 8.1. Risk Matrix

| ID | Risk | Probability | Impact | Mitigation |
|----|------|-------------|--------|------------|
| R1 | V3-J `blockedOnCall` definition bug — maps to `receiveQ` instead of `sendQ` | High | High | Verify and fix definition before starting proofs (Phase 0) |
| R2 | V3-J-op-1 (enqueue preservation) proof complexity — hardest proof in plan | High | Medium | Factor into helper lemmas for reachability transfer; start early |
| R3 | V3-J intermediate invariant violations during multi-step operations | Medium | High | Prove at operation level, not primitive level; use helper lemma pattern |
| R4 | V3-K-op-1 needs V3-J-like reasoning for head disjointness | Medium | Medium | Use self-contained `queuePPrev` argument (Section 7.1) |
| R5 | Structural.lean exceeds manageable size | Medium | Low | Create sub-modules (Section 7.3) |
| R6 | Bundle integration breaks downstream proofs | Medium | Medium | Full `lake build` after integration; audit all extractor call sites |
| R7 | V3-J reachability proofs require QueueNextPath induction, which is complex in Lean 4 | Medium | Medium | Use one-hop reachability (predecessor existence) instead of full transitive closure |
| R8 | `endpointQueueRemoveDual` has complex case splits (head/tail/middle removal) | Medium | Low | Factor into per-case helpers; reuse existing remove preservation infrastructure |

### 8.2. Highest-Risk Item: R1 (blockedOnCall Definition)

This must be resolved in Phase 0 before any V3-J work begins. If the
definition is wrong, all V3-J proofs for `endpointCall` and
`endpointReceiveDual` will fail. The fix is simple (~2 lines) but must be
done first.

### 8.3. Second-Highest Risk: R2 (Enqueue Reachability)

The `endpointQueueEnqueue` preservation proof for V3-J must show that after
enqueue, the newly added thread is reachable from the queue head. This requires
reasoning about the `queueNext` chain structure after the enqueue's TCB
modifications. The proof will need to:

1. Show the new thread is linked by the old tail's `queueNext` (non-empty case)
2. Show existing threads' reachability is preserved (no chain breaks)
3. Handle both empty-queue and non-empty-queue sub-cases

This is estimated at ~100-140 lines and may require 2-3 intermediate helper
lemmas.

---

## 9. Testing & Validation Strategy

### 9.1. Per-Phase Build Verification

| Phase | Build Command |
|-------|--------------|
| Phase 0 | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Defs` |
| Phase 1-2 (V3-K) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| Phase 3-4 (V3-J) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| Phase 5 (Bundle) | `source ~/.elan/env && lake build SeLe4n.Kernel.Architecture.Invariant` |
| If sub-modules created | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.QueueNoDup` etc. |

### 9.2. Integration Validation

```bash
./scripts/test_fast.sh      # Tier 0+1: Hygiene + full build
./scripts/test_smoke.sh     # Tier 0-2: + trace + negative-state
./scripts/test_full.sh      # Tier 0-3: + invariant surface anchors (REQUIRED)
```

### 9.3. Proof Hygiene

```bash
grep -r "sorry" SeLe4n/ --include="*.lean" | grep -v "^--" | grep -v "doc"
grep -r "axiom " SeLe4n/ --include="*.lean" | grep -v "^--"
./scripts/test_tier3_invariant_surface.sh
```

### 9.4. Regression Safety

No runtime code changes — trace harness output is unaffected:
```bash
lake exe sele4n > /tmp/trace_output.txt 2>&1
diff tests/fixtures/main_trace_smoke.expected /tmp/trace_output.txt
```

---

## 10. Documentation Synchronization

| Document | Update Required |
|----------|----------------|
| `docs/WORKSTREAM_HISTORY.md` | Add V3-J/K preservation completion entry |
| `docs/spec/SELE4N_SPEC.md` | Update proof coverage for queue membership and no-dup |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Add evidence entries for new theorems |
| `docs/gitbook/12-proof-and-invariant-map.md` | Add V3-J/K to invariant map with preservation status |
| `docs/codebase_map.json` | Regenerate (Lean sources changed) |
| `CHANGELOG.md` | Add V3-J/K preservation entries |

### 10.1. CHANGELOG Entry Template

```markdown
## [v0.22.X] - YYYY-MM-DD

### Added
- **V3-K/L-LIFE-1**: Preservation proofs for `endpointQueueNoDup` across all
  IPC operations. Queue head disjointness maintained through enqueue, popHead,
  removeDual, and all compound IPC operations. Self-loop component follows
  from existing `tcbQueueChainAcyclic` preservation. Integrated into
  `ipcInvariantFull` as 6th conjunct.
- **V3-J/L-IPC-3**: Preservation proofs for `ipcStateQueueMembershipConsistent`
  across all IPC operations. Bidirectional consistency between TCB `ipcState`
  and endpoint queue reachability machine-verified through all send/receive/
  call/reply/notification paths. Integrated into `ipcInvariantFull` as 7th
  conjunct.
```

---

## Appendix A: Complete Sub-Task Registry

| ID | Finding | Task Summary | File(s) | Scope | Depends On |
|----|---------|-------------|---------|-------|------------|
| V3-J-fix | L-IPC-3 | Fix `blockedOnCall` queue assignment (sendQ, not receiveQ) | `Defs.lean` | S | — |
| V3-K-prim-1 | L-LIFE-1 | Non-TCB/non-endpoint frame lemma | `Structural.lean` | S | — |
| V3-K-prim-2 | L-LIFE-1 | `storeTcbQueueLinks` K-2 preservation | `Structural.lean` | S | — |
| V3-K-prim-3 | L-LIFE-1 | Endpoint store with known heads | `Structural.lean` | M | — |
| V3-K-op-1 | L-LIFE-1 | `endpointQueueEnqueue` K-2 preservation | `Structural.lean` | M | prim-1,2,3 |
| V3-K-op-2 | L-LIFE-1 | `endpointQueuePopHead` K-2 preservation | `Structural.lean` | M | prim-1,2,3 |
| V3-K-op-3 | L-LIFE-1 | `endpointQueueRemoveDual` K-2 preservation | `Structural.lean` | M | prim-1,2,3 |
| V3-K-op-4 | L-LIFE-1 | `endpointSendDual` preservation | `Structural.lean` | M | op-1,2 |
| V3-K-op-5 | L-LIFE-1 | `endpointReceiveDual` preservation | `Structural.lean` | M | op-1,2 |
| V3-K-op-6 | L-LIFE-1 | `endpointCall` preservation | `Structural.lean` | M | op-1,2 |
| V3-K-op-7 | L-LIFE-1 | `endpointReply` preservation | `Structural.lean` | S | prim-2 |
| V3-K-op-8 | L-LIFE-1 | `endpointReplyRecv` preservation | `Structural.lean` | M | op-5,7 |
| V3-K-op-9 | L-LIFE-1 | Notification ops preservation | `NotificationPres.lean` | S | prim-1,2 |
| V3-J-prim-1 | L-IPC-3 | Non-TCB/non-endpoint frame lemma | `Structural.lean` | S | — |
| V3-J-prim-2 | L-IPC-3 | `storeTcbIpcState` preservation | `Structural.lean` | M | — |
| V3-J-prim-3 | L-IPC-3 | `storeTcbIpcStateAndMessage` preservation | `Structural.lean` | M | — |
| V3-J-op-1 | L-IPC-3 | `endpointQueueEnqueue` reachability | `Structural.lean` | H | prim-1,2,3 |
| V3-J-op-2 | L-IPC-3 | `endpointQueuePopHead` reachability | `Structural.lean` | H | prim-1,2,3 |
| V3-J-op-3 | L-IPC-3 | `endpointSendDual` preservation | `Structural.lean` | H | op-1,2; prim-2,3 |
| V3-J-op-4 | L-IPC-3 | `endpointReceiveDual` preservation | `Structural.lean` | H | op-1,2; prim-2,3 |
| V3-J-op-5 | L-IPC-3 | `endpointCall` preservation | `Structural.lean` | M-H | op-1,2; prim-2,3 |
| V3-J-op-6 | L-IPC-3 | `endpointReply`/`endpointReplyRecv` preservation | `Structural.lean` | M | prim-2,3; op-4 |
| V3-J-op-7 | L-IPC-3 | Notification ops preservation | `NotificationPres.lean` | S | prim-1 |
| V3-JK-int | L-IPC-3/L-LIFE-1 | Bundle integration (Defs + extractors + reconstruction) | Multiple | M | ALL above |

**Total sub-tasks**: 24 (5 Small, 12 Medium, 6 Hard, 1 Integration)
**Total estimated new Lean proof lines**: ~1075-1450
**Total estimated modified lines**: ~39-49
**Files touched**: 5-7 (depending on sub-module decision)

