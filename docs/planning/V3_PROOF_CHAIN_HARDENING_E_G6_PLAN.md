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

**Approach**: Self-contained via `queuePPrev`. A thread being enqueued has
`queuePPrev = none` (guard at Core.lean:296). A queue head has
`queuePPrev = some .endpointHead` (set at Core.lean:306). Since
`none ≠ some .endpointHead`, the enqueuing thread cannot be any queue head.
This completely avoids any V3-J dependency.

**Sub-step K-op-1a: Case split on `isReceiveQ` × `q.tail`**

The proof unfolds `endpointQueueEnqueue` and splits into 4 top-level cases:
- `(isReceiveQ = false, q.tail = none)` — sendQ empty enqueue
- `(isReceiveQ = false, q.tail = some tailTid)` — sendQ non-empty enqueue
- `(isReceiveQ = true, q.tail = none)` — receiveQ empty enqueue
- `(isReceiveQ = true, q.tail = some tailTid)` — receiveQ non-empty enqueue

By symmetry, send-side and receive-side proofs are structurally identical
(one modifies sendQ, the other receiveQ), so we describe the send-side in
detail.

**Sub-step K-op-1b: Empty-queue case (sendQ, `q.tail = none`)**

Post-state: `sendQ' = { head := some tid, tail := some tid }`, `receiveQ' = receiveQ`
(unchanged because only sendQ was modified).

Proof of K-2 for the **stored endpoint** (at `endpointId`):
```
-- Goal: some tid = none ∨ receiveQ.head = none ∨ some tid ≠ receiveQ.head
-- Case: receiveQ.head = none → middle disjunct, done
-- Case: receiveQ.head = some x →
--   Need: tid ≠ x
--   From guard: tid has queuePPrev = none (Core.lean:296)
--   If x is receiveQ head, x has queuePPrev = some .endpointHead
--     (from intrusiveQueueWellFormed / endpointQueueEnqueue setup)
--   Since none ≠ some .endpointHead → tid ≠ x
```

Proof of K-2 for **other endpoints** (at `oid ≠ endpointId`):
```
-- storeObject_objects_ne: st'.objects[oid]? = st.objects[oid]?
-- Therefore their queue heads are unchanged → hInv transfers
```

Proof of K-1: follows from `hAcyclic` (post-state `tcbQueueChainAcyclic`).

**Sub-step K-op-1c: Non-empty-queue case (sendQ, `q.tail = some tailTid`)**

Post-state: `sendQ' = { head := q.head, tail := some tid }`, `receiveQ' = receiveQ`.

Proof of K-2: **Queue head is unchanged** (`sendQ'.head = q.head`).
The pre-state `hInv` already gave `q.head = none ∨ receiveQ.head = none ∨
q.head ≠ receiveQ.head`. Since `sendQ'.head = q.head` and `receiveQ'` is
unchanged, K-2 transfers directly from `hInv`. No `queuePPrev` reasoning
needed — this is the trivial case.

**Sub-step K-op-1d: Precondition for `queuePPrev` argument**

The proof requires access to the enqueuing thread's pre-state TCB to read
`queuePPrev = none`. This is available from the enqueue guard check at
Core.lean:296 (`tcb.queuePPrev.isSome`). Extracting this from the
`endpointQueueEnqueue` success means:
```lean
-- From hEnqueue success:
-- lookupTcb st tid = some tcb
-- tcb.queuePPrev.isSome = false → tcb.queuePPrev = none
```

For the opposite queue's head, we need `head.queuePPrev = some .endpointHead`.
This follows from `intrusiveQueueWellFormed` (part of `dualQueueSystemInvariant`).
Specifically, when an endpoint has `receiveQ.head = some x`, then `x` was
placed there by a prior `endpointQueueEnqueue` (empty case) which set
`queuePPrev := some .endpointHead` (Core.lean:306), or by a prior
`endpointQueuePopHead` which set the next thread's `queuePPrev := some .endpointHead`
(Core.lean:274).

**Theorem signature**:
```lean
theorem endpointQueueEnqueue_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hDQWF : dualQueueEndpointWellFormed st)  -- for queuePPrev = endpointHead on heads
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    endpointQueueNoDup st'
```

#### V3-K-op-2: `endpointQueuePopHead` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~50-70 lines)

PopHead removes the head of one queue and advances to the next element.

**Approach**: Self-contained via `queuePrev` reasoning. Uses existing
`dualQueueSystemInvariant` infrastructure (no V3-J dependency).

**Sub-step K-op-2a: Case split on `headTcb.queueNext`**

PopHead at Core.lean:246-282 has two sub-cases after finding head `tid`:
- `headTcb.queueNext = none` → queue becomes empty (`q' = {}`)
- `headTcb.queueNext = some nextTid` → head advances (`q'.head = some nextTid`)

**Sub-step K-op-2b: Queue-becomes-empty case (`queueNext = none`)**

Post-state: `sendQ' = { head := none, tail := none }`, receiveQ unchanged.
K-2 becomes: `none = none ∨ ...` — first disjunct, trivially true. Done.

**Sub-step K-op-2c: Head-advances case (`queueNext = some nextTid`)**

Post-state: `sendQ'.head = some nextTid`, receiveQ unchanged.
Need: `some nextTid ≠ receiveQ.head` (when receiveQ.head is non-empty).

Self-contained argument using `queuePrev`:
```
-- From PopHead implementation (Core.lean:274):
--   nextTid gets queuePPrev := some .endpointHead, queuePrev := none
--   BUT before that, nextTid has queuePrev = some tid (it's tid's successor)
-- Wait — PopHead CLEARS nextTid's prev: storeTcbQueueLinks st1 nextTid none (some .endpointHead) nextTcb.queueNext
-- So post-PopHead: nextTid.queuePrev = none
--
-- This means we can't use queuePrev to distinguish nextTid from receiveQ.head
-- (both might have queuePrev = none after the operation).
--
-- Better argument: use queuePPrev on the OPPOSITE queue's head.
-- receiveQ.head (if some x) has queuePPrev = some .endpointHead (from DQWF)
-- nextTid also gets queuePPrev = some .endpointHead (from PopHead at Core.lean:274)
-- These are the same! So we need a different distinguisher.
--
-- CORRECT argument: use the PRE-state dualQueueEndpointWellFormed.
-- In the pre-state:
--   nextTid has queuePrev = some tid (it's the 2nd element, predecessor is the head)
--   receiveQ.head (if some x) has queuePrev = none (well-formed queue head)
-- Since queuePrev differs, nextTid ≠ receiveQ.head in the pre-state.
-- storeObject for the endpoint doesn't change TCB objects.
-- storeTcbQueueLinks for nextTid changes nextTid's prev but doesn't change receiveQ.head's identity.
-- The ObjId inequality (nextTid ≠ x) is a value identity, not a field property — it persists.
```

Refined proof:
```lean
-- From dualQueueEndpointWellFormed (pre-state):
--   if ep.receiveQ.head = some x, then lookupTcb st x = some xTcb with xTcb.queuePrev = none
-- From tcbQueueLinkIntegrity (pre-state):
--   if headTcb.queueNext = some nextTid, then lookupTcb st nextTid = some nextTcb
--     with nextTcb.queuePrev = some tid   (tid is the head being popped)
-- Since some tid ≠ none, nextTcb.queuePrev ≠ xTcb.queuePrev
-- By objects.invExt (ObjId injective), nextTid ≠ x
-- ThreadId inequality persists across state changes → sendQ'.head ≠ receiveQ.head
```

**Sub-step K-op-2d: Frame for other endpoints**

Other endpoints at `oid ≠ endpointId` are unchanged by `storeObject_objects_ne`.
K-2 transfers from `hInv`.

**Theorem signature**:
```lean
theorem endpointQueuePopHead_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hDQWF : dualQueueEndpointWellFormed st)
    (hLinkInt : tcbQueueLinkIntegrity st)
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    endpointQueueNoDup st'
```

#### V3-K-op-3: `endpointQueueRemoveDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~60-80 lines)

`endpointQueueRemoveDual` (Transport.lean:798-870) removes an arbitrary thread
from a queue using the `queuePPrev` metadata for O(1) unlinking. Three cases
based on position in the queue.

**Sub-step K-op-3a: Case split on `tcb.queuePPrev`**

The implementation branches on `pprev`:
- `pprev = .endpointHead` → removing the queue head
- `pprev = .tcbNext prevTid` → removing a non-head element

Combined with `tcb.queueNext`:
- `queueNext = none` → removing the tail
- `queueNext = some nextTid` → removing a middle element (or head with successor)

This gives 3 distinct proof cases:

**Sub-step K-op-3b: Head removal (`pprev = .endpointHead`)**

Post-state: queue head advances to `tcb.queueNext` (or `none` if tail).
Same argument as V3-K-op-2c: the new head (if any) had `queuePrev = some tid`
in the pre-state, while the opposite queue's head has `queuePrev = none`.
By `tcbQueueLinkIntegrity` + `dualQueueEndpointWellFormed`, the new head
cannot be the opposite queue's head.

Note: `endpointQueueRemoveDual` also stores a SECOND endpoint object at
line 866 (updating head/tail). The proof must track through both storeObject
calls. The first storeObject (line 827) updates the queue head, and the
second storeObject (line 866) is a no-op for the head case (`q.head = some tid`
means the if-branch at line 861 uses `tcb.queueNext`).

**Sub-step K-op-3c: Non-head tail removal (`pprev = .tcbNext prevTid`, `queueNext = none`)**

Queue head is unchanged. Only the tail pointer and `prevTid.queueNext` change.
K-2 transfers directly from `hInv` since heads are identical.

**Sub-step K-op-3d: Non-head middle removal (`pprev = .tcbNext prevTid`, `queueNext = some nextTid`)**

Queue head is unchanged. `prevTid.queueNext` is relinked to `nextTid`, and
`nextTid.queuePrev/queuePPrev` are updated. K-2 transfers from `hInv` since
heads are identical.

**Sub-step K-op-3e: Frame for other endpoints**

`endpointQueueRemoveDual` only modifies the endpoint at `endpointId` and the
removed thread's TCB (plus up to 2 neighbor TCBs). Other endpoints are
unchanged by `storeObject_objects_ne`.

**Theorem signature**:
```lean
theorem endpointQueueRemoveDual_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hDQWF : dualQueueEndpointWellFormed st)
    (hLinkInt : tcbQueueLinkIntegrity st)
    (hRemove : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    endpointQueueNoDup st'
```

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
| `IPC/Invariant/Structural.lean` | ~500 | 0 | Primitives (105) + queue ops (170) + IPC ops (225) |
| `IPC/Invariant/NotificationPreservation.lean` | ~25 | 0 | Frame proofs |
| **Total** | **~525** | **0** | |

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

**This is the hardest proof in the entire plan.** The complexity arises from
three interacting concerns: the enqueued thread's own ipcState, previously
blocked threads' continued reachability, and cross-endpoint frame reasoning
when `queueNext` pointers change.

`endpointQueueEnqueue(endpointId, isReceiveQ, tid)` (Core.lean:284-319)
modifies:
1. The endpoint's queue head/tail
2. The old tail's `queueNext` (from `none` to `some tid`) — non-empty case only
3. The new thread's `queuePrev`/`queuePPrev` — both cases

**Decomposition into 5 focused sub-lemmas:**

##### V3-J-op-1a: Helper — enqueued thread has trivial obligation

```lean
/-- The enqueued thread has ipcState = .ready (from guard), so V3-J evaluates to True. -/
private theorem enqueue_target_ipcState_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hLookup : lookupTcb st tid = some tcb)
    (hReady : tcb.ipcState = .ready) :
    -- V3-J for tid: match .ready with ... => True
    True := trivial
```

This is trivial but documents the key invariant: `endpointQueueEnqueue`'s
guard checks `tcb.ipcState ≠ .ready` and errors, so success implies
`ipcState = .ready`. V3-J maps `.ready` to `True`. The enqueued thread
is not yet in scope — it enters scope only when the parent operation calls
`storeTcbIpcState` to transition to a blocking state.

##### V3-J-op-1b: Helper — empty-queue case preserves existing reachability

**Proof target**: When the queue was empty (`q.tail = none`), no existing
thread was blocked on this endpoint's queue (because the queue had no head).
After enqueue, `head = some tid`, but `tid` has `ipcState = .ready`, so no
thread in the post-state has a blocking state pointing to this queue.

```lean
/-- Empty-queue enqueue: no existing thread's reachability is affected.
    Pre-state: q.head = none (empty queue), so no thread had
    ipcState = .blockedOnSend epId with reachability from this queue's head.
    Post-state: q'.head = some tid, but tid.ipcState = .ready.
    All other threads' TCBs and ipcStates are unchanged. -/
private theorem endpointQueueEnqueue_empty_preserves_reachability ...
```

Proof structure:
```
-- intro tid' tcb' hObj'
-- by_cases hEq : tid' = tid
-- Case tid' = tid:
--   tcb'.ipcState was .ready (from guard), modified TCB still has .ready
--   (enqueue only changes queuePrev/queuePPrev/queueNext, not ipcState)
--   V3-J maps .ready → True
-- Case tid' ≠ tid:
--   tid'.tcb is unchanged (storeObject_objects_ne for endpoint store + storeTcbQueueLinks for tid)
--   tid'.ipcState is unchanged
--   Need: tid' still reachable if blocked
--   Subcase: tid' blocked on this endpoint (epId = endpointId)
--     Pre-state: impossible — queue was empty (head = none), so no thread was reachable from head
--     This contradicts hInv (pre-state V3-J required reachability, but head was none)
--     Wait: hInv says blocked → reachable from head OR has predecessor
--     With head = none and no predecessor in empty queue, this is impossible
--     So no thread had ipcState = .blockedOnSend endpointId → vacuously true
--   Subcase: tid' blocked on different endpoint (epId ≠ endpointId)
--     That endpoint is unchanged → reachability preserved from hInv
--     But tid' might gain a NEW predecessor (the old tail's queueNext changed)
--     NO: in empty-queue case, no old tail exists, so no queueNext changed
--     Only tid's queuePrev/queuePPrev changed → tid' is unaffected
```

##### V3-J-op-1c: Helper — non-empty-queue case preserves existing reachability

**This is the most complex sub-lemma.** When the queue has existing members,
the old tail's `queueNext` changes from `none` to `some tid`. This means:

1. `tid` gains a new predecessor (the old tail) — harmless since `tid` has
   `ipcState = .ready`
2. No existing thread LOSES a predecessor — the old tail previously had
   `queueNext = none`, so it wasn't anyone's predecessor before
3. The queue head is unchanged → all threads reachable from head via
   `queueNext` remain reachable

```lean
/-- Non-empty-queue enqueue: existing threads remain reachable.
    Key insight: the old tail's queueNext was none (it was the tail),
    so changing it to some tid doesn't remove any existing predecessor link.
    The head is unchanged, so head-reachable threads stay head-reachable. -/
private theorem endpointQueueEnqueue_nonempty_preserves_reachability ...
```

Proof structure:
```
-- intro tid' tcb' hObj'
-- by_cases hEq : tid' = tid → .ready, trivially True
-- by_cases hEq2 : tid' = tailTid
--   Case tid' = tailTid (the old tail):
--     tailTid's ipcState is unchanged (storeTcbQueueLinks doesn't change ipcState)
--     tailTid's reachability: was reachable in pre-state (by hInv)
--     Post-state: tailTid's TCB has modified queueNext but same ObjId
--     tailTid is STILL reachable because:
--       - Head is unchanged
--       - tailTid's predecessor's queueNext is unchanged (only tailTid's own queueNext changed)
--       - So tailTid still has the same predecessor pointing to it
-- Case tid' ≠ tid ∧ tid' ≠ tailTid:
--   tid'.tcb is unchanged (frame: storeObject for endpoint at endpointId,
--     storeTcbQueueLinks for tailTid, storeTcbQueueLinks for tid — all at different ObjIds)
--   tid'.ipcState unchanged
--   If blocked on this endpoint: predecessor is unchanged (predecessor ≠ tailTid by case split,
--     and predecessor ≠ tid since tid was .ready). Head unchanged. Reachability preserved.
--   If blocked on other endpoint: frame — other endpoint unchanged, predecessor unchanged
```

##### V3-J-op-1d: Helper — cross-endpoint frame

When `tid` is enqueued on `endpointId`'s queue, threads blocked on OTHER
endpoints must remain reachable. This requires showing that no reachability
link for another endpoint was broken.

```lean
/-- Enqueue on one endpoint preserves reachability for all other endpoints. -/
private theorem endpointQueueEnqueue_cross_endpoint_frame
    -- For any thread tid' blocked on epId ≠ endpointId:
    -- (a) The endpoint at epId is unchanged (storeObject_objects_ne)
    -- (b) tid''s predecessor's queueNext is unchanged (no TCB modification
    --     touched a thread in a different endpoint's queue)
    -- (c) Therefore reachability is preserved
```

The key observation: `endpointQueueEnqueue` modifies exactly 3 objects:
- The endpoint at `endpointId` (storeObject)
- The old tail TCB at `tailTid` (storeTcbQueueLinks — queueNext changed)
- The new thread TCB at `tid` (storeTcbQueueLinks — queuePrev/queuePPrev set)

For threads blocked on a different endpoint `epId ≠ endpointId`:
- The endpoint at `epId` is unchanged → queue heads unchanged
- If a thread's predecessor is `tailTid`: `tailTid.queueNext` changed from
  `none` to `some tid`. But `tailTid.queueNext = none` in pre-state means
  `tailTid` was NOT anyone's predecessor before. So no thread had
  `tailTid` as predecessor → this case is vacuous.
- If a thread's predecessor is `tid`: `tid` had `queueNext = none` in
  pre-state (from enqueue guard at Core.lean:296). Same argument — `tid`
  was not anyone's predecessor.

##### V3-J-op-1e: Main theorem — compose sub-lemmas

```lean
theorem endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ipcStateQueueMembershipConsistent st'
```

Proof outline:
```
-- unfold endpointQueueEnqueue, extract guards and case splits
-- intro tid' tcb' hObj'
-- cases q.tail
-- | none => apply endpointQueueEnqueue_empty_preserves_reachability
-- | some tailTid => apply endpointQueueEnqueue_nonempty_preserves_reachability
```

**Estimated breakdown**: 1a (~5 lines), 1b (~25 lines), 1c (~45 lines),
1d (~30 lines), 1e (~35 lines) = ~140 lines total.

#### V3-J-op-2: `endpointQueuePopHead` Helper Lemmas (NOT standalone preservation)

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~80-120 lines)

**Critical design decision**: PopHead **temporarily violates** V3-J. After
popping the head, the old head still has `ipcState = .blockedOnReceive epId`
(or `.blockedOnSend`) but is no longer reachable from the queue. The caller
operation (`endpointSendDual`, etc.) restores the invariant by changing the
popped thread's `ipcState` to `.ready` or `.blockedOnReply`. Therefore, we
do NOT prove standalone V3-J preservation for PopHead. Instead, we prove
**transfer lemmas** that the operation-level proofs (V3-J-op-3, V3-J-op-4)
compose.

**Decomposition into 4 focused helper lemmas:**

##### V3-J-op-2a: Remaining-threads reachability transfer

```lean
/-- After PopHead, all threads that were reachable from the OLD head's successor
    are reachable from the NEW head (= old head's queueNext). -/
private theorem endpointQueuePopHead_remaining_reachable
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    -- For any thread tid' ≠ tid that had a predecessor in the pre-state:
    (tid' : SeLe4n.ThreadId) (hNe : tid' ≠ tid)
    (prev : SeLe4n.ThreadId) (prevTcb : TCB)
    (hPrevLookup : st.objects[prev.toObjId]? = some (.tcb prevTcb))
    (hPrevNext : prevTcb.queueNext = some tid') :
    -- tid' still has a predecessor in the post-state, or is the new head
    (st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ prevTcb.queueNext = some tid') ∨
    (∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ.head else ep'.sendQ.head) = some tid')
```

Proof structure:
```
-- Case: prev ≠ tid (predecessor is not the popped head)
--   prev's TCB is unchanged (frame: storeTcbQueueLinks targets tid and nextTid, not prev)
--   prev.queueNext still = some tid' → left disjunct
-- Case: prev = tid (predecessor IS the popped head)
--   tid.queueNext = some tid' (from hPrevNext)
--   But headTcb.queueNext = some tid' means tid' is the NEW head
--   PopHead sets q'.head = some tid' (Core.lean:262)
--   → right disjunct (tid' is the new head)
```

##### V3-J-op-2b: Popped head's ipcState unchanged

```lean
/-- PopHead does not modify the popped thread's ipcState.
    The returned headTcb records the pre-dequeue ipcState. -/
private theorem endpointQueuePopHead_ipcState_stable
    -- After PopHead, the popped thread's ipcState in st' equals headTcb.ipcState
    -- (storeTcbQueueLinks only modifies queue link fields, not ipcState)
```

This is essential for the operation-level proofs: they need to know the
popped thread's ipcState to discharge the `storeTcbIpcStateAndMessage`
precondition (V3-J-prim-3).

Proof: `storeTcbQueueLinks` stores `{ tcb with queuePrev, queuePPrev, queueNext }`,
which preserves `tcb.ipcState`. The popped thread's final TCB (after clearing
links) has the same `ipcState` as `headTcb`.

##### V3-J-op-2c: Popped head's links are cleared

```lean
/-- After PopHead, the popped thread has queuePrev = none, queuePPrev = none,
    queueNext = none. -/
private theorem endpointQueuePopHead_clears_head_links
    -- storeTcbQueueLinks st2 tid none none none (Core.lean:278)
```

This is needed by operation-level proofs to show the popped thread is no
longer anyone's predecessor (queueNext = none) after PopHead.

##### V3-J-op-2d: Cross-endpoint frame

```lean
/-- PopHead on one endpoint preserves reachability for threads blocked on
    other endpoints. -/
private theorem endpointQueuePopHead_cross_endpoint_frame
    -- Other endpoints at oid ≠ endpointId: unchanged (storeObject_objects_ne)
    -- TCB modifications: only tid and nextTid are touched
    -- For a thread blocked on epId ≠ endpointId with predecessor prev:
    --   If prev ≠ tid ∧ prev ≠ nextTid: prev.tcb unchanged → reachability preserved
    --   If prev = tid: tid was the head of THIS endpoint's queue, not another's
    --     (by dualQueueEndpointWellFormed, tid can only be head of one queue)
    --     So prev was tid only for threads in this endpoint's queue, not others
    --   If prev = nextTid: nextTid.queueNext is preserved by storeTcbQueueLinks
    --     (Core.lean:274 stores queuePrev/queuePPrev but preserves queueNext via nextTcb.queueNext)
    --     So prev.queueNext is unchanged → reachability preserved
```

**Estimated breakdown**: 2a (~35 lines), 2b (~15 lines), 2c (~10 lines),
2d (~40 lines) = ~100 lines total.

#### V3-J-op-3: `endpointSendDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~80-120 lines)

`endpointSendDual` (Transport.lean:1586-1614) has two paths. Each path is a
multi-step composition where the invariant may transiently break between steps
but is restored by the final step.

##### V3-J-op-3a: Rendezvous path — state transition trace

```
st0 (pre-state, V3-J holds)
 │ endpointQueuePopHead(ep, true)
st1 ← INVARIANT TEMPORARILY BROKEN for popped receiver
 │     (receiver.ipcState = .blockedOnReceive, but no longer reachable from receiveQ.head)
 │ storeTcbIpcStateAndMessage(receiver, .ready, some msg)
st2 ← INVARIANT RESTORED
 │     (receiver.ipcState = .ready → True; remaining threads reachable via V3-J-op-2a)
 │ ensureRunnable(receiver)
st3 ← INVARIANT STILL HOLDS (ensureRunnable only modifies scheduler)
```

Proof composition for rendezvous:
```
-- Step 1: PopHead removes receiver from receiveQ
--   Use V3-J-op-2a: remaining threads in receiveQ are still reachable from new head
--   Use V3-J-op-2d: threads in other endpoints unaffected
--   The popped receiver is the ONLY thread that violates V3-J in st1
--
-- Step 2: storeTcbIpcStateAndMessage sets receiver.ipcState = .ready
--   For the receiver: .ready → True, invariant satisfied
--   For other threads:
--     The store modifies receiver's TCB (at receiver.toObjId)
--     No other thread's TCB, ipcState, or queueNext is changed
--     No endpoint object is changed
--     → Other threads' reachability is unchanged from st1
--     Combined with V3-J-op-2a (remaining threads still reachable), V3-J holds in st2
--
-- Step 3: ensureRunnable — scheduler only, objects unchanged → V3-J preserved
```

**Key helper needed for Step 2**: A lemma showing that if V3-J holds for
all threads EXCEPT one specific thread `t`, and then `t`'s ipcState is set
to a non-blocking state, then V3-J holds in the result:

```lean
/-- If V3-J holds for all threads except tid, and tid's ipcState becomes
    non-blocking (ready/blockedOnReply/blockedOnNotification), then V3-J holds. -/
private theorem ipcStateQueueMembership_restore_by_clearing_ipcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hAllExcept : ∀ tid' tcb', tid' ≠ tid →
      st.objects[tid'.toObjId]? = some (.tcb tcb') →
      <V3-J predicate for tid'>)
    (hStore : storeTcbIpcStateAndMessage st tid .ready msg = .ok st')
    (hObjInv : st.objects.invExt) :
    ipcStateQueueMembershipConsistent st'
```

##### V3-J-op-3b: Block path — state transition trace

```
st0 (pre-state, V3-J holds)
 │ endpointQueueEnqueue(ep, false, sender)
st1 ← V3-J STILL HOLDS (sender.ipcState = .ready → True; existing threads preserved by V3-J-op-1)
 │ storeTcbIpcStateAndMessage(sender, .blockedOnSend endpointId, some msg)
st2 ← V3-J HOLDS (sender now in scope, must verify reachability)
 │ removeRunnable(sender)
st3 ← V3-J HOLDS (scheduler only)
```

Proof composition for block path:
```
-- Step 1: endpointQueueEnqueue adds sender to sendQ
--   By V3-J-op-1e: V3-J preserved in st1
--   Additionally, we need a FACT about st1: sender is reachable from sendQ.head
--   Empty case: sender IS the head → head = some sender
--   Non-empty case: old tail's queueNext = some sender → sender has predecessor
--
-- Step 2: storeTcbIpcStateAndMessage sets sender.ipcState = .blockedOnSend endpointId
--   For sender: must verify reachability from ep.sendQ.head
--     From Step 1 fact: sender is head OR has predecessor
--     Endpoint object is UNCHANGED by storeTcbIpcStateAndMessage (it stores a TCB, not endpoint)
--     Predecessor's queueNext is UNCHANGED (storeTcbIpcStateAndMessage modifies sender's TCB only)
--     → sender's reachability established
--   For other threads: frame — sender's TCB modification doesn't affect their reachability
--
-- Step 3: removeRunnable — scheduler only → V3-J preserved
```

**Key helper needed for Step 2**: A lemma extracting the enqueue post-condition
(sender is reachable) from `endpointQueueEnqueue` success:

```lean
/-- After endpointQueueEnqueue, the enqueued thread is reachable from the queue head:
    either it IS the head, or the old tail's queueNext points to it. -/
private theorem endpointQueueEnqueue_thread_reachable
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      let q' := if isReceiveQ then ep'.receiveQ else ep'.sendQ
      (q'.head = some tid ∨
       ∃ prev prevTcb, st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
         prevTcb.queueNext = some tid)
```

##### V3-J-op-3c: Main theorem

```lean
theorem endpointSendDual_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hDQSI : dualQueueSystemInvariant st)
    (hSend : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st'
```

**Estimated breakdown**: 3a rendezvous (~40 lines), 3b block path (~45 lines),
3c dispatch (~15 lines), helpers (~20 lines) = ~120 lines total.

#### V3-J-op-4: `endpointReceiveDual` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Hard (~100-140 lines)

`endpointReceiveDual` (Transport.lean:1632-1678) is the **most complex
operation** due to the Call/Send split in the rendezvous path. Three distinct
sub-paths must be proven.

##### V3-J-op-4a: Rendezvous + Send sub-path — state transition trace

When `senderTcb.ipcState` is NOT `.blockedOnCall`:

```
st0 (pre-state, V3-J holds)
 │ endpointQueuePopHead(ep, false)   — pop sender from sendQ
st1 ← TRANSIENTLY BROKEN (sender.ipcState = .blockedOnSend, not reachable)
 │ storeTcbIpcStateAndMessage(sender, .ready, none)
st2 ← RESTORED (sender.ipcState = .ready → True)
 │ ensureRunnable(sender)
st3 ← scheduler only, unchanged
 │ storeTcbPendingMessage(receiver, senderMsg)
st4 ← STILL HOLDS (receiver.ipcState unchanged by storeTcbPendingMessage)
```

Proof composition:
```
-- Steps 1-3: Identical structure to V3-J-op-3a (rendezvous path of Send)
--   except PopHead is on sendQ (isReceiveQ = false) not receiveQ
--   Use V3-J-op-2a for remaining sendQ threads, V3-J-op-2d for cross-endpoint
--   ipcStateQueueMembership_restore_by_clearing_ipcState handles sender → .ready
--
-- Step 4: storeTcbPendingMessage modifies only receiver's pendingMessage
--   V3-J does NOT depend on pendingMessage at all
--   All TCB ipcStates unchanged, all queueNext unchanged, all endpoints unchanged
--   → V3-J trivially preserved from st3
```

##### V3-J-op-4b: Rendezvous + Call sub-path — state transition trace

When `senderTcb.ipcState = .blockedOnCall epId`:

```
st0 (pre-state, V3-J holds)
 │ endpointQueuePopHead(ep, false)   — pop sender from sendQ
st1 ← TRANSIENTLY BROKEN (sender.ipcState = .blockedOnCall, not reachable from sendQ)
 │ storeTcbIpcStateAndMessage(sender, .blockedOnReply endpointId (some receiver), none)
st2 ← RESTORED (.blockedOnReply → True in V3-J predicate)
 │ storeTcbPendingMessage(receiver, senderMsg)
st3 ← STILL HOLDS
```

The key difference from sub-path 4a: the sender transitions from
`.blockedOnCall` to `.blockedOnReply`, NOT to `.ready`. But `.blockedOnReply`
evaluates to `True` in V3-J just like `.ready` does. So the same
`ipcStateQueueMembership_restore_by_clearing_ipcState` helper works here
(generalized to accept any non-send/receive/call ipcState).

**Critical correctness check**: After the V3-J-fix (Phase 0), the
`.blockedOnCall` case maps to `sendQ`. The sender was indeed in `sendQ`
(PopHead pops from sendQ). So in the pre-state, the sender satisfied V3-J
for `.blockedOnCall` (reachable from `sendQ.head`). After PopHead, the
sender is no longer reachable, but `storeTcbIpcStateAndMessage` changes
ipcState to `.blockedOnReply`, which exits scope. All consistent.

##### V3-J-op-4c: Block path — state transition trace

```
st0 (pre-state, V3-J holds)
 │ endpointQueueEnqueue(ep, true, receiver)
st1 ← V3-J STILL HOLDS (receiver.ipcState = .ready → True)
 │ storeTcbIpcState(receiver, .blockedOnReceive endpointId)
st2 ← V3-J HOLDS (receiver now in scope with blocking state)
 │ removeRunnable(receiver)
st3 ← scheduler only
```

Proof composition:
```
-- Step 1: endpointQueueEnqueue on receiveQ
--   V3-J-op-1e: V3-J preserved
--   endpointQueueEnqueue_thread_reachable: receiver reachable from receiveQ.head
--
-- Step 2: storeTcbIpcState(receiver, .blockedOnReceive endpointId)
--   For receiver: .blockedOnReceive endpointId → must be reachable from ep.receiveQ.head
--     From Step 1: receiver is reachable (head or has predecessor)
--     storeTcbIpcState stores a TCB, not endpoint → endpoint unchanged → queue heads unchanged
--     storeTcbIpcState modifies only receiver's TCB → predecessor's queueNext unchanged
--     → receiver still reachable in st2
--   For other threads: frame (only receiver's TCB changed)
--
-- Step 3: removeRunnable → scheduler only → preserved
```

##### V3-J-op-4d: Main theorem

```lean
theorem endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st : SystemState) (sender : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hDQSI : dualQueueSystemInvariant st)
    (hRecv : endpointReceiveDual endpointId receiver st = .ok (sender, st')) :
    ipcStateQueueMembershipConsistent st'
```

**Estimated breakdown**: 4a Send sub-path (~35 lines), 4b Call sub-path
(~30 lines, shares helpers with 4a), 4c block path (~35 lines), 4d dispatch
(~15 lines), storeTcbPendingMessage frame lemma (~10 lines) = ~125 lines total.

#### V3-J-op-5: `endpointCall` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium-Hard (~70-100 lines)

`endpointCall` (Transport.lean:1710-1743) has rendezvous and block paths.

**Prerequisite**: V3-J-fix must be applied first. The current definition maps
`blockedOnCall epId` to `receiveQ.head`, but `endpointCall` enqueues callers on
`sendQ` (Transport.lean:1735: `endpointQueueEnqueue endpointId false caller`).
After V3-J-fix, `blockedOnCall` maps to `sendQ.head`, matching the implementation.

##### V3-J-op-5a: Rendezvous path — state transition trace

```
st0 (pre-state, V3-J holds)
 │ endpointQueuePopHead(ep, true)   — pop receiver from receiveQ
st1 ← TRANSIENTLY BROKEN (receiver.ipcState = .blockedOnReceive, not reachable)
 │ storeTcbIpcStateAndMessage(receiver, .ready, some msg)
st2 ← RESTORED (receiver.ipcState = .ready → True)
 │ ensureRunnable(receiver)
st3 ← scheduler only
 │ storeTcbIpcState(caller, .blockedOnReply endpointId (some receiver))
st4 ← HOLDS (.blockedOnReply → True)
 │ removeRunnable(caller)
st5 ← scheduler only
```

Proof composition:
```
-- Steps 1-3: Same pattern as V3-J-op-3a (Send rendezvous)
--   PopHead on receiveQ, then clear receiver's blocking state
--   V3-J-op-2a: remaining receiveQ threads reachable
--   ipcStateQueueMembership_restore_by_clearing_ipcState: receiver → .ready
--
-- Step 4: storeTcbIpcState(caller, .blockedOnReply ...)
--   .blockedOnReply → True in V3-J → no reachability obligation
--   For other threads: caller's TCB modification doesn't affect their reachability
--   (caller was .ready throughout, no queue links changed)
--
-- Step 5: removeRunnable → scheduler only → preserved
```

##### V3-J-op-5b: Block path — state transition trace

```
st0 (pre-state, V3-J holds)
 │ endpointQueueEnqueue(ep, false, caller)   — enqueue on sendQ
st1 ← V3-J HOLDS (caller.ipcState = .ready → True)
 │ storeTcbIpcStateAndMessage(caller, .blockedOnCall endpointId, some msg)
st2 ← V3-J HOLDS (caller now in scope)
 │ removeRunnable(caller)
st3 ← scheduler only
```

Proof composition:
```
-- Step 1: endpointQueueEnqueue on sendQ
--   V3-J-op-1e: V3-J preserved
--   endpointQueueEnqueue_thread_reachable: caller reachable from sendQ.head
--
-- Step 2: storeTcbIpcStateAndMessage(caller, .blockedOnCall endpointId, msg)
--   After V3-J-fix: .blockedOnCall → reachable from sendQ.head (not receiveQ!)
--   From Step 1: caller IS reachable from sendQ.head (head or has predecessor)
--   storeTcbIpcStateAndMessage modifies only caller's TCB, not endpoint
--   → caller still reachable from sendQ.head in st2
--   For other threads: frame
--
-- Step 3: removeRunnable → scheduler only → preserved
```

**Structural similarity**: The block path is identical to V3-J-op-3b (Send
block path) except the ipcState is `.blockedOnCall` instead of `.blockedOnSend`.
After V3-J-fix, both map to `sendQ.head`, so the same reachability argument
applies. Consider factoring out a shared helper.

##### V3-J-op-5c: V3-J Definition Fix (V3-J-fix) — detailed specification

**File**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (line ~806)

Current (incorrect):
```lean
| .blockedOnCall epId =>
    ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
      (ep.receiveQ.head = some tid ∨
       ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
         st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
         TCB.queueNext prevTcb = some tid)
```

Fixed (correct):
```lean
| .blockedOnCall epId =>
    ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
      (ep.sendQ.head = some tid ∨
       ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
         st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
         TCB.queueNext prevTcb = some tid)
```

Change: `ep.receiveQ.head` → `ep.sendQ.head` in the `blockedOnCall` case.

**Justification**: `endpointCall` enqueues callers on sendQ via
`endpointQueueEnqueue endpointId false caller` (Transport.lean:1735, where
`false` = sendQ). `endpointReceiveDual` pops from sendQ via
`endpointQueuePopHead endpointId false st` (Transport.lean:1640). The caller
is always in sendQ, never receiveQ.

**Impact of fix**: No existing proofs reference V3-J predicates (this is the
first preservation work). The fix changes the definition before any proof
consumers exist. Build gate: `lake build SeLe4n.Kernel.IPC.Invariant.Defs`.

**Estimated breakdown**: 5a rendezvous (~30 lines), 5b block (~30 lines),
5c definition fix (~2 lines) = ~62 lines total.

#### V3-J-op-6: `endpointReply` / `endpointReplyRecv` Preservation

**File**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Scope**: Medium (~60-80 lines combined)

##### V3-J-op-6a: `endpointReply` — trivial preservation

`endpointReply` (Transport.lean:1754-1776) modifies exactly one TCB:
- `storeTcbIpcStateAndMessage_fromTcb(target, .ready, some msg)` — target goes from `.blockedOnReply` to `.ready`
- `ensureRunnable(target)` — scheduler only

Both `.blockedOnReply` and `.ready` evaluate to `True` in V3-J. No endpoint
objects change. No `queueNext` links change. No queue heads change.

```lean
theorem endpointReply_preserves_ipcStateQueueMembershipConsistent
    -- Proof: unfold, extract storeObject, by_cases tid' = target
    -- Same thread: .ready → True
    -- Other threads: frame (storeObject_objects_ne)
```

Estimated: ~25 lines.

##### V3-J-op-6b: `endpointReplyRecv` — composition

`endpointReplyRecv` (Transport.lean:1782-1810) = Reply + ReceiveDual.

```
st0 → endpointReply (target) → st1 → endpointReceiveDual (receiver) → st2
```

Proof: Chain V3-J-op-6a (Reply preserves V3-J) with V3-J-op-4d (ReceiveDual
preserves V3-J). The intermediate state `st1` satisfies V3-J by 6a. Then
`endpointReceiveDual` preserves it by 4d.

**Precondition threading**: V3-J-op-4d requires `dualQueueSystemInvariant st1`.
This must come from the existing `endpointReply` preservation proofs for
`dualQueueSystemInvariant`. This is an existing theorem — no new work.

Estimated: ~35 lines (mostly precondition discharge).

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
| `IPC/Invariant/Defs.lean` | 0 | ~2 (blockedOnCall fix) | Definition fix |
| `IPC/Invariant/Structural.lean` | ~960 | 0 | Helpers (240) + queue ops (375) + IPC ops (345) |
| `IPC/Invariant/NotificationPreservation.lean` | ~30 | 0 | Frame proofs |
| **Total** | **~990** | **~2** | |

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

**Specific reconstruction theorems to update** (each currently builds a 5-way
`And.intro`, must become 7-way):

| Theorem | File | Current Pattern |
|---------|------|----------------|
| `endpointSendDual_preserves_ipcInvariantFull` | `Structural.lean` | `⟨hIpc, hDQ, hPMB, hBWF, hWTPN⟩` |
| `endpointReceiveDual_preserves_ipcInvariantFull` | `Structural.lean` | same |
| `endpointCall_preserves_ipcInvariantFull` | `CallReplyRecv.lean` | same |
| `endpointReply_preserves_ipcInvariantFull` | `CallReplyRecv.lean` | same |
| `endpointReplyRecv_preserves_ipcInvariantFull` | `CallReplyRecv.lean` | same |
| `notificationSignal_preserves_ipcInvariantFull` | `NotificationPres.lean` | same |
| `notificationWait_preserves_ipcInvariantFull` | `NotificationPres.lean` | same |

Each must be extended to: `⟨hIpc, hDQ, hPMB, hBWF, hWTPN, hNoDup, hQMC⟩`

### 5.4. Phase 4: Lifecycle Integration

`lifecycleRetypeObject_preserves_coreIpcInvariantBundle` in
`Capability/Invariant/Preservation.lean` must thread the two new components.

**Retype preserves both predicates trivially** because:
- Retype creates a NEW object at an unused ObjId
- No existing endpoint queue heads change (no endpoint modified)
- No existing TCB ipcState/queueNext changes (no TCB modified)
- The new object is fresh — not in any queue, not blocking on anything

### 5.5. Phase 5: Cascading Call-Site Audit

The conjunction path change for `waitingThreadsPendingMessageNone` (from
`.2.2.2.2.2.2` to `.2.2.2.2.2.1`) will break any proof that destructures
`ipcInvariantFull` or `coreIpcInvariantBundle` positionally. Files to audit:

| File | What to Check |
|------|--------------|
| `IPC/Invariant/Structural.lean` | All `_preserves_ipcInvariantFull` theorems |
| `IPC/Invariant/EndpointPreservation.lean` | All bundle deconstruction |
| `IPC/Invariant/CallReplyRecv.lean` | All bundle deconstruction |
| `IPC/Invariant/NotificationPreservation.lean` | All bundle deconstruction |
| `Capability/Invariant/Preservation.lean` | Extractor theorems, lifecycle |
| `Kernel/CrossSubsystem.lean` | Cross-subsystem invariant composition |
| `Kernel/API.lean` | If it uses bundle extractors |
| `Service/Invariant/Policy.lean` | If it extracts IPC invariants |

**Strategy**: After updating `ipcInvariantFull`, run `lake build` and fix
each compilation error. The errors will be type mismatches in conjunction
destructuring — each is a mechanical fix (add the two new conjunct bindings).

### 5.6. Bundle Integration File Changes (Revised)

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Invariant/Defs.lean` | 2 | 2 | Definition extension |
| `Capability/Invariant/Preservation.lean` | ~20 | ~15 | Extractors + lifecycle |
| `IPC/Invariant/Structural.lean` | ~40-60 | ~30-40 | Bundle reconstruction |
| `IPC/Invariant/EndpointPreservation.lean` | ~10 | ~10 | Path fixes |
| `IPC/Invariant/CallReplyRecv.lean` | ~10 | ~10 | Path fixes |
| `IPC/Invariant/NotificationPreservation.lean` | ~5 | ~5 | Path fixes |
| `Kernel/CrossSubsystem.lean` | 0 | ~5 | Path fixes if needed |
| **Total** | **~87-107** | **~77-87** | |

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

### 6.2. Recommended Execution Phases (Optimized)

The execution order is optimized for three goals: (1) resolve blockers
earliest, (2) maximize parallelism between V3-K and V3-J chains, and
(3) fail fast — validate the hardest proof (V3-J-op-1) before investing
in the easier downstream proofs.

**Phase 0: Definition Fix + Validation** (blocking prerequisite)
- V3-J-fix: Change `blockedOnCall` from `receiveQ.head` to `sendQ.head`
- Verify with `lake build SeLe4n.Kernel.IPC.Invariant.Defs`
- **Gate**: Build succeeds, no downstream breakage

**Phase 1a: V3-K Primitives** (no dependencies)
- V3-K-prim-1: Non-TCB/non-endpoint frame lemma
- V3-K-prim-2: `storeTcbQueueLinks` K-2 preservation
- V3-K-prim-3: Endpoint store with known heads
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 1b: V3-J Primitives + Shared Helpers** (parallel with 1a)
- V3-J-prim-1: Non-TCB/non-endpoint frame lemma
- V3-J-prim-2: `storeTcbIpcState` preservation (with reachability precondition)
- V3-J-prim-3: `storeTcbIpcStateAndMessage` preservation
- Shared helper: `ipcStateQueueMembership_restore_by_clearing_ipcState`
- Shared helper: `storeTcbPendingMessage_preserves_ipcStateQueueMembershipConsistent`
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 2a: V3-K Queue Operations** (depends on Phase 1a)
- V3-K-op-1: `endpointQueueEnqueue` K-2 (4 sub-steps: K-op-1a through 1d)
- V3-K-op-2: `endpointQueuePopHead` K-2 (4 sub-steps: K-op-2a through 2d)
- V3-K-op-3: `endpointQueueRemoveDual` K-2 (5 sub-steps: K-op-3a through 3e)
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 2b: V3-J Queue Operations — CRITICAL PATH** (depends on Phase 1b)
- V3-J-op-1: `endpointQueueEnqueue` reachability (5 sub-lemmas: J-op-1a through 1e)
  - **This is the hardest proof. Do it first to unblock Phases 3-4.**
- V3-J-op-2: `endpointQueuePopHead` helper lemmas (4 sub-lemmas: J-op-2a through 2d)
- V3-J helper: `endpointQueueEnqueue_thread_reachable` (used by all block paths)
- **Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

**Phase 3: IPC Operation Proofs** (depends on Phase 2a + 2b)
- V3-K-op-4 through V3-K-op-9: Compose primitive proofs for K
- V3-J-op-3: `endpointSendDual` (3 sub-steps: J-op-3a through 3c)
- V3-J-op-4: `endpointReceiveDual` (4 sub-steps: J-op-4a through 4d)
- V3-J-op-5: `endpointCall` (3 sub-steps: J-op-5a through 5c)
- V3-J-op-6: `endpointReply`/`endpointReplyRecv` (2 sub-steps: J-op-6a, 6b)
- V3-J-op-7 + V3-K-op-9: Notification ops (both predicates, separate file)
- **Gate**: All module builds pass

**Phase 4: Bundle Integration** (depends on ALL of Phase 3)
- Step 4a: Update `ipcInvariantFull` definition (Defs.lean)
- Step 4b: Add 2 new extractor theorems, fix 1 changed path (Preservation.lean)
- Step 4c: Update all bundle reconstruction theorems (Structural.lean + others)
- Step 4d: Lifecycle integration (Preservation.lean)
- Step 4e: Cascading call-site audit — fix all compilation errors
- **Gate**: Full `lake build` succeeds

**Phase 5: Validation & Documentation**
- `test_full.sh` (Tier 0-3)
- `grep -r "sorry"` / `grep -r "axiom "` hygiene check
- Trace regression: `lake exe sele4n` vs `tests/fixtures/main_trace_smoke.expected`
- Documentation sync (Section 10)
- **Gate**: All tests pass; zero `sorry`; docs synchronized

### 6.3. Critical Path Analysis

The longest dependency chain determines the minimum total execution time:

```
Phase 0 → Phase 1b → Phase 2b (V3-J-op-1) → Phase 3 (V3-J-op-3/4/5) → Phase 4 → Phase 5
```

**V3-J-op-1 is on the critical path.** Any delay in the enqueue reachability
proof directly delays all downstream work. Prioritize this proof above all
V3-K work.

V3-K work runs in parallel off the critical path:
```
Phase 0 → Phase 1a → Phase 2a → Phase 3 (V3-K IPC ops) → (merge at Phase 4)
```

### 6.4. Parallelization Opportunities

| Can Parallelize | Cannot Parallelize |
|-----------------|-------------------|
| Phase 1a (V3-K prims) ∥ Phase 1b (V3-J prims + helpers) | Phase 2 depends on Phase 1 |
| Phase 2a (V3-K queue ops) ∥ Phase 2b (V3-J queue ops) | Phase 3 depends on Phase 2 |
| V3-K IPC ops ∥ V3-J IPC ops (within Phase 3) | Phase 4 depends on ALL of Phase 3 |
| V3-K notification ∥ V3-K endpoint proofs (different files) | Bundle integration is sequential |
| V3-J-op-3 (Send) ∥ V3-J-op-5 (Call) — structurally similar | V3-J-op-6b (ReplyRecv) depends on V3-J-op-4 |

### 6.5. Shared Helper Lemma Registry

Several V3-J sub-tasks share helper lemmas. Building these first avoids
duplication and accelerates downstream work:

| Helper Lemma | Used By | Phase |
|-------------|---------|-------|
| `ipcStateQueueMembership_restore_by_clearing_ipcState` | J-op-3a, J-op-4a, J-op-4b, J-op-5a | 1b |
| `endpointQueueEnqueue_thread_reachable` | J-op-3b, J-op-4c, J-op-5b | 2b |
| `storeTcbPendingMessage_preserves_ipcStateQueueMembershipConsistent` | J-op-4a, J-op-4b | 1b |
| `endpointQueuePopHead_remaining_reachable` | J-op-3a, J-op-4a, J-op-4b, J-op-5a | 2b |
| `endpointQueuePopHead_cross_endpoint_frame` | J-op-3a, J-op-4a, J-op-4b, J-op-5a | 2b |

---

## 7. Cross-Cutting Concerns

### 7.1. V3-K / V3-J Interaction at `endpointQueueEnqueue`

**Resolution**: Self-contained via `queuePPrev` (no V3-J dependency).

The enqueued thread has `queuePPrev = none` (guard check at Core.lean:296).
Queue heads have `queuePPrev = some .endpointHead` (set at Core.lean:306
for empty-queue enqueue and Core.lean:274 for PopHead successor promotion).
Since `none ≠ some .endpointHead`, the enqueuing thread cannot be any queue
head. This proves K-2 for the empty-queue case (where the new thread becomes
a queue head — it cannot also be the opposite queue's head) without invoking
V3-J reasoning. See V3-K-op-1 (Section 3.3) for full proof sketch.

### 7.2. V3-J `blockedOnCall` Queue Assignment Issue

**Resolution**: Fix the definition (Phase 0, V3-J-fix).

The V3-J predicate maps `blockedOnCall epId` to `receiveQ.head`, but the
implementation enqueues Call callers on `sendQ` (Transport.lean:1735:
`endpointQueueEnqueue endpointId false caller` where `false` = sendQ).
The definition must be changed to use `sendQ.head`. See V3-J-op-5c
(Section 4.3) for the exact 2-line diff.

No existing proofs consume V3-J, so the fix has zero downstream breakage.

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

The `endpointQueueEnqueue` preservation proof for V3-J (sub-tasks J-op-1a
through 1e, ~140 lines total) is the **hardest proof in the plan**. It has
been decomposed into 5 focused sub-lemmas to manage complexity:

1. **J-op-1a** (~5 lines): Trivial — enqueued thread has `.ready` ipcState
2. **J-op-1b** (~25 lines): Empty-queue — no existing thread affected
3. **J-op-1c** (~45 lines): **CORE DIFFICULTY** — non-empty queue, must show
   existing threads remain reachable when old tail's `queueNext` changes
4. **J-op-1d** (~30 lines): Cross-endpoint frame — old tail/tid were nobody's
   predecessor in other endpoints' queues
5. **J-op-1e** (~35 lines): Main theorem composing sub-lemmas

The highest-risk sub-lemma is **J-op-1c**. The key insight is that the old
tail's `queueNext` was `none` (it was the tail), so changing it to `some tid`
doesn't remove any existing predecessor relationship. No thread had the old
tail as its predecessor before, so no thread loses reachability.

If J-op-1c proves harder than expected, a fallback strategy is to strengthen
the lemma's preconditions by requiring `dualQueueEndpointWellFormed` (which
gives `queuePrev` chain properties that can substitute for direct
`queueNext`-based reasoning).

---

## 9. Testing & Validation Strategy

### 9.1. Per-Phase Build Verification

| Phase | Build Command |
|-------|--------------|
| Phase 0 (Def fix) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Defs` |
| Phase 1a/1b (Primitives) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| Phase 2a/2b (Queue ops) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| Phase 3 (IPC ops) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| Phase 3 (Notifications) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation` |
| Phase 4 (Bundle) | `source ~/.elan/env && lake build` (full build — catches all downstream breakage) |
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

### A.1. Phase 0: Definition Fix

| ID | Task Summary | File(s) | Lines | Depends On |
|----|-------------|---------|-------|------------|
| V3-J-fix | Fix `blockedOnCall` → `sendQ.head` (was `receiveQ.head`) | `Defs.lean:806` | ~2 mod | — |

### A.2. V3-K Preservation Tasks

| ID | Task Summary | File(s) | Lines | Depends On |
|----|-------------|---------|-------|------------|
| V3-K-prim-1 | Non-TCB/non-endpoint `storeObject` frame lemma | `Structural.lean` | ~25 | — |
| V3-K-prim-2 | `storeTcbQueueLinks` K-2 preservation (endpoint unchanged by TCB store) | `Structural.lean` | ~30 | — |
| V3-K-prim-3 | Endpoint `storeObject` K-2 preservation (with `hDisjoint` precondition) | `Structural.lean` | ~50 | — |
| V3-K-op-1a | `endpointQueueEnqueue` K-2: `isReceiveQ × q.tail` case split | `Structural.lean` | ~10 | prim-1,2,3 |
| V3-K-op-1b | Empty-queue case: `queuePPrev` self-contained disjointness argument | `Structural.lean` | ~25 | 1a |
| V3-K-op-1c | Non-empty-queue case: head unchanged, trivial K-2 transfer | `Structural.lean` | ~15 | 1a |
| V3-K-op-1d | Extract `queuePPrev = none` from enqueue guard success | `Structural.lean` | ~10 | 1b |
| V3-K-op-2a | `endpointQueuePopHead` K-2: `queueNext` case split | `Structural.lean` | ~10 | prim-1,2,3 |
| V3-K-op-2b | Queue-becomes-empty: trivial (head = none → first disjunct) | `Structural.lean` | ~5 | 2a |
| V3-K-op-2c | Head-advances: `queuePrev` argument (pre-state nextTid.prev ≠ oppositeHead.prev) | `Structural.lean` | ~30 | 2a |
| V3-K-op-2d | Frame for other endpoints | `Structural.lean` | ~10 | 2a |
| V3-K-op-3a | `endpointQueueRemoveDual` K-2: `queuePPrev` case split | `Structural.lean` | ~10 | prim-1,2,3 |
| V3-K-op-3b | Head removal: same `queuePrev` argument as K-op-2c | `Structural.lean` | ~25 | 3a |
| V3-K-op-3c | Non-head tail removal: heads unchanged, trivial transfer | `Structural.lean` | ~10 | 3a |
| V3-K-op-3d | Non-head middle removal: heads unchanged, trivial transfer | `Structural.lean` | ~10 | 3a |
| V3-K-op-3e | Frame for other endpoints | `Structural.lean` | ~10 | 3a |
| V3-K-op-4 | `endpointSendDual` K-2: compose PopHead/Enqueue + frame lemmas | `Structural.lean` | ~45 | op-1,2 |
| V3-K-op-5 | `endpointReceiveDual` K-2: compose (3 sub-paths) | `Structural.lean` | ~55 | op-1,2 |
| V3-K-op-6 | `endpointCall` K-2: compose PopHead/Enqueue | `Structural.lean` | ~45 | op-1,2 |
| V3-K-op-7 | `endpointReply` K-2: no queue changes, trivial | `Structural.lean` | ~20 | prim-2 |
| V3-K-op-8 | `endpointReplyRecv` K-2: chain Reply + ReceiveDual | `Structural.lean` | ~35 | op-5,7 |
| V3-K-op-9 | Notification ops K-2: no endpoint changes, frame | `NotificationPres.lean` | ~25 | prim-1,2 |

### A.3. V3-J Preservation Tasks

| ID | Task Summary | File(s) | Lines | Depends On |
|----|-------------|---------|-------|------------|
| V3-J-prim-1 | Non-TCB/non-endpoint `storeObject` frame lemma | `Structural.lean` | ~25 | — |
| V3-J-prim-2 | `storeTcbIpcState` with reachability precondition | `Structural.lean` | ~60 | — |
| V3-J-prim-3 | `storeTcbIpcStateAndMessage` with reachability precondition | `Structural.lean` | ~60 | — |
| V3-J-helper-1 | `ipcStateQueueMembership_restore_by_clearing_ipcState` | `Structural.lean` | ~40 | prim-2,3 |
| V3-J-helper-2 | `storeTcbPendingMessage_preserves_ipcStateQueueMembershipConsistent` | `Structural.lean` | ~20 | — |
| V3-J-helper-3 | `endpointQueueEnqueue_thread_reachable` (post-enqueue reachability) | `Structural.lean` | ~35 | — |
| V3-J-op-1a | Enqueue: enqueued thread has `.ready` → `True` (trivial) | `Structural.lean` | ~5 | — |
| V3-J-op-1b | Enqueue empty-queue: no existing thread's reachability affected | `Structural.lean` | ~25 | prim-1 |
| V3-J-op-1c | Enqueue non-empty: existing threads remain reachable (main complexity) | `Structural.lean` | ~45 | prim-1 |
| V3-J-op-1d | Enqueue cross-endpoint frame: old tail/tid were nobody's predecessor | `Structural.lean` | ~30 | 1b,1c |
| V3-J-op-1e | Main `endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent` | `Structural.lean` | ~35 | 1a-1d |
| V3-J-op-2a | PopHead: remaining threads reachability transfer helper | `Structural.lean` | ~35 | — |
| V3-J-op-2b | PopHead: ipcState unchanged by queue link clearing | `Structural.lean` | ~15 | — |
| V3-J-op-2c | PopHead: popped head links cleared (queueNext = none) | `Structural.lean` | ~10 | — |
| V3-J-op-2d | PopHead: cross-endpoint frame | `Structural.lean` | ~40 | — |
| V3-J-op-3a | `endpointSendDual` rendezvous: PopHead + clear ipcState composition | `Structural.lean` | ~40 | op-2a-2d, helper-1 |
| V3-J-op-3b | `endpointSendDual` block: Enqueue + set blocking state composition | `Structural.lean` | ~45 | op-1e, helper-3 |
| V3-J-op-3c | Main `endpointSendDual_preserves_ipcStateQueueMembershipConsistent` | `Structural.lean` | ~15 | 3a,3b |
| V3-J-op-4a | `endpointReceiveDual` rendezvous + Send sub-path | `Structural.lean` | ~35 | op-2a-2d, helper-1,2 |
| V3-J-op-4b | `endpointReceiveDual` rendezvous + Call sub-path | `Structural.lean` | ~30 | op-2a-2d, helper-1,2 |
| V3-J-op-4c | `endpointReceiveDual` block path | `Structural.lean` | ~35 | op-1e, helper-3 |
| V3-J-op-4d | Main `endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent` | `Structural.lean` | ~15 | 4a-4c |
| V3-J-op-5a | `endpointCall` rendezvous: PopHead + clear + block caller as reply | `Structural.lean` | ~30 | op-2a-2d, helper-1 |
| V3-J-op-5b | `endpointCall` block: Enqueue + set `.blockedOnCall` (uses V3-J-fix) | `Structural.lean` | ~30 | op-1e, helper-3, J-fix |
| V3-J-op-5c | Main `endpointCall_preserves_ipcStateQueueMembershipConsistent` | `Structural.lean` | ~15 | 5a,5b |
| V3-J-op-6a | `endpointReply`: `.blockedOnReply → .ready`, both `True` | `Structural.lean` | ~25 | prim-3 |
| V3-J-op-6b | `endpointReplyRecv`: chain Reply + ReceiveDual | `Structural.lean` | ~35 | 6a, op-4d |
| V3-J-op-7 | Notification ops: `.blockedOnNotification` → `True` | `NotificationPres.lean` | ~30 | prim-1 |

### A.4. Bundle Integration Tasks

| ID | Task Summary | File(s) | Lines | Depends On |
|----|-------------|---------|-------|------------|
| V3-JK-int-1 | Add V3-J/K to `ipcInvariantFull` (5 → 7 conjuncts) | `Defs.lean` | ~4 | ALL proofs |
| V3-JK-int-2 | Add 2 new extractor theorems | `Cap/Inv/Preservation.lean` | ~10 | int-1 |
| V3-JK-int-3 | Fix `waitingThreadsPendingMessageNone` extractor path | `Cap/Inv/Preservation.lean` | ~3 mod | int-1 |
| V3-JK-int-4 | Update all `_preserves_ipcInvariantFull` bundle reconstruction | `Structural.lean` + others | ~50 mod | int-1, ALL proofs |
| V3-JK-int-5 | Lifecycle `retype` integration (trivial — fresh object) | `Cap/Inv/Preservation.lean` | ~15 | int-1 |
| V3-JK-int-6 | Cascading call-site audit — fix compilation errors | Multiple | ~30 mod | int-1-5 |

### A.5. Summary Statistics

**Total atomic sub-tasks**: 55 (was 24 — each complex task decomposed)

| Category | Count | Total Lines (est.) |
|----------|-------|--------------------|
| Phase 0 (definition fix) | 1 | ~2 modified |
| V3-K primitives | 3 | ~105 new |
| V3-K queue ops (sub-steps) | 12 | ~170 new |
| V3-K IPC ops | 6 | ~225 new |
| V3-J primitives + helpers | 6 | ~240 new |
| V3-J queue ops (sub-steps) | 14 | ~375 new |
| V3-J IPC ops (sub-steps) | 11 | ~345 new |
| Bundle integration | 6 | ~82 new, ~83 modified |
| **Grand Total** | **59** | **~1542 new, ~85 modified** |

**Files touched**: 7-8 (Defs.lean, Structural.lean, NotificationPreservation.lean,
EndpointPreservation.lean, CallReplyRecv.lean, Capability/Invariant/Preservation.lean,
CrossSubsystem.lean, possibly Architecture/Invariant.lean)

