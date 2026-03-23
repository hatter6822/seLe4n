# T4-D Proof Plan: Full Queue Chain Acyclicity + endpointQueueRemoveDual

## 1. Problem

`endpointQueueRemoveDual` has 4 success paths. Path D (mid-queue removal)
requires `prevTid ≠ nextTid` which cannot be derived from the current
invariant surface. The current `tcbQueueLinkIntegrity` allows cycles.

## 2. Solution: tcbQueueChainAcyclic

Add a full chain acyclicity invariant following the pattern established by
`serviceDependencyAcyclic` in `Service/Invariant/Acyclicity.lean`. This
prevents cycles of ANY length in queueNext chains.

## 3. Definitions (new file: SeLe4n/Kernel/IPC/Invariant/Acyclicity.lean)

### 3.1 tcbQueueNextEdge — direct edge via queueNext

```lean
def tcbQueueNextEdge (st : SystemState) (a b : ThreadId) : Prop :=
  ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b
```

~3 lines. Analogous to `serviceEdge`.

### 3.2 tcbQueueNontrivialPath — path of length ≥ 1

```lean
inductive tcbQueueNontrivialPath (st : SystemState) : ThreadId → ThreadId → Prop where
  | single : tcbQueueNextEdge st a b → tcbQueueNontrivialPath st a b
  | cons   : tcbQueueNextEdge st a b → tcbQueueNontrivialPath st b c →
             tcbQueueNontrivialPath st a c
```

~5 lines. Analogous to `serviceNontrivialPath`.

### 3.3 tcbQueueChainAcyclic — no thread reaches itself

```lean
def tcbQueueChainAcyclic (st : SystemState) : Prop :=
  ∀ tid, ¬ tcbQueueNontrivialPath st tid tid
```

~2 lines. Analogous to `serviceDependencyAcyclic`.

### 3.4 Add to dualQueueSystemInvariant

```lean
def dualQueueSystemInvariant (st : SystemState) : Prop :=
  (∀ epId ep, st.objects[epId]? = some (.endpoint ep) →
    dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity st ∧
  tcbQueueChainAcyclic st
```

## 4. Structural Lemmas (same file)

### 4.1 tcbQueueNontrivialPath_trans
If there's a nontrivial path a→b and a nontrivial path b→c, there's one a→c.
~5 lines. Direct induction on first path.

### 4.2 tcbQueueNontrivialPath_of_edge
A single edge is a nontrivial path. ~2 lines. Constructor application.

### 4.3 acyclic_implies_distinct_neighbors
THE KEY LEMMA for T4-D: if a.next=some b AND b.next=some c AND acyclicity
holds, then a ≠ c (because a→b→c→a would be a cycle of length 3 if a=c,
and a→b→a would be a cycle of length 2 if b=c=a, etc.)

More precisely:
```lean
theorem acyclic_no_two_cycle (st : SystemState)
    (hAcyclic : tcbQueueChainAcyclic st)
    (a b : ThreadId) (tcbA tcbB : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA))
    (hB : st.objects[b.toObjId]? = some (.tcb tcbB))
    (hAB : tcbA.queueNext = some b)
    (hBA : tcbB.queueNext = some a) : False
```
~5 lines. Construct path a→b→a, apply hAcyclic.

```lean
theorem acyclic_prevTid_ne_nextTid (st : SystemState)
    (hAcyclic : tcbQueueChainAcyclic st)
    (hLink : tcbQueueLinkIntegrity st)
    (tid prevTid nextTid : ThreadId) (tcb prevTcb : TCB)
    (hTid : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hPrev : st.objects[prevTid.toObjId]? = some (.tcb prevTcb))
    (hTidPrev : tcb.queuePrev = some prevTid)
    (hTidNext : tcb.queueNext = some nextTid)
    (hPrevNext : prevTcb.queueNext = some tid) :
    prevTid.toObjId ≠ nextTid.toObjId
```
~15 lines. If prevTid=nextTid, derive 2-cycle via link integrity.

### 4.4 acyclic_no_self_loop
```lean
theorem acyclic_no_self_loop (st : SystemState)
    (hAcyclic : tcbQueueChainAcyclic st)
    (a : ThreadId) (tcbA : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA)) :
    tcbA.queueNext ≠ some a
```
~4 lines. Single edge a→a is a nontrivial path.

## 5. Preservation Proofs

### 5.1 Approach: State-Monotonicity of Paths

The key preservation principle: if a nontrivial path exists in the POST-state,
we must derive a contradiction by showing a cycle exists in the PRE-state
(which violates the pre-state acyclicity).

For each operation, the proof strategy is:
- Assume ¬acyclic in post-state (i.e., ∃ cycle)
- Show the cycle also exists (possibly transformed) in the pre-state
- Contradict pre-state acyclicity

### 5.2 storeObject_endpoint_preserves_acyclic

Storing an endpoint doesn't modify any TCB. So any path in the post-state
exists identically in the pre-state.
~10 lines.

### 5.3 storeTcbQueueLinks_clearing_preserves_acyclic

When clearing tid (setting next=none), tid can no longer participate as a
source of any edge. Any path in the post-state that doesn't go through tid
exists in the pre-state. Any path going through tid is impossible (tid.next=none).
~15 lines.

### 5.4 storeTcbQueueLinks_general_preserves_acyclic

This is the HARD case. When storeTcbQueueLinks modifies tid's next from
`some oldNext` to `newNext`, we must show acyclicity is preserved.

Key insight: if a cycle exists in the post-state going through tid, then
tid→newNext→...→tid is a cycle. In the pre-state, tid→oldNext existed.
We need to show this creates a cycle in the pre-state too.

BUT: the new next might point to a different thread than before, so the
post-state cycle might NOT exist in the pre-state. Example: 
pre: a→b→c, change a.next to c. Post: a→c→... If c→a existed before,
now a→c→a is a 2-cycle in post-state but not in pre-state.

HOWEVER: all actual operations that modify next in this codebase either:
(a) Set next=none (clearing) — trivially preserves
(b) Set next=some tid where tid.next=none (append to tail) — can't create cycle
    because tid has no successor
(c) Set oldTail.next=some newTid where newTid is fresh (not in any chain) — 
    can't create cycle because newTid.next=none
(d) Set prevTid.next=some nextTid as part of removal splice — need to prove

For case (d) specifically: in the pre-state, prevTid→tid→nextTid. After
splice, prevTid→nextTid. If there's now a cycle prevTid→nextTid→...→prevTid,
then in the pre-state prevTid→tid→nextTid→...→prevTid is also a cycle
(longer, but still a cycle). Contradiction with pre-state acyclicity.

This is the critical proof technique: **cycle shortening**. If removing
a node from a chain creates a cycle, then the chain with the node included
was also a cycle (just longer).

Formal statement:
```lean
theorem storeTcbQueueLinks_splice_preserves_acyclic
    (st st' : SystemState)
    (prevTid tid : ThreadId) (prevTcb : TCB)
    (newNext : Option ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev newNext = .ok st')
    (hAcyclic : tcbQueueChainAcyclic st)
    (hPrevTcb : st.objects[prevTid.toObjId]? = some (.tcb prevTcb))
    -- The new next was reachable from prevTid via the old chain
    (hReachable : ∀ nid, newNext = some nid →
      tcbQueueNextEdge st prevTid tid ∧ 
      (nid = tid ∨ tcbQueueNontrivialPath st tid nid)) :
    tcbQueueChainAcyclic st'
```
~30 lines. By contradiction: assume cycle in st'. Transform it to a cycle in st.

Actually, the approach is simpler than this. Let me refine:

**Simpler approach for splice**: The splice sets prevTid.next := some nextTid.
In the pre-state, prevTid.next = some tid and tid.next = some nextTid. So
the edge prevTid→nextTid in the post-state is "shortcutting" prevTid→tid→nextTid
from the pre-state. Any cycle in the post-state using the shortcut can be
"expanded" by inserting tid back, giving a longer cycle in the pre-state.

More precisely: if there's a nontrivial path from x to x in st' that uses
the edge prevTid→nextTid, replace that edge with prevTid→tid→nextTid. The
result is a nontrivial path from x to x in st (since all other edges are
unchanged, and prevTid→tid and tid→nextTid are edges in st). This is a
cycle in st. Contradiction.

This proof technique works for ANY splice where the new edge is a shortcut
of existing edges. It does NOT work for arbitrary next-pointer modifications.

### 5.5 Operation-specific preservation

For `endpointQueueEnqueue`:
- Sets oldTail.next = some newTid (where newTid.next was none)
- Sets newTid.prev = some oldTail, newTid.next = none
- Acyclicity: newTid.next=none means no edge FROM newTid. oldTail.next=some newTid
  adds one new edge. A cycle would need to reach oldTail again from newTid, but
  newTid has no outgoing edge. So no cycle. ~15 lines.

For `endpointQueuePopHead`:
- Clears head's links (next=none, prev=none)
- Sets nextTid.prev=none (doesn't change next, so no new edges)
- Acyclicity: fewer edges → fewer cycles. ~10 lines.

For `endpointQueueRemoveDual` Path D (the splice):
- Sets prevTid.next=some nextTid (shortcut)
- Sets nextTid.prev=some prevTid (doesn't change next, no new edge)
- Clears tid's links
- Acyclicity: the only new edge is prevTid→nextTid. Any cycle using it
  can be expanded to a cycle in the pre-state (see 5.4). ~20 lines.

## 6. Threading Through Existing Proofs

### 6.1 Update dualQueueSystemInvariant destructuring

Every `obtain ⟨hEpInv, hLink⟩ := hInv` becomes `obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv`.
Every `⟨hEpInv', hLink'⟩` construction becomes `⟨hEpInv', hLink', hAcyclic'⟩`.

Search for all sites:
```bash
grep -n "hEpInv, hLink" SeLe4n/Kernel/IPC/Invariant/Structural.lean
grep -n "hLink⟩" SeLe4n/Kernel/IPC/Invariant/Structural.lean
```

Estimated ~20 sites to update.

### 6.2 Prove acyclicity preservation at each site

At each construction site where `dualQueueSystemInvariant` is assembled,
add the `hAcyclic'` component. For most operations, acyclicity is preserved
because:
- storeObject (endpoint) preserves acyclicity (5.2)
- storeTcbQueueLinks (clearing) preserves acyclicity (5.3)
- The composition of these preserves

For endpointQueuePopHead and endpointQueueEnqueue, we need the operation-
specific proofs from 5.5.

## 7. The Main Theorem: endpointQueueRemoveDual_preserves_dualQueueSystemInvariant

### 7.1 Theorem signature

```lean
set_option maxHeartbeats 1600000 in
theorem endpointQueueRemoveDual_preserves_dualQueueSystemInvariant
    (endpointId : ObjId) (isReceiveQ : Bool) (tid : ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st'
```

### 7.2 Preamble (~50 lines)

1. obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
2. unfold endpointQueueRemoveDual at hStep
3. Case split: objects[endpointId]?, object type, lookupTcb, queuePPrev
4. Guards: head/tail isNone, pprevConsistent
5. Split on pprev: endpointHead vs tcbNext

### 7.3 Path A: endpointHead + no next (~80 lines)

State: st → storeObject(ep1) → st1 → storeObject(ep') → st3 → clear(tid) → st4

- Link integrity: storeObject preserves (×2), clearing preserves
- Endpoint WF: empty queue + preserved other queue
- Acyclicity: storeObject preserves (×2), clearing preserves

### 7.4 Path B: endpointHead + some nextTid (~150 lines)

State: st → storeObject(ep1) → st1 → storeTcbQueueLinks(nextTid) → st2 → 
       storeObject(ep') → st3 → clear(tid) → st4

- Link integrity: direct construction in st4 (intermediate states broken)
- Endpoint WF: head=nextTid with prev=none, tail unchanged
- Acyclicity: nextTid update doesn't add new forward edges (next unchanged),
  storeObject preserves, clearing preserves

### 7.5 Path C: tcbNext + no next (~120 lines)

State: st → storeTcbQueueLinks(prevTid, next=none) → st1 → 
       storeObject(ep') → st3 → clear(tid) → st4

- Link integrity: direct construction in st4
- Endpoint WF: head unchanged, tail=prevTid with next=none
- Acyclicity: prevTid.next set to none (removes an edge, can't create cycle),
  storeObject preserves, clearing preserves

### 7.6 Path D: tcbNext + some nextTid (~200 lines)

State: st → storeTcbQueueLinks(prevTid, next=some nextTid) → st1 → 
       storeTcbQueueLinks(nextTid, prev=some prevTid) → st2 →
       storeObject(ep') → st3 → clear(tid) → st4

- Derive prevTid ≠ nextTid from acyclic_prevTid_ne_nextTid (§4.3)
- Link integrity: direct construction in st4
- Endpoint WF: head/tail unchanged (mid-queue removal)
- Acyclicity: splice shortcut argument (§5.4)

## 8. File Organization

| File | Content | Est. Lines |
|------|---------|------------|
| SeLe4n/Kernel/IPC/Invariant/Acyclicity.lean (NEW) | Definitions + structural lemmas (§3-4) | ~60 |
| SeLe4n/Kernel/IPC/Invariant/Defs.lean | Update dualQueueSystemInvariant (§3.4) | ~5 |
| SeLe4n/Kernel/IPC/Invariant/Structural.lean | Preservation helpers (§5) | ~80 |
| SeLe4n/Kernel/IPC/Invariant/Structural.lean | Threading updates (§6) | ~60 |
| SeLe4n/Kernel/IPC/Invariant/Structural.lean | Main theorem (§7) | ~600 |
| **Total** | | **~805** |

## 9. Execution Order (atomic commits)

1. Create Acyclicity.lean with definitions + structural lemmas
2. Update Defs.lean to add tcbQueueChainAcyclic conjunct
3. Add preservation helpers in Structural.lean (§5)
4. Thread hAcyclic through all existing proofs in Structural.lean (§6)
5. Add Path A of main theorem (build + verify)
6. Add Path B (build + verify)
7. Add Path C (build + verify)
8. Add Path D (build + verify)
9. Final: zero sorry scan, test_smoke.sh, documentation update

## 10. Risk Mitigation

**Risk**: Existing proofs break when adding third conjunct to dualQueueSystemInvariant.
**Mitigation**: Do §6 (threading) in one atomic step. Every obtain/constructor site
must be updated together.

**Risk**: The splice shortcut proof (§5.4) doesn't go through.
**Mitigation**: The proof relies on: if edge a→b is a shortcut of a→x→b, then any
cycle using a→b can be expanded. This is a standard graph theory result. The
inductive proof on path length is straightforward.

**Risk**: Path D exceeds maxHeartbeats.
**Mitigation**: Set maxHeartbeats to 1600000. Factor sub-proofs into `have` blocks.

**Risk**: storeTcbQueueLinks modifications in intermediate states complicate
object tracking.
**Mitigation**: Use by_cases on ObjId equality at each tracking point, matching
the PopHead proof pattern exactly.
