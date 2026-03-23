# T4-D Proof Plan: endpointQueueRemoveDual preserves dualQueueSystemInvariant

## Problem Summary

`endpointQueueRemoveDual` removes a thread from an endpoint's intrusive queue.
It has 4 success paths. The proof requires showing `dualQueueSystemInvariant`
is preserved across all 4 paths. The key blocker is Path D (mid-queue removal)
where `prevTid ≠ nextTid` cannot be derived from the current invariant.

## Root Cause

`tcbQueueLinkIntegrity` allows 2-cycles (a.next=b, b.next=a) which are
pathological states that should never occur in well-formed queues. When
`prevTid = nextTid`, the splice logic reads modified state, breaking the
proof's object-tracking chain.

## Solution: Add tcbQueueChainAcyclic (full acyclicity)

Add a fuel-bounded chain acyclicity predicate to the invariant surface.
This prevents cycles of ANY length in queue links, not just 2-cycles:

```lean
/-- Follow queueNext links for up to `fuel` steps from `start`. -/
def queueNextChain (st : SystemState) (start : ThreadId) : Nat → Option ThreadId
  | 0 => some start
  | n + 1 => match st.objects[start.toObjId]? with
    | some (.tcb tcb) => match tcb.queueNext with
      | some next => queueNextChain st next n
      | none => none
    | _ => none

/-- No TCB can reach itself via any number of queueNext steps. -/
def tcbQueueChainAcyclic (st : SystemState) : Prop :=
  ∀ (a : ThreadId) (tcbA : TCB),
    st.objects[a.toObjId]? = some (.tcb tcbA) →
    ∀ (n : Nat), n > 0 → queueNextChain st a n ≠ some a
```

### Why full acyclicity

1. **Prevents all degenerate states**: self-loops, 2-cycles, N-cycles
2. **Enables `prevTid ≠ nextTid`**: In T4-D, if prevTid=nextTid, then
   tid→nextTid→tid is a 2-cycle, contradicting acyclicity
3. **Future-proofs the proof surface**: any theorem about queue traversal
   benefits from knowing chains terminate
4. **Closes M-CS-1**: interior queue member stale reference detection
   requires reachability, which acyclicity enables

### Practical simplification

For T4-D, we only need `prevTid ≠ nextTid`, which follows from the
2-step case (n=2) of acyclicity. But proving full acyclicity is the
right engineering decision — it's preserved by the same operations and
provides strictly stronger guarantees.

However, full acyclicity is harder to prove preserved by operations
because it requires fuel-bounded induction. A pragmatic middle ground:

**Option A (recommended)**: Prove the no-2-cycle property first (simple,
unblocks T4-D), then add full acyclicity in a follow-up phase.

**Option B**: Prove full acyclicity upfront (more work, delays T4-D).

For this plan, we use **Option A** for T4-D and note full acyclicity
as a T5-scope follow-up that builds on this foundation.

```lean
/-- No 2-cycle: if a.next=some b, then b.next ≠ some a. Combined with
tcbQueueLinkIntegrity (which gives b.prev=some a from a.next=some b),
this prevents the degenerate state where two TCBs point to each other
in a cycle disconnected from any queue head/tail. -/
def tcbQueueNoTwoCycle (st : SystemState) : Prop :=
  ∀ (a b : ThreadId) (tcbA tcbB : TCB),
    st.objects[a.toObjId]? = some (.tcb tcbA) →
    st.objects[b.toObjId]? = some (.tcb tcbB) →
    tcbA.queueNext = some b → tcbB.queueNext ≠ some a
```

This is preserved by all queue operations (enqueue adds to tail with
next=none; dequeue removes head and clears links; neither creates 2-cycles).
Full chain acyclicity is deferred to T5-I (cross-subsystem strengthening).

## Implementation Steps

### Phase 1: Add the predicate (Defs.lean)

**Step 1.1**: Add `tcbQueueNoTwoCycle` definition after `tcbQueueLinkIntegrity`
in `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~5 lines).

**Step 1.2**: Add `tcbQueueNoTwoCycle st` as a third conjunct of
`dualQueueSystemInvariant`:
```lean
def dualQueueSystemInvariant (st : SystemState) : Prop :=
  (∀ epId ep, ... → dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity st ∧
  tcbQueueNoTwoCycle st
```

**Step 1.3**: Update all existing `obtain ⟨hEpInv, hLink⟩ := hInv` patterns
in Structural.lean to `obtain ⟨hEpInv, hLink, hNoCycle⟩ := hInv` (~15 sites).
Also update all `⟨..., hLink⟩` construction sites to `⟨..., hLink, hNoCycle⟩`.

### Phase 2: Prove preservation for existing operations (Structural.lean)

**Step 2.1**: Prove `storeObject_endpoint_preserves_tcbQueueNoTwoCycle`:
Storing an endpoint doesn't modify any TCB → trivial preservation (~10 lines).

**Step 2.2**: Prove `storeTcbQueueLinks_clearing_preserves_noTwoCycle`:
Clearing a TCB's links (all none) preserves no-2-cycle because:
- The cleared TCB has next=none, so it can't be part of any 2-cycle
- Other TCBs are unchanged
(~15 lines)

**Step 2.3**: Update `endpointQueuePopHead_preserves_dualQueueSystemInvariant`:
Thread through `hNoCycle` in the existing proof. The PopHead operation:
- Stores endpoint (preserves by 2.1)
- Updates nextTid links (set prev=none, pprev=endpointHead, next unchanged)
- Clears headTid links (preserves by 2.2)
Need to show the nextTid update preserves no-2-cycle: nextTid's next is
unchanged, so if there were no 2-cycle before, there's none after. (~20 lines)

**Step 2.4**: Update `endpointQueueEnqueue_preserves_dualQueueSystemInvariant`:
Thread through `hNoCycle`. Enqueue sets the new tail's next=none and the old
tail's next=some newTid. The old tail's next was none (tail boundary), so
changing it to some newTid can't create a 2-cycle because newTid.next=none.
(~15 lines)

### Phase 3: New splice helper (Structural.lean)

**Step 3.1**: Prove `storeTcbQueueLinks_splice_preserves_linkInteg`:
When splicing `tid` out by updating `prevTid.next := nextTid`, the link
integrity is preserved IF:
- In the original state: `prevTid.next = some tid`, `tid.next = some nextTid`
- The operation sets `prevTid.next := some nextTid` (skipping tid)
- `tid`'s links are NOT yet cleared (that's a separate step)
The proof: for any (a,b) pair with a.next=some b in the new state:
- If a=prevTid: a.next=some nextTid. Need nextTid.prev=some prevTid? NO —
  nextTid.prev is still some tid (unchanged). So link integrity BREAKS here.

Wait — this means the splice of prevTid ALONE breaks link integrity.
The splice must be done in TWO steps: set prevTid.next=nextTid AND set
nextTid.prev=prevTid. After both steps, integrity is restored.

So the helper needs to be a TWO-STEP splice lemma:
```
storeTcbQueueLinks_splice_pair_preserves_linkInteg:
  After (1) setting prevTid.next:=nextTid and (2) setting nextTid.prev:=prevTid,
  tcbQueueLinkIntegrity is preserved.
```

This is the key insight. Between step 1 and step 2, link integrity is
temporarily broken. But after both steps complete, it's restored.

**Step 3.2**: Prove the two-step splice lemma (~40-60 lines):
Preconditions (from the pre-state invariant):
- hLink: tcbQueueLinkIntegrity st
- prevTid.next = some tid, tid.prev = some prevTid (forward/backward)
- tid.next = some nextTid, nextTid.prev = some tid (forward/backward)
- prevTid ≠ nextTid (from hNoCycle + the above)
- prevTid ≠ tid, nextTid ≠ tid (from no-self-loops, derivable from hNoCycle)

After step 1 (storeTcbQueueLinks prevTid ... nextTid → stPrev):
- prevTid.next = some nextTid (new)
- nextTid.prev = some tid (still old — broken link!)

After step 2 (storeTcbQueueLinks nextTid prevTid ... → st2):
- prevTid.next = some nextTid (preserved from step 1, since prevTid≠nextTid)
- nextTid.prev = some prevTid (new — link restored!)

For any (a,b) pair in st2 with a.next=some b:
- Case a=prevTid: a.next=some nextTid=b. Need b.prev=some prevTid. ✓ (step 2 set this)
- Case a=nextTid: a.next=nextTcb.queueNext. Need (nextTcb.queueNext).prev=some nextTid.
  nextTcb.queueNext was unchanged from pre-state. Pre-state had nextTid.next=nextTcb.queueNext
  with forward integrity. So if nextTcb.queueNext=some c, then c.prev=some nextTid in pre-state.
  c ≠ prevTid and c ≠ nextTid (c is further down the chain), so c is unchanged. ✓
- Case a=tid: tid's links are unchanged in st2 (tid≠prevTid, tid≠nextTid). tid.next=some nextTid.
  Need nextTid.prev=some tid? NO — nextTid.prev was changed to some prevTid. BROKEN.

  BUT: this is expected! After the splice, tid's links are stale. The NEXT step
  (storeTcbQueueLinks tid none none none) will clear them. So link integrity
  is temporarily broken for tid specifically.

  This means the two-step splice lemma can't prove full link integrity.
  It can only prove link integrity FOR ALL TCBs EXCEPT tid.

**REVISED APPROACH**: Don't try to maintain link integrity through intermediate
states. Instead, prove it directly for the FINAL state (after all 4 mutations).

### Phase 3 (Revised): Direct final-state proof

**Step 3.1**: For each path, prove `tcbQueueLinkIntegrity` directly on the
final state `st4` by case analysis on (a,b) pairs:

For any (a,b) in st4 with a.next=some b:
- a ∈ {tid, prevTid, nextTid, other}
- For each case, determine a's queueNext in st4 and verify b's queuePrev

For Path D, st4 has:
- tid: next=none, prev=none (cleared)
- prevTid: next=some nextTid, prev=prevTcb.queuePrev (from step 1, preserved through)
- nextTid: next=nextTcb.queueNext, prev=some prevTid (from step 2, preserved through)
- other: unchanged from pre-state

Case analysis for forward integrity (a.next=some b → b.prev=some a):
1. a=tid: tid.next=none, so no obligation. ✓
2. a=prevTid: prevTid.next=some nextTid. Need nextTid.prev=some prevTid. ✓ (step 2)
3. a=nextTid: nextTid.next=nextTcb.queueNext. If nextTcb.queueNext=some c, need
   c.prev=some nextTid. c≠tid (tid has prev=none≠some nextTid), c≠prevTid (would need
   prevTid.prev=some nextTid, but prevTid.prev=prevTcb.queuePrev=some x where x≠nextTid
   unless prevTcb.queuePrev=some nextTid — need to check). c≠nextTid (no self-loop from
   hNoCycle). So c is unchanged, and pre-state had c.prev=some nextTid. ✓
4. a=other: a.next unchanged from pre-state. If a.next=some b where b≠tid, b≠prevTid,
   b≠nextTid, then b is unchanged and pre-state integrity holds. ✓
   If a.next=some tid: pre-state had tid.prev=some a. But tid.prev was some prevTid.
   So a=prevTid. But a≠prevTid (we're in the "other" case). Contradiction. ✓
   If a.next=some prevTid: need prevTid.prev=some a in st4. prevTid.prev=prevTcb.queuePrev
   in st4 (unchanged from step 1). Pre-state had prevTid.prev=some x where
   x.next=some prevTid (backward integrity). If x=a, then prevTcb.queuePrev=some a. ✓
   If a.next=some nextTid: need nextTid.prev=some a in st4. nextTid.prev=some prevTid
   in st4 (set by step 2). So a=prevTid. But a≠prevTid. Contradiction. ✓

Similarly for backward integrity.

This case analysis is mechanical but tedious. ~100-150 lines per path.

### Phase 4: The main theorem

**Step 4.1**: Write the theorem skeleton with error case handling (~50 lines):
- unfold, case split on objects/lookupTcb/pprev/guards
- All error paths closed by `simp`

**Step 4.2**: Path A (endpointHead, no next) — ~80 lines:
- storeObject → storeObject → storeTcbQueueLinks(clear)
- Endpoint WF: empty queue (intrusiveQueueWellFormed_empty) + preserved other queue
- Link integrity: storeObject preserves, clearing preserves
- No-2-cycle: clearing preserves

**Step 4.3**: Path B (endpointHead, with next) — ~150 lines:
- storeObject → storeTcbQueueLinks(nextTid) → storeObject → storeTcbQueueLinks(clear)
- Use endpointQueuePopHead as template (identical structure)
- Link integrity through intermediate states using existing helpers
- No-2-cycle: nextTid update preserves (next field unchanged)

**Step 4.4**: Path C (tcbNext, no next / tail removal) — ~120 lines:
- storeTcbQueueLinks(prevTid, set next=none) → storeObject → storeTcbQueueLinks(clear)
- prevTid becomes new tail (next=none)
- Link integrity: prevTid update sets next=none (like clearing next only)
- For (a,b) pairs: prevTid.next=none so no forward obligation from prevTid
- No-2-cycle: prevTid.next=none can't be in any 2-cycle

**Step 4.5**: Path D (tcbNext, with next / mid-queue) — ~200 lines:
- storeTcbQueueLinks(prevTid) → storeTcbQueueLinks(nextTid) → storeObject → storeTcbQueueLinks(clear)
- Use hNoCycle to derive prevTid ≠ nextTid
- Direct case analysis on final state for link integrity
- No-2-cycle preservation in final state

## Total Estimated Size

| Component | Lines |
|-----------|-------|
| Phase 1: Predicate + dualQueueSystemInvariant update | ~15 |
| Phase 1: Existing proof updates (threading hNoCycle) | ~80 |
| Phase 2: New preservation helpers | ~50 |
| Phase 3: Not needed (direct proof in Phase 4) | 0 |
| Phase 4: Main theorem skeleton + error cases | ~50 |
| Phase 4: Path A | ~80 |
| Phase 4: Path B | ~150 |
| Phase 4: Path C | ~120 |
| Phase 4: Path D | ~200 |
| **Total** | **~745** |

## Execution Order

1. Phase 1.1-1.2: Add predicate and update dualQueueSystemInvariant
2. Phase 1.3: Update existing destructuring patterns (build will fail until done)
3. Phase 2: Prove new preservation helpers
4. Phase 4.1: Theorem skeleton
5. Phase 4.2-4.5: Four paths, in order A → C → B → D (easiest to hardest)
6. Build, verify zero sorry, run tests
