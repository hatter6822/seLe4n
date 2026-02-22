# M2C — Fuel Adequacy

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Resolve the fuel adequacy question — the most architecturally significant
decision in M2. This document analyzes the problem, presents options, and provides
implementation guidance for the chosen approach.

---

## 1. The fuel adequacy problem

### 1.1 Background

The BFS function uses `serviceBfsFuel st` as the initial fuel:

```lean
-- SeLe4n/Kernel/Service/Operations.lean:96-97
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

The BFS consumes one unit of fuel per **expansion** (visiting a new, previously
unvisited node). If fuel runs out before all reachable nodes are explored, the BFS
returns `false` even if the target is reachable.

For the completeness proof, we need to guarantee that `serviceBfsFuel st` is always
large enough to explore all nodes on any path from `src` to `target`.

### 1.2 Why this is non-trivial

The `SystemState` stores services as a total function:

```lean
-- SeLe4n/Model/State.lean:49
services : ServiceId → Option ServiceGraphEntry
```

Where `ServiceId` wraps `Nat`:

```lean
-- SeLe4n/Prelude.lean:112-113
structure ServiceId where
  val : Nat
  deriving Repr, DecidableEq, BEq, Hashable
```

This means:
- The domain of `services` is infinite (all natural numbers).
- There is no built-in bound on how many `ServiceId` values map to `some`.
- The BFS could, in principle, discover an unbounded number of nodes through
  dependency lists.
- `serviceBfsFuel st = objectIndex.length + 256` is a heuristic bound based on
  the kernel object index, but there's no formal proof connecting object count
  to service count.

### 1.3 The gap to bridge

We need one of:
1. A proof that `serviceBfsFuel st ≥ |reachable nodes from src|` for all `src`.
2. A hypothesis that the number of registered services is bounded.
3. A proof that the model's construction constrains service registration.

---

## 2. Analysis of the model

### 2.1 Service registration pathway

Services enter the model through `storeServiceState`:

```lean
-- SeLe4n/Model/State.lean:168-172
def storeServiceState (sid : ServiceId) (entry : ServiceGraphEntry) (st : SystemState) :=
  { st with services := fun sid' => if sid' = sid then some entry else st.services sid' }
```

And the public API is `serviceRegisterDependency` (Operations.lean:142), which calls
`storeServiceEntry`. The key question: **does every registered service have a
corresponding object in `objectIndex`?**

### 2.2 The `ServiceIdentity` connection

```lean
-- SeLe4n/Model/Object.lean:21-26
structure ServiceGraphEntry where
  identity : ServiceIdentity
  status : ServiceStatus
  dependencies : List ServiceId
  isolatedFrom : List ServiceId
```

Each service has an `identity.backingObject : ObjId`. The policy invariant
`policyBackingObjectTyped` (Invariant.lean:53-54) requires:

```lean
∃ ty, SystemState.lookupObjectTypeMeta st svc.identity.backingObject = some ty
```

This means every registered service's backing object must exist in the lifecycle
metadata. However, this doesn't directly imply the backing object is in `objectIndex`.

### 2.3 The `objectIndex` as a bound

`objectIndex : List ObjId` tracks known kernel objects. It's a `List`, so it's finite.
The BFS fuel `objectIndex.length + 256` is finite and concrete.

**The missing link:** We need to show either:
- Every service's backing object is in `objectIndex` (one-to-one or many-to-one
  mapping from services to objectIndex entries), OR
- The number of distinct `ServiceId` values with `services sid = some _` is ≤
  `objectIndex.length + 256`.

### 2.4 The 256 constant

The `+ 256` provides headroom for services that might not have a direct objectIndex
entry. This is a design heuristic, not a proven bound. For the formal proof, we
either need to:
- Justify the constant, or
- Treat the bound as a precondition.

---

## 3. Approaches

### 3.1 Approach A: Preconditioned theorem (RECOMMENDED)

Add an explicit fuel adequacy hypothesis to the completeness theorem:

```lean
/-- Fuel adequacy precondition: the number of registered services is bounded
    by the BFS fuel. This captures the model-level invariant that service
    registration is disciplined and the service graph is finite.

    In concrete models, this is dischargeable because:
    1. Services are created through controlled APIs.
    2. Each service has a backing kernel object.
    3. The objectIndex tracks all kernel objects.
    4. serviceBfsFuel = objectIndex.length + 256 provides generous headroom. -/
def serviceFuelAdequate (st : SystemState) : Prop :=
  ∀ (sids : List ServiceId),
    sids.Nodup →
    (∀ sid ∈ sids, lookupService st sid ≠ none) →
    sids.length ≤ serviceBfsFuel st
```

**This says:** Any list of distinct registered service IDs has length at most
`serviceBfsFuel st`. Equivalently, the number of registered services is bounded
by the fuel.

**Advantages:**
- Clean separation of concerns: BFS correctness is independent of model specifics.
- The precondition is clearly documentable and auditable.
- Easily dischargeable in concrete test states.
- No changes to operational code.

**Disadvantages:**
- The final preservation theorem gains an additional hypothesis.
- Auditors must verify the precondition is maintained across transitions.

### 3.2 Approach B: Model-level proof (ASPIRATIONAL)

Prove that registered services are bounded by `objectIndex.length + 256` from the
model structure. This requires:

1. A model invariant: `∀ sid, lookupService st sid ≠ none →
   sid.backingObject ∈ st.objectIndex` (or similar).
2. Injectivity: distinct `ServiceId` values map to distinct `objectIndex` entries
   (or at least the mapping is bounded).
3. Preservation: the invariant is maintained by all state transitions.

**This is significantly more work** and crosses subsystem boundaries (service ↔
lifecycle ↔ object store). It would eliminate the precondition but at substantial
implementation cost.

**Recommendation:** Defer Approach B. Use Approach A for M2, with Approach B as a
future enhancement (possibly M6 or a separate workstream).

### 3.3 Approach C: Strengthen BFS to use visited count (REJECTED)

Modify `serviceHasPathTo` to use `visited.length` as fuel or add a separate
termination check based on the visited set size.

**Rejected because:** The project constraint is "no operational code changes" for
TPI-D07 closure. Modifying the BFS would require re-validating all test fixtures
and potentially breaking the M3 preservation proof.

---

## 4. Fuel adequacy in the completeness proof

### 4.1 How the precondition is used

The completeness proof (CP1 in [M2D](./M2D_COMPLETENESS_PROOF.md)) uses fuel adequacy
at exactly one point: showing that fuel doesn't run out before all reachable nodes
are explored.

The argument structure:

1. Initially, fuel = `serviceBfsFuel st` and visited = `[]`.
2. Each expansion consumes 1 fuel and adds 1 node to visited.
3. After `k` expansions: fuel = `serviceBfsFuel st - k`, visited has `k` distinct nodes.
4. By `serviceFuelAdequate`: the total number of registered services ≤ `serviceBfsFuel st`.
5. The BFS only expands registered services (nodes with `lookupService st node ≠ none`).
   Nodes with no service entry have `deps = []` and add nothing to the frontier.
6. Therefore: the BFS can expand at most `serviceBfsFuel st` distinct nodes before
   either finding the target or exhausting ALL reachable nodes.

### 4.2 A subtlety: unregistered nodes in the frontier

The BFS frontier can contain `ServiceId` values with no service entry (i.e.,
`lookupService st node = none`). When such a node is expanded:

```lean
let deps := match lookupService st node with
  | some svc => svc.dependencies
  | none => []
```

The dependencies are `[]`, so no new nodes are added. The node still consumes
1 fuel unit (it's a fresh expansion). However, this node is NOT a registered
service, so it doesn't count against the `serviceFuelAdequate` bound.

**Resolution:** Strengthen `serviceFuelAdequate` to also count unregistered nodes
that appear in dependency lists:

```lean
/-- Strengthened fuel adequacy: the number of distinct ServiceId values that
    could ever appear in a BFS frontier is bounded. This includes both
    registered services and ServiceId values referenced in dependency lists
    but not themselves registered. -/
def serviceFuelAdequateStrong (st : SystemState) : Prop :=
  ∀ (sids : List ServiceId),
    sids.Nodup →
    (∀ sid ∈ sids,
      lookupService st sid ≠ none ∨
      ∃ parent, lookupService st parent ≠ none ∧
        sid ∈ (lookupService st parent).get!.dependencies) →
    sids.length ≤ serviceBfsFuel st
```

**Actually, this over-complicates things.** The simpler resolution: an unregistered
node in the frontier has `deps = []` and contributes nothing. It wastes 1 fuel unit.
The total fuel waste from unregistered nodes is bounded by the number of such
references, which is itself bounded by the sum of all dependency list lengths. Since
each dependency list is finite and the number of registered services is bounded,
this sum is bounded (though not tightly).

**Practical resolution:** Use the simple `serviceFuelAdequate` definition and observe
that:
- Unregistered frontier nodes waste fuel but don't propagate (deps = []).
- The total number of frontier nodes (registered + unregistered) that could ever
  be expanded is bounded by the sum of all dependency list lengths + 1 (for src).
- This sum is bounded by `(# registered services) × (max dependency list length)`.

For the proof, it's cleaner to use a slightly different formulation:

```lean
/-- Fuel adequacy: the BFS fuel bounds the number of distinct nodes
    that could ever be enqueued into the BFS frontier.

    This is a weaker (easier to satisfy) condition than bounding all
    registered services — it only requires bounding the reachable
    subgraph from any given source. -/
def serviceFuelAdequate (st : SystemState) : Prop :=
  ∀ (src : ServiceId),
    ∀ (sids : List ServiceId),
      sids.Nodup →
      (∀ sid ∈ sids, serviceReachable st src sid) →
      sids.length ≤ serviceBfsFuel st
```

This says: for any source, the number of distinct nodes reachable from it is bounded
by the fuel. This is more precise and aligns with the BFS behavior.

### 4.3 Incorporating into bfs_complete_for_nontrivialPath

The final theorem signature becomes:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hFuel : serviceFuelAdequate st) :  -- NEW: fuel adequacy precondition
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

**Impact on M3:** The preservation theorem at line 591 currently calls
`bfs_complete_for_nontrivialPath` at line 634. Adding `hFuel` means the preservation
theorem must also carry the fuel adequacy precondition, OR we must prove that
`serviceFuelAdequate` is preserved by `storeServiceState`.

**Preserving fuel adequacy across storeServiceState:**

```lean
theorem serviceFuelAdequate_preserved_by_storeServiceState
    (st : SystemState) (sid : ServiceId) (entry : ServiceGraphEntry)
    (hFuel : serviceFuelAdequate st) :
    serviceFuelAdequate (storeServiceState sid entry st)
```

This requires showing that `storeServiceState` doesn't increase the reachable set
beyond the fuel bound. Since `storeServiceState` can ADD edges (new dependencies),
this is NOT trivially true. Adding edge `svcId → depId` can make previously
unreachable nodes reachable.

**Resolution for M3:** The preservation theorem's proof at line 634 calls
`bfs_complete_for_nontrivialPath` on the PRE-STATE `st`, not the post-state.
So we only need `serviceFuelAdequate st` (pre-state), which can be a hypothesis
on the preservation theorem.

### 4.4 Alternative: unconditional via sorry-compatible weakening

If adding a precondition to the preservation theorem is undesirable, we can keep
the original signature and accept that `bfs_complete_for_nontrivialPath` is
unconditional but relies on the (unproven) assumption that `serviceBfsFuel` is
always adequate.

In this case, the sorry on `bfs_complete_for_nontrivialPath` is replaced with
actual proof under a `have : serviceFuelAdequate st := by sorry` internal sorry.
This moves the sorry from the BFS bridge to the fuel adequacy — a much more
narrow and well-understood obligation.

---

## 5. Decision matrix

| Approach | Adds hypothesis? | Proof complexity | Future-proof | Recommended? |
|---|---|---|---|---|
| **A: Preconditioned** | Yes (to preservation thm) | Medium | Yes (clean, auditable) | **YES** |
| **B: Model-level** | No | High (cross-subsystem) | Yes (ideal) | Future work |
| **C: Modify BFS** | N/A | Low | No (violates constraint) | No |
| **D: Internal sorry** | No | Low | No (sorry remains) | Fallback only |

---

## 6. Implementation checklist

1. [ ] Define `serviceFuelAdequate` in `Invariant.lean` (before the BFS bridge)
2. [ ] Add `hFuel : serviceFuelAdequate st` to `bfs_complete_for_nontrivialPath`
3. [ ] Verify the call site in the preservation theorem (line 634) — add `hFuel`
       parameter threading
4. [ ] Add `hFuel : serviceFuelAdequate st` to
       `serviceRegisterDependency_preserves_acyclicity` (line 591)
5. [ ] Verify `lake build` succeeds with the new signatures
6. [ ] Update test fixtures if the preservation theorem's signature changes
7. [ ] Document the precondition in the module docstring and GitBook chapter 12
