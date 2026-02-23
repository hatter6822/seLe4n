# seLe4n Codebase Audit — 2026-02-23

**Scope**: End-to-end audit of the entire seLe4n Lean 4 codebase (v0.11.6)
**Toolchain**: Lean 4.27.0, Lake 0.11.6
**Files audited**: 33 `.lean` source files, 8 test/script files, 12+ documentation files
**Proof-soundness sweep**: Zero `sorry`, `axiom`, `native_decide`, `unsafe`, `panic!`, `noncomputable`, or `Classical.*` instances found

---

## Executive Summary

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics. It models
scheduler transitions, capability-space operations, synchronous IPC, notification
signaling, object lifecycle, service orchestration, and information-flow policy
enforcement — producing machine-checked proofs of invariant preservation over
executable transition semantics.

**The codebase is mechanically sound** — every theorem compiles without `sorry`
or axioms, and the build completes cleanly. However, this audit identifies
**structural and semantic issues** that weaken the assurance claims the project
makes. The core concern is not that the proofs are *wrong*, but that several
proofs are **trivially true by construction** or **prove weaker properties than
the documentation implies**.

### Severity Tally

| Severity | Count | Description |
|----------|-------|-------------|
| CRITICAL | 4 | Fundamental semantic gaps vs seL4; proof assurance undermined |
| HIGH     | 5 | Significant model incompleteness or misleading proof structure |
| MEDIUM   | 10 | Model simplifications, testing gaps with correctness implications |
| LOW      | 8 | Minor gaps, stylistic issues, or known deferrals |

---

## Section 1: Proof Soundness Surface

### 1.1 Zero Unsound Constructs (POSITIVE)

A comprehensive sweep of all 33 `.lean` files found:

- **0** `sorry` — no deferred proof obligations
- **0** `axiom` — no unproven logical assumptions
- **0** `native_decide` — no reflection bypasses
- **0** `unsafe` / `unsafeCast` — no memory-unsafe operations
- **0** `panic!` / `unreachable!` — no runtime abort paths
- **0** `noncomputable` — all definitions are computable
- **0** `Classical.*` — no classical logic dependencies
- **0** `@[extern]` — no FFI calls

This is a genuine strength. The entire proof surface is constructive, computable,
and self-contained within Lean's kernel.

### 1.2 Tautological Proofs (CRITICAL — C-01)

Several key invariant proofs are **mathematically trivial** — they prove
properties that are automatically satisfied by the Lean type system, providing
zero additional assurance.

**`cspaceSlotUnique_holds`** (`Capability/Invariant.lean:456-466`):
Claims "lookup is deterministic" — but `cspaceLookupSlot` is a pure function,
so `f x = f x` is a type-system tautology. The proof does not verify any
meaningful property about the CSpace implementation.

**`cspaceLookupSound_holds`** (`Capability/Invariant.lean:468-477`):
Claims "lookup is sound" — but the proof's first step *assumes* lookup is
read-only (via `cspaceLookupSlot_preserves_state`), then *concludes* the
operation is sound. The conclusion contains the assumption, making this circular.

**Impact**: The `capabilityInvariantBundle` includes both of these as components.
Documentation claims these are "high assurance" theorems, but they provide no
evidence beyond what the type system guarantees for free.

**Recommendation**: Either (a) remove these theorems and note that determinism
is a meta-property of pure functions, or (b) reformulate them to prove
non-trivial properties (e.g., that lookup returns the *correct* capability
relative to a specification, not just *a* capability).

### 1.3 Non-Compositional Preservation Proofs (HIGH — H-01)

All `*_preserves_capabilityInvariantBundle` theorems (6 instances in
`Capability/Invariant.lean:519-570`, plus 3 IPC instances at lines 778-809)
follow this pattern:

```lean
theorem op_preserves_capabilityInvariantBundle
    (hInv : capabilityInvariantBundle st)
    (_hStep : op st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_, _, hAttRule, _⟩  -- discard pre-state evidence
  exact ⟨cspaceSlotUnique_holds st',     -- re-prove from scratch
         cspaceLookupSound_holds st',
         hAttRule,
         lifecycleAuthorityMonotonicity_holds st'⟩
```

The pre-state invariant `hInv` is destructured and **discarded**. Each component
is re-proven from scratch on the post-state `st'`. This means the proof strategy
shows that **any state** (not just reachable states) satisfies these invariants —
which is exactly the tautology issue from C-01.

The `_hStep` hypothesis (the actual operation) is unused in most cases, meaning
these theorems do not actually verify that the operation preserves the invariant
through its specific state transformation.

**Recommendation**: Refactor preservation proofs to be compositional — each proof
should derive post-state invariant components from pre-state components *through*
the operation's effect on state. If the components are universally true, the
invariant definition needs strengthening.

---

## Section 2: Capability Subsystem

### 2.1 Missing Capability Operations (CRITICAL — C-02)

The seL4 CSpace has four core operations: **copy**, **mint**, **move**, and
**mutate**. The seLe4n model implements only:

- `cspaceMint` — derive with rights attenuation
- `cspaceDeleteSlot` — remove capability
- `cspaceRevoke` — local revocation

**Missing operations**:

| Operation | seL4 Semantics | Impact of Absence |
|-----------|----------------|-------------------|
| **Copy** | Duplicate capability without rights change; no CDT link | Cannot model basic capability transfer between address spaces |
| **Move** | Transfer capability, clearing source slot atomically | Cannot model slot migration; source slot semantics are wrong |
| **Mutate** | In-place rights modification | Cannot model authority refinement without derivation |

Without `copy`, the model cannot represent the most fundamental seL4 capability
operation. `mint` is not a substitute — copy and mint have different
preconditions (copy doesn't require Grant rights) and different CDT effects
(copy doesn't create a derivation edge).

### 2.2 No Capability Derivation Tree (CRITICAL — C-03)

seL4's capability system tracks parent-child relationships in a **Capability
Derivation Tree (CDT)**. The CDT is essential for:

1. **Revocation**: Walking the tree to find all derived capabilities
2. **Acyclicity**: Ensuring derivation chains are well-founded
3. **Authority tracking**: Proving authority monotonicity globally

seLe4n has no CDT model. `cspaceRevoke` only removes capabilities *within the
same CNode* that share the same target — it cannot trace derivation chains
across CNode boundaries.

### 2.3 Local-Only Revocation (CRITICAL — C-04)

`cspaceRevoke` (`Capability/Operations.lean:220-235`) uses
`CNode.revokeTargetLocal`, which filters slots within one CNode:

```lean
def revokeTargetLocal (node : CNode) (sourceSlot : Slot) (target : CapTarget) : CNode :=
  { node with slots := node.slots.filter (fun entry =>
    entry.fst = sourceSlot ∨ entry.snd.target ≠ target) }
```

The `lifecycleAuthorityMonotonicity` invariant (`Capability/Invariant.lean:76-86`)
quantifies only over slots in `addr.cnode`:

```lean
∀ slot cap,
  SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap →
  cap.target = parent.target → slot = addr.slot
```

This means capabilities in other CNodes pointing to the same target are **not
revoked**. Authority can leak across CNode boundaries, violating seL4's global
revocation guarantee.

### 2.4 Silent Slot Overwrites (HIGH — H-02)

`cspaceInsertSlot` (`Capability/Operations.lean:53-61`) calls `CNode.insert`,
which silently overwrites existing capabilities:

```lean
def insert (node : CNode) (slot : Slot) (cap : Capability) : CNode :=
  let slots := (slot, cap) :: node.slots.filter (fun entry => entry.fst ≠ slot)
  { node with slots }
```

In real seL4, inserting into an occupied slot either fails or requires prior
revocation. The current model allows overwriting a parent capability that may
have derived children, silently breaking derivation chains (when CDT is added).

### 2.5 Badge Override Safety Gap (HIGH — H-03)

`mintDerivedCap` (`Capability/Operations.lean:184-189`) accepts an arbitrary
badge parameter. The theorem `mintDerivedCap_rights_attenuated_with_badge_override`
proves that *rights* are attenuated, but makes no statement about badge
correctness.

In seL4, badges identify IPC message senders. An arbitrary badge override could
cause a receiver to misidentify the sender. No theorem proves that badge values
are semantically safe with respect to notification routing.

---

## Section 3: IPC Subsystem

### 3.1 Endpoint Model Diverges from seL4 (MEDIUM — M-01)

The `Endpoint` structure (`Model/Object.lean`) was updated from the original
model to include:

```lean
structure Endpoint where
  state : EndpointState
  queue : List ThreadId        -- single queue (not separate send/receive)
  waitingReceiver : Option ThreadId  -- at most one receiver
```

seL4 uses separate send and receive queues on each endpoint. The seLe4n model
uses a single `queue` plus an `Option ThreadId` for the receiver. This means:

- At most one receiver can wait on an endpoint at a time
- The receive path (`endpointReceive`) only consumes from the send queue
- Multiple concurrent receivers cannot be modeled

### 3.2 No Message Payload in IPC (MEDIUM — M-02)

IPC operations (`IPC/Operations.lean`) manage thread queues on endpoints but
**transfer no data**. `endpointSend` enqueues a sender thread ID;
`endpointReceive` dequeues it. There is no message register, capability
transfer, or data buffer involved.

This means the model cannot verify:
- Message integrity across IPC
- Capability transfer during IPC (a core seL4 feature)
- Register-based message passing semantics

### 3.3 Notification Badge Merging Implemented (POSITIVE)

`notificationSignal` (`IPC/Operations.lean:87-118`) correctly implements
bitwise-OR badge merging:

```lean
let mergedBadge := match ntfn.pendingBadge with
  | some existing => Badge.ofNat (existing.toNat ||| badge.toNat)
  | none => badge
```

This matches seL4 semantics. The notification model also correctly:
- Wakes one waiter when threads are waiting
- Merges badges when no threads are waiting
- Transitions state appropriately (idle/waiting/active)

### 3.4 Duplicate-Wait Prevention (POSITIVE)

`notificationWait` (`IPC/Operations.lean:125-157`) checks for duplicate
waiters (F-12):

```lean
if waiter ∈ ntfn.waitingThreads then .error .alreadyWaiting
```

With a corresponding proof (`notificationWait_error_alreadyWaiting`, line 218).

---

## Section 4: Scheduler Subsystem

### 4.1 Scheduler Invariants Are Meaningful (POSITIVE)

The scheduler defines three invariants (`Scheduler/Invariant.lean`):

1. **`queueCurrentConsistent`**: If a current thread is selected, it must be in
   the runnable queue
2. **`runQueueUnique`**: No duplicate thread IDs in the runnable queue
3. **`currentThreadValid`**: The current thread must resolve to a TCB in the
   object store

These are substantive properties, and the preservation proofs in
`Scheduler/Operations.lean` are genuinely compositional — they thread pre-state
assumptions through the operation's case analysis.

### 4.2 Priority Scheduling Bias (MEDIUM — M-03)

`chooseBestRunnable` (`Scheduler/Operations.lean:7-22`) has a subtle bias:

```lean
if bestPrio.toNat < tcb.priority.toNat then some (tid, tcb.priority) else best
```

The strict-less-than comparison (`<`) means ties are broken by **first
occurrence** in the runnable list. This is documented but differs from seL4's
round-robin within same-priority behavior. The `handleYield` operation partially
addresses this by rotating the current thread to the back, but only when yield
is explicitly called.

### 4.3 No Time-Slice or Preemption Model (MEDIUM — M-04)

The TCB structure includes `timeSlice : Nat` but no operation decrements it,
checks it, or triggers preemption. The scheduler is purely cooperative — threads
must explicitly yield. seL4 uses tick-based preemption within scheduling domains.

### 4.4 No Domain Scheduling (MEDIUM — M-05)

seL4's scheduler operates at two levels: domain scheduling (security-critical
temporal partitioning) and priority scheduling (within a domain). The seLe4n
model has no domain scheduling — all threads are in a single flat priority queue.
The `DomainId` field exists in TCB but is never used by any scheduler operation.

---

## Section 5: Lifecycle Subsystem

### 5.1 Retype Operation Well-Structured (POSITIVE)

`lifecycleRetypeObject` (`Lifecycle/Operations.lean:21-38`) has clear
precondition checking:

1. Target object must exist
2. Lifecycle metadata must be consistent with object store
3. Authority capability must exist and carry write rights
4. Authority capability must target the object directly

The decomposition theorem `lifecycleRetypeObject_ok_as_storeObject` (line 120)
correctly extracts all preconditions from a successful execution.

### 5.2 Composed Lifecycle Operation (POSITIVE)

`lifecycleRevokeDeleteRetype` (`Lifecycle/Operations.lean:53-71`) composes
revoke → delete → verify-deleted → retype as a staged pipeline. The
decomposition theorem `lifecycleRevokeDeleteRetype_ok_implies_staged_steps`
(line 270) correctly proves the pipeline structure.

The aliasing guard (`authority ≠ cleanup`, line 58) prevents a subtle bug where
revoking the authority capability would invalidate the retype step.

---

## Section 6: Service Subsystem

### 6.1 BFS Cycle Detection Fuel Bound (MEDIUM — M-06)

`serviceHasPathTo` (`Service/Operations.lean:110-127`) uses bounded BFS with
fuel `st.objectIndex.length + 256`. The bound is heuristic:

- The `+ 256` constant accounts for "service IDs that may not have corresponding
  kernel objects" but is not formally justified
- If more than `objectIndex.length + 256` distinct services exist, the BFS
  returns `false` (conservatively reports no path), which could allow cycle
  insertion

No theorem proves that the fuel bound is adequate for all reachable states.

### 6.2 Restart Partial-Failure Semantics (POSITIVE)

`serviceRestart` (`Service/Operations.lean:76-83`) has clearly documented
partial-failure behavior: if stop succeeds but start fails, the service remains
stopped. The theorem `serviceRestart_ok_implies_staged_steps` (line 245)
correctly decomposes successful restarts.

### 6.3 Service Dependency Model Is Sound (POSITIVE)

`serviceRegisterDependency` (`Service/Operations.lean:142-160`) correctly:
- Rejects self-loops (line 151)
- Detects cycles via BFS (line 155)
- Is idempotent for existing edges (line 153)

---

## Section 7: Information Flow

### 7.1 Two-Level Lattice Is Too Coarse (HIGH — H-04)

The security label model (`InformationFlow/Policy.lean`) defines a product
lattice of only **4 elements**:

```lean
inductive Confidentiality where | low | high
inductive Integrity where | untrusted | trusted
```

This gives exactly 4 labels: (low, untrusted), (low, trusted), (high, untrusted),
(high, trusted). Real seL4 information-flow proofs use per-domain labels with
the policy graph specified externally.

**Impact**: The model can express "high cannot flow to low" but cannot express:
- Multi-domain policies (3+ security domains)
- Intransitive non-interference (e.g., declassifiers)
- Per-endpoint flow policies
- Runtime label changes

### 7.2 Enforcement Is Pre-Gate Only (MEDIUM — M-07)

Information flow enforcement (`InformationFlow/Enforcement.lean`) wraps three
operations with `securityFlowsTo` checks:

1. `endpointSendChecked` — sender→endpoint
2. `cspaceMintChecked` — source CNode→destination CNode
3. `serviceRestartChecked` — orchestrator→service

The enforcement proofs are correct but weak — they only prove:
- If flow is allowed, the checked operation equals the unchecked operation
- If flow is denied, the result is `.error .flowDenied`

**Missing**: No theorem proves that the *unchecked* operations cannot leak
information. The enforcement layer is a **gate**, not a **guarantee**. An
operation that bypasses the `*Checked` wrapper (calling `endpointSend` directly)
receives no flow enforcement.

### 7.3 No Non-Interference Theorem (HIGH — H-05)

The projection machinery (`InformationFlow/Projection.lean`) defines:
- `projectState` — filter state to observer-visible subset
- `lowEquivalent` — two states agree on observable projections

The file proves reflexivity, symmetry, and transitivity of `lowEquivalent`,
confirming it's an equivalence relation. However, **no non-interference theorem
exists** — there is no proof that kernel operations preserve low-equivalence:

```lean
-- This theorem does NOT exist in the codebase:
theorem schedule_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState)
    (hEq : lowEquivalent ctx observer s₁ s₂) :
    lowEquivalent ctx observer (schedule s₁) (schedule s₂)
```

Without this, the information-flow model is **scaffolding** — it defines the
framework for non-interference proofs but does not contain any actual security
theorems.

---

## Section 8: Architecture Layer

### 8.1 Assumptions Are Structural Only (MEDIUM — M-08)

`Architecture/Assumptions.lean` defines 5 architecture-facing assumptions and
maps them to transition surfaces, invariant bundles, and contract obligations.
The theorems prove:

- All assumptions are enumerated (completeness)
- Each assumption has ≥1 contract obligation
- Each assumption maps to ≥1 transition and ≥1 invariant

However, **no assumption is actually used by any proof**. The boundary contracts
(`BootBoundaryContract`, `RuntimeBoundaryContract`, `InterruptBoundaryContract`)
are structures with fields but are never instantiated or consumed. The assumption
machinery is documentation infrastructure, not proof infrastructure.

### 8.2 API.lean Is Just Imports (LOW — L-01)

`Kernel/API.lean` contains only import statements (22 lines). There is no public
API definition, no entry point composition, and no API-level invariant bundle.
The "public kernel interface" mentioned in documentation does not exist as a
unified interface.

---

## Section 9: Foundation Layer

### 9.1 Inhabited Instances Create Magic ID 0 (HIGH — H-06)

All 12 identifier types (`Prelude.lean:4-47`) derive `Inhabited`, making
`default` return `⟨0⟩`. Any code accidentally using `default : ObjId`
silently refers to object 0. ID 0 is not reserved or treated specially anywhere
in the codebase.

**Risk**: An uninitialized variable or default-constructed ID could silently
collide with a real object, causing isolation violations.

### 9.2 Default Memory Returns Zero for All Addresses (LOW — L-02)

`Machine.lean:29-30` initializes memory as `fun _ => 0`. The model cannot
distinguish between "address was written with value 0" and "address was never
written." There is no page-fault or unmapped-address mechanism.

### 9.3 Metadata Sync Hazard in storeObject (MEDIUM — M-09)

`State.lean:91-108` synchronizes `lifecycle.capabilityRefs` metadata when
storing objects. When a non-CNode object replaces a CNode at the same ID, all
capability reference metadata for that ID is silently cleared (`| _ => none`).
This is correct behavior for type changes but creates a fragile sync point —
a single bug in this logic breaks 40+ theorems that assume metadata consistency.

### 9.4 Missing Monad Helpers (LOW — L-03)

`KernelM` (`Prelude.lean:50-74`) defines only `pure` and `bind`. Standard
helpers (`get`, `set`, `modify`, `liftExcept`) are absent, forcing every
operation to write boilerplate `fun st => ...` patterns with manual state
threading. This increases the surface area for state-threading bugs.

### 9.5 ID Conversion Without Validation (LOW — L-04)

`ThreadId.toObjId` (`Prelude.lean:39`) converts by copying the numeric value
without any validation. No invariant ensures that a thread ID used as an object
ID actually points to a TCB. The check is deferred to runtime lookups.

### 9.6 objectIndex Never Pruned (LOW — L-05)

`objectIndex` (`State.lean:107-108`) grows monotonically — IDs are appended on
first store but never removed. No object deletion is modeled, so the list
grows unbounded.

### 9.7 No Initialization Proof (LOW — L-06)

No theorem proves that the default `SystemState` satisfies
`lifecycleMetadataConsistent`. This should be trivially true (everything is
empty) but is not stated or proven.

---

## Section 10: Cross-Cutting Observations

### 10.1 Operations/Invariant Split Is Consistently Maintained (POSITIVE)

Every kernel subsystem maintains the `Operations.lean` / `Invariant.lean` split.
Operations define transitions; invariants define preservation theorems. This
architectural discipline makes the codebase navigable and maintainable.

### 10.2 Deterministic Error Ordering (POSITIVE)

Every operation documents its error-checking order and commits to deterministic
failure modes. The `KernelError` enumeration covers 17 distinct error cases,
and operations use them consistently. Error-case theorems (e.g.,
`serviceStart_error_policyDenied`) explicitly verify failure conditions.

### 10.3 Total Theorem Count

Approximate theorem counts by subsystem:

| Subsystem | File(s) | Approx. Theorems |
|-----------|---------|-----------------|
| Model/State | State.lean | ~79 |
| Model/Object | Object.lean | ~40 |
| Scheduler | Operations + Invariant | ~25 |
| Capability | Operations + Invariant | ~45 |
| IPC | Operations + Invariant | ~30 |
| Lifecycle | Operations + Invariant | ~20 |
| Service | Operations + Invariant | ~20 |
| InformationFlow | Policy + Projection + Enforcement + Invariant | ~20 |
| Architecture | Assumptions + VSpace + Invariant | ~15 |
| **Total** | | **~295** |

All 295 theorems compile without `sorry` or axioms.

---

## Section 11: Prioritized Recommendations

### Tier 1: Critical Fixes (Addresses C-01 through C-04)

1. **Implement CDT model**: Add `CapDerivation` structure tracking parent-child
   edges. Prove acyclicity. This is prerequisite for items 2 and 3.

2. **Add `cspaceCopy` and `cspaceMove`**: Copy should not require Grant rights
   and should not create CDT edges. Move should atomically clear the source.

3. **Extend revocation to cross-CNode**: `cspaceRevoke` should traverse the CDT
   to find and remove all derived capabilities across all CNodes.

4. **Replace tautological proofs**: Either strengthen invariant definitions to
   encode non-trivial properties, or explicitly document that certain components
   are meta-properties guaranteed by construction.

### Tier 2: High-Priority Improvements (Addresses H-01 through H-06)

5. **Make preservation proofs compositional**: Each preservation proof should
   derive post-state invariant components from pre-state components via the
   operation's specific state transformation.

6. **Prove badge-override safety for IPC**: Add theorem that badge values
   propagated through mint are consistent with notification routing semantics.

7. **Add non-interference theorem**: Prove that at least one core operation
   (e.g., `schedule`) preserves `lowEquivalent`. Even a single concrete theorem
   would transform the information-flow layer from scaffolding to evidence.

8. **Guard slot insertion**: `cspaceInsertSlot` should check that the
   destination slot is empty, or document why overwrites are safe.

9. **Reserve or validate ID 0**: Either explicitly reserve ID 0 as a sentinel,
   or remove `Inhabited` instances from identifier types.

### Tier 3: Medium-Priority Enhancements (Addresses M-01 through M-09)

10. **Add message payload to IPC**: Extend endpoint operations with message
    registers and capability transfer.

11. **Add domain scheduling**: Use `DomainId` in TCB to implement two-level
    scheduling with temporal partitioning.

12. **Prove BFS fuel adequacy**: Add theorem that `serviceBfsFuel` is sufficient
    for all reachable service graphs, or switch to a structurally-decreasing
    traversal.

13. **Extend security label lattice**: Parameterize labels by a domain type
    rather than hardcoding `{low, high} × {untrusted, trusted}`.

14. **Add preemption and time-slice decrement**: Model tick-based preemption
    using `TCB.timeSlice` and `MachineState.timer`.

---

## Section 12: Testing Infrastructure

### 12.1 Tiered Architecture Is Well-Designed (POSITIVE)

The project uses a 5-tier validation pipeline:

| Tier | Script | Purpose |
|------|--------|---------|
| 0 | `test_fast.sh` | Hygiene: scans for `sorry`/`axiom`/`TODO`, validates type wrappers, shell lint |
| 1 | `test_fast.sh` | Build: `lake build` compilation |
| 2 | `test_smoke.sh` | Trace + negative state: fixture comparison, explicit error-path testing |
| 3 | `test_full.sh` | Invariant surface: 483 anchor points for theorem existence and doc sync |
| 4 | `test_nightly.sh` | Deterministic replay with seeded random traces |

### 12.2 Negative Testing Done Right (POSITIVE)

`NegativeStateSuite.lean` (372 lines) explicitly tests error paths with an
`expectError` helper that validates both success and failure scenarios. The suite
covers: invalid capability lookups, endpoint state mismatches, service policy
denials, VSpace mapping conflicts, and scheduler invariant violations.

### 12.3 Shallow Input Space Exploration (MEDIUM — M-10)

All tests use hardcoded fixture values:

- Object IDs: always 1, 10, 11, 12, 20, 30, 31
- Priorities: only 10 vs 42 tested
- CNode: single guard/radix pair (guard=1, radix=2)
- VSpace: single mapping (asid=2, vaddr=4096, paddr=12288)
- Scheduler: always 2-thread queues
- Endpoints: always 1 endpoint, 2 threads, 3 operations

No property-based testing, fuzzing, or parametric variation exists. A bug
triggered only by specific guard/radix combinations, large queue sizes, or
unusual priority values would not be detected.

### 12.4 Missing Runtime Invariant Checks (MEDIUM — M-11)

`InvariantChecks.lean` validates scheduler and IPC queue invariants but does
**not** check:

- CSpace coherency (capabilities must reference valid objects)
- Capability rights attenuation (derived rights must subset source rights)
- Lifecycle metadata consistency (`objectTypes[oid]` must match actual object)
- Service graph acyclicity at runtime
- VSpace ASID uniqueness

### 12.5 Fixture Matching Is Fragile (LOW — L-07)

The main trace fixture (`tests/fixtures/main_trace_smoke.expected`) uses
`grep -Fq` substring matching against `reprStr` output. If Lean's `repr` format
changes across toolchain versions, tests silently fail without detecting actual
regressions. No version-locking of repr output format exists.

### 12.6 Anchor Presence ≠ Correctness (LOW — L-08)

Tier 3 (`test_tier3_invariant_surface.sh`) validates that 483 theorem names and
documentation anchors exist in the codebase. However, anchor presence does not
verify proof *correctness* — a theorem could be trivially true or prove a weaker
property than the anchor implies. This is a known limitation of anchor-based
testing.

---

## Conclusion

seLe4n demonstrates genuine engineering discipline: clean module structure,
deterministic transitions, comprehensive error handling, and 295 machine-checked
theorems with zero unsound constructs. The codebase is well-positioned as an
executable reference model (milestone M0-M1 level).

However, for **security-critical formalization** claims (M2+), the project must
address:

1. The absence of a Capability Derivation Tree, which makes revocation
   correctness unprovable across CNode boundaries
2. Tautological invariant proofs that provide no assurance beyond what the type
   system guarantees
3. The lack of any actual non-interference theorem in the information-flow layer
4. Missing core capability operations (copy, move) that prevent modeling
   fundamental seL4 workflows

The gap between the project's documentation claims ("high assurance") and the
actual proof strength ("structurally valid but semantically incomplete") is the
most important finding of this audit. Closing this gap requires either
strengthening the proofs or recalibrating the documentation to accurately reflect
the current assurance level.
