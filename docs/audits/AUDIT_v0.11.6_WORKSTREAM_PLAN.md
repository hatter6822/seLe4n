# AUDIT v0.11.6 — Workstream Planning Backbone (WS-E)

This document is the canonical execution plan for the **WS-E portfolio**,
closing findings from [`AUDIT_CODEBASE_v0.11.6.md`](./AUDIT_CODEBASE_v0.11.6.md)
and carrying forward remaining items from the WS-D portfolio (WS-D5, WS-D6).

Supersedes: WS-D portfolio as active planning backbone (WS-D1–D4 completed;
WS-D5/D6 findings absorbed into WS-E).

---

## 1. Planning objective

Close all actionable findings from the v0.11.6 codebase audit (32 findings:
4 CRITICAL, 9 HIGH, 11 MEDIUM, 8 LOW) plus carry-forward items from WS-D5
(F-09, F-10) and WS-D6 (F-13, F-14, F-15, F-17).

Strategy: prioritize by blast radius and proof-assurance impact, grouping
related findings into coherent implementation slices.

---

## 2. Planning principles

1. **Truth over optimism**: documentation must describe what the code actually
   does, not what we wish it did.
2. **Canonical-first docs**: root `docs/` files own policy/spec text; GitBook
   mirrors summarize and link.
3. **Evidence-gated completion**: no workstream closes without passing its
   designated validation gate.
4. **Invariant-valid test entry**: every test must exercise a meaningful
   property, not a tautology.
5. **No claim without theorem**: documentation must not imply proof strength
   beyond what theorems actually establish.
6. **Continuity**: preserve all closed WS-D1–D4 contracts.

---

## 3. Finding-to-workstream matrix

### 3.1 Findings from AUDIT_CODEBASE_v0.11.6.md

| ID | Severity | Description | Workstream |
|----|----------|-------------|------------|
| C-01 | CRITICAL | Tautological proofs (cspaceSlotUnique, cspaceLookupSound) | WS-E2 |
| C-02 | CRITICAL | Missing capability operations (copy, move, mutate) | WS-E4 |
| C-03 | CRITICAL | No Capability Derivation Tree (CDT) | WS-E4 |
| C-04 | CRITICAL | Local-only revocation (cannot cross CNode boundaries) | WS-E4 |
| H-01 | HIGH | Non-compositional preservation proofs | WS-E2 |
| H-02 | HIGH | Silent slot overwrites in cspaceInsertSlot | WS-E4 |
| H-03 | HIGH | Badge override safety gap | WS-E2 |
| H-04 | HIGH | Two-level security lattice too coarse | WS-E5 |
| H-05 | HIGH | No non-interference theorem | WS-E5 |
| H-06 | HIGH | Inhabited instances create magic ID 0 | WS-E3 |
| H-07 | HIGH | VSpace missing from composed invariant bundle | WS-E3 |
| H-08 | HIGH | BFS cycle detection unsound on fuel exhaustion | WS-E3 |
| H-09 | HIGH | Endpoint operations never transition thread IPC state | WS-E3 |
| M-01 | MEDIUM | Endpoint model diverges from seL4 (single queue) | WS-E4 |
| M-02 | MEDIUM | No message payload in IPC | WS-E4 |
| M-03 | MEDIUM | Priority scheduling bias (tie-breaking) | WS-E6 |
| M-04 | MEDIUM | No time-slice or preemption model | WS-E6 |
| M-05 | MEDIUM | No domain scheduling | WS-E6 |
| M-07 | MEDIUM | Enforcement is pre-gate only | WS-E5 |
| M-08 | MEDIUM | Assumptions are structural only | WS-E6 |
| M-09 | MEDIUM | Metadata sync hazard in storeObject | WS-E3 |
| M-10 | MEDIUM | Shallow input space exploration in tests | WS-E1 |
| M-11 | MEDIUM | Missing runtime invariant checks | WS-E1 |
| M-12 | MEDIUM | No reply operation for bidirectional IPC | WS-E4 |
| M-13 | MEDIUM | Integrity flow semantics contradict documentation | **RESOLVED** |
| L-01 | LOW | API.lean is just imports | WS-E6 |
| L-02 | LOW | Default memory returns zero for all addresses | WS-E6 |
| L-03 | LOW | Missing monad helpers | WS-E6 |
| L-04 | LOW | ID conversion without validation | WS-E6 |
| L-05 | LOW | objectIndex never pruned | WS-E6 |
| L-06 | LOW | No initialization proof | WS-E3 |
| L-07 | LOW | Fixture matching is fragile | WS-E1 |
| L-08 | LOW | Anchor presence ≠ correctness | WS-E1 |

### 3.2 Carry-forward items from WS-D5/D6

| ID | Severity | Description | Workstream | Status |
|----|----------|-------------|------------|--------|
| F-09 | MEDIUM | Add intermediate RuntimeContractFixtures | WS-E1 | **RESOLVED** |
| F-10 | MEDIUM | Remove 512-ID bound from InvariantChecks | WS-E1 | **RESOLVED** |
| F-13 | LOW | Version badge discrepancy | — | **RESOLVED** (v0.11.6 correct) |
| F-14 | LOW | SHA-pin GitHub Actions | WS-E1 | Pending |
| F-15 | LOW | Add permissions block to CI workflows | WS-E1 | **RESOLVED** |
| F-17 | LOW | Document O(n) design decision | WS-E6 | Pending |

---

## 4. Workstream definitions

### WS-E1 — Test infrastructure and CI hardening (Medium)

**Findings:** M-10, M-11, L-07, L-08, F-14; F-09 (resolved), F-10 (resolved),
F-15 (resolved)

**Scope:**

1. ~~F-09~~ Add intermediate RuntimeContractFixtures — **DONE** (timer-only
   and read-only memory fixtures added).
2. ~~F-10~~ Remove 512-ID bound from InvariantChecks — **DONE** (uses
   `st.objectIndex` now).
3. ~~F-15~~ Add explicit permissions blocks to CI workflows — **DONE**.
4. **F-14** SHA-pin all GitHub Actions across 4 workflow files.
5. **M-10** Add parameterized test topologies (vary thread count, priority
   levels, CNode radix, ASID count) to supplement hardcoded fixtures.
6. **M-11** Add runtime invariant checks for CSpace coherency, capability
   rights attenuation, lifecycle metadata consistency, service graph
   acyclicity, and VSpace ASID uniqueness.
7. **L-07** Add structured trace format alongside current substring matching
   (backward-compatible) to reduce fixture brittleness.
8. **L-08** Add spot-check theorem-body validation (verify key theorems do
   not contain `sorry` or trivial `rfl`-only proofs).

**Validation gate:** `test_smoke.sh` + `test_full.sh` pass; new test
topologies exercise at least 3 distinct configurations per subsystem.

**Dependencies:** None (can start immediately).

---

### WS-E2 — Proof quality and invariant strengthening (High)

**Findings:** C-01, H-01, H-03

**Scope:**

1. **C-01** Reformulate `cspaceSlotUnique` and `cspaceLookupSound` to prove
   non-trivial properties. Either strengthen the invariant definitions to
   encode lookup correctness relative to a specification, or explicitly
   document them as meta-properties (and remove from the "high assurance"
   categorization in documentation).
2. **H-01** Refactor capability preservation proofs to be compositional —
   each proof should derive post-state invariant components from pre-state
   components through the operation's specific state transformation, not
   re-prove from scratch.
3. **H-03** Add theorem proving that badge values propagated through
   `cspaceMint` are consistent with notification routing semantics.

**Validation gate:** `test_full.sh` passes; preservation proofs use `hInv`
destructured components in post-state derivation (not just `_`-prefixed
discards).

**Dependencies:** None.

---

### WS-E3 — Kernel semantic hardening (High)

**Findings:** H-06, H-07, H-08, H-09, M-09, L-06

**Scope:**

1. **H-09** Implement thread blocking in endpoint operations:
   - `endpointSend` must call `storeTcbIpcState sender (.blockedOnSend eid)`
     and `removeRunnable` when sender blocks.
   - `endpointAwaitReceive` must set `.blockedOnReceive`.
   - `endpointReceive` must unblock dequeued sender (set `.ready`,
     `ensureRunnable`).
   This makes the IPC-scheduler contract predicates (`blockedOnSendNotRunnable`,
   `blockedOnReceiveNotRunnable`) non-vacuous.
2. **H-07** Add `vspaceInvariantBundle` to `proofLayerInvariantBundle`
   composition. Add preservation theorems for all adapter operations.
3. **H-08** Change `serviceHasPathTo` to return conservative `true` on fuel
   exhaustion (safer for cycle detection). Add adequacy theorem.
4. **H-06** Either reserve ID 0 as sentinel or remove `Inhabited` instances
   from identifier types. Document the decision.
5. **M-09** Add explicit theorem proving `storeObject` metadata sync is
   correct for type-changing stores.
6. **L-06** Add theorem proving default `SystemState` satisfies
   `lifecycleMetadataConsistent`.

**Validation gate:** `test_full.sh` passes; IPC-scheduler contract predicates
are non-vacuous; VSpace in composed bundle.

**Dependencies:** WS-E2 (proof pattern improvements inform proof structure here).

---

### WS-E4 — Capability and IPC model completion (Critical)

**Findings:** C-02, C-03, C-04, H-02, M-01, M-02, M-12

**Scope:**

1. **C-02** Implement missing capability operations:
   - `cspaceCopy` — duplicate without rights change, no CDT link.
   - `cspaceMove` — transfer with atomic source clearing.
   - `cspaceMutate` — in-place rights modification.
2. **C-03** Implement Capability Derivation Tree (CDT) model:
   - `CapDerivation` structure tracking parent-child edges.
   - Acyclicity invariant.
   - Integration with `cspaceMint` (creates derivation edge).
3. **C-04** Extend `cspaceRevoke` to cross-CNode traversal via CDT.
4. **H-02** Guard `cspaceInsertSlot` against occupied-slot overwrites.
5. **M-01** Restructure endpoint model to support separate send/receive
   queues and multiple concurrent receivers.
6. **M-02** Add message payload (message registers + capability transfer)
   to endpoint operations.
7. **M-12** Add reply operation for bidirectional IPC (reply capabilities,
   `seL4_ReplyRecv`-style call).

**Validation gate:** `test_full.sh` passes; new operations have preservation
theorems; CDT acyclicity proven; cross-CNode revocation demonstrated.

**Dependencies:** WS-E2 (proof patterns), WS-E3 (thread blocking).

---

### WS-E5 — Information-flow maturity (High)

**Findings:** H-04, H-05, M-07

**Scope:**

1. **H-04** Parameterize security labels by a domain type rather than
   hardcoding `{low, high} × {untrusted, trusted}`. Support 3+ security
   domains, per-endpoint flow policies.
2. **H-05** Prove at least one composed bundle-level non-interference
   theorem (connecting IF-M3 seeds into IF-M4 composition). This advances
   the IF roadmap from scaffolding to evidence.
3. **M-07** Prove that unchecked operations cannot leak information when
   the enforcement gate is bypassed — or explicitly document which
   operations require the `*Checked` wrapper.

**Validation gate:** `test_full.sh` passes; at least one composed
non-interference theorem exists; label lattice supports ≥3 domains.

**Dependencies:** WS-E3 (endpoint blocking makes IF proofs meaningful),
WS-E4 (CDT integration for capability flow proofs).

---

### WS-E6 — Model completeness and documentation (Low)

**Findings:** M-03, M-04, M-05, M-08, L-01, L-02, L-03, L-04, L-05, F-17

**Scope:**

1. **M-03** Document priority tie-breaking semantics and difference from
   seL4 round-robin. Optionally implement round-robin within same-priority.
2. **M-04** Model time-slice decrement and tick-based preemption using
   `TCB.timeSlice` and `MachineState.timer`.
3. **M-05** Implement domain scheduling using `DomainId` in TCB for
   two-level temporal partitioning.
4. **M-08** Connect architecture assumptions to actual proofs (consume
   boundary contracts in adapter preservation theorems).
5. **F-17** Document O(n) data structure design decision with rationale,
   scope note, and future migration path.
6. **L-01** Define unified public API in `API.lean` with entry-point
   composition and API-level invariant bundle.
7. **L-02** Document default-memory-returns-zero semantics and absence
   of page-fault model.
8. **L-03** Add standard monad helpers (`get`, `set`, `modify`,
   `liftExcept`) to `KernelM`.
9. **L-04** Add validation to `ThreadId.toObjId` or document the deferred
   check assumption.
10. **L-05** Document monotonic `objectIndex` as intentional design.

**Validation gate:** `test_full.sh` passes; documentation synchronized.

**Dependencies:** WS-E4 (capability model changes may affect API definition).

---

## 5. Execution phases

- **Phase P0:** Baseline — close quick fixes, publish WS-E planning backbone,
  update documentation to reflect v0.11.6 audit (**current phase**).
- **Phase P1:** WS-E1 (test/CI hardening) + WS-E2 (proof quality) — parallel.
- **Phase P2:** WS-E3 (kernel hardening) — depends on E2 patterns.
- **Phase P3:** WS-E4 (capability/IPC completion) — depends on E2 + E3.
- **Phase P4:** WS-E5 (information-flow maturity) — depends on E3 + E4.
- **Phase P5:** WS-E6 (model completeness/docs) — parallel with E4/E5.

---

## 6. Status dashboard

| Workstream | Status | Priority | Key findings | Phase |
|------------|--------|----------|--------------|-------|
| WS-E1 | **In progress** | Medium | M-10, M-11, F-14, L-07, L-08 | P1 |
| WS-E2 | Planned | High | C-01, H-01, H-03 | P1 |
| WS-E3 | Planned | High | H-06, H-07, H-08, H-09, M-09, L-06 | P2 |
| WS-E4 | Planned | Critical | C-02, C-03, C-04, H-02, M-01, M-02, M-12 | P3 |
| WS-E5 | Planned | High | H-04, H-05, M-07 | P4 |
| WS-E6 | Planned | Low | M-03, M-04, M-05, M-08, F-17, L-01–L-05 | P5 |

---

## 7. Resolved items (quick fixes applied in P0)

| Finding | Resolution | PR/Commit |
|---------|-----------|-----------|
| M-13 | Clarified `securityFlowsTo` comment to document non-standard lattice semantics | P0 baseline |
| F-09 | Added `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` fixtures | P0 baseline |
| F-10 | Replaced hardcoded 512-ID bound with `st.objectIndex` discovery | P0 baseline |
| F-13 | Version badge verified correct (v0.11.7) | Already resolved |
| F-15 | Added explicit `permissions: contents: read` to `lean_action_ci.yml` and `nightly_determinism.yml` | P0 baseline |
