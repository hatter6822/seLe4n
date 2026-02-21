# TPI-D07 Execution Strategy — Service Dependency Acyclicity Invariant

## 1) Purpose and scope

This document provides an implementation-grade strategy to close tracked issue **TPI-D07** from [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md):

- replace the deferred `sorry` in
  `serviceRegisterDependency_preserves_acyclicity`,
- keep runtime behavior unchanged (same deterministic check ordering and error semantics),
- land closure evidence across proof surface, tests, and documentation.

This strategy is based on direct code inspection, not documentation-only assumptions.

---

## 2) Deep audit snapshot (code-first)

### 2.1 Repository and development-state baseline

- The current root export and executable entrypoints show a Lean-first kernel model with runtime harnesses and theorem surfaces split by subsystem (`Architecture`, `Capability`, `IPC`, `Scheduler`, `Service`, `InformationFlow`).
- The testing stack is tiered (`tier0` hygiene through nightly candidates) and includes invariant-anchor checks, runtime negative suites, and trace fixtures.
- The active portfolio in docs is WS-D, with WS-D4 marked complete but with TPI-D07 explicitly carried as in-progress proof debt.

### 2.2 TPI-D07 implementation reality (what code does today)

1. **Cycle-prevention operational logic is implemented and reachable in production path**:
   - `serviceRegisterDependency` rejects self-loops,
   - is idempotent for existing edges,
   - invokes `serviceHasPathTo st depId svcId (serviceBfsFuel st)` before inserting `svcId → depId`.
2. **Reachability is a bounded BFS**:
   - frontier/visited lists,
   - fuel decremented only when expanding an unvisited node,
   - dependency fan-out from `lookupService`.
3. **Invariant theorem exists but is not complete**:
   - `serviceDependencyAcyclic` is defined via no self-reachability,
   - `serviceRegisterDependency_preserves_acyclicity` contains one deferred `sorry` at the BFS-soundness step.
4. **Executable evidence exists**:
   - negative test suite covers self-loop rejection, missing target rejection, successful A→B insertion, B→A cycle rejection, and idempotent re-registration.

### 2.3 Documentation-to-code consistency checks

- The tracked-proof doc correctly marks TPI-D07 as in progress and identifies BFS soundness as the remaining theorem obligation.
- The workstream plan and proof map chapters also describe TPI-D07 as partially closed.
- Tier-0 hygiene intentionally excludes `sorry` markers tagged with `TPI-D*`, confirming this deferred proof is accepted technical debt but still debt.

Conclusion: the gap is narrow and precise: **not an algorithm absence, but proof infrastructure insufficiency for bounded-BFS soundness relative to graph reachability semantics.**

---

## 3) Root-cause analysis of the proof gap

The current theorem skeleton is already structurally correct up to the difficult branch:

- once registration succeeds, all non-insert branches are discharged,
- idempotent branch reduces to `st' = st`,
- insertion branch needs the argument:
  > if pre-check `serviceHasPathTo st depId svcId fuel = false`, then inserting edge `svcId → depId` cannot create a cycle.

Why this stalls today:

1. `serviceHasPathTo` is executable but lacks accompanying **relational graph semantics** (path predicate) and **soundness/completeness bridge lemmas**.
2. `serviceDependencyAcyclic` is defined in terms of the executable predicate itself, so post-state reasoning requires non-trivial normalization over changed service map + path decomposition.
3. No reusable closure lemmas currently express “any newly created cycle must use the newly inserted edge exactly once”, which is the key decomposition step.

---

## 4) Milestone plan (small, efficient, closure-oriented)

## Milestone M0 — Baseline lock + theorem-surface map

**Goal:** Freeze behavior and establish exact proof target.

### Tasks

1. Record the exact branch shape of `serviceRegisterDependency` in the strategy PR notes.
2. Confirm no semantics change target (proof-only closure unless a boundedness bug is discovered).
3. Add focused theorem TODO map in `Service/Invariant.lean` comments for planned intermediate lemmas.

### Exit criteria

- No behavior changes in operations.
- Target theorem and branch obligations enumerated.

---

## Milestone M1 — Introduce declarative graph-path semantics

**Goal:** Add a proof-friendly path relation independent from BFS implementation details.

### Tasks

1. Define a relation over service graph edges, e.g.:
   - `serviceEdge st a b : Prop` (dependency membership),
   - `serviceReachable st a b : Prop` (reflexive-transitive closure or inductive path).
2. Prove structural lemmas:
   - edge lookup equivalence (`serviceEdge` iff dependency membership in lookup entry),
   - reachability transitivity,
   - decomposition/composition helpers for path concatenation.

### Exit criteria

- `serviceReachable` supports induction and composition proofs without unfolding BFS internals.

---

## Milestone M2 — Prove BFS adequacy against declarative reachability

**Goal:** Replace the deferred BFS soundness assumption with formal lemmas.

### Tasks

1. Add local invariants for BFS state (`frontier`, `visited`, `fuel`) in helper lemmas.
2. Prove at least one direction required for TPI-D07 branch discharge:
   - **Soundness needed here:** if `serviceHasPathTo ... = false` under sufficient fuel assumptions, then no declarative path exists.
3. Establish a sufficient-fuel lemma tied to current bound:
   - reason that `serviceBfsFuel st = st.objectIndex.length + 256` dominates distinct nodes explored for model-valid states, or
   - if this cannot be proven robustly, introduce and prove a stronger preconditioned lemma used by acyclicity theorem and document bound assumptions explicitly.

### Exit criteria

- A theorem is available that can directly replace the `sorry` branch premise in `serviceRegisterDependency_preserves_acyclicity`.

---

## Milestone M3 — Prove edge-insertion acyclicity preservation

**Goal:** Show adding `svcId → depId` preserves acyclicity when `depId` cannot reach `svcId` pre-insert.

### Tasks

1. Prove “new-cycle uses new-edge” lemma for single-edge insertion.
2. Reduce post-insert self-reachability contradiction to pre-state reachability `depId ⟶* svcId`.
3. Combine with M2 BFS lemma and pre-check branch hypothesis to discharge contradiction.

### Exit criteria

- `serviceRegisterDependency_preserves_acyclicity` compiles with **no `sorry`**.

---

## Milestone M4 — Strengthen executable evidence (regression safety)

**Goal:** Keep runtime confidence aligned with proof closure.

### Tasks

1. Extend `tests/NegativeStateSuite.lean` with at least one deeper-chain case (length ≥ 3) where final back-edge is rejected.
2. Add one positive non-cycle insertion check in same chain to avoid over-restrictive logic.
3. Keep deterministic error-contract checks unchanged for existing cases.

### Exit criteria

- Tier-2 negative suite passes with added graph-depth coverage.

---

## Milestone M5 — Closure synchronization and claim hygiene

**Goal:** satisfy tracked-issue closure contract across docs + CI gates.

### Tasks

1. Update tracked issue status:
   - `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`: TPI-D07 `IN PROGRESS → CLOSED`.
2. Update status narratives:
   - `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` (remove “partially closed/sorry deferred” wording).
3. Update proof map / claim index:
   - `docs/CLAIM_EVIDENCE_INDEX.md`,
   - `docs/gitbook/12-proof-and-invariant-map.md` and relevant WS-D chapter.
4. Run required validation path and proof-surface checks.

### Exit criteria

- No residual mention of deferred `sorry` for TPI-D07.
- Tiered checks pass and evidence is attachable to PR.

---

## 5) Recommended theorem inventory (implementation checklist)

The following theorem shapes are suggested for efficient proof decomposition:

1. `serviceEdge_storeServiceState_eq` / `_ne` (edge behavior under single-service update).
2. `serviceReachable_trans` and path append lemma.
3. `serviceHasPathTo_false_implies_not_reachable` (with explicit fuel assumptions).
4. `reachable_after_insert_implies_old_or_uses_new_edge`.
5. `cycle_after_insert_implies_pre_reach_dep_to_svc`.
6. Final closure theorem:
   `serviceRegisterDependency_preserves_acyclicity` (no placeholder).

---

## 6) Risks and decision points

1. **Fuel adequacy proof risk (highest):**
   current bound uses `objectIndex.length + 256`; service IDs need not be in `objectIndex`.
   - Preferred mitigation: prove a model-level boundedness invariant linking active services to object-index discipline.
   - Fallback: strengthen theorem preconditions and document explicitly until a global boundedness invariant lands.
2. **Proof brittleness risk from list-based graph operations:**
   list append/filter can create rewriting-heavy proofs.
   - Mitigation: add small canonical lemmas around membership and lookup preservation before tackling the final theorem.
3. **Documentation drift risk:**
   many docs mirror this status.
   - Mitigation: perform closure docs in same PR as theorem completion.

---

## 7) Validation plan (aligned to development guide)

Minimum closure gate sequence:

1. `./scripts/test_fast.sh`
2. `./scripts/test_smoke.sh`
3. `./scripts/test_tier2_negative.sh`
4. `./scripts/test_tier3_invariant_surface.sh`
5. `./scripts/test_full.sh`

Optional for final confidence:

- `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`

---

## 8) Definition of done for TPI-D07

TPI-D07 is closed when all are true:

1. `serviceRegisterDependency_preserves_acyclicity` contains no `sorry`.
2. BFS-to-reachability adequacy lemmas required by the proof are in production theorem surface.
3. Negative tests include deeper-chain cycle-rejection evidence.
4. Workstream + tracked-issue + claim/proof-map docs are synchronized to `CLOSED`.
5. Tiered checks pass in CI-equivalent local run.

