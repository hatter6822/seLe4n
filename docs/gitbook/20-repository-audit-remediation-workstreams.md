# Repository Audit Remediation Workstreams

This chapter is the execution companion to the full repository audit in
[`docs/REPOSITORY_AUDIT.md`](../REPOSITORY_AUDIT.md).

For the full implementation plan (workstream definitions, sequencing, and traceability), use:
[`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](../AUDIT_REMEDIATION_WORKSTREAMS.md).

## 1. Why this chapter exists

The audit identified a healthy codebase with targeted gaps across CI enforcement, architecture
symmetry, type safety, test scale, and contributor discoverability. This chapter turns those
findings into the active M7 delivery program.

## 2. Workstream portfolio (WS-A1..WS-A8)

1. **WS-A1 — CI hardening and quality gate promotion**
   - promote Tier 3 to required CI,
   - add caching, nightly determinism, and documented branch protection.

2. **WS-A2 — Architecture modularity and API surface**
   - split IPC operations/invariants,
   - define a stable API facade boundary.

3. **WS-A3 — Type-safety uplift for IDs/pointers**
   - replace critical `Nat` aliases with newtype wrappers.

4. **WS-A4 — Test architecture expansion**
   - add scale scenarios, fixture traceability, and stochastic/property-style checks.

5. **WS-A5 — Hardware-boundary safety + test-only contracts**
   - isolate permissive runtime contracts into testing-only modules.

6. **WS-A6 — Documentation IA and contributor UX**
   - add root CONTRIBUTING/CHANGELOG,
   - normalize checklist templates,
   - add architecture diagrams and rebalance thin chapters.

7. **WS-A7 — Proof documentation and maintainability automation**
   - theorem docstrings,
   - reduced proof duplication,
   - reusable preservation helpers.

8. **WS-A8 — Platform/security maturity for the post-remediation path**
   - cross-platform CI,
   - baseline security scanning,
   - staged information-flow roadmap.

## 3. Sequencing

- **Phase 1:** WS-A1, WS-A2, WS-A5, plus low-risk WS-A6 doc fixes.
- **Phase 2:** WS-A3 and WS-A4 once IPC split is stable.
- **Phase 3:** WS-A7 and WS-A8 for deeper scalability and security maturity.

## 4. Completion contract

A workstream is considered closed only when all are true:

1. mapped audit criticism/recommendation IDs are explicitly closed,
2. tests/theorem anchors/docs are updated together,
3. PR evidence is reproducible via documented commands,
4. no regression in proof completeness expectations.
