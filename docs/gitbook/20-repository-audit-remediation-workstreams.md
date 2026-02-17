# Repository Audit Remediation Workstreams

This chapter is the execution companion to the full repository audit in
[`docs/REPOSITORY_AUDIT.md`](../REPOSITORY_AUDIT.md).

For the implementation plan that defines each workstream in detail, use:
[`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](../AUDIT_REMEDIATION_WORKSTREAMS.md).

For current-slice target outcomes and closure gates, use:
[M7 Current Slice Outcomes and Workstreams](21-m7-current-slice-outcomes-and-workstreams.md).

## 1. Why this chapter exists

The audit shows a strong formal core with practical delivery gaps around CI enforcement,
module symmetry, type-safety boundaries, test scale, and documentation discoverability.

This chapter converts those findings into an execution portfolio contributors can use directly.

## 2. Program-level outcomes

The remediation program targets eight concrete repository outcomes:

1. enforceable CI gates and deterministic validation,
2. cleaner architecture boundaries and public API stability,
3. type-safe identity domains to reduce alias confusion,
4. broader test evidence including scale and adversarial paths,
5. explicit production-vs-test hardware contract boundaries,
6. cohesive contributor-facing documentation and navigation,
7. proof-surface maintainability and theorem explainability,
8. platform/security baseline readiness for hardware-facing expansion.

## 3. Workstream portfolio (WS-A1..WS-A8)

1. **WS-A1 — CI hardening and quality gate promotion** ✅ **completed**
   - promote Tier 3 obligations to strict merge gates,
   - improve workflow determinism and cache efficiency,
   - document branch protection and required evidence flows.

2. **WS-A2 — Architecture modularity and API surface** ✅ **completed**
   - split IPC operations (`SeLe4n/Kernel/IPC/Operations.lean`) from invariant/proof surfaces (`SeLe4n/Kernel/IPC/Invariant.lean`),
   - preserve `SeLe4n/Kernel/API.lean` as the stable public facade with explicit IPC exports,
   - update architecture maps to document the now-symmetric module layout and dependency boundaries.

3. **WS-A3 — Type-safety uplift for IDs/pointers** ✅ **completed**
   - migrated critical aliases to explicit wrappers,
   - enforce explicit object-store conversion boundaries via `ThreadId.toObjId`,
   - preserved theorem ergonomics with migration helpers and explicit conversion points.

4. **WS-A4 — Test architecture expansion** ✅ **completed**
   - add high-scale and edge-heavy scenarios,
   - improve fixture provenance and scenario traceability,
   - incorporate stochastic/property-style checks where practical.
   - status in active slice: **completed** (see chapter 21 closure evidence).

5. **WS-A5 — Hardware-boundary safety + test-only contracts** ✅ **completed**
   - isolate permissive contracts to test-only modules,
   - prevent accidental production-surface usage,
   - document trusted-contract policy and review expectations.
   - status in active slice: **completed** (see chapter 21 closure evidence).

6. **WS-A6 — Documentation IA and contributor UX** ✅ **completed**
   - standardized root-level contributor guidance with a 5-minute path in `CONTRIBUTING.md` and synchronized ordering in `README.md`,
   - aligned handbook structure with contributor entry flow via quickstart sequencing in `docs/gitbook/README.md`,
   - synchronized active/next slice status markers across root docs and GitBook workstream chapters.

7. **WS-A7 — Proof documentation and maintainability automation** ✅ **completed**
   - added theorem-purpose docstrings for endpoint scheduler-bundle theorem entrypoints,
   - consolidated repeated scheduler-bundle proof blocks through `endpoint_store_preserves_schedulerInvariantBundle`,
   - preserved readability by keeping transition-specific obligations explicit in wrapper theorems.
   - status in active slice: **completed** (see chapter 21 closure evidence).

8. **WS-A8 — Platform/security maturity for post-remediation path**
   - add architecture-relevant CI expansion,
   - establish baseline automated scanning,
   - define staged information-flow roadmap milestones.

## 4. Sequencing model

- **Phase 1: hardening foundations**
  - WS-A1, WS-A2, WS-A5 plus low-risk WS-A6 updates.
- **Phase 2: quality depth expansion**
  - WS-A3 and WS-A4 after boundary stability improves.
- **Phase 3: scalability and trajectory maturity**
  - WS-A7 and WS-A8 once migration churn is controlled.

This sequencing minimizes proof churn and avoids rework while safety rails are established.

## 5. Workstream-ready PR checklist

Every remediation PR should include:

1. audit criticism/recommendation IDs closed,
2. workstream ID(s) and target outcome ID(s),
3. exact command evidence with reproducible outputs,
4. synchronized documentation updates,
5. explicit “what this unlocks next” statement.

## 6. Completion contract

A workstream is considered closed only when all are true:

1. mapped audit criticism/recommendation IDs are explicitly closed,
2. tests/theorem anchors/docs are updated together,
3. PR evidence is reproducible via documented commands,
4. no regression in proof completeness expectations,
5. active-slice and next-slice documentation are synchronized across root docs and GitBook.

## 7. Handoff to next slice

When WS-A1..WS-A8 close, maintainers should publish a short remediation closeout packet with:

- completed/deferred workstream table,
- residual risks accepted for next slice,
- next-slice kickoff dependencies and owners,
- links to updated roadmap and hardware-path chapters.

That packet is the gate artifact for starting the post-M7 hardware-facing slice.
