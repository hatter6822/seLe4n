# Repository Audit Remediation Workstreams

This plan translates the findings in [`docs/REPOSITORY_AUDIT.md`](./REPOSITORY_AUDIT.md)
into execution-ready workstreams for the active M7 slice and post-remediation delivery.

## 1. Program goals

1. Close every criticism and recommendation from the repository audit with explicit ownership,
   dependencies, acceptance criteria, and evidence.
2. Preserve M1–M6 proof discipline while executing remediation before hardware-binding expansion.
3. Keep documentation, CI, and test evidence synchronized as first-class deliverables.

## 2. Workstream map (all audit items covered)

| WS ID | Theme | Priority | Audit items covered |
|---|---|---|---|
| WS-A1 | CI hardening and quality gate promotion | High | Testing #1, CI/CD #1/#3/#4/#5/#6, Recommendation #1/#2 |
| WS-A2 | Architecture modularity and API surface | High | Architecture #1/#3, Recommendation #3 |
| WS-A3 | Type-safety uplift for IDs and pointers | High | Code Quality aliasing criticism, Security #1, Recommendation #4 |
| WS-A4 | Test architecture expansion (scale + stochastic) | Medium | Testing #2–#8, Recommendation #10/#12/#13/#17 |
| WS-A5 | Hardware-boundary safety and test-only contract separation | High | Security #3, Recommendation #5 |
| WS-A6 | Documentation IA refresh and contributor experience | Medium | Documentation #1/#3/#4/#5, Recommendation #7/#8/#11 |
| WS-A7 | Proof documentation and maintainability automation | Medium | Documentation #6, Code Quality duplication criticisms, Recommendation #6/#14/#15 |
| WS-A8 | Platform and security maturity for post-remediation hardware trajectory | Medium/Low | CI/CD #2, Security #2/#4, Recommendation #9/#16 |

## 3. Detailed workstreams

### WS-A1 — CI hardening and quality gate promotion (High)

**Objective**
Promote proof-surface and determinism checks to enforced CI gates while reducing pipeline latency.

**Scope**
- add `test_full.sh` (Tier 3) as required CI status check,
- add optional scheduled/nightly Tier 4 job,
- add cache for `~/.elan` and `.lake`,
- document branch protection and required checks,
- pin/setup installer provenance and add baseline security scans.

**Deliverables**
- expanded `.github/workflows/lean_action_ci.yml`,
- CI policy section in `docs/DEVELOPMENT.md`,
- reproducibility and security-check notes in `docs/TESTING_FRAMEWORK_PLAN.md`.

**Acceptance criteria**
- PRs cannot merge without Tier 0–3 passing,
- CI runtime median drops after cache warmup,
- deterministic replay runs at least nightly,
- branch protection expectations documented and discoverable.

---

### WS-A2 — Architecture modularity and API surface (High)

**Objective**
Restore module symmetry and prepare a stable syscall-facing facade.

**Scope**
- split `SeLe4n/Kernel/IPC/Invariant.lean` into `Operations.lean` + `Invariant.lean`,
- keep theorem names and imports backward-compatible during migration,
- introduce a thin, stable API facade in `SeLe4n/Kernel/API.lean` for external callers.

**Deliverables**
- IPC module split with migration notes,
- dependency update in architecture docs,
- API facade section defining intended public surface.

**Acceptance criteria**
- no semantic drift in Tier 2 traces,
- Tier 3 anchors updated and passing,
- architecture chapter includes updated dependency graph.

---

### WS-A3 — Type-safety uplift for IDs and pointers (High)

**Objective**
Eliminate cross-domain confusion by replacing raw `Nat` aliases with wrappers.

**Scope**
- migrate `ThreadId`, `ObjId`, `CPtr`, and `Slot` to `structure` newtypes,
- derive/implement equality, ordering, and serialization helpers as needed,
- update operation signatures and theorem statements,
- add migration helper constructors for ergonomic proofs/tests.

**Deliverables**
- newtype definitions in foundational modules,
- compile-clean updates across transitions and invariants,
- proof adaptation notes for contributors.

**Acceptance criteria**
- invalid cross-domain argument mixes fail at compile-time,
- no net loss of theorem coverage,
- no new placeholder debt (`sorry`/`admit`).

---

### WS-A4 — Test architecture expansion (Medium)

**Objective**
Scale evidence beyond fixed-path fixtures and improve behavioral confidence depth.

**Scope**
- extend Tier 2 scenarios for deep CSpace radix, large run queues, multi-endpoint IPC,
  service dependency chains, and memory-boundary addresses,
- annotate fixture lines with semantic comments and source scenario IDs,
- prototype Lean-native assertions for state-level checks,
- add property/fuzz-style sequence generation where practical.

**Deliverables**
- expanded `Main.lean` scenario coverage,
- richer fixture and `tests/scenarios/README.md` mapping,
- optional Lean-native test harness module.

**Acceptance criteria**
- fixture scenarios traceably map to targeted risk classes,
- at least one stochastic/property suite runs in CI or nightly,
- failure diagnostics remain concise and actionable.

---

### WS-A5 — Hardware-boundary safety and test-only contract separation (High)

**Objective**
Prevent accidental production use of permissive runtime contracts.

**Scope**
- move `runtimeContractAcceptAll`/`runtimeContractDenyAll` out of `Main.lean`,
- place them in a dedicated testing-only module namespace,
- document trusted vs test-only contract usage rules.

**Deliverables**
- `SeLe4n/Testing/Contracts.lean` (or equivalent) with explicit usage intent,
- import boundaries that keep test utilities out of runtime-facing surfaces,
- docs updates in development/testing guides.

**Acceptance criteria**
- no non-test module imports permissive contracts,
- boundary policy is documented and enforced by review checklist.

---

### WS-A6 — Documentation IA refresh and contributor experience (Medium)

**Objective**
Improve discoverability, consistency, and onboarding speed.

**Scope**
- publish a root `CONTRIBUTING.md` that points to `docs/DEVELOPMENT.md`,
- introduce a root `CHANGELOG.md` with version/milestone history,
- normalize checklist template semantics (`[ ]` by default),
- add architecture dependency diagrams to handbook chapters,
- rebalance thin GitBook chapters with concrete content or merge them.

**Deliverables**
- CONTRIBUTING + CHANGELOG,
- updated docs/checklists/handbook navigation,
- architecture visuals maintained with module changes.

**Acceptance criteria**
- new contributors find contribution policy from repo root,
- version progression is auditable in one file,
- no ambiguous pre-checked checklist templates remain.

---

### WS-A7 — Proof documentation and maintainability automation (Medium)

**Objective**
Increase theorem-level explainability while reducing repetitive proof boilerplate.

**Scope**
- add concise docstrings for theorem significance,
- refactor repeated endpoint transport lemmas into parameterized helpers,
- explore a generic preservation tactic for bundle-preservation patterns.

**Deliverables**
- theorem docstring policy and rollout tracker,
- reduced duplication in IPC and bundle-preservation proofs,
- optional helper tactic/module with examples.

**Acceptance criteria**
- theorem doc coverage reaches agreed threshold (target: 100% for public theorem surfaces),
- duplicated proof patterns reduced measurably,
- no readability regression in final proofs.

---

### WS-A8 — Platform and security maturity for post-remediation trajectory (Medium/Low)

**Objective**
Prepare for hardware realism and stronger security claims beyond capability invariants.

**Scope**
- add ARM64/cross-platform CI path before full Raspberry Pi 5 binding,
- establish baseline SAST/secret scanning even with minimal dependencies,
- define staged information-flow model plan (noninterference trajectory).

**Deliverables**
- cross-platform CI job(s),
- security scanning workflow,
- information-flow proof roadmap document.

**Acceptance criteria**
- architecture-targeted CI evidence exists pre-hardware binding,
- security scans run automatically,
- info-flow milestones are explicit and reviewable.

## 4. Sequencing and dependency plan

### Phase 1 (Immediate hardening)
- WS-A1, WS-A2, WS-A5 start immediately.
- WS-A6 starts in parallel for low-risk documentation fixes (checklists, diagrams, navigation).

### Phase 2 (Core model quality uplift)
- WS-A3 begins after WS-A2 IPC split stabilizes.
- WS-A4 expands fixtures/scenarios as type migration lands.

### Phase 3 (Scalability and long-horizon verification)
- WS-A7 and WS-A8 execute incrementally after Phase 2 baseline closes.

## 5. Traceability matrix: audit criticisms → workstreams

- **Architecture criticisms** → WS-A2, WS-A6.
- **Code quality criticisms** → WS-A3, WS-A7.
- **Testing criticisms** → WS-A1, WS-A4.
- **Documentation criticisms** → WS-A6, WS-A7.
- **CI/CD criticisms** → WS-A1, WS-A8.
- **Security criticisms** → WS-A3, WS-A5, WS-A8.
- **Recommendations #1–#17** → distributed across WS-A1..WS-A8 (see Section 2 mapping).

## 6. Execution governance

Each workstream PR should include:

1. scope statement (what criticism/recommendation IDs are being closed),
2. evidence links (tests, theorem anchors, docs sections),
3. rollback/compatibility note (especially WS-A2 and WS-A3),
4. synchronized documentation updates in the same PR.

This keeps the audit remediation program measurable, reviewable, and aligned with proof integrity.
