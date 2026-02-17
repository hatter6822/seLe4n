# Repository Audit Remediation Workstreams

This plan translates findings in [`docs/audits/REPOSITORY_AUDIT.md`](./REPOSITORY_AUDIT.md)
into execution-ready workstreams for the (now completed) M7 slice and the post-remediation handoff.

## 1. Program goals

1. close every criticism and recommendation from the repository audit with explicit ownership,
   dependencies, acceptance criteria, and evidence,
2. preserve M1–M6 proof discipline while executing remediation before hardware-binding expansion,
3. keep documentation, CI, and test evidence synchronized as first-class deliverables,
4. produce a clean handoff contract for the first post-M7 hardware-facing slice.

## 2. Completed slice outcomes (M7-O1..M7-O8)

| Outcome ID | Target outcome |
|---|---|
| M7-O1 | CI and proof gates are enforced, reproducible, and documented as policy. |
| M7-O2 | Architecture modules are symmetric and API boundaries are explicit. |
| M7-O3 | Core identifier/pointer domains are type-safe by construction. |
| M7-O4 | Test evidence covers scale, edge, and sequence-diversity scenarios. |
| M7-O5 | Test-only permissive contracts are isolated from runtime-facing surfaces. |
| M7-O6 | Documentation IA is consistent and contributor-first from root to GitBook. |
| M7-O7 | Theorem surfaces are documented and repetitive proofs are reduced. |
| M7-O8 | Platform/security baseline maturity is in place for next-slice start. |

## 3. Workstream map (all audit items covered)

| WS ID | Theme | Priority | M7 outcomes advanced | Audit items covered |
|---|---|---|---|---|
| WS-A1 | CI hardening and quality gate promotion | High | M7-O1 | Testing #1, CI/CD #1/#3/#4/#5/#6, Recommendation #1/#2 |
| WS-A2 | Architecture modularity and API surface | High | M7-O2 | Architecture #1/#3, Recommendation #3 |
| WS-A3 | Type-safety uplift for IDs and pointers | High | M7-O3 | Code Quality aliasing criticism, Security #1, Recommendation #4 |
| WS-A4 | Test architecture expansion (scale + stochastic) | Medium | M7-O4 | Testing #2–#8, Recommendation #10/#12/#13/#17 |
| WS-A5 | Hardware-boundary safety and test-only contract separation | High | M7-O5 | Security #3, Recommendation #5 |
| WS-A6 | Documentation IA refresh and contributor experience | Medium | M7-O6 | Documentation #1/#3/#4/#5, Recommendation #7/#8/#11 |
| WS-A7 | Proof documentation and maintainability automation | Medium | M7-O7 | Documentation #6, Code Quality duplication criticisms, Recommendation #6/#14/#15 |
| WS-A8 | Platform and security maturity for post-remediation trajectory | Medium/Low | M7-O8 | CI/CD #2, Security #2/#4, Recommendation #9/#16 |

## 4. Detailed workstreams

### WS-A1 — CI hardening and quality gate promotion (High) ✅ completed

**Objective**
Promote proof-surface and determinism checks to enforced CI gates while reducing pipeline latency.

**Scope**
- keep `test_full.sh` (Tier 3) as required CI status check,
- maintain/expand scheduled Tier 4 or nightly deterministic validation,
- maintain cache strategy for `~/.elan` and `.lake`,
- document branch protection and required checks,
- preserve installer provenance and baseline security scanning posture.

**Acceptance criteria**
- PRs cannot merge without Tier 0–3 passing,
- deterministic replay runs are visible and auditable,
- branch protection expectations are documented and discoverable.

**Closure evidence (implemented)**
- CI includes `Fast`, `Smoke`, and `Full` jobs with Tier 3 in the required path (`.github/workflows/lean_action_ci.yml`),
- scheduled nightly replay workflow exists (`.github/workflows/nightly_determinism.yml`) with artifact retention,
- branch-protection and required-check policy is codified in `docs/CI_POLICY.md`.

---

### WS-A2 — Architecture modularity and API surface (High) ✅ completed

**Objective**
Keep module symmetry and maintain a stable syscall-facing facade.

**Closure evidence (implemented)**
- IPC transition semantics are now isolated in `SeLe4n/Kernel/IPC/Operations.lean`,
- IPC invariant/proof obligations remain in `SeLe4n/Kernel/IPC/Invariant.lean`,
- `SeLe4n/Kernel/API.lean` preserves a stable public import facade while exporting both IPC layers,
- architecture docs now map IPC as `Kernel/IPC/{Operations,Invariant}.lean` with explicit dependency boundaries.

---

### WS-A3 — Type-safety uplift for IDs and pointers (High) ✅ completed

**Objective**
Eliminate cross-domain confusion by replacing raw aliases with wrappers.

**Closure evidence (implemented)**
- migrated `ThreadId`, `ObjId`, `CPtr`, and `Slot` from `abbrev` aliases to dedicated wrapper structures in `SeLe4n/Prelude.lean`,
- added explicit constructor/projection helpers (`ofNat`/`toNat`) and typed bridge instances used by existing theorem and transition surfaces,
- adapted scheduler/IPC invariant typing so runnable-membership obligations are carried by `ThreadId` while object-store keys remain `ObjId`,
- validated all test tiers (`test_fast`, `test_smoke`, `test_full`, `test_nightly`) with no placeholder debt introduced.

---

### WS-A4 — Test architecture expansion (Medium) ✅ completed

**Objective**
Scale evidence beyond fixed-path fixtures and improve behavioral confidence depth.

**Closure evidence (implemented)**
- Tier 2 fixture entries are now scenario/risk tagged (`scenario_id | risk_class | expected_trace_fragment`) with comment support for readable, auditable maintenance,
- Tier 2 fixtures now explicitly cover the audit-recommended scale set (deep CNode radix shape, large runnable queue, multiple IPC endpoints, depth-5 service dependency chain, boundary memory addresses),
- Tier 2 trace parser surfaces scenario+risk metadata in concise failure reports,
- Tier 4 nightly candidates execute seeded `trace_sequence_probe` runs that check IPC endpoint-state consistency under sequence-diverse operation streams.

**Acceptance criteria status**
- fixture scenarios map to targeted risk classes ✅,
- at least one sequence-diversity/stochastic check exists in CI or nightly ✅,
- failure diagnostics remain concise and actionable ✅.

---

### WS-A5 — Hardware-boundary safety and test-only contract separation (High) ✅ completed

**Objective**
Prevent accidental production use of permissive runtime contracts.

**Closure evidence (implemented)**
- permissive runtime fixtures are isolated into `SeLe4n/Testing/RuntimeContractFixtures.lean` under the testing namespace (`SeLe4n.Testing.runtimeContractAcceptAll` / `runtimeContractDenyAll`),
- executable trace driver usage in `Main.lean` now imports those fixtures directly from testing-only modules,
- Tier 0 hygiene adds an explicit import-boundary guard that fails if `SeLe4n/` modules reference testing fixtures,
- trusted-vs-test contract usage policy is documented in `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` with contributor/reviewer checklist language.

**Acceptance criteria status**
- non-test modules do not import permissive contracts ✅,
- boundary policy is documented and visible in contributor workflow ✅.

---

### WS-A6 — Documentation IA refresh and contributor experience (Medium) ✅ completed

**Objective**
Improve discoverability, consistency, and onboarding speed.

**Closure evidence (implemented)**
- root onboarding now includes an explicit 5-minute contributor path in `CONTRIBUTING.md` and synchronized start-here ordering in `README.md`,
- GitBook handbook index now mirrors this path through a dedicated contributor quickstart sequence in `docs/gitbook/README.md`,
- active-slice markers and completion snapshots are synchronized across root docs, remediation plan chapters, and current-slice chapter status.

**Acceptance criteria status**
- contribution policy and required workflow are discoverable from repo root ✅,
- slice progression is auditable through one contributor-first navigation path ✅,
- conflicting active-slice markers were removed/synchronized ✅.

---

### WS-A7 — Proof documentation and maintainability automation (Medium) ✅ completed

**Objective**
Increase theorem-level explainability while reducing repetitive proof boilerplate.

**Scope**
- add concise theorem-purpose docstrings,
- refactor repeated proof patterns into helper lemmas/tactics where helpful,
- maintain readability while reducing maintenance surface.

**Closure evidence (implemented)**
- added theorem-purpose docstrings to scheduler-bundle IPC preservation entrypoints and to the shared proof helper in `SeLe4n/Kernel/IPC/Invariant.lean`,
- reduced repeated proof blocks by introducing `endpoint_store_preserves_schedulerInvariantBundle`, then routing send/await/receive bundle theorems through that helper,
- preserved theorem readability by keeping transition-specific obligations explicit in thin wrapper theorems.

**Acceptance criteria status**
- public theorem surface doc coverage reaches agreed threshold ✅,
- repeated proof patterns are measurably reduced ✅,
- no readability regression in final proofs ✅.

---

### WS-A8 — Platform and security maturity for post-remediation trajectory (Medium/Low) ✅ completed

**Objective**
Prepare for hardware realism and stronger security claims beyond capability invariants.

**Scope**
- add architecture-relevant CI path(s),
- maintain baseline SAST/secret scanning,
- define staged information-flow model milestones.

**Closure evidence (implemented)**
- architecture-targeted CI evidence now runs in `.github/workflows/platform_security_baseline.yml` via `Platform Signal / ARM64 Fast Gate` on `ubuntu-24.04-arm` with `./scripts/test_fast.sh`,
- baseline security scanning is automated in the same workflow through Gitleaks (secret scan), Trivy (HIGH/CRITICAL repository scan), and CodeQL analysis for workflow security posture,
- staged post-M7 information-flow proof milestones are published in `docs/INFORMATION_FLOW_ROADMAP.md` with explicit IF-M1..IF-M5 deliverables and exit evidence.

**Acceptance criteria status**
- architecture-targeted CI evidence exists pre-hardware binding ✅,
- security scans run automatically ✅,
- information-flow milestones are explicit and reviewable ✅.

## 5. Sequencing and dependency plan

### Phase 1 (Immediate hardening)
- WS-A1, WS-A2, WS-A5 start immediately.
- WS-A6 runs in parallel for doc/navigation synchronization.

### Phase 2 (Core model quality uplift)
- WS-A3 begins after WS-A2 boundary stability is verified.
- WS-A4 completed scenario expansion and sequence-diversity checks after type migration stabilization.

### Phase 3 (Scalability and long-horizon verification)
- WS-A7 and WS-A8 execute incrementally after Phase 2 baseline closes.

## 6. Traceability matrix: audit criticisms → workstreams

- **Architecture criticisms** → WS-A2, WS-A6.
- **Code quality criticisms** → WS-A3, WS-A7.
- **Testing criticisms** → WS-A1, WS-A4.
- **Documentation criticisms** → WS-A6, WS-A7.
- **CI/CD criticisms** → WS-A1, WS-A8.
- **Security criticisms** → WS-A3, WS-A5, WS-A8.
- **Recommendations #1–#17** → distributed across WS-A1..WS-A8 (see Section 3 mapping).

## 7. Execution governance and reporting

Each workstream PR should include:

1. scope statement (audit IDs closed),
2. outcome statement (M7-O* advanced),
3. evidence links (tests, theorem anchors, docs sections),
4. rollback/compatibility note for risky refactors,
5. synchronized documentation updates in the same PR.

Each checkpoint report should include:

- completed workstreams,
- blocked in-progress workstreams and unblock plans,
- evidence delta since previous checkpoint,
- confidence assessment for the M7 exit gate.

## 8. M7 exit package and next-slice handoff

M7 closeout gate artifact: `docs/M7_CLOSEOUT_PACKET.md`.


M7 closeout is valid only when:

1. high-priority workstreams are complete with reproducible evidence,
2. medium-priority workstreams are complete or explicitly deferred with accepted risk,
3. documentation and GitBook agree on completion status,
4. next-slice dependencies are listed with owner and start criteria.

This closeout package is the contractual handoff for the first post-M7 hardware-facing slice.
