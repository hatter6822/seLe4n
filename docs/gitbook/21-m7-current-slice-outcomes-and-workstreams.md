# M7 Current Slice Outcomes and Workstreams

This chapter is the practical execution map for the active slice.

Use this chapter when you need to answer:

- what outcomes M7 must deliver,
- which workstream closes which risk,
- how we sequence delivery,
- and what evidence is required before M7 can close.

For normative scope, always defer to [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md).
For audit source findings, use [`docs/REPOSITORY_AUDIT.md`](../REPOSITORY_AUDIT.md).
For implementation-level details, use [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](../AUDIT_REMEDIATION_WORKSTREAMS.md).

## 1. M7 slice goal statement

M7 exists to convert audit findings into durable delivery controls without destabilizing M1–M6 proof guarantees.

Concretely, M7 should leave the repository in a state where:

1. CI quality gates are strict, reproducible, and fast enough to sustain contribution velocity.
2. Architecture boundary modules are symmetric and easy to navigate.
3. Type confusion classes (ID/pointer alias misuse) are structurally harder to write.
4. Test evidence scales beyond happy-path fixtures.
5. Documentation and contributor workflow are consistent from root README to GitBook chapters.
6. Security and platform readiness are sufficient to start the post-remediation hardware slice.

## 2. Target outcome matrix (what “M7 done” means)

| Outcome ID | Target outcome | Primary workstreams | Required closure evidence |
|---|---|---|---|
| M7-O1 | Tiered CI is enforced as policy, not convention | WS-A1 | Required checks active + CI workflow docs + deterministic replay evidence |
| M7-O2 | Kernel module boundaries are clearer and externally consumable | WS-A2 | IPC split complete, stable API facade, updated architecture map |
| M7-O3 | Core identity domains are type-safe by construction | WS-A3 | newtype migration merged, theorem surfaces adapted, no placeholder debt |
| M7-O4 | Test evidence covers scale and adversarial-style paths | WS-A4 | expanded scenarios + fixture traceability + at least one stochastic/property track |
| M7-O5 | Hardware contract safety is explicit and non-production test contracts are isolated | WS-A5 | permissive contract isolation + usage policy docs + import boundary enforcement |
| M7-O6 | Documentation IA is contributor-first and milestone-accurate | WS-A6 | root contribution/changelog artifacts + synchronized handbook navigation |
| M7-O7 | Proof surfaces are explainable and easier to maintain | WS-A7 | theorem docstring coverage + duplicated proof reduction evidence |
| M7-O8 | Platform and baseline security maturity gates are operational | WS-A8 | cross-platform CI signal + scanning workflow + information-flow roadmap draft |

## 3. Workstream deep map

### WS-A1 — CI hardening and quality gate promotion ✅ completed

**Intent:** shift from “best effort checks” to enforced proof and determinism gates.

**Completed closure evidence:**

- Tier 0–3 are promoted into CI lanes (`Fast`, `Smoke`, `Full`) with Tier 3 included in merge-gate flow,
- deterministic replay is scheduled in a dedicated nightly workflow with artifact retention,
- Lean/Lake cache restoration is active to reduce cold-start latency,
- branch protection and required-check policy is documented in `docs/CI_POLICY.md`,
- failure diagnostics remain actionable through trace/nightly artifact uploads and category-labeled script output.

**DoD signals status:**

- branch protection requirements are documented and reproducible ✅,
- no milestone-moving PR bypasses proof-surface checks ✅,
- failed checks produce actionable diagnostics ✅.

### WS-A2 — Architecture modularity and API surface

**Intent:** make subsystem boundaries composable for future platform binding work.

**Execution focus now:**

- maintain symmetry between operations and invariants,
- keep external entrypoints stable via `SeLe4n/Kernel/API.lean`,
- preserve theorem discoverability while moving internal modules.

**DoD signals:**

- IPC layering is split and mapped in docs,
- dependent imports are minimal and explicit,
- no trace/theorem regression during refactors.

### WS-A3 — Type-safety uplift for IDs and pointers

**Intent:** remove classes of cross-domain misuse at compile time.

**Execution focus now:**

- migrate high-risk aliases first (`ThreadId`, `ObjId`, `CPtr`, `Slot`),
- preserve ergonomics with helper constructors/projections,
- align theorem statements and executable traces after migration.

**DoD signals:**

- mixed-domain mistakes fail to typecheck,
- migration does not introduce theorem API ambiguity,
- no newly introduced `sorry`/`admit`/placeholder debt.

### WS-A4 — Test architecture expansion

**Intent:** grow confidence from curated stories to broader behavioral coverage.

**Execution focus now:**

- add scale-heavy and edge-case-rich scenarios,
- improve fixture readability and scenario traceability,
- add at least one stochastic/property-oriented validation path.

**DoD signals:**

- scenario-to-risk mapping exists and is easy to audit,
- failure output is concise enough for rapid debugging,
- CI or nightly runs include nontrivial sequence diversity.

### WS-A5 — Hardware-boundary safety and test-only contract separation

**Intent:** prevent permissive contracts from leaking into runtime-facing semantics.

**Execution focus now:**

- isolate permissive runtime contracts in testing-only namespaces,
- encode import boundaries that make misuse obvious in review,
- document trusted-contract policy and examples.

**DoD signals:**

- no production path references permissive test contracts,
- policy is enforced by contributor checklist language,
- contract intent is unambiguous in code and docs.

### WS-A6 — Documentation IA and contributor UX

**Intent:** make contributor onboarding and milestone navigation frictionless.

**Execution focus now:**

- keep root docs and handbook chapter ordering synchronized,
- avoid stale slice markers,
- capture current and next-slice context in every milestone chapter.

**DoD signals:**

- a new contributor can find setup/workflow/testing path from root in minutes,
- GitBook hierarchy mirrors actual development flow,
- active slice status is consistent across canonical docs.

### WS-A7 — Proof documentation and maintainability automation

**Intent:** reduce proof fragility and increase theorem-level legibility.

**Execution focus now:**

- add concise theorem purpose docstrings,
- eliminate copy-paste proof blocks via reusable helpers,
- preserve readability while reducing maintenance surface.

**DoD signals:**

- public theorem surfaces are documented,
- repeated proof patterns are parameterized,
- reviewers can identify preservation obligations faster.

### WS-A8 — Platform/security maturity for next slice readiness

**Intent:** avoid a large maturity cliff at hardware-binding start.

**Execution focus now:**

- establish architecture-relevant CI signals,
- automate baseline scanning and security hygiene,
- define information-flow proof trajectory.

**DoD signals:**

- at least one architecture-targeted CI lane is operational,
- scanning evidence is present in automation,
- post-M7 security proof path is published.

## 4. Dependency and sequencing model

M7 workstreams are intentionally staged:

1. **Stabilization-first:** WS-A1, WS-A2, WS-A5, and doc hygiene from WS-A6.
2. **Model-quality uplift:** WS-A3 and WS-A4 after architecture boundaries are stable.
3. **Scalability/trajectory hardening:** WS-A7 and WS-A8 once migration churn is reduced.

This order protects the proof baseline while allowing high-value hardening early.

## 5. Operating rhythm for M7 execution

For each PR that advances M7, include:

1. **Workstream binding:** WS-A* ID(s) being advanced.
2. **Outcome binding:** which M7-O* target(s) move.
3. **Evidence commands:** exact checks used for validation.
4. **Docs sync:** links to updated handbook/reference sections.
5. **Next unlock:** one sentence on which downstream task is now unblocked.

For each checkpoint summary, report:

- completed outcome IDs,
- in-progress workstreams with blockers,
- deferred items and rationale,
- confidence status for the M7 → next-slice gate.

## 6. Exit gate to start the next slice

M7 should be declared complete only when all are true:

1. all high-priority workstreams (WS-A1, WS-A2, WS-A3, WS-A5) are closed with reproducible evidence,
2. medium-priority workstreams have either closure evidence or explicit, risk-accepted deferrals,
3. CI/test/docs state is consistent across root docs and GitBook,
4. next-slice kickoff dependencies are explicitly listed and owned.

That closure package becomes the handoff contract for the first post-remediation hardware-oriented slice.
