# M4-B Execution Playbook

This chapter translates M4-B goals into concrete execution tracks so contributors can pick work that
moves milestone outcomes forward without reopening M4-A contracts.

## 1. Scope of this playbook

M4-B is about **composition hardening**. The milestone is not complete by adding isolated new defs;
it is complete when lifecycle and capability operations are integrated, proven, and evidenced in
runnable traces.

Use this playbook together with:

- `docs/SEL4_SPEC.md` (normative scope + acceptance),
- `docs/DEVELOPMENT.md` (workflow + proof standards),
- `docs/TESTING_FRAMEWORK_PLAN.md` (test expansion contract).

## 2. Workstream map

### Workstream A — Transition composition semantics ✅ completed

Goal: establish deterministic lifecycle+revoke/delete interaction behavior.

Deliverables:

1. one or more composition helper transitions with explicit error branches,
2. theorem-visible ordering assumptions (e.g., delete-before-reuse),
3. API comments documenting authority and state preconditions.

Definition of done:

- transitions compile,
- error variants are explicit,
- behavior is observable from executable scenarios.

### Workstream B — Invariant hardening ✅ completed

Goal: eliminate stale-reference ambiguity across lifecycle operations.

Deliverables:

1. stale-reference exclusion components,
2. links to identity/aliasing and capability-authority components,
3. reusable helper lemmas for local proof ergonomics.

Definition of done:

- invariants are named and narrowly scoped,
- helper lemmas are transition-local,
- no monolithic mega-invariant introduced.

### Workstream C — Preservation theorem expansion ✅ completed

Goal: keep proofs layered while broadening composition guarantees.

Deliverables:

1. local preservation theorem entrypoints for each new operation,
2. composed preservation theorem(s) spanning lifecycle + capability bundles,
3. failure-path preservation statements (not just success-path proofs).

Definition of done:

- theorem naming follows `<transition>_preserves_<target>`,
- local-first structure is visible in code organization,
- no `axiom`/`sorry` placeholders.

### Workstream D — Executable and fixture evidence ✅ completed

Goal: prove milestone behavior is externally visible and regression-testable.

Deliverables:

1. success/failure M4-B scenarios in `Main.lean`,
2. stable fixture anchors for new semantic fragments,
3. rationale notes for each fixture update.

Definition of done:

- `test_tier2_trace` and `test_smoke` pass,
- fragments are stable semantic signals (not formatting noise),
- scenario coverage maps back to M4-B target outcomes.

### Workstream E — Testing and CI growth ✅ completed

Goal: ensure M4-B regression detection is reliable.

Deliverables:

1. Tier 3 symbol anchors for new composition theorem surfaces,
2. nightly extension candidates documented and staged,
3. failure triage notes linked to exact script entrypoints.

Definition of done:

- `test_full` remains green,
- M4-B anchors are present and discoverable,
- nightly is still explicit about extension-point status.

## 3. Recommended sequencing

1. Land semantics + local helpers.
2. Land local invariants + local preservation.
3. Land composed preservation + failure-path proofs.
4. Land scenario/fixture expansion.
5. Land Tier 3/CI anchor expansion.
6. Land docs closeout + deferred M5 notes.

This order minimizes churn and avoids fixture drift before semantics stabilize.

## 4. PR template for M4-B work

Each M4-B PR should answer:

1. Which workstream(s) does this PR advance?
2. Which target outcome(s) from the spec are moved?
3. What command evidence validates the claim?
4. What remains deferred in M4-B after this PR?
5. What M5 direction does this work unlock?

## 5. Common pitfalls to avoid

1. **Proof-first without semantic anchors** — causes theorem churn when behavior changes.
2. **Fixture-first without deterministic behavior** — causes fragile trace expectations.
3. **Composed proof before local proof maturity** — hides root-cause failures.
4. **Untracked deferred work** — creates milestone ambiguity and roadmap drift.
5. **Undocumented failure paths** — reduces confidence in authority/lifecycle safety claims.

## 6. Exit checklist for M4-B maintainers

Before declaring M4-B complete, verify:

- composed lifecycle+capability transition story exists and is deterministic,
- stale-reference exclusion is explicit and machine-checked,
- failure-path preservation is implemented and documented,
- executable traces cover both success and failure composition stories,
- Tier 3 contains M4-B theorem/bundle anchors,
- docs across README/spec/development/gitbook/testing are synchronized.
