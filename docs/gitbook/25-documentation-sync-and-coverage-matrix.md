# Documentation Sync and Coverage Matrix

Canonical source document:

- [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)

This chapter is a concise navigation entry. Keep normative synchronization rules and coverage tables in the canonical root document.

## 1) Why this chapter exists

Use this chapter when reviewing or planning documentation-heavy changes to ensure:

- current workstream status remains synchronized through WS-B11 completion,
- root docs and GitBook remain in sync,
- workstream planning references point to canonical files,
- testing evidence expectations are applied consistently.

## 2) What to update together

- planning docs (`docs/audits/*` + active planning chapters),
- workflow/test policy docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md`, chapter 07),
- roadmap/spec docs (`docs/SEL4_SPEC.md`, chapter 05, next-slice chapter 22).
- dedup ownership docs (`docs/DOCS_DEDUPLICATION_MAP.md`, chapter 27).

## 3) Validation minimum

For documentation synchronization changes:

1. run `./scripts/test_smoke.sh`,
2. run `./scripts/test_full.sh` when theorem/invariant anchors or chapter references are touched,
3. run targeted `rg -n` link/reference checks for newly introduced docs.

For release-gate or planning baseline changes, also run:

- `./scripts/test_nightly.sh`.

