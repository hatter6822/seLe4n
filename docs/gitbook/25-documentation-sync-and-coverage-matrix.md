# Documentation Sync and Coverage Matrix

Canonical source document:

- [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)

This chapter is a concise navigation entry. Keep normative synchronization rules and coverage tables in the canonical root document.

## 1) Why this chapter exists

Use this chapter during doc/planning reviews to ensure:

- active planning references point to the `AUDIT_v0.9.32` baseline,
- root docs and GitBook remain synchronized,
- historical WS-B content is clearly separated from active WS-C planning,
- testing evidence expectations are applied consistently.

## 2) What to update together

- planning docs (`docs/audits/AUDIT_v0.9.32*.md`, including tracked proof issues + chapter 24),
- workflow/test policy docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md`, chapter 07),
- roadmap/spec docs (`docs/SEL4_SPEC.md`, chapter 05, chapter 22),
- dedup ownership docs (`docs/DOCS_DEDUPLICATION_MAP.md`, chapter 27).

## 3) Validation minimum

For documentation synchronization changes:

1. run `./scripts/test_smoke.sh`,
2. run `./scripts/test_full.sh` when theorem/invariant anchors or planning policies are touched,
3. run targeted `rg -n` reference checks for newly introduced docs.

For baseline planning changes, also run:

- `./scripts/test_nightly.sh`.
