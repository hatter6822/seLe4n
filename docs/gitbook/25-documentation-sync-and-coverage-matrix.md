# Documentation Sync and Coverage Matrix

Canonical source: [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md).

This chapter explains how seLe4n documentation stays synchronized across two surfaces (root `docs/` and `docs/gitbook/`), and what validation steps apply to documentation changes.

## Purpose

Every documentation change touches at least two locations: a canonical root document and its GitBook mirror. Without a synchronization contract, these diverge over time. The sync matrix is the authoritative map of which file owns which topic and what validation to run when it changes.

## What to update together

When changing documentation, ensure the paired files are updated in the same PR:

| Change area | Canonical doc | GitBook chapter |
|-------------|--------------|-----------------|
| Planning/workstream status | `docs/audits/AUDIT_v0.12.2*.md` | `24-*` |
| Workflow/test policy | `TESTING_FRAMEWORK_PLAN.md`, `CI_POLICY.md` | `07-*` |
| Spec/roadmap | `docs/spec/SELE4N_SPEC.md`, `SEL4_SPEC.md` | `05-*`, `22-*` |
| Dedup ownership | `DOCS_DEDUPLICATION_MAP.md` | `27-*` |
| Claim/evidence index | `CLAIM_EVIDENCE_INDEX.md` | `31-*` |
| Security | `THREAT_MODEL.md`, `INFORMATION_FLOW_ROADMAP.md` | `28-*` |
| ADRs | `*_ADR.md` | `26-*`, `30-*` |

## Validation minimum

For documentation changes:

1. Run `./scripts/test_smoke.sh` — validates docs sync + builds + trace
2. Run `./scripts/test_full.sh` when theorem/invariant anchors or planning policies change
3. Run targeted reference checks for newly introduced documents

For baseline planning changes, also run `./scripts/test_nightly.sh`.

## Related

- [Documentation Deduplication Map](27-documentation-deduplication-map.md) — canonical ownership rules
- [Testing & CI](07-testing-and-ci.md) — tier definitions
- [Claim vs Evidence Index](31-claim-vs-evidence-index.md) — claim-to-evidence mapping
