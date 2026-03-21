# Documentation Deduplication Map

Canonical source: [`docs/DOCS_DEDUPLICATION_MAP.md`](../DOCS_DEDUPLICATION_MAP.md).

This chapter explains how seLe4n avoids documentation drift between root docs and GitBook chapters.

## The problem

With two documentation surfaces (root `docs/` and `docs/gitbook/`), content can easily diverge. A change to `DEVELOPMENT.md` that is not reflected in `06-development-workflow.md` creates contradictions that erode trust.

## The solution: canonical ownership

Every topic has exactly one canonical source. GitBook chapters summarize and link to canonical sources; they never contain normative text that contradicts the root document.

## Ownership map

| Topic | Canonical source | GitBook chapter | Mirror rule |
|-------|-----------------|-----------------|-------------|
| Milestones, scope, acceptance | `docs/spec/SELE4N_SPEC.md` | `05-specification-and-roadmap.md` | Spec is normative; chapter digests and links |
| seL4 reference | `docs/spec/SEL4_SPEC.md` | `02-microkernel-and-sel4-primer.md` | Reference-only |
| Active audit findings | `docs/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` | `05-*` | Findings canonical in audits |
| Workstream execution | `docs/WORKSTREAM_HISTORY.md` | `05-*` | Status tables in canonical plan |
| Contributor workflow | `docs/DEVELOPMENT.md` | — | Checklists canonical in root |
| Test/CI contract | `docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md` | `07-testing-and-ci.md` | Root owns gate semantics |
| Claim/evidence mapping | `docs/CLAIM_EVIDENCE_INDEX.md` | `31-claim-vs-evidence-index.md` | Root owns claim table |
| ADRs | `docs/*_ADR.md` | `26-*`, `30-*` | ADRs canonical; chapters link back |
| Security trajectory | `docs/THREAT_MODEL.md`, `docs/INFORMATION_FLOW_ROADMAP.md` | `28-*` | Root is normative |
| Historical records | `docs/dev_history/` | — | Archived; not mirrored |

## Automation

Three scripts maintain synchronization:

1. **`scripts/generate_doc_navigation.py`** — generates `SUMMARY.md` and `README.md` from `navigation_manifest.json`.
2. **`scripts/check_markdown_links.py`** — validates local markdown links across all tracked `*.md` files.
3. **`scripts/test_docs_sync.sh`** — runs navigation generation, verifies generated files are committed, runs link validation.

## PR checklist for documentation changes

1. Update canonical root docs first.
2. Update GitBook mirrors in the same PR.
3. Regenerate navigation (`scripts/generate_doc_navigation.py`).
4. Run `./scripts/test_smoke.sh`.
5. Verify references with targeted searches for newly introduced docs.

## Related

- [Documentation Sync and Coverage Matrix](25-documentation-sync-and-coverage-matrix.md) — full sync index
- [Testing & CI](07-testing-and-ci.md) — validation tiers
