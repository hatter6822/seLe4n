# Documentation Deduplication Map (WS-C8)

This document defines the canonical-vs-mirror split used to reduce drift between root docs and GitBook.

## 1) Canonical ownership rules

- Canonical policy/spec/planning text lives under `docs/` (root docs + `docs/audits/`).
- GitBook chapter files under `docs/gitbook/` are mirror/navigation surfaces; they should summarize and link to canonical sources.
- If a topic changes, update canonical first and GitBook mirrors second in the same PR.

## 2) Root ↔ GitBook deduplication map

| Topic | Canonical root file(s) | GitBook mirror chapter(s) | Mirror rule |
|---|---|---|---|
| Active scope, milestones, and acceptance | `docs/spec/SELE4N_SPEC.md` | `05-specification-and-roadmap.md` | Keep normative decisions in spec; chapter is digest + links only. |
| seL4 microkernel reference | `docs/spec/SEL4_SPEC.md` | `02-microkernel-and-sel4-primer.md` | Reference-only; update when seL4 spec content changes. |
| Active workstream (WS-SM) | `docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md` + per-phase `docs/planning/SMP_*.md`; active audit baseline in `docs/audits/AUDIT_v0.30.11_*` | `05-specification-and-roadmap.md` | Keep status/closure evidence canonical in the plans and `docs/WORKSTREAM_HISTORY.md`; chapter summarizes and links. |
| Workstream history | `docs/WORKSTREAM_HISTORY.md` | `05-specification-and-roadmap.md` | Canonical record; chapter provides navigation. |
| Contributor workflow expectations | `docs/DEVELOPMENT.md` | — (archived to dev_history) | Canonical workflow in root doc. |
| Test/CI evidence contract | `docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md` | `07-testing-and-ci.md` | Root docs own gate semantics and policy details; chapter links and summarizes. |
| Documentation synchronization governance | `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`, `docs/DOCS_DEDUPLICATION_MAP.md` | `25-documentation-sync-and-coverage-matrix.md`, `27-documentation-deduplication-map.md` | Keep canonical matrices in root; GitBook points readers at canonical tables. |
| Claim/audit evidence mapping | `docs/CLAIM_EVIDENCE_INDEX.md` | `31-claim-vs-evidence-index.md` | Root file owns claim→evidence rows; GitBook chapter remains a pointer only. |
| Architecture decisions (ADRs) | `docs/FINITE_OBJECT_STORE_ADR.md`, `docs/VSPACE_MEMORY_MODEL_ADR.md`, `docs/ON_DESIGN_DECISION_ADR.md`, `docs/PLATFORM_BINDING_ADR.md` | `30-ws-c7-model-structure-and-maintainability.md`, `26-ws-b1-vspace-memory-adr.md` | ADRs are canonical; GitBook chapters stay concise and link back. |
| Security trajectory | `docs/INFORMATION_FLOW_ROADMAP.md`, `docs/THREAT_MODEL.md`, `docs/SECURITY_ADVISORY.md`, `docs/DEPLOYMENT_GUIDE.md` | `28-threat-model-and-security-hardening.md` | Milestone shifts must update roadmap and at least one active planning chapter. |
| Hardware validation | `docs/HARDWARE_TESTING.md`, `docs/hardware_validation/` | `10-path-to-real-hardware-mobile-first.md` | Root docs own procedures and reports; chapter summarizes. |
| Rust ABI audit notes | `docs/AUDIT_NOTES.md` | `15-rust-syscall-wrappers.md` | Root file owns per-finding notes; chapter summarizes the crates. |
| Translations | `docs/i18n/` (11 locales + `LANGUAGES.md`) | — | Mirrors of the root `README`/`CONTRIBUTING`/`QUICKSTART`; badges and Version rows are version-sites (`scripts/version_locations.sh`). |
| Historical records | `docs/dev_history/` | — | Archived; not mirrored in GitBook. See `docs/dev_history/README.md`. |

## 3) Automation hooks

WS-C8 automation is intentionally simple and reproducible:

1. `scripts/generate_doc_navigation.py` generates `docs/gitbook/README.md` and `docs/gitbook/SUMMARY.md` from `docs/gitbook/navigation_manifest.json`.
2. `scripts/check_markdown_links.py` validates local markdown links across tracked `*.md` files.
3. `scripts/test_docs_sync.sh` runs navigation generation, verifies generated files are committed, runs markdown-link validation, and opportunistically invokes `doc-gen4` when available. It runs in CI on every PR (the smoke lane of `lean_action_ci.yml`) and inside `scripts/test_smoke.sh` (WS-H3/M-19).

## 4) PR checklist additions (planning/doc changes)

For planning/docs workstreams (including WS-C8+), PRs should explicitly confirm:

- canonical root docs were updated first,
- GitBook mirrors were synchronized in the same PR,
- generated navigation outputs were regenerated,
- markdown-link checks passed,
- active-slice status text is consistent across README/spec/development/workstream plan/chapter 05,
- claim/evidence rows are updated when baseline claims or validation commands change.
