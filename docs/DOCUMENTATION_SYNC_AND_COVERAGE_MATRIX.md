# Documentation Sync and Coverage Matrix

This document is the synchronization index for:

1. canonical root documentation,
2. GitBook chapter mirrors/navigation,
3. test/verification coverage for active planning.

Use this file during planning and PR review to keep documentation status aligned with code reality.
It is also the documentation **ownership map**: it absorbed the former
`docs/DOCS_DEDUPLICATION_MAP.md`, and the GitBook chapters that only restated a
root document (former chapters 25–31) were retired in favour of navigation links
to the root document itself.

## 0) Ownership rules

- Every topic has exactly **one** canonical home. Canonical policy/spec/planning
  text lives under `docs/` (root docs, `docs/spec/`, `docs/planning/`,
  `docs/audits/`).
- GitBook chapters under `docs/gitbook/` are a reading path: they introduce a
  topic and **link** to its canonical document rather than restating it. A
  chapter that would only mirror a root document is not written; the GitBook
  navigation (`docs/gitbook/navigation_manifest.json`) links the root document
  directly.
- If a topic changes, update the canonical document first, then any chapter that
  summarises it, in the same PR.
- `CHANGELOG.md` owns the per-version narrative and `docs/REGISTERED_DEBT.md`
  owns workstream status; a plan under `docs/planning/` owns a phase's
  *schedule* (its sub-task table), not an account of what each cut changed —
  duplicating that account produces two records that drift.
- When a workstream closes, its plan moves to `docs/dev_history/planning/`,
  after any obligation it still holds is lifted into an active row of
  `docs/REGISTERED_DEBT.md`.  Source must not reference `docs/dev_history/`
  (a Tier 0 gate), so it cites an archived plan by workstream or phase ID,
  and the "Archived plans by ID" table in
  `docs/agent_guide/WORKSTREAM_CONTEXT.md` resolves the ID.

## 1) Canonical source-of-truth map

| Topic | Canonical document | GitBook chapter(s) | Sync rule |
|---|---|---|---|
| Milestones, scope, acceptance | `docs/spec/SELE4N_SPEC.md` | `05-specification-and-roadmap.md` | Update spec first; GitBook summarizes and links back. |
| seL4 microkernel reference | `docs/spec/SEL4_SPEC.md` | `02-microkernel-and-sel4-primer.md` | Reference-only; update when seL4 spec content changes. |
| Active audit / workstream (WS-SM) | `docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md` + per-phase `docs/planning/SMP_*.md`; active audit baseline `docs/audits/AUDIT_v0.30.11_*` | `05-specification-and-roadmap.md` | Findings and status tables canonical in the plans and `docs/REGISTERED_DEBT.md`; GitBook chapter summarizes and links back. |
| Registered debt and workstream registry | `docs/REGISTERED_DEBT.md` | `05-specification-and-roadmap.md` | Canonical record; GitBook chapter provides navigation. |
| Completed performance portfolio (WS-G) | `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` | `08-kernel-performance-optimization.md` | All findings closed; chapter documents optimizations. Archived to `docs/dev_history/`. |
| Prior audit findings (WS-E, completed) | `docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md` | — | Archived to `docs/dev_history/`; WS-E1..E6 all completed. |
| Prior audit findings (WS-D, completed) | `docs/dev_history/audits/AUDIT_v0.11.0.md` | — | Archived to `docs/dev_history/`; WS-D1..D4 completed. |
| Claim vs evidence index (active semantics/proofs/docs) | `docs/CLAIM_EVIDENCE_INDEX.md` | — (linked from the GitBook navigation) | Keep auditable claim→command mapping canonical in root. |
| Historical execution portfolios | `docs/dev_history/audits/` | Archived to `docs/dev_history/gitbook/` | Historical-only; see `docs/dev_history/README.md`. |
| Documentation ownership and sync | this file | — (linked from the GitBook navigation) | One canonical home per topic (§0). |
| Finite object-store ADR (WS-C7) | `docs/FINITE_OBJECT_STORE_ADR.md` | — (linked from the GitBook navigation) | ADR is canonical. |
| VSpace memory-model ADR (WS-B1) | `docs/VSPACE_MEMORY_MODEL_ADR.md` | — (linked from the GitBook navigation) | ADR is canonical. |
| O(n) list-based data-structure ADR (F-17) | `docs/ON_DESIGN_DECISION_ADR.md` | — | ADR is canonical. |
| Platform-binding ADR | `docs/PLATFORM_BINDING_ADR.md` | `10-path-to-real-hardware-mobile-first.md` | ADR is canonical; chapter links. |
| Security advisories + deployment guidance | `docs/SECURITY_ADVISORY.md`, `docs/DEPLOYMENT_GUIDE.md` | — (linked from `docs/THREAT_MODEL.md` §8) | Root docs own advisory statuses and deployment obligations. |
| Hardware testing + validation reports | `docs/HARDWARE_TESTING.md`, `docs/hardware_validation/` | `10-path-to-real-hardware-mobile-first.md` | Root docs own procedures and report data. |
| Rust ABI audit notes | `docs/AUDIT_NOTES.md` | `15-rust-syscall-wrappers.md` | Root file owns per-finding notes. |
| Translations | `docs/i18n/` (11 locales + `LANGUAGES.md`) | — | Mirror the root README/CONTRIBUTING/QUICKSTART; badges + Version rows are version-sites. The three metric rows are written by `scripts/sync_translated_metrics.py` — edit its `TARGETS` table, not the row, when a translation's wording or inflected noun changes. |
| Development workflow | `docs/DEVELOPMENT.md` | — (archived to dev_history) | Canonical workflow in root doc. |
| Test tiers and CI contract | `docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md` | `07-testing-and-ci.md` | Script/workflow changes require synchronized updates. |
| Hardware-boundary contract policy | `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` | `10-path-to-real-hardware-mobile-first.md` | Normative constraints in policy doc; chapter links policy implications. |
| Security trajectory | `docs/INFORMATION_FLOW_ROADMAP.md`, `docs/THREAT_MODEL.md` | `12-proof-and-invariant-map.md` | Milestone shifts must update roadmap and at least one active planning chapter. |
| CI telemetry baseline | `docs/CI_TELEMETRY_BASELINE.md` | — (linked from the GitBook navigation) | Root doc owns the telemetry schema and policy. |
| Agent guidance | `CLAUDE.md` (durable rules; `AGENTS.md` is a static pointer file to it), `docs/agent_guide/` (long-form rationale, live workstream context, large-file list) | — | `CLAUDE.md` carries no workstream content; see its first section. |

## 2) Test and verification coverage map

| Validation area | Command | What it verifies |
|---|---|---|
| Hygiene + forbidden markers + fixture isolation | `./scripts/test_tier0_hygiene.sh` | No `sorry`/`axiom` debt in proof surface; no test contract leakage into production kernel modules; theorem-body spot-check; SHA-pinning regression guard; version sync; workstream-plan arithmetic; **SMP theorem-manifest drift** (`generate_smp_theorem_manifest.py --self-test` then `--check`: every theorem inventory in the tree is claimed by exactly one WS-SM phase, with the entry count the tree measures and a kind the gate validates rather than trusts; the *proposition* count is checked instead by the census inside `PhaseTheoremManifest.lean`, since a text scanner has no elaborator). |
| Lean build soundness | `./scripts/test_tier1_build.sh` | Project compiles successfully via `lake build`. |
| End-to-end executable trace fixture | `./scripts/test_tier2_trace.sh` | Runtime trace still satisfies fixture expectations and scenario/risk-tagged entries. |
| Negative/adversarial malformed-state suite | `./scripts/test_tier2_negative.sh` | Malformed capability/object/IPC/VSpace/scheduler states fail safely with explicit modeled errors. |
| Invariant surface anchors | `./scripts/test_tier3_invariant_surface.sh` | Critical theorem/definition/trace anchors still exist after refactors. |
| Documentation sync | `./scripts/test_docs_sync.sh` | GitBook navigation generation is reproducible, local markdown links resolve, metrics stay synced from `codebase_map.json`. Runs in CI on every PR (smoke lane) and inside `test_smoke.sh`. |
| Nightly candidates / determinism replay | `./scripts/test_tier4_nightly_candidates.sh` and `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | Multi-run determinism, nightly artifacts, and seeded stochastic probe replay. |
| Fast lane | `./scripts/test_fast.sh` | Tier 0 + Tier 1 quick validation. |
| Smoke lane | `./scripts/test_smoke.sh` | Tier 0 + Tier 1 + scenario-catalog validation + Tier 2 trace + determinism + negative-state + Sim-contract build + Rust gate (`test_rust.sh`) + docs sync. |
| Full lane | `./scripts/test_full.sh` | Tier 0 + Tier 1 + Tier 2 + Tier 3 validation. |

## 3) Automation hooks

1. `scripts/generate_doc_navigation.py` generates `docs/gitbook/README.md` and
   `docs/gitbook/SUMMARY.md` from `docs/gitbook/navigation_manifest.json`.
2. `scripts/check_markdown_links.py` validates local markdown links across
   tracked `*.md` files (`docs/dev_history/` excluded).
3. `scripts/test_docs_sync.sh` runs navigation generation, verifies the
   generated files are stable, runs markdown-link validation, checks metric
   propagation and the large-files list, and opportunistically invokes
   `doc-gen4` when available. It runs in CI on every PR.

## 4) PR synchronization checklist (required)

For documentation/planning PRs:

1. Update canonical source docs first.
2. Update any GitBook chapter that summarises the topic, and the navigation manifest if a document is added, moved or retired.
3. Run at least `test_smoke.sh`; run `test_full.sh` when theorem/invariant anchors or policy text changes.
4. If planning baseline or test policy changes, run `test_nightly.sh` (or explain why not run).
5. Verify references with targeted `rg -n` checks for newly introduced docs/chapters.
6. Regenerate the navigation outputs (`python3 scripts/generate_doc_navigation.py`) when the manifest changes.
7. Keep active-slice status consistent across `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, the workstream plan and GitBook chapter 05.
8. Update `docs/CLAIM_EVIDENCE_INDEX.md` rows when a baseline claim or its validation command changes.

## 5) Current-stage status summary

- **Active workstream**: WS-SM (SMP multi-core completion) — SM0–SM9
  landed, SM10 pending (→ v1.0.0); WS-RA complete. See
  `docs/REGISTERED_DEBT.md`'s *Current status* and the phase tables in `docs/agent_guide/WORKSTREAM_CONTEXT.md`.
- **Completed portfolios**: WS-B through WS-AN, WS-RC R0–R5, WS-RA — the
  full traceability table is in `docs/REGISTERED_DEBT.md`.
- **Historical baselines**: prior audits and workstream plans archived in
  `docs/dev_history/audits/`; the active baseline family is
  `docs/audits/AUDIT_v0.30.11_*`.
- **Quality-gate contract**: Tier 0–3 required, Tier 4 nightly determinism
  evidence, Tier 5 cross-language correspondence (nightly, experimental).
- **Hardware target**: Raspberry Pi 5 (ARM64), SMP-on by default.
- **Metrics**: live values in `docs/codebase_map.json` → `readme_sync`
  (run `python3 scripts/report_current_state.py` for the live figures; a
  snapshot pinned here is drift by construction).
  **The translated and GitBook figures are synced** (WS-RR RR7.35,
  `v0.34.85`): `scripts/sync_translated_metrics.py` drives the eleven i18n
  READMEs and the four GitBook surfaces that quote them, and
  `scripts/test_docs_sync.sh` fails on drift, so "the translations mirror the
  root README" is enforced rather than asserted.  It had not been: the locales
  published a `v0.33.101` snapshot and the GitBook surfaces two *different*
  stale generations.  Three of those languages inflect the counted noun, so the
  sync selects the form by CLDR plural category and **refuses to run** rather
  than guess an inflection it has not been given.
  **This file still pins no figure of its own**, and should not start: run
  `python3 scripts/report_current_state.py` for the live numbers.
