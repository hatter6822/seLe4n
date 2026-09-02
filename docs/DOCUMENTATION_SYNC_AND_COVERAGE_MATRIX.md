# Documentation Sync and Coverage Matrix

This document is the synchronization index for:

1. canonical root documentation,
2. GitBook chapter mirrors/navigation,
3. test/verification coverage for active planning.

Use this file during planning and PR review to keep documentation status aligned with code reality.

## 1) Canonical source-of-truth map

| Topic | Canonical document | GitBook chapter(s) | Sync rule |
|---|---|---|---|
| Milestones, scope, acceptance | `docs/spec/SELE4N_SPEC.md` | `05-specification-and-roadmap.md` | Update spec first; GitBook summarizes and links back. |
| seL4 microkernel reference | `docs/spec/SEL4_SPEC.md` | `02-microkernel-and-sel4-primer.md` | Reference-only; update when seL4 spec content changes. |
| Active audit / workstream (WS-SM) | `docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md` + per-phase `docs/planning/SMP_*.md`; active audit baseline `docs/audits/AUDIT_v0.30.11_*` | `05-specification-and-roadmap.md` | Findings and status tables canonical in the plans and `docs/WORKSTREAM_HISTORY.md`; GitBook chapter summarizes and links back. |
| Workstream history (all prior portfolios) | `docs/WORKSTREAM_HISTORY.md` | `05-specification-and-roadmap.md` | Canonical record; GitBook chapter provides navigation. |
| Completed performance portfolio (WS-G) | `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` | `08-kernel-performance-optimization.md` | All findings closed; chapter documents optimizations. Archived to `docs/dev_history/`. |
| Prior audit findings (WS-E, completed) | `docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md` | — | Archived to `docs/dev_history/`; WS-E1..E6 all completed. |
| Prior audit findings (WS-D, completed) | `docs/dev_history/audits/AUDIT_v0.11.0.md` | — | Archived to `docs/dev_history/`; WS-D1..D4 completed. |
| Claim vs evidence index (active semantics/proofs/docs) | `docs/CLAIM_EVIDENCE_INDEX.md` | `31-claim-vs-evidence-index.md` | Keep auditable claim→command mapping canonical in root; GitBook chapter points to index. |
| Historical execution portfolios | `docs/dev_history/audits/` | Archived to `docs/dev_history/gitbook/` | Historical-only; see `docs/dev_history/README.md`. |
| Documentation dedup ownership | `docs/DOCS_DEDUPLICATION_MAP.md` | `27-documentation-deduplication-map.md` | Canonical dedup map stays in root docs. |
| Finite object-store ADR (WS-C7) | `docs/FINITE_OBJECT_STORE_ADR.md` | `30-ws-c7-model-structure-and-maintainability.md` | ADR is canonical; GitBook chapter stays concise and links back. |
| VSpace memory-model ADR (WS-B1) | `docs/VSPACE_MEMORY_MODEL_ADR.md` | `26-ws-b1-vspace-memory-adr.md` | ADR is canonical; GitBook chapter stays concise and links back. |
| Platform-binding ADR | `docs/PLATFORM_BINDING_ADR.md` | `10-path-to-real-hardware-mobile-first.md` | ADR is canonical; chapter links. |
| Security advisories + deployment guidance | `docs/SECURITY_ADVISORY.md`, `docs/DEPLOYMENT_GUIDE.md` | `28-threat-model-and-security-hardening.md` | Root docs own advisory statuses and deployment obligations; chapter summarizes. |
| Hardware testing + validation reports | `docs/HARDWARE_TESTING.md`, `docs/hardware_validation/` | `10-path-to-real-hardware-mobile-first.md` | Root docs own procedures and report data. |
| Rust ABI audit notes | `docs/AUDIT_NOTES.md` | `15-rust-syscall-wrappers.md` | Root file owns per-finding notes. |
| Translations | `docs/i18n/` (11 locales + `LANGUAGES.md`) | — | Mirror the root README/CONTRIBUTING/QUICKSTART; badges + Version rows are version-sites. |
| Development workflow | `docs/DEVELOPMENT.md` | — (archived to dev_history) | Canonical workflow in root doc. |
| Test tiers and CI contract | `docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md` | `07-testing-and-ci.md` | Script/workflow changes require synchronized updates. |
| Hardware-boundary contract policy | `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` | `10-path-to-real-hardware-mobile-first.md` | Normative constraints in policy doc; chapter links policy implications. |
| Security trajectory | `docs/INFORMATION_FLOW_ROADMAP.md`, `docs/THREAT_MODEL.md` | `12-proof-and-invariant-map.md`, `28-threat-model-and-security-hardening.md` | Milestone shifts must update roadmap and at least one active planning chapter. |

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

## 3) PR synchronization checklist (required)

For documentation/planning PRs:

1. Update canonical source docs first.
2. Update GitBook mirror/navigation references.
3. Run at least `test_smoke.sh`; run `test_full.sh` when theorem/invariant anchors or policy text changes.
4. If planning baseline or test policy changes, run `test_nightly.sh` (or explain why not run).
5. Verify references with targeted `rg -n` checks for newly introduced docs/chapters.

## 4) Current-stage status summary

- **Active workstream**: WS-SM (SMP multi-core completion) — SM0–SM9
  landed, SM10 pending (→ v1.0.0); WS-RA complete. See
  `docs/WORKSTREAM_HISTORY.md` "What's next" and CLAUDE.md's phase table.
- **Completed portfolios**: WS-B through WS-AN, WS-RC R0–R5, WS-RA — the
  full traceability table is in `docs/WORKSTREAM_HISTORY.md`.
- **Historical baselines**: prior audits and workstream plans archived in
  `docs/dev_history/audits/`; the active baseline family is
  `docs/audits/AUDIT_v0.30.11_*`.
- **Quality-gate contract**: Tier 0–3 required, Tier 4 nightly determinism
  evidence, Tier 5 cross-language correspondence (nightly, experimental).
- **Hardware target**: Raspberry Pi 5 (ARM64), SMP-on by default.
- **Metrics**: live values in `docs/codebase_map.json` → `readme_sync`
  (at v0.34.26: 289,335 production LoC across 288 files, 64,535 test LoC
  across 69 suites, 9,680 proved declarations; zero sorry/axiom).
  **This figure is hand-copied**: `scripts/sync_documentation_metrics.sh`
  drives `README.md` and `docs/spec/SELE4N_SPEC.md` only, so this file — and
  the eleven i18n READMEs and four GitBook chapters — drift silently between
  hand updates.  Registered as WS-RR **RR7.35**; until it lands, treat any
  metric here as of the version stamped beside it.
