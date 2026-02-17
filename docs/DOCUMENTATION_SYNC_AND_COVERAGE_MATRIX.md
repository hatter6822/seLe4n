# Documentation Sync and Coverage Matrix

This document is the single synchronization index for:

1. canonical root documentation,
2. GitBook chapter mirrors/navigation,
3. test/verification coverage for the current project stage.

Use this file during planning and PR review to verify that docs, GitBook, and test evidence stay aligned.

## 1) Canonical source-of-truth map

| Topic | Canonical document | GitBook chapter(s) | Sync rule |
|---|---|---|---|
| Milestones, scope, acceptance | `docs/SEL4_SPEC.md` | `05-specification-and-roadmap.md` | Update spec first; GitBook chapter summarizes and links back. |
| Comprehensive audit findings | `docs/audits/COMPREHENSIVE_AUDIT_2026_02.md` | `19-end-to-end-audit-and-quality-gates.md`, `24-comprehensive-audit-2026-workstream-planning.md` | Keep findings canonical in audits dir; avoid duplicating full audit prose in chapters. |
| Comprehensive audit execution portfolio | `docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md` | `24-comprehensive-audit-2026-workstream-planning.md` | Workstream status tables live in canonical plan; GitBook only navigates/summarizes. |
| M7 historical remediation closeout | `docs/M7_CLOSEOUT_PACKET.md` + `docs/audits/AUDIT_REMEDIATION_WORKSTREAMS.md` | `21-m7-current-slice-outcomes-and-workstreams.md`, `23-m7-remediation-closeout-packet.md`, `20-repository-audit-remediation-workstreams.md` | Keep marked as historical context for post-M7 planning, not active baseline. |
| Development workflow | `docs/DEVELOPMENT.md` | `06-development-workflow.md` | Workflow command changes must be reflected in both files in same PR. |
| Test tiers and CI contract | `docs/TESTING_FRAMEWORK_PLAN.md`, `docs/CI_POLICY.md` | `07-testing-and-ci.md` | Script/workflow changes require root docs + GitBook updates together. |
| Hardware-boundary contract policy | `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` | `10-path-to-real-hardware-mobile-first.md` | Keep normative constraints in policy doc; chapter links policy and planning implications. |
| Security trajectory | `docs/INFORMATION_FLOW_ROADMAP.md` | `12-proof-and-invariant-map.md`, `22-next-slice-development-path.md` | Milestone shifts must update roadmap and at least one active planning chapter. |

## 2) Test and verification coverage map

| Validation area | Command | What it verifies |
|---|---|---|
| Hygiene + forbidden markers + fixture isolation | `./scripts/test_tier0_hygiene.sh` | No `sorry`/`axiom`/`TODO` debt in proof surface; no test contract leakage into production kernel modules. |
| Lean build soundness | `./scripts/test_tier1_build.sh` | Project compiles successfully via `lake build`. |
| End-to-end executable trace fixture | `./scripts/test_tier2_trace.sh` | Runtime trace still satisfies fixture expectations and scenario/risk-tagged entries. |
| Invariant/doc anchor surface | `./scripts/test_tier3_invariant_surface.sh` | Critical theorem/definition/document anchors still exist after refactors. |
| Nightly candidates / determinism replay | `./scripts/test_tier4_nightly_candidates.sh` and `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | Multi-run determinism, nightly artifacts, and seeded stochastic probe replay. |
| Fast lane | `./scripts/test_fast.sh` | Tier 0 + Tier 1 quick validation. |
| Smoke lane | `./scripts/test_smoke.sh` | Tier 0 + Tier 1 + Tier 2 validation. |
| Full lane | `./scripts/test_full.sh` | Tier 0 + Tier 1 + Tier 2 + Tier 3 validation. |

## 3) PR synchronization checklist (required)

For documentation/planning PRs:

1. Update canonical source docs first.
2. Update GitBook navigation and chapter links.
3. Run at least `test_smoke.sh`; run `test_full.sh` when docs mention theorem/anchor surfaces.
4. If planning/test policy changed, run `test_nightly.sh` (or explain why not run).
5. Verify references with targeted `rg -n` checks for newly introduced docs/chapters.

## 4) Current-stage status summary

- Active planning baseline: `COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`.
- Historical closeout baseline: M7 remediation docs (`AUDIT_REMEDIATION_WORKSTREAMS.md`, `M7_CLOSEOUT_PACKET.md`).
- Current quality-gate contract: Tier 0–3 required, Tier 4 nightly determinism evidence.

