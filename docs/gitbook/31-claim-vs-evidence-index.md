# Claim vs Evidence Index

Canonical source: [`docs/CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md).

This chapter summarizes how seLe4n ties every public claim to executable or inspectable evidence. The canonical document contains the full claim table; this chapter explains the framework and highlights key claims.

## Purpose

Every claim in seLe4n documentation (README, spec, GitBook) must be backed by evidence that anyone can reproduce. The claim-evidence index maps each claim to:

1. **Canonical source** — where the claim is stated.
2. **Evidence command** — a script that validates the claim.
3. **Evidence artifact** — what the script checks or produces.

## How evidence works

| Evidence type | Example | Assurance level |
|---------------|---------|----------------|
| **Tier 0 hygiene scan** | `test_tier0_hygiene.sh` — no `sorry`/`axiom` in production files | High: forbidden-marker scan is exhaustive |
| **Tier 1 build** | `lake build` — all 84 jobs compile | High: Lean type-checker verifies proofs |
| **Tier 2 fixture** | `test_tier2_trace.sh` — runtime output matches locked fixture | Medium-High: covers exercised paths |
| **Tier 3 surface anchor** | `test_tier3_invariant_surface.sh` — named theorems still exist | High: prevents silent proof-surface regression |

## Key active claims

| Claim | Evidence |
|-------|---------|
| Zero `sorry`/`axiom` in production proof surface | `./scripts/test_tier0_hygiene.sh` |
| All 14 performance findings closed (WS-G) | `./scripts/test_full.sh` |
| IPC dual-queue structural invariant with 13 preservation theorems | `./scripts/test_full.sh` (Tier 3 anchors) |
| README/spec/GitBook metrics synchronized from single script | `./scripts/report_current_state.py` |
| Root docs and GitBook mirrors stay synchronized | `./scripts/test_docs_sync.sh` |
| Executable behavior is fixture-backed and malformed-state safe | `./scripts/test_tier2_trace.sh` + `test_tier2_negative.sh` |
| 17 inter-transition invariant assertions across all trace functions (WS-I1/R-01) | `./scripts/test_smoke.sh` |
| Mandatory determinism: trace output identical across runs (WS-I1/R-02) | `./scripts/test_tier2_determinism.sh` |
| 121 trace lines tagged with unique scenario IDs; registry validated bidirectionally (WS-I1/R-03) | `./scripts/test_tier0_hygiene.sh` + `test_tier2_trace.sh` |
| WS-I3 operations coverage expansion: six operation-chain tests + scheduler stress + declassification runtime checks (including distinct `declassificationDenied` policy-denial path) | `./scripts/test_tier2_negative.sh` |
| WS-L IPC subsystem audit — PORTFOLIO COMPLETE (v0.16.9–v0.16.13) | `./scripts/test_full.sh` |
| WS-M Capability subsystem audit — Phase 1 COMPLETED (v0.16.14), 4 phases remaining | [Workstream plan](../audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md) |

## Proof claim qualification

The index distinguishes six categories of proof:

| Category | Assurance |
|----------|-----------|
| **Substantive preservation** | High — proves successful operation preserves invariant over changed state |
| **Error-case preservation** | Low — trivially true (failed op returns unchanged state) |
| **Compositional preservation** | High — derives post-state via transfer lemmas |
| **Structural invariant** | High — proves genuine structural property with witness |
| **End-to-end chain** | High — multi-step semantic property across subsystem boundaries |
| **Non-interference** | Critical — proves high-domain operation preserves low-equivalence |

## Update policy

When a claim changes:

1. Update the canonical root document ([`CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md)) first.
2. Update GitBook mirrors in the same PR.
3. Run `./scripts/test_smoke.sh` (minimum); `./scripts/test_full.sh` when Tier 3 anchors change.

## Related

- [Testing & CI](07-testing-and-ci.md) — tier definitions and quality gates
- [Proof and Invariant Map](12-proof-and-invariant-map.md) — theorem inventory
