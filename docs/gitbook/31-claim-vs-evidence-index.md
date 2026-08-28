# Claim vs Evidence Index

Canonical source: [`docs/CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md).

This chapter summarizes how seLe4n ties every public claim to executable or inspectable evidence. The canonical document contains the full claim table; this chapter explains the framework and highlights key claims.

### Purpose

Every claim in seLe4n documentation (README, spec, GitBook) must be backed by evidence that anyone can reproduce. The claim-evidence index maps each claim to:

1. **Canonical source** — where the claim is stated.
2. **Evidence command** — a script that validates the claim.
3. **Evidence artifact** — what the script checks or produces.

### How evidence works

| Evidence type | Example | Assurance level |
|---------------|---------|----------------|
| **Tier 0 hygiene scan** | `test_tier0_hygiene.sh` — no `sorry`/`axiom` in production files | High: forbidden-marker scan is exhaustive |
| **Tier 1 build** | `lake build` — all modules compile | High: Lean type-checker verifies proofs |
| **Tier 2 fixture** | `test_tier2_trace.sh` — runtime output matches locked fixture | Medium-High: covers exercised paths |
| **Tier 3 surface anchor** | `test_tier3_invariant_surface.sh` — named theorems still exist | High: prevents silent proof-surface regression |

## Active baseline claims

| Claim | Evidence |
|-------|---------|
| Zero `sorry`/`axiom` in production proof surface | `./scripts/test_tier0_hygiene.sh` |
| All 14 performance findings closed (WS-G) | `./scripts/test_full.sh` |
| IPC dual-queue structural invariant with 16 preservation theorems | `./scripts/test_full.sh` (Tier 3 anchors) |
| README/spec/GitBook metrics synchronized from single script | `./scripts/report_current_state.py` |
| Root docs and GitBook mirrors stay synchronized | `./scripts/test_docs_sync.sh` |
| Executable behavior is fixture-backed and malformed-state safe | `./scripts/test_tier2_trace.sh` + `test_tier2_negative.sh` |
| 38 inter-transition invariant assertions across all trace functions (WS-I1/R-01, V8-C) | `./scripts/test_smoke.sh` |
| Mandatory determinism: trace output identical across runs (WS-I1/R-02) | `./scripts/test_tier2_determinism.sh` |
| Trace lines tagged with unique scenario IDs (233 fixture lines at v0.33.101, 231 bracket-tagged); registry validated bidirectionally (WS-I1/R-03) | `./scripts/test_tier0_hygiene.sh` + `test_tier2_trace.sh` |
| WS-I3 operations coverage expansion: six operation-chain tests + scheduler stress + declassification runtime checks (including distinct `declassificationDenied` policy-denial path) | `./scripts/test_tier2_negative.sh` |
| WS-L IPC subsystem audit — PORTFOLIO COMPLETE (v0.16.9–v0.16.13) | `./scripts/test_full.sh` |
| WS-M Capability subsystem audit — PORTFOLIO COMPLETE (v0.16.14–v0.17.0) | `./scripts/test_full.sh` |
| WS-N Robin Hood hashing — PORTFOLIO COMPLETE (v0.17.0–v0.17.5) | `./scripts/test_full.sh` |
| WS-Q Kernel State Architecture — PORTFOLIO COMPLETE (v0.17.7–v0.17.14, 9 phases) | `./scripts/test_full.sh` |
| WS-R Comprehensive Audit Remediation — PORTFOLIO COMPLETE (R1–R8, v0.18.0–v0.18.7) | [Workstream plan](../dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md) |
| WS-S Pre-Benchmark Strengthening — PORTFOLIO COMPLETE (S1–S7, v0.19.0–v0.19.6) | [Workstream plan](../dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md) |
| WS-T Deep-Dive Audit Remediation — PORTFOLIO COMPLETE (T1–T8, v0.20.0–v0.20.7, 94 sub-tasks) | [Workstream plan](../dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md), [Closure report](../dev_history/audits/WS_T_CLOSURE_REPORT.md) |
| WS-U Phase U1 Correctness Fixes — COMPLETE (U1-A–U1-M, v0.21.0, 13 sub-tasks) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U2 Safety Boundary Hardening — COMPLETE (U2-A–U2-N, v0.21.1, 14 sub-tasks) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U3 Rust ABI Hardening — COMPLETE (U3-A–U3-J, v0.21.2, 10 sub-tasks) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U4 Proof Chain & Invariant Composition — COMPLETE (U4-A/B/C/D, U4-K, U4-N, v0.21.3) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U5 API & Dispatch Integrity — COMPLETE (U5-A–U5-N, v0.21.4, 14 sub-tasks) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U6 Architecture & Platform Fidelity — COMPLETE (v0.21.5) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U7 Dead Code & Proof Hygiene — COMPLETE (v0.21.6) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-U Phase U8 — COMPLETE (v0.21.7) | [Workstream plan](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-Z composable performance objects (SchedContext, CBS, donation, timeouts) — PORTFOLIO COMPLETE (v0.23.0–v0.23.21) | `./scripts/test_full.sh` (Tier 3 anchors) |
| WS-AB deferred operations + bounded latency (WCRT) — PORTFOLIO COMPLETE (v0.24.0–v0.25.5) | `lake exe liveness_suite` |
| WS-AG H3 hardware binding (HAL, GIC-400, timer, ARMv8 page tables, FFI bridge, QEMU) — PORTFOLIO COMPLETE (v0.26.0–v0.27.1) | `./scripts/test_rust.sh` |
| WS-AK / WS-AN audit-remediation portfolios — COMPLETE (through v0.30.11) | [Active audit baseline](../audits/AUDIT_v0.30.11_COMPREHENSIVE.md) |
| WS-RC pre-1.0 remediation R0–R5 — CLOSED at v0.31.2 (R6–R14 absorbed into WS-SM per SM0.Q) | [Workstream plan](../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md) |
| WS-RA syscall return ABI (exact seL4 ARM64 frame; `SYSCALL_ABI_VERSION = 2` pinned on both sides) — COMPLETE (v0.33.37–v0.33.38) | `./scripts/test_rust.sh` (ABI conformance suite) |
| WS-SM SM0–SM9 landed — verified lock primitives, per-object locks, per-core scheduler state, cross-core IPC, TLB shootdown + cache maintenance, SMP information flow, declassification completion (SM9 CLOSED v0.33.100); SM10 (release closure → v1.0.0) pending | Canonical per-phase rows in [`docs/CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md); golden fixtures under `tests/fixtures/` |
| Enforcement boundary: 43 entries (13 policy-gated), pinned by `enforcementBoundaryExtended_count`; per-core boundary 58 (`enforcementBoundaryPerCore_count`) | `./scripts/test_full.sh` (Tier 3 anchors) |

## Proof claim qualification (WS-D3/F-16, updated by v0.11.6 audit C-01/H-01; C-01/H-01 resolved by WS-E2)

The index distinguishes six categories of proof:

| Category | Assurance |
|----------|-----------|
| **Substantive preservation** | High — proves successful operation preserves invariant over changed state |
| **Error-case preservation** | Low — trivially true (failed op returns unchanged state) |
| **Compositional preservation** | High — derives post-state via transfer lemmas |
| **Structural invariant** | High — proves genuine structural property with witness |
| **End-to-end chain** | High — multi-step semantic property across subsystem boundaries |
| **Non-interference** | Critical — proves high-domain operation preserves low-equivalence |

## Closed proof obligations (WS-D tracked issues)

All WS-D tracked proof obligations have been resolved. See the canonical
[`CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md) for the full closure
table.

## Update policy

When a claim changes:

1. Update the canonical root document ([`CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md)) first.
2. Update GitBook mirrors in the same PR.
3. Run `./scripts/test_smoke.sh` (minimum); `./scripts/test_full.sh` when Tier 3 anchors change.

### Related

- [Testing & CI](07-testing-and-ci.md) — tier definitions and quality gates
- [Proof and Invariant Map](12-proof-and-invariant-map.md) — theorem inventory
