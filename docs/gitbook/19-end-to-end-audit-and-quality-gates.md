# End-to-End Audit and Quality Gates

This chapter summarizes the current audit posture and quality gate framework.

## 1. Active audit baseline

Two independent audits of the v0.12.2 codebase serve as the active findings baseline:

- [Executive summary (v1)](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) — high-level proof soundness, critical gaps, recommendations.
- [Detailed audit (v2)](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) — subsystem-by-subsystem analysis, 28 classified findings.

For the execution plan: [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).

Prior audits (v0.8.0–v0.11.6) are archived in [`docs/dev_history/audits/`](../dev_history/audits/)
and [`docs/audits/`](../audits/README.md).

## 2. Current quality state

seLe4n v0.13.1 has:

- **Zero sorry/axiom** in the production proof surface — fully machine-checked.
- **752 theorem/lemma declarations** across 7 kernel subsystems.
- **O(1) hash-based data structures** for all kernel hot paths (WS-G, 14 findings closed).
- **Tiered CI** with 4 validation tiers plus security scanning.
- **Comprehensive negative-state testing** with per-mutation invariant checking.
- **Phase 1–2 correctness fixes** (WS-H1..H5): IPC call-path semantic bug fixed, lifecycle safety guards, build/CI infrastructure hardened, capability invariant redesign, IPC dual-queue structural invariant.

Critical audit gaps (all resolved by WS-F1..F4):

- ~~IPC operations transfer scheduling state but not message data (CRIT-01).~~ **RESOLVED** (WS-F1)
- ~~No Untyped memory model (CRIT-04).~~ **RESOLVED** (WS-F2)
- ~~Information-flow covers 5 of 30+ operations (CRIT-03).~~ **RESOLVED** (WS-F3) — extended to 12+ operations with 15 NI theorems.
- ~~Dual-queue IPC model has zero formal proofs (CRIT-05/F-10).~~ **RESOLVED** (WS-F1)

Remaining medium/low findings (WS-F5..F8): model fidelity, invariant quality,
testing expansion, cleanup.

## 3. Quality gates

| Tier | Gate | What it validates |
|------|------|-------------------|
| **0** | Hygiene | No sorry/axiom, SHA-pinning, fixture isolation, shellcheck |
| **1** | Build | Full `lake build` compilation (84 jobs) |
| **2** | Trace + Negative | Fixture-diff trace + corruption testing + information-flow suite |
| **3** | Invariant surface | 300+ symbol/doc anchor presence checks |
| **4** | Nightly | Determinism replay + stochastic probe |

Commands:
```bash
./scripts/test_fast.sh      # Tier 0+1
./scripts/test_smoke.sh     # Tier 0-2
./scripts/test_full.sh      # Tier 0-3
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Tier 0-4
```

## 4. Coverage interpretation

"Full coverage" means closure of quality obligations, not a single metric:

- Theorem/invariant surface anchor coverage (Tier 3).
- Build/typing closure (Tier 1).
- Executable semantic fixture coverage (Tier 2).
- Negative/adversarial failure-path sensitivity (Tier 2).
- Deterministic replay evidence (Tier 4).

## 5. Audit lineage

| Version | Portfolio | Status |
|---------|-----------|--------|
| v0.12.15 | WS-H | Phase 1–3 **Completed** (WS-H1..H5: IPC fix, lifecycle guards, CI hardening, capability invariant redesign, dual-queue structural invariant); Phase 4–5 pending |
| v0.12.5 | WS-G | **Completed** — all 9 workstreams, 14 performance findings closed |
| v0.12.2 | WS-F | WS-F1..F4 completed; **WS-F5..F8 remaining** |
| v0.11.6 | WS-E | Completed (WS-E1..E6) |
| v0.11.0 | WS-D | Completed (WS-D1..D4) |
| v0.9.32 | WS-C | Completed (WS-C1..C8) |
| v0.9.0 | WS-B | Completed (WS-B1..B11) |
