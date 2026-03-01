# End-to-End Audit and Quality Gates

This chapter summarizes the current audit posture and quality gate framework.

## 1. Active audit baseline

Three audit documents form the active baseline:

- [Hardware readiness audit (v0.12.5)](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md) — H3 readiness assessment, WS-G workstream planning, 8 findings for hardware binding.
- [Executive summary (v1)](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) — high-level proof soundness, critical gaps, recommendations.
- [Detailed audit (v2)](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) — subsystem-by-subsystem analysis, 28 classified findings.

For the WS-F execution plan: [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).

Prior audits (v0.8.0–v0.11.6) are archived in [`docs/dev_history/audits/`](../dev_history/audits/)
and [`docs/audits/`](../audits/README.md).

## 2. Current quality state

seLe4n v0.12.5 has:

- **Zero sorry/axiom** in the production proof surface — fully machine-checked.
- **522 proved theorems** across 7 kernel subsystems.
- **Tiered CI** with 4 validation tiers plus security scanning.
- **Comprehensive negative-state testing** with per-mutation invariant checking.
- **All WS-F audit findings resolved** — H2 complete, H3 ready to begin.

All critical gaps resolved:

- ~~IPC operations transfer scheduling state but not message data (CRIT-01).~~ **RESOLVED** (WS-F1)
- ~~No Untyped memory model (CRIT-04).~~ **RESOLVED** (WS-F2)
- ~~Information-flow covers 5 of 30+ operations (CRIT-03).~~ **RESOLVED** (WS-F3) — extended to 12+ operations with 15 NI theorems.
- ~~Dual-queue IPC model has zero formal proofs (CRIT-05/F-10).~~ **RESOLVED** (WS-F1)
- ~~Proof gaps for timerTick, cspaceMutate, notifications (F-03, F-06, F-12).~~ **RESOLVED** (WS-F4)

## 3. Quality gates

| Tier | Gate | What it validates |
|------|------|-------------------|
| **0** | Hygiene | No sorry/axiom, SHA-pinning, fixture isolation, shellcheck |
| **1** | Build | Full `lake build` compilation (64 jobs) |
| **2** | Trace + Negative | Fixture-diff trace (80 expectations) + corruption testing |
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
| v0.12.5 | Hardware readiness | **Complete** — H3 ready, WS-G planned |
| v0.12.2 | WS-F | **Complete** — WS-F1..F4 all completed |
| v0.11.6 | WS-E | Completed (WS-E1..E6) |
| v0.11.0 | WS-D | Completed (WS-D1..D4) |
| v0.9.32 | WS-C | Completed (WS-C1..C8) |
| v0.9.0 | WS-B | Completed (WS-B1..B11) |
