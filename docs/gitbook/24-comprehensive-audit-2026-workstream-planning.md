# Comprehensive Audit 2026 Workstream Planning

Canonical planning source:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

Tracked proof obligations source:
[`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md).

This chapter is intentionally concise and navigational. It summarizes active workstream status and points to canonical details.

## 1) Active planning baseline

- **Findings baseline:** `AUDIT_v0.9.32.md`
- **Execution baseline:** `AUDIT_v0.9.32_WORKSTREAM_PLAN.md`
- **Tracked theorem obligations:** `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`
- **Current planning stage:** Phase P0/P1 transition (documentation baseline reset complete/in progress, and execution is beginning on current correctness-blocker workstreams).

## 2) Active workstreams (WS-C portfolio)

### Critical/high correctness and assurance

- **WS-C1:** IPC handshake correctness (critical; completed — notification badge OR accumulation + waiter ipcState transitions validated)
- **WS-C2:** Scheduler semantic fidelity (high, completed)
- **WS-C3:** Proof-surface de-tautologization (critical; execution beginning)
  - remove tautological `vspaceLookup_deterministic` and `projectState_deterministic`,
  - add module docstrings clarifying determinism as a meta-property of pure Lean,
  - track replacement theorem obligations in `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
- **WS-C4:** Test validity hardening (high; execution beginning)
- **WS-C5:** Information-flow assurance (critical)

### Platform and sustainability

- **WS-C6:** CI and supply-chain hardening (medium)
- **WS-C7:** Model structure and maintainability (medium)
- **WS-C8:** Documentation and GitBook consolidation (high, in progress)

## 3) Updating status

When any WS-C status changes, update all of the following in the same PR:

1. `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` (canonical source)
2. `docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md` (if theorem obligations/status changed)
3. `README.md` (current state + quick index)
4. `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`
5. this chapter (`24-comprehensive-audit-2026-workstream-planning.md`)

## 4) Historical references

The WS-B portfolio (`AUDIT_v0.9.0_WORKSTREAM_PLAN.md`) is retained for provenance and completed-history context only; it is no longer the active planning baseline.
