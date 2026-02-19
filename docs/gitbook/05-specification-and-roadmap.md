# Specification and Roadmap

This chapter is the GitBook-facing translation of the normative project spec in
[`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md). For the original seL4 microkernel
specification, see [`docs/spec/SEL4_SPEC.md`](../spec/SEL4_SPEC.md).

## 1) Status snapshot

Current milestone state:

- M4-A complete
- M4-B complete
- M5 complete
- M6 complete
- M7 complete
- **Active:** Comprehensive Audit v0.9.32 WS-C execution (WS-C1 + WS-C2 + WS-C3 + WS-C4 + WS-C5 + WS-C6 + WS-C7 + WS-C8 complete)

## 2) Stable contracts contributors must preserve

1. deterministic kernel transition behavior,
2. layered invariants + preservation theorem continuity,
3. architecture-boundary assumption/adapter interfaces from M6,
4. fixture-backed executable evidence,
5. tiered testing gates used in CI and local workflows.

## 3) Active workstream portfolio (WS-C)

- WS-C1: IPC handshake correctness (critical; completed for notification badge accumulation and waiter ipcState wiring)
- WS-C2: Scheduler semantic fidelity (high; completed)
- WS-C3: Proof-surface de-tautologization (critical; completed)
- WS-C4: Test validity hardening (high; completed)
- WS-C5: Information-flow assurance (critical; completed — observer-scoped service projection + endpoint-send low-equivalence preservation theorem)
- WS-C6: CI and supply-chain hardening (medium; completed)
- WS-C7: Model structure and maintainability (medium; completed)
- WS-C8: Documentation and GitBook consolidation (high; completed)

Canonical execution plan:
[Comprehensive Audit 2026 Workstream Planning](24-comprehensive-audit-2026-workstream-planning.md).

Security baseline reference:
[Threat Model and Security Hardening](28-threat-model-and-security-hardening.md).

## 4) Sequencing model

- **Phase P0:** WS-C8 baseline reset + active-plan publication (completed)
- **Phase P1:** WS-C4 fixture-repair completion (WS-C1 + WS-C2 + WS-C3 + WS-C4 complete)
- **Phase P2:** WS-C5 assurance expansion (completed)
- **Phase P3:** WS-C7 sustainment hardening (completed)

## 5) Historical context

WS-B and earlier slice chapters remain valuable references for delivered patterns,
but are archival in status. Use them for precedent, not active scope ownership.

## 6) M6 closeout continuity note

- WS-M6-D and WS-M6-E complete.
- WS-M6-E: documentation synchronization and handoff packaging ✅ completed.
