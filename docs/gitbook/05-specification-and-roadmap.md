# Specification and Roadmap

This chapter is the GitBook-facing translation of the normative spec in
[`docs/SEL4_SPEC.md`](../SEL4_SPEC.md).

## 1) Status snapshot

Current milestone state:

- M4-A complete
- M4-B complete
- M5 complete
- M6 complete
- M7 complete
- **Active:** Comprehensive Audit 2026-02 workstream execution (WS-B portfolio; WS-B1 completed)

## 2) Stable contracts contributors must preserve

1. deterministic kernel transition behavior,
2. layered invariants + preservation theorem continuity,
3. architecture-boundary assumption/adapter interfaces from M6,
4. fixture-backed executable evidence,
5. tiered testing gates used in CI and local workflows.

## 3) Active workstream portfolio (WS-B)

- WS-B1: VSpace + memory model foundation ✅ completed
- WS-B2: Generative + negative testing expansion
- WS-B3: Main trace harness refactor
- WS-B4: Remaining type-wrapper migration
- WS-B5: CSpace guard/radix completion
- WS-B6: Notification-object IPC completion
- WS-B7: Information-flow proof-track start
- WS-B8: Documentation automation + consolidation
- WS-B9: Threat model and security hardening
- WS-B10: CI maturity upgrades
- WS-B11: Scenario framework finalization

Canonical execution plan:
[Comprehensive Audit 2026 Workstream Planning](24-comprehensive-audit-2026-workstream-planning.md).

## 4) Sequencing model

- **Phase P1:** WS-B4 + WS-B3 + WS-B8
- **Phase P2:** WS-B5 + WS-B6 + WS-B2 (WS-B1 complete)
- **Phase P3:** WS-B7 + WS-B9 + WS-B10 + WS-B11

## 5) Historical context

M7 and earlier slice chapters remain valuable references for delivered patterns,
but are archival in status. Use them for precedent, not active scope ownership.


## 6) M6 closeout continuity note

- WS-M6-D and WS-M6-E complete.
- WS-M6-E: documentation synchronization and handoff packaging ✅ completed.
