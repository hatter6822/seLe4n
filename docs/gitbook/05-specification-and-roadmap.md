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
- WS-B portfolio (v0.9.0): all completed
- WS-C portfolio (v0.9.32): all completed
- WS-D portfolio (v0.11.0): WS-D1..WS-D4 completed; WS-D5/WS-D6 absorbed into WS-E
- **Active:** WS-E portfolio (v0.11.6 audit remediation) — WS-E1, WS-E2, WS-E3, WS-E4 completed; WS-E5..WS-E6 planned

## 2) Stable contracts contributors must preserve

1. deterministic kernel transition behavior,
2. layered invariants + preservation theorem continuity,
3. architecture-boundary assumption/adapter interfaces from M6,
4. fixture-backed executable evidence,
5. tiered testing gates used in CI and local workflows.

## 3) Active workstream portfolio (WS-E)

The WS-E portfolio is based on the v0.11.6 audit baseline. Prior WS-D5/WS-D6 scope has been absorbed.

Canonical execution plan:
[`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).

Security baseline reference:
[Threat Model and Security Hardening](28-threat-model-and-security-hardening.md).

### Completed WS-D portfolio (v0.11.0 — historical)

- **WS-D1:** Test error handling and validity (critical/high; **completed** — F-01, F-03, F-04)
- **WS-D2:** Information-flow enforcement and proof (high; **completed** — F-02, F-05)
- **WS-D3:** Proof gap closure (medium; **completed** — F-06, F-08, F-16)
- **WS-D4:** Kernel design hardening (medium; **completed** — F-07, F-11, F-12)
- **WS-D5/WS-D6:** Absorbed into WS-E portfolio

## 4) Sequencing model (WS-E)

- **Phase P0:** Baseline transition — publish v0.11.6 planning backbone, demote WS-D to historical — **completed**
- **Phase P1:** WS-E1 + WS-E2 (test/CI hardening + proof quality) — **completed**
- **Phase P2:** WS-E3 (kernel semantic hardening) — **completed**
- **Phase P3:** WS-E4 (capability/IPC completion) — **completed**
- **Phase P4:** WS-E5 (information-flow maturity) — **current**

See [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) for full WS-E phase sequencing.

### Historical WS-D sequencing (completed)

- **Phase P0:** Baseline transition — publish v0.11.0 planning backbone, demote WS-C to historical — **completed**
- **Phase P1:** WS-D1 test validity restoration (critical/high) — **completed**
- **Phase P2:** WS-D2 information-flow enforcement and proof expansion (high) — **completed**
- **Phase P3:** WS-D3 proof gap closure + WS-D4 kernel design hardening (medium) — **completed**
- **Phase P4:** WS-D5/WS-D6 — absorbed into WS-E portfolio

## 5) Historical context

WS-C (v0.9.32), WS-B (v0.9.0), and earlier slice chapters remain valuable references
for delivered patterns, but are archival in status. Use them for precedent, not active
scope ownership.

## 6) Completed audit portfolios (historical)

- **WS-D portfolio** (v0.11.0): WS-D1..WS-D4 completed; WS-D5/WS-D6 absorbed into WS-E.
- **WS-C portfolio** (v0.9.32): WS-C1..WS-C8 completed.
- **WS-B portfolio** (v0.9.0): WS-B1..WS-B11 completed.
- **M6 closeout:** WS-M6-D and WS-M6-E complete.
