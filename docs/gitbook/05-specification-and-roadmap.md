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
- **Active:** WS-D portfolio (v0.11.0 audit remediation) — WS-D1..WS-D4 completed; WS-D5..WS-D6 planned

## 2) Stable contracts contributors must preserve

1. deterministic kernel transition behavior,
2. layered invariants + preservation theorem continuity,
3. architecture-boundary assumption/adapter interfaces from M6,
4. fixture-backed executable evidence,
5. tiered testing gates used in CI and local workflows.

## 3) Active workstream portfolio (WS-D)

- **WS-D1:** Test error handling and validity (critical/high; **completed** — F-01, F-03, F-04)
- **WS-D2:** Information-flow enforcement and proof (high; **completed** — F-02, F-05)
- **WS-D3:** Proof gap closure (medium; **completed** — F-06, F-08, F-16)
- **WS-D4:** Kernel design hardening (medium; **completed** — F-07, F-11, F-12)
- **WS-D5:** Test infrastructure expansion (medium; **planned** — F-09, F-10)
- **WS-D6:** CI/CD and documentation polish (low; **planned** — F-13, F-14, F-15, F-17)

Canonical execution plan:
[v0.11.0 Audit Workstream Planning](32-v0.11.0-audit-workstream-planning.md).

Security baseline reference:
[Threat Model and Security Hardening](28-threat-model-and-security-hardening.md).

## 4) Sequencing model (WS-D)

- **Phase P0:** Baseline transition — publish v0.11.0 planning backbone, demote WS-C to historical (**completed**)
- **Phase P1:** WS-D1 test validity restoration (critical/high) — **completed**
- **Phase P2:** WS-D2 information-flow enforcement and proof expansion (high) — **completed**
- **Phase P3:** WS-D3 proof gap closure + WS-D4 kernel design hardening (medium) — **completed**
- **Phase P4:** WS-D5 test infrastructure expansion + WS-D6 CI/documentation polish (medium/low) — current

## 5) Historical context

WS-C (v0.9.32), WS-B (v0.9.0), and earlier slice chapters remain valuable references
for delivered patterns, but are archival in status. Use them for precedent, not active
scope ownership.

## 6) Completed audit portfolios (historical)

- **WS-C portfolio** (v0.9.32): WS-C1..WS-C8 completed.
- **WS-B portfolio** (v0.9.0): WS-B1..WS-B11 completed.
- **M6 closeout:** WS-M6-D and WS-M6-E complete.
