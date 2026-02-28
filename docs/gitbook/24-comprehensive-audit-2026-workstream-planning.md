# v0.12.2 Audit Workstream Planning (WS-F)

This chapter is a concise mirror of the canonical workstream plan. For full detail:
[`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).

## Findings baseline

Two independent audits of the v0.12.2 codebase:
- [Executive summary (v1)](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) — 6 CRIT, 8 HIGH, 8 MED, 9 LOW
- [Detailed audit (v2)](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) — 28 classified findings (F-01..F-28)

## Workstream summary

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F1** | IPC message transfer + dual-queue verification | Critical | Planning |
| **WS-F2** | Untyped memory model | Critical | Planning |
| **WS-F3** | Information-flow completeness | High | Planning |
| **WS-F4** | Proof gap closure (timerTick, cspaceMutate, notifications) | High | Planning |
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | Planning |
| **WS-F6** | Invariant quality (tautology reclassification, adapter hooks) | Medium | Planning |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | Planning |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | Planning |

## Execution phases

| Phase | Workstreams | Description |
|-------|-------------|-------------|
| **P0** | — | Publish WS-F backbone, update docs |
| **P1** | WS-F1, WS-F2, WS-F4 | Critical IPC/memory + proof gaps (parallel) |
| **P2** | WS-F3 | Info-flow completeness (after WS-F1 IPC) |
| **P3** | WS-F5, WS-F6 | Model fidelity + invariant quality |
| **P4** | WS-F7, WS-F8 | Testing + cleanup |

## Prior completed portfolios

- **WS-E** (v0.11.6): WS-E1..E6 all completed.
  See [`AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).
- **WS-D** (v0.11.0): WS-D1..D4 completed.
  See [`AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).
