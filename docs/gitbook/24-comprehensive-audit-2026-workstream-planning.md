# v0.12.2 Audit Remediation (WS-F)

This chapter is a concise mirror of the canonical workstream plan. For full detail:
[`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).

## Findings baseline

Two independent audits of the v0.12.2 codebase:
- [Executive summary (v1)](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) — 6 CRIT, 8 HIGH, 8 MED, 9 LOW
- [Detailed audit (v2)](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) — 28 classified findings (F-01..F-28)

## Workstream summary

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F1** | IPC message transfer + dual-queue verification | Critical | **Completed** |
| **WS-F2** | Untyped memory model | Critical | **Completed** |
| **WS-F3** | Information-flow completeness | High | **Completed** |
| **WS-F4** | Proof gap closure (timerTick, cspaceMutate, notifications) | High | **Completed** |
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | **Completed** |
| **WS-F6** | Invariant quality (tautology reclassification, adapter hooks) | Medium | **Completed** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | Planned |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | Planned |

## Execution phases

| Phase | Workstreams | Description | Status |
|-------|-------------|-------------|--------|
| ~~**P0**~~ | — | Publish WS-F backbone, update docs | **Done** |
| ~~**P1**~~ | WS-F1, WS-F2, WS-F4 | Critical IPC/memory + proof gaps | **Completed** |
| ~~**P2**~~ | WS-F3 | Info-flow completeness | **Completed** |
| ~~**P3**~~ | ~~WS-F5, WS-F6~~ | ~~Model fidelity + invariant quality~~ | **Completed** |
| **P4** | WS-F7, WS-F8 | Testing + cleanup | Planned |

## Related: WS-G (completed)

The WS-G kernel performance optimization portfolio (v0.12.6–v0.12.15) was
completed between WS-F1..F4 and the remaining WS-F7..F8 workstreams.
See [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md).

## Prior completed portfolios

- **WS-G** (v0.12.15): WS-G1..G9 all completed (14 performance findings closed).
  See [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).
- **WS-E** (v0.11.6): WS-E1..E6 all completed.
  See [`AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).
- **WS-D** (v0.11.0): WS-D1..D4 completed.
  See [`AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).
