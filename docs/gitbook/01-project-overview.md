# Project Overview

## 1. What is seLe4n?

seLe4n is a **production-oriented microkernel** built from the ground up in Lean 4.
Every kernel transition is an executable pure function. Every invariant is
machine-checked — zero `sorry`, zero `axiom` across the entire production proof surface.

The project began as a formalization of seL4 semantics and is now a novel kernel
that preserves seL4's capability-based security model while introducing improvements
that the Lean 4 proof framework enables.

**First hardware target: Raspberry Pi 5 (ARM64).**

## 2. Why this project matters

Most kernel verification efforts work backward — write C, then verify it. seLe4n
works forward: executable semantics and proofs are developed together, and the
kernel *is* the specification. This eliminates the verification gap between
specification and implementation.

Current state: 21,340 lines of Lean across 40 modules, 575 machine-checked theorems, zero unsound
constructs, comprehensive tiered CI with security scanning.

## 3. Architectural improvements over seL4

| Area | seL4 | seLe4n |
|------|------|--------|
| **Service lifecycle** | No kernel-level concept | Dependency graphs with acyclic enforcement |
| **CDT** | Mutable doubly-linked list | Node-stable with O(1) slot transfer |
| **IPC queuing** | Intrusive linked list | Dual-queue with O(1) arbitrary removal |
| **Information flow** | Binary partition | Parameterized N-domain labels |
| **Scheduling** | Priority round-robin | Priority + EDF with domain partitioning |
| **Revocation** | Silent error handling | Strict variant with failure context reporting |

## 4. What is implemented today

### Completed milestone slices

Bootstrap, M1 (scheduler), M2 (capability), M3/M3.5 (IPC + coherence),
M4-A/M4-B (lifecycle), M5 (service graph), M6 (architecture boundary),
M7 (audit remediation).

### Completed audit portfolios

| Portfolio | Scope | Status |
|-----------|-------|--------|
| **WS-H3** (v0.12.17) | Build/CI infrastructure fixes: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | Completed |
| **WS-H2** (v0.12.16) | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, CNode CDT detach, atomic retype | Completed |
| **WS-H1** (v0.12.16) | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct contract predicates | Completed |
| **WS-G** (v0.12.15) | Kernel performance: O(1) hash-based data structures for all hot paths | All 9 workstreams completed |
| **WS-F1..F4** (v0.12.2) | Critical audit remediation: IPC messages, untyped memory, info-flow, proof gaps | All 4 completed |
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, info-flow | All 6 completed |
| **WS-D** (v0.11.0), **WS-C** (v0.9.32), **WS-B** (v0.9.0) | Earlier audit portfolios | All completed |

### What's next

The immediate next steps are completing the remaining WS-F workstreams (F5–F8),
which address medium/low-priority findings from the v0.12.2 audits:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

After WS-F: Raspberry Pi 5 hardware binding (H3).
See [Next Development Path](22-next-slice-development-path.md) and
[v0.12.2 Audit Remediation](24-comprehensive-audit-2026-workstream-planning.md).

## 5. Architecture mental model

```
┌─────────────────────────────────────────────────────┐
│  Kernel API  (SeLe4n/Kernel/API.lean)               │
├────────┬────────┬──────┬───────────┬────────────────┤
│Sched   │Capabil │ IPC  │ Lifecycle │ Service (ext)  │
│ uler   │  ity   │      │           │                │
├────────┴────────┴──────┴───────────┴────────────────┤
│  Information Flow  (Policy, Projection, Enforcement) │
├─────────────────────────────────────────────────────┤
│  Architecture  (VSpace, Adapter, Assumptions)        │
├─────────────────────────────────────────────────────┤
│  Model  (Object, State, CDT)                         │
├─────────────────────────────────────────────────────┤
│  Foundations  (Prelude, Machine)                      │
└─────────────────────────────────────────────────────┘
```

Each subsystem follows the **Operations/Invariant split**: executable transitions
in `Operations.lean`, machine-checked proofs in `Invariant.lean`.

## 6. Contributor definition-of-done loop

For milestone-moving changes:

1. implement transition semantics,
2. add/refine invariant components,
3. prove local preservation,
4. prove composed preservation,
5. expose behavior in executable traces,
6. add symbol/fixture anchors in tests,
7. synchronize spec, README, and GitBook docs.

## 7. Key links

- Project specification: [`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md)
- seL4 reference: [`docs/spec/SEL4_SPEC.md`](../spec/SEL4_SPEC.md)
- Performance optimization: [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
- Audit findings: [`AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md)
- Next workstream plan: [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) (WS-F5..F8)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
