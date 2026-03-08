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

Current state: 29,249 lines of production Lean across 40 modules, 2,063 lines across 3 Lean test suites,
863 theorem/lemma declarations, zero unsound constructs, and a deterministic build surface of 84 jobs.

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
| **WS-H10** (v0.13.6) | Security model foundations: MachineState in ObservableState, BIBA lattice alternatives, declassification model, endpoint flow policy well-formedness. Closes C-05/A-38, A-34, A-39, M-16 | Completed |
| **WS-H7/H8/H9 gaps closed** (v0.13.5) | Comprehensive audit: BEq soundness lemmas, `endpointReceiveDualChecked_NI` bridge, 3 IPC NI theorems, NonInterferenceStep extended to 31 constructors | Completed |
| **WS-H9** (v0.13.4) | Non-interference coverage extension: 27 new NI theorems, NonInterferenceStep 28 constructors, >80% kernel operation coverage | Completed |
| **WS-H8** (v0.13.2) | Enforcement-NI bridge & missing wrappers: 5 enforcement soundness meta-theorems, 4 new `*Checked` wrappers, `ObservableState` domain timing metadata, NI bridge theorems. Closes A-35/H-07, A-36/A-37/H-11 | Completed |
| **WS-H6** (v0.13.1) | Scheduler proof completion: `timeSlicePositive` preservation for all 6 scheduler ops, EDF invariant domain-fix, candidate optimality, `schedulerInvariantBundleFull` 5-tuple bundle | Completed |
| **WS-H5** (v0.12.19) | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems. Closes C-04/A-22, A-23, A-24 | Completed |
| **WS-H4** (v0.12.18) | Capability invariant redesign: `capabilityInvariantBundle` extended from 4-tuple to 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`; all 25+ preservation theorems re-proved | Completed |
| **WS-H3** (v0.12.17) | Build/CI infrastructure fixes: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | Completed |
| **WS-H2** (v0.12.16) | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, CNode CDT detach, atomic retype | Completed |
| **WS-H1** (v0.12.16) | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct contract predicates | Completed |
| **WS-G** (v0.12.15) | Kernel performance: O(1) hash-based data structures for all hot paths | All 9 workstreams completed |
| **WS-F1..F4** (v0.12.2) | Critical audit remediation: IPC messages, untyped memory, info-flow, proof gaps | All 4 completed |
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, info-flow | All 6 completed |
| **WS-D** (v0.11.0), **WS-C** (v0.9.32), **WS-B** (v0.9.0) | Earlier audit portfolios | All completed |

### What's next

The immediate next steps are:

1. **WS-H10..H16** — Remaining v0.12.15 audit remediation workstreams (Phases 4-5):
   security model foundations, VSpace enrichment, scheduler/IPC semantic alignment,
   CSpace/service model enrichment, type safety, platform hardening, testing expansion.
2. **Raspberry Pi 5 hardware binding** — ARM64 code generation and hardware bring-up.

See [Next Development Path](22-next-slice-development-path.md) and
[v0.12.15 Audit Workstream Plan](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

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
- Active workstream plan: [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) (WS-H10..H16)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
