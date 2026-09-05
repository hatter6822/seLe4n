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

Current state (as of v0.33.101): 286,841 lines of production Lean across 286 files, 64,078 lines across 69 Lean test suites,
9,601 theorem/lemma declarations, zero unsound constructs.
Metrics source: [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key).

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

### Where the project is

Phases SM0–SM9 of the SMP multi-core workstream have landed: foundational SMP
types and the lock hierarchy, the Rust HAL bring-up, verified lock primitives,
per-object locks, per-core scheduler state and scheduling, cross-core IPC, TLB
shootdown and cache maintenance, SMP information flow, and declassification.
The syscall return ABI is complete.

**SM10 — release closure at v1.0.0 — is blocked on WS-RR**, the pre-1.0
remediation phase now in flight: 187 sub-tasks across nine phases, of which
RR0–RR6 have landed — most recently the boot-path fail-open closure (v0.34.48)
and the verified lock primitives (v0.34.50), which made the deployed
reader-writer lock the ticket-FIFO one the Lean spec describes and refined it
to that spec before the switch. The remaining phases sweep the
medium-severity findings and hand off to SM10.

**WS-LC** runs ahead of RR7 and closes the two lock **datatype** residuals
RR6 re-registered rather than absorbed. LC1 (v0.34.51) added the abstract
withdrawal — a queued core may take its request back — with all five
reader-writer invariants preserved and the liveness results that conclude
"becomes the holder" restated under an explicit no-withdrawal window. The
deployed lock cannot withdraw yet, and no bound on that surface is denominated
in time; both are open phases of the same plan.

**The kernel does not boot yet.** Producing a bootable image is SM10.1's work;
until it lands, every runtime seam behind the per-core readiness gate is wired
and dormant. What the project does and does not claim is enumerated in
[`CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md), including a table of
what is *not* claimed and who owns each gap.

| For | Read |
|-----|------|
| What changed in a version | [`CHANGELOG.md`](../../CHANGELOG.md) |
| What is deferred, and who owns it | [`REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) |
| What a phase is scheduled to do | [`docs/planning/`](../planning/) |
| How to build, test and contribute | [`DEVELOPMENT.md`](../DEVELOPMENT.md) |

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
- Registered debt: [`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
