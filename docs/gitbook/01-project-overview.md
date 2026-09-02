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
remediation phase now in flight: 184 sub-tasks across nine phases, of which
RR0–RR4 have landed. The remaining phases close the boot-path fail-open
latents, complete the verified lock primitives, and sweep the medium-severity
findings.

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
