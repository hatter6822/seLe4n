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

Current state: 54,573 lines of production Lean across 98 files, 7,309 lines across 10 Lean test suites,
1,660 theorem/lemma declarations, zero unsound constructs.
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

### Completed audit portfolios

| Portfolio | Scope | Status |
|-----------|-------|--------|
| **WS-H14** (v0.14.6) | Type safety & Prelude foundations: `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness, identifier roundtrip/injectivity, `OfNat` removal, sentinel completion. Closes A-02, A-01, A-03, A-04/M-11, A-06, M-09, M-10 | Completed |
| **Module restructuring** (v0.14.5) | 9 monolithic files decomposed into 24 focused submodules via re-export hub pattern; 15 private defs tightened; 209 Tier 3 anchor checks updated. Zero sorry/axiom | Completed |
| **WS-H13** (v0.14.4) | CSpace/service model enrichment: multi-level CSpace resolution, backing-object verification, `serviceCountBounded`. Closes H-01, A-21, A-29, A-30, M-17/A-31 | Completed |
| **WS-H12f** (v0.14.3) | Test harness update & documentation sync: 3 new trace scenarios, fixture update, 9 new Tier 3 anchors. Completes WS-H12 composite workstream | Completed |
| **WS-H12e** (v0.14.2) | Cross-subsystem invariant reconciliation: `coreIpcInvariantBundle` upgraded to `ipcInvariantFull`, `schedulerInvariantBundleFull` extended with `contextMatchesCurrent`, `ipcSchedulerCouplingInvariantBundle` extended with register-context and dequeue coherence, `proofLayerInvariantBundle` uses full scheduler bundle, all preservation proofs updated. Closes systemic invariant composition gaps from WS-H12a–d | Completed |
| **WS-H12d** (v0.14.1) | IPC message payload bounds: `IpcMessage` registers/caps migrated to `Array` with `maxMessageRegisters`(120)/`maxExtraCaps`(3), bounds enforcement at all 4 send boundaries, `allPendingMessagesBounded` system invariant. Closes A-09 | Completed |
| **WS-H12c** (v0.14.0) | Per-TCB register context with inline context switch: `registerContext` field on TCB, inline `saveOutgoingContext`/`restoreIncomingContext` in `schedule`, `contextMatchesCurrent` invariant with preservation proofs for scheduler and IPC operations, IF projection stripping. Closes H-03 | Completed |
| **WS-H12b** (v0.13.9) | Dequeue-on-dispatch scheduler semantics: `queueCurrentConsistent` inverted to `current ∉ runnable` matching seL4's `switchToThread`/`tcbSchedDequeue`; schedule/handleYield/timerTick/switchDomain updated; `currentTimeSlicePositive` and `schedulerPriorityMatch` predicates; IPC coherence predicates; ~1800 lines of proofs re-proved. Closes H-04 | Completed |
| **WS-H12a** (v0.13.8) | Legacy endpoint removal: `EndpointState` deleted, legacy IPC ops removed, ~60 dead theorems cleaned, `endpointReplyRecv` migrated to dual-queue. Closes A-08, M-01, A-25 | Completed |
| **WS-H11** (v0.13.7) | VSpace & architecture enrichment: PagePermissions with W^X enforcement, ARM64 52-bit address bounds, TLB model with per-VAddr flush and cross-ASID isolation, VSpaceBackend typeclass. Closes H-02/A-32, H-10, A-05/M-12, A-12, M-14 | Completed |
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

**WS-Q** (Kernel State Architecture) is **PORTFOLIO COMPLETE** (v0.17.7–v0.17.14) —
all 9 phases delivered: Q1 service interface simplification, Q2 universal RHTable
migration, Q3 IntermediateState formalization, Q4 CNode radix tree, Q5 FrozenSystemState +
freeze, Q6 freeze correctness proofs, Q7 frozen kernel operations, Q8 Rust syscall
wrappers, Q9 integration testing + documentation.

**WS-R** (Comprehensive Audit Remediation) is the **active workstream** — 8 phases
(R1–R8), 111 sub-tasks addressing all 82 findings from the pre-release audit.
R1–R8 complete (v0.18.0–v0.18.7).
After WS-R: **Raspberry Pi 5 hardware binding (H3)**.

See [Specification & Roadmap](05-specification-and-roadmap.md) and
[WS-R workstream plan](../dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).

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
- Active workstream plan: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md) (WS-R)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
