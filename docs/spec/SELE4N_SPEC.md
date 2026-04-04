# seLe4n Project Specification

This document defines the normative scope, milestone structure, active workstream
portfolio, and acceptance criteria for **seLe4n** — a production-oriented microkernel
written in Lean 4 with machine-checked proofs, improving on seL4 architecture.

For the reference specification of the original seL4 microkernel that seLe4n builds on,
see [`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md).

---

## Table of Contents

1. [Project Identity](#1-project-identity)
2. [Current State Snapshot](#2-current-state-snapshot)
3. [Milestone History](#3-milestone-history)
4. [Architectural Improvements over seL4](#4-architectural-improvements-over-sel4)
5. [Completed Workstream Portfolio (WS-G) and Next Steps](#5-completed-workstream-portfolio-ws-g-and-next-steps)
6. [Hardware Target: Raspberry Pi 5](#6-hardware-target-raspberry-pi-5)
7. [Acceptance Expectations](#7-acceptance-expectations)
8. [Model Fidelity & Type Safety (WS-S Phase S4)](#8-model-fidelity--type-safety-ws-s-phase-s4)
9. [Non-Negotiable Baseline Contracts](#9-non-negotiable-baseline-contracts)
10. [Audit Baselines](#10-audit-baselines)
11. [Security and Threat Model](#11-security-and-threat-model)

---

## 1. Project Identity

**seLe4n** is a novel microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked — zero
`sorry`, zero `axiom` across the entire production proof surface.

The project keeps four concerns in one engineering loop:

1. deterministic transition semantics (executable pure functions),
2. machine-checked invariant preservation (2,341 theorem/lemma declarations),
3. architectural improvements over seL4 where the proof framework enables them,
4. milestone-oriented delivery toward production on **Raspberry Pi 5** (ARM64).

The project began as a formalization of seL4 semantics and is now a production-oriented
kernel that preserves seL4's capability-based security model while introducing novel
improvements in service orchestration, capability management, IPC queuing, information-flow
enforcement, and scheduling.

---

## 2. Current State Snapshot

| Attribute | Value |
|-----------|-------|
| **Package version** | `0.24.3` (`lakefile.toml`) |
| **Lean toolchain** | `v4.28.0` (`lean-toolchain`) |
| **Production LoC** | 81,299 across 118 Lean files |
| **Test LoC** | 10,058 across 13 Lean test suites |
| **Proved declarations** | 2,341 theorem/lemma declarations (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_v0.22.17_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md) — pre-release audit remediation (4 CRIT, 9 HIGH, 9 MED, 2 LOW) |
| **Active workstream** | **WS-AB Deferred Operations** — Phase D1 COMPLETE (v0.24.0–v0.24.1): Thread Suspension & Resumption. Phase D2 COMPLETE (v0.24.1): Priority Management. Phase D3 COMPLETE (v0.24.2–v0.24.3): IPC Buffer Configuration. Plan: [`WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md`](../planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md). Prior: WS-Z (v0.23.0–v0.23.19), WS-AA (v0.23.21–v0.23.23), WS-Y–WS-B — all COMPLETE. |
| **Workstream history** | [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) |
| **Metrics source of truth** | [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key) |
| **Codebase map** | `docs/codebase_map.json` (generated via `./scripts/generate_codebase_map.py --pretty`; validated with `--check`; auto-refreshed on `main` by `.github/workflows/codebase_map_sync.yml`) |

---

## 3. Milestone History

seLe4n has been developed through incremental milestone slices, each building on the
semantic and proof foundations of the previous one.

### 3.1 Completed Milestone Slices

| Milestone | Scope | Status |
|-----------|-------|--------|
| **Bootstrap** | Typed identifiers, monad foundations, machine state | Complete |
| **M1** | Scheduler semantics and preservation theorems | Complete |
| **M2** | Capability/CSpace operations + authority invariants | Complete |
| **M3** | IPC seed semantics | Complete |
| **M3.5** | Waiting handshake + scheduler coherence | Complete |
| **M4-A** | Lifecycle/retype foundations | Complete |
| **M4-B** | Lifecycle-capability composition hardening | Complete |
| **M5** | Service-graph and policy-surface completion | Complete |
| **M6** | Architecture-boundary assumptions/adapters/invariant hooks | Complete |
| **M7** | Audit remediation WS-A1..WS-A8 | Complete |

### 3.2 Completed Audit Portfolios

| Portfolio | Scope | Workstreams |
|-----------|-------|-------------|
| **WS-S** (v0.19.0–v0.19.6) | Pre-Benchmark Strengthening: 7 phases (S1–S7), 83 sub-tasks addressing 115+ findings from dual v0.18.7 audits. Security boundary hardening, Rust type safety, test hardening, proof surface closure (CDT maps consistency, RunQueue well-formedness, SecurityLabel lattice), model fidelity (capacity enforcement, typed IPC registers, alignment predicates), API cleanup (removed deprecated wrappers, SimRestrictive platform), hardware preparation (WithFlush VSpace, memory scrubbing, DeviceTree abstraction), documentation & polish. 5 High, 29 Medium, 19 Low findings resolved. Zero sorry/axiom | WS-S completed |
| **WS-R8** (v0.18.7) | Infrastructure & CI hardening: elan binary pinning with SHA-256, PR-based codebase map workflow, Rust test skip annotation, compiled test suite execution, Rust newtype encapsulation | WS-R8 completed |
| **WS-R7** (v0.18.6) | Architecture & hardware preparation: `TlbState` integrated into `SystemState`, `tlbConsistent` added to `proofLayerInvariantBundle` (M-17); TLB-flushing VSpace wrappers with preservation proofs; `RegName.isValid` ARM64 GPR bounds (L-02); `isWord64` predicate + `machineWordBounded` invariant for 64-bit value bounds (L-03); TCB `faultHandler`/`boundNotification` for seL4 fidelity (L-06); `KernelObjectType` enum replacing raw `Nat` in `LifecycleRetypeArgs` with typed decode boundary (L-10) | WS-R7 completed |
| **WS-R6** (v0.18.5) | Model & frozen state correctness: `apiInvariantBundle_frozenDirect` freeze-time equivalence, badge deprecation, `RegisterFile` BEq, scheduler bundle extension with `schedulerPriorityMatch`, all preservation proofs sorry-free | WS-R6 completed |
| **WS-R5** (v0.18.4) | Information flow completion: internalized IPC NI, service NI, content-aware memory projection | WS-R5 completed |
| **WS-R1–R4** (v0.18.0–v0.18.3) | Pre-release blockers, capability & CDT hardening, IPC invariant completion, lifecycle & service coherence | WS-R1–R4 completed |
| **WS-M2** (v0.16.15) | Capability subsystem performance optimization: fused revoke path eliminating redundant CDT traversal (M-P01), CDT `parentMap` reverse index for O(1) parent lookup (M-P02/M-P03), reply-capability lemma extraction into dedicated module (M-P05) | WS-M2 completed |
| **WS-M1** (v0.16.14) | Capability subsystem audit & remediation Phase 1: initial audit findings triage, critical invariant gap closure, baseline proof surface hardening | WS-M1 completed |
| **WS-F6** | Invariant quality: `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (tautological predicates removed); `blockedOnNotificationNotRunnable` added to `ipcSchedulerContractPredicates` (6-tuple); `runnableThreadsAreTCBs` in `schedulerInvariantBundleFull` (6-tuple) with sorry-free preservation for all scheduler ops; `vspaceCrossAsidIsolation` in `vspaceInvariantBundle` (6-tuple); `default_serviceCountBounded` and `default_serviceGraphInvariant` proved; zero sorry/axiom | WS-F6 completed |
| **WS-H13** (v0.14.4) | CSpace, lifecycle & service model enrichment: `cspaceDepthConsistent` invariant in `capabilityInvariantBundle` (8-tuple → 6-tuple after WS-F6), `resolveCapAddress` theorems (`_deterministic`, `_zero_bits`, `_result_valid_cnode`), `serviceGraphInvariant` preservation proofs (`serviceRegisterDependency`), `cspaceMove` error-path atomicity theorem (A-21); CNode field migration (`depth`/`guardWidth`/`guardValue`/`radixWidth`); addresses H-01, A-21, A-29, A-30, M-17/A-31. *(WS-Q1: `serviceStart`/`serviceStop` lifecycle ops and backing-object verification removed; registry-only model.)* | WS-H13 completed |
| **WS-H12f** (v0.14.3) | Test harness update & documentation sync: `runDequeueOnDispatchTrace`, `runInlineContextSwitchTrace`, `runBoundedMessageExtendedTrace` trace scenarios; legacy `endpointInvariant` comment cleanup; fixture updated (108 lines); 9 new Tier 3 anchors; documentation synchronized. Completes WS-H12 composite workstream | WS-H12f completed |
| **WS-H12b** (v0.13.9) | Dequeue-on-dispatch scheduler semantics: `queueCurrentConsistent` inverted to `current ∉ runnable` matching seL4's `switchToThread`/`tcbSchedDequeue`; `schedule`/`handleYield`/`timerTick`/`switchDomain` updated; `currentTimeSlicePositive` and `schedulerPriorityMatch` predicates; IPC predicates (`currentThreadIpcReady`, `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, `currentThreadDequeueCoherent`); ~1800 lines of proofs re-proved; closes H-04 (HIGH) | WS-H12b completed |
| **WS-H11** (v0.13.7) | VSpace & architecture enrichment: `PagePermissions` struct with `wxCompliant` and W^X enforcement at insertion, `vspaceMapPageChecked` with ARM64 52-bit physical address bounds, `vspaceInvariantBundle` 5-conjunct preservation proofs, TLB/cache maintenance model (`TlbState`, `adapterFlushTlb`, `adapterFlushTlbByAsid`, `tlbConsistent`), `VSpaceBackend` typeclass abstraction; 10 new theorems | WS-H11 completed |
| **WS-H8** (v0.13.2) | Enforcement-NI bridge & missing wrappers: enforcement soundness meta-theorems, 4 new enforcement wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`), NI bridge theorems, projection hardening (domain timing metadata), `enforcementBoundaryExtended` (8 policy-gated ops); 26 new theorems | WS-H8 completed |
| **WS-H6** (v0.13.1) | Scheduler proof-surface completion: RunQueue reverse bridge (`flat_wf_rev`, `membership_implies_flat`, `mem_toList_iff_mem`) and scheduler candidate-selection lemmas (`isBetterCandidate_transitive`, `bucketFirst_fullScan_equivalence`); schedule membership validation now uses O(1) runQueue membership checks | WS-H6 completed |
| **WS-H5** (v0.12.19) | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems for all dual-queue operations; closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH) | WS-H5 completed |
| **WS-H4** (v0.12.18) | Capability invariant redesign: `capabilityInvariantBundle` extended from 4-tuple to 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`; all 25+ preservation theorems re-proved against non-trivial predicates | WS-H4 completed |
| **WS-H3** (v0.12.17) | Build/CI infrastructure fixes: `run_check` return value fix (H-12), `test_docs_sync.sh` CI integration (M-19), Tier 3 `rg` availability guard with `grep -P` fallback (M-20) | WS-H3 completed |
| **WS-H2** (v0.12.16) | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup on retype, CNode CDT detach, atomic retype | WS-H2 completed |
| **WS-H1** (v0.12.16) | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | WS-H1 completed |
| **WS-G** (v0.12.6–v0.12.15) | Kernel performance optimization: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | WS-G1..G9 + refinement completed |
| **WS-F1..F4** (v0.12.2–v0.12.5) | Critical audit remediation: IPC message transfer, untyped memory, info-flow completeness, proof gap closure | WS-F1..F4 completed |
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, capability/IPC, info-flow, completeness | WS-E1..E6 completed |
| **WS-D** (v0.11.0) | Test validity, info-flow enforcement, proof gaps, kernel design | WS-D1..D4 completed; D5/D6 absorbed into WS-E |
| **WS-C** (v0.9.32) | Model structure, documentation, maintainability | WS-C1..C8 completed |
| **WS-B** (v0.9.0) | Comprehensive audit 2026-02 | WS-B1..B11 completed |

### 3.3 Security Hardening (implemented)

- IPC thread-state updates fail with `objectNotFound` for missing/reserved TCBs, preventing ghost queue entries.
- Sentinel ID `0` rejected at IPC boundaries (`lookupTcb`/`storeTcbIpcState`).
- Intrusive dual-queue endpoints with `sendQ`/`receiveQ` and per-thread links for O(1) removal. Formal structural invariant (`dualQueueSystemInvariant`) with doubly-linked integrity proofs (WS-H5).
- IPC message transfer via `TCB.pendingMessage`: messages (registers, caps, badge) flow through sender→receiver rendezvous with combined state+message helpers (`storeTcbIpcStateAndMessage`).
- **WS-H12d/A-09:** IPC message payloads bounded by `maxMessageRegisters` (120) and `maxExtraCaps` (3), matching seL4's `seL4_MsgMaxLength`/`seL4_MsgMaxExtraCaps`. Bounds enforced at all IPC send boundaries with `ipcMessageTooLarge`/`ipcMessageTooManyCaps` errors. `IpcMessage.bounded` predicate with proven send-produces-bounded theorems.
- Node-stable CDT with bidirectional slot↔node maps and strict revocation error reporting.
- Policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `registerServiceChecked`) exercised by default in trace and probe harnesses. `enforcementBoundary` classifies 25 operations (11 policy-gated, 8 capability-only, 4 read-only, 2 lifecycle). Includes SchedContext ops (WS-Z8). (WS-Q1: `serviceRestartChecked` removed, `registerServiceChecked` added — service lifecycle simplified to registry-only model.)
- **WS-G1/WS-J1:** All 16 typed identifiers and the composite `SlotRef` key have `Hashable` instances with `@[inline]` for zero overhead. `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, enabling O(1) hash-based data structures for kernel performance optimization (WS-G2..G9). WS-J1-A added `RegName`/`RegValue` (v0.15.4); WS-J1-F added `CdtNodeId` (v0.15.10).

---

## 4. Architectural Improvements over seL4

seLe4n is not a 1:1 formalization of seL4. It preserves seL4's capability-based
security model while introducing improvements that the Lean 4 proof framework enables:

| Area | seL4 | seLe4n Improvement |
|------|------|-------------------|
| **Service registry** *(seLe4n extension)* | No kernel-level service concept | Service registry with dependency graphs, acyclic policy enforcement, isolation edges (novel seLe4n extension — not present in seL4). WS-Q1 simplified to stateless registry model: no `ServiceStatus`/`ServiceConfig`/lifecycle ops. R4: cross-subsystem invariants — endpoint cleanup on TCB retype, service registration authority check (Write right + endpoint type verification), dependency graph cleanup on revocation, `crossSubsystemInvariant` bundle (8 predicates, Z9-extended) in `proofLayerInvariantBundle` (10 conjuncts, Z9-extended) |
| **CDT representation** | Mutable doubly-linked list | Node-stable CDT with O(1) slot transfer via pointer/backpointer fixup |
| **IPC queuing** | Intrusive linked list | Dual-queue model (`sendQ`/`receiveQ`) with O(1) arbitrary removal; `blockedOnCall` state for call/reply semantics; reply-target scoping for confused-deputy prevention; formal `dualQueueSystemInvariant` with doubly-linked integrity (WS-H5) |
| **Information flow** | Binary high/low partition | Parameterized N-domain labels with per-endpoint flow policies |
| **Scheduling** | Priority-based round-robin | Priority + EDF scheduling with dequeue-on-dispatch semantics, per-TCB register context with inline context switch, and domain-aware partitioning |
| **Revocation** | Silent error swallowing | Strict variant (`cspaceRevokeCdtStrict`) reporting first failure with context |
| **Syscall boundary** *(WS-J1-A/B/C/D completed; WS-V V2 complete)* | C code extracts args from registers | Typed register wrappers (J1-A) + total decode layer with `RegisterDecode.lean`, complete round-trip proof surface for all 3 decode components (`decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`, `decodeMsgInfo_roundtrip` with bitwise `Nat.testBit` extensionality, plus composite `decode_components_roundtrip`), determinism proof, and error exclusivity (J1-B) + `syscallEntry` register-sourced entry point with capability-gated dispatch to all 17 kernel operations (13 original + `notificationSignal`/`notificationWait`/`replyRecv` added in V2), soundness theorems (J1-C) + invariant preservation and NI coverage for decode/dispatch path with `registerDecodeConsistent` predicate and 2 new `NonInterferenceStep` constructors (J1-D); `MessageInfo` label field bounded to 20 bits (seL4 convention, V2-E/V2-H); cap transfer slot base configurable via `capRecvSlot` (V2-F/V2-G) |

These are not abstract research extensions — they are design decisions that will be
carried forward into the production kernel.

---

## 5. Completed Workstream Portfolio (WS-G) and Next Steps

The WS-G portfolio addressed kernel performance optimization findings from the
[v0.12.5 performance audit](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All 9 workstreams completed (v0.12.6–v0.12.15), closing all 14 findings.

Authoritative detail:
[`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).

### 5.1 Completed — Data Structure Optimization

- **WS-G1:** ~~Typed identifier Hashable instances~~ **COMPLETED** — `Hashable` + `LawfulHashable` for all 16 typed identifiers (13 original + `RegName`/`RegValue` via WS-J1-A + `CdtNodeId` via WS-J1-F); `Std.HashMap`/`Std.HashSet` imports; zero-overhead foundation for O(1) lookups (v0.12.6, extended v0.15.4/v0.15.10)
- **WS-G2:** ~~Object store & ObjectIndex HashMap~~ **COMPLETED** — `objects : Std.HashMap ObjId KernelObject` replacing closure-chain accumulation; `objectIndexSet : Std.HashSet ObjId` shadow set for O(1) membership; `objectTypes : Std.HashMap ObjId KernelObjectType` lifecycle metadata; 9 bridge lemmas; full proof migration (599 theorems verified); closes F-P01, F-P10, F-P13 (v0.12.7)
- **WS-G3:** ~~ASID Resolution Table~~ **COMPLETED** — `asidTable : Std.HashMap ASID ObjId` in `SystemState`; `resolveAsidRoot` rewritten from O(n) `objectIndex.findSome?` to O(1) HashMap lookup with object-store validation; bidirectional `asidTableConsistent` invariant (soundness + completeness); `vspaceInvariantBundle` extended to 3-conjunct; erase-before-insert maintenance in `storeObject`; 3 bridge lemmas; round-trip theorems simplified; closes F-P06 (v0.12.8)

### 5.2 Completed — Scheduler Optimization

- **WS-G4:** ~~Run queue restructure~~ **COMPLETED** — `RunQueue` structure with `Std.HashMap Priority (List ThreadId)` + `Std.HashSet ThreadId` + bidirectional structural invariants (`flat_wf`, `flat_wf_rev`); `SchedulerState.runQueue` replaces flat `runnable : List ThreadId`; O(1) `insert`/`remove`/`contains`/`rotateHead`/`rotateToBack`; `chooseBestInBucket` bucket-first scheduling reduces best-candidate selection from O(t) to O(k); `withRunnableQueue`/`runnableHead`/`runnableTail` eliminated; 13 bridge lemmas; 30+ IPC invariant proofs migrated; info-flow projection re-proved; closes F-P02, F-P07, F-P12 (v0.12.9)

### 5.3 Completed — CNode Optimization

- **WS-G5:** ~~CNode slot HashMap~~ **COMPLETED** — `CNode.slots : Std.HashMap Slot Capability` replacing `List (Slot × Capability)`; `lookup`/`insert`/`remove` all O(1) amortized; `slotsUnique` trivially true (HashMap key uniqueness); 2 bridge lemmas (`HashMap_filter_preserves_key`, `HashMap_filter_filter_getElem?`); `projectKernelObject_idempotent` reformulated to slot-level lookup equality; `cspaceRevoke` `revokedRefs` via `HashMap.fold` (single O(m) pass); manual `BEq CNode`/`BEq KernelObject` instances; 10 files modified; closes F-P03 (v0.12.10)

### 5.4 Completed — VSpace Optimization

- **WS-G6:** ~~VSpace mapping HashMap~~ **COMPLETED** — `VSpaceRoot.mappings : Std.HashMap VAddr PAddr` replacing `List (VAddr × PAddr)` (enriched to `Std.HashMap VAddr (PAddr × PagePermissions)` by WS-H11); `lookup`/`mapPage`/`unmapPage` all O(1) amortized; universal `noVirtualOverlap_trivial` theorem proves the property for all VSpaceRoots (HashMap key uniqueness); round-trip theorems re-proved with HashMap bridge lemmas; manual `BEq VSpaceRoot` instance; `boundedAddressTranslation` reformulated for HashMap; `hashMapVSpaceBackend` replaces `listVSpaceBackend`; 7 files modified; closes F-P05 (v0.12.11)

### 5.5 Completed — IPC Queue & Notification Optimization

- **WS-G7:** ~~IPC Queue Completion & Notification~~ **COMPLETED** — Legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` deprecated (removed in WS-H12a); trace harness and sequence probe migrated to O(1) dual-queue (`endpointSendDual`/`endpointReceiveDual`). `notificationWait` O(n) duplicate check replaced with O(1) TCB `ipcState` check; O(n) append replaced with O(1) prepend. New `notificationWaiterConsistent` invariant bridges TCB state to queue membership. `endpointSendDualChecked` enforcement wrapper added. All invariant proofs re-proved; 9 files modified; closes F-P04 and F-P11 (v0.12.12)

### 5.6 WS-G8: Graph Traversal Optimization (completed, v0.12.13)

- **WS-G8:** ~~Graph Traversal Optimization~~ **COMPLETED** — `serviceHasPathTo` rewritten from O(n²) BFS with `List ServiceId` to O(n+e) DFS with `Std.HashSet ServiceId`. `CapDerivationTree` extended with `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed edge index; `childrenOf` O(1) HashMap lookup; `descendantsOf` O(N+E) total. `childMapConsistent` invariant with `empty`/`addEdge` preservation proofs. Full invariant proof migration; closes F-P08, F-P14 (v0.12.13)

### 5.7 WS-G9: Information-Flow Projection Optimization (completed, v0.12.14)

- **WS-G9:** ~~Information-Flow Projection Optimization~~ **COMPLETED** — `computeObservableSet` precomputes `Std.HashSet ObjId` via single `foldl` pass; `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` use O(1) `contains` lookups instead of redundant `objectObservable` re-evaluation. `projectStateFast_eq` proves equivalence with original `projectState` (`@[csimp]`-ready). Zero downstream proof breakage — all NI theorems, enforcement wrappers, and invariant proofs unchanged. 3 HashSet foldl bridge lemmas in `Prelude.lean`; closes F-P09 (v0.12.14)

### 5.8 WS-G Refinement Pass (v0.12.15)

Post-completion refinement addressing residual code quality, validation gaps, and test coverage across the WS-G portfolio:

- **RunQueue.remove optimization:** Eliminated redundant bucket computation — filtered bucket now computed once and reused for both `byPriority` and `maxPriority` updates.
- **WS-H6 scheduler proof completion:** Added reverse RunQueue bridge `membership_implies_flat`, bidirectional membership/list equivalence `mem_toList_iff_mem`, candidate-order transitivity `isBetterCandidate_transitive`, and bucket/full-scan equivalence theorem `bucketFirst_fullScan_equivalence`.
- **WS-H6 scheduler runtime optimization:** `schedule` now validates selection using O(1) `tid ∈ st.scheduler.runQueue` while preserving list-level reasoning via bridge lemmas.
- **MachineConfig validation hardening:** `wellFormed` now validates `pageSize` as a positive power of two via `isPowerOfTwo` (bitwise check), strengthening platform configuration safety.
- **Dead code removal:** Removed unused `filterByDomain` from `Scheduler/Operations.lean` (superseded by WS-G4 bucket-first scheduling).
- **Phantom object cleanup:** Removed object ID 200 from `bootstrapInvariantObjectIds` (no corresponding bootstrap object).
- **Runtime invariant checks:** Added `runQueueThreadPriorityConsistentB` (RunQueue membership ↔ threadPriority consistency) and `cdtChildMapConsistentCheck` (CDT childMap ↔ edges bidirectional consistency).
- **StateBuilder priority fix:** `BootstrapBuilder.build` uses actual TCB priorities for RunQueue bucketing instead of defaulting to priority 0.
- **Test coverage expansion:** `NegativeStateSuite` extended with `endpointReplyRecv` (2 negative + 1 positive via endpointCall chain) and `cspaceMutate` (2 negative + 2 positive including badge override) audit coverage checks.

### 5.9 WS-H1: IPC Call-Path Semantic Fix (completed, v0.12.16)

WS-H1 addresses the IPC call-path semantic gap identified in the v0.12.15 audit.
The `endpointCall` operation now transitions the caller to a distinct `blockedOnCall`
state (rather than reusing `blockedOnReply`), and reply operations validate the
authorized replier via reply-target scoping.

- **Part A (C-01 CRITICAL):** Added `blockedOnCall endpointId` variant to `ThreadIpcState`; `endpointCall` transitions caller to `blockedOnCall` instead of `blockedOnReply`; `endpointReceiveDual` detects call-origin senders via `senderWasCall` match and transitions them to `blockedOnReply endpointId (some caller)` with reply-target scoping.
- **Part B (M-02 MEDIUM):** `endpointReply`/`endpointReplyRecv` validate `expectedReplier` field — only the designated receiver can complete the reply, preventing confused-deputy attacks.
- **Part C (Invariant maintenance):** `ipcSchedulerContractPredicates` expanded from 3 to 6 conjuncts (added `blockedOnCallNotRunnable`, `blockedOnReplyNotRunnable`, `blockedOnNotificationNotRunnable` via WS-F6/D2); all 62+ IPC invariant preservation theorems re-proved with zero sorry/axiom; 5 H1-series trace anchors added.

### 5.10 WS-H11: VSpace & Architecture Enrichment (completed, v0.13.7)

WS-H11 enriches the VSpace subsystem with per-page permissions, W^X enforcement,
bounded address translation checks, and an abstract TLB maintenance model.

- **Part A (H-02/A-32):** `PagePermissions` structure with `read`/`write`/`execute`/`user`/`cacheable` fields; `VSpaceRoot.mappings` enriched from `HashMap VAddr PAddr` to `HashMap VAddr (PAddr × PagePermissions)`; `vspaceMapPage` enforces W^X at insertion (returns `policyDenied` on violation); `vspaceLookupFull` returns `(PAddr × PagePermissions)`; `VSpaceBackend` typeclass enriched with permissions; all round-trip and preservation theorems re-proved.
- **Part B (A-05/M-12/M-14):** `MemoryRegion.wellFormed` validates `endAddr ≤ 2^physicalAddressWidth`; `MachineConfig.wellFormed` extended with per-region overflow check; `boundedAddressTranslation` integrated into `vspaceInvariantBundle`.
- **Part C (A-12):** Global ASID uniqueness via `vspaceAsidRootsUnique` and `asidTableConsistent` (already in bundle since WS-G3); preservation proven for all VSpace operations.
- **Part D (H-10):** Abstract TLB model — `TlbEntry`/`TlbState` structures; `adapterFlushTlb` (full flush) and `adapterFlushTlbByAsid` (per-ASID flush); `tlbConsistent` invariant; flush-restoration and composition theorems.

`vspaceInvariantBundle` now contains 6 conjuncts: `vspaceAsidRootsUnique`, `vspaceRootNonOverlap`, `asidTableConsistent`, `wxExclusiveInvariant`, `boundedAddressTranslation`, `vspaceCrossAsidIsolation` (WS-F6/D6).

### 5.11 Prior Portfolio: WS-F (completed, v0.12.2)

The WS-F portfolio addressed findings from two independent v0.12.2 codebase audits.
Combined: 6 CRITICAL, 6 HIGH, 12 MEDIUM, 9 LOW findings.

- **WS-F1:** ~~IPC message transfer and dual-queue verification~~ **COMPLETED**
- **WS-F2:** ~~Untyped memory model~~ **COMPLETED**
- **WS-F3:** ~~Information-flow completeness~~ **COMPLETED**
- **WS-F4:** ~~Proof gap closure~~ **COMPLETED**
- **WS-F5–F8:** Medium/Low priority — immediate next steps (see below)

### 5.12 Next Steps: Remaining WS-F Workstreams (F5–F8)

The remaining WS-F workstreams address medium/low-priority findings:

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium | **Completed** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | **Completed** (v0.14.9) |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | **Completed** (v0.14.9) |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | **Completed** (v0.14.9) |
| **WS-I1** | Critical testing infrastructure (inter-transition assertions, mandatory determinism, scenario ID traceability) | High | **Completed** (v0.15.0) |
| **WS-I3** | Test coverage expansion — operations (multi-operation chains, scheduler stress, declassification checks) | Medium | **Completed** (v0.15.2) |
| **WS-I4** | Test coverage expansion — subsystems (VSpace multi-ASID sharing, IPC interleaving, lifecycle cascading chains) | Low | **Completed** (v0.15.3) |

After WS-F/WS-I1: Raspberry Pi 5 hardware binding (H3).

### 5.13 WS-I1: Critical Testing Infrastructure (completed, v0.15.0)

WS-I1 is the first workstream of the WS-I improvement portfolio, addressing three
critical testing infrastructure recommendations from the v0.14.9 audit.

- **Part A (R-01 — Inter-transition assertions):** 17 `checkInvariants` calls inserted across all 13 trace functions in `MainTraceHarness.lean`. Each call invokes `assertStateInvariantsFor` (17 invariant check families covering scheduler, CSpace, IPC, lifecycle, service, VSpace, CDT, ASID, untyped, notification, blocked-thread, and domain invariants) with `IO.Ref Nat` counter tracking. Summary `[ITR-001]` line confirms all 17 checks passed. Zero sorry/axiom.
- **Part B (R-02 — Mandatory determinism):** `scripts/test_tier2_determinism.sh` runs the trace harness twice and diffs output, failing on any divergence. Integrated into `test_smoke.sh` Tier 2 gate (between trace and negative checks), making determinism a mandatory CI property rather than an optional Tier 4 extension.
- **Part C (R-03 — Scenario ID traceability):** All 121 trace output lines tagged with unique scenario IDs (15 prefix families: ENT, CAT, SST, LEP, CIC, IMT, IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY). Fixture format upgraded to pipe-delimited (`SCENARIO_ID | SUBSYSTEM | expected_trace_fragment`). `tests/fixtures/scenario_registry.yaml` maps all 121 IDs to source functions and subsystems. `scripts/scenario_catalog.py validate-registry` checks bidirectional fixture↔registry consistency. Tier 0 hygiene validates registry on every PR.
- **WS-I2 (v0.15.1):** proof/validation depth completed: Tier 0 now runs semantic L-08 theorem-body analysis (`scripts/check_proof_depth.py` with regex fallback), Tier 3 now runs Lean `#check` correctness anchors across scheduler/capability/IPC/lifecycle/service/VSpace/IF preservation theorems, and IF projection now supports optional memory-domain ownership (`memoryOwnership`) with backward-compatible default (`none`).
- **WS-I3 (v0.15.2):** operations coverage expansion completed: new `tests/OperationChainSuite.lean` adds six multi-operation chain tests and scheduler stress coverage (16-thread repeated schedule/yield, same-priority determinism, multi-domain domain-switch isolation); Tier 2 now executes this suite via `scripts/test_tier2_negative.sh`; `tests/InformationFlowSuite.lean` adds declassification runtime checks for authorized downgrade, normal-flow rejection, policy-denied rejection, and three-domain lattice behavior. The declassification policy-denied branch is represented explicitly as `KernelError.declassificationDenied` for clearer failure-mode discrimination.
- **WS-I4 (v0.15.3):** subsystem coverage expansion completed in `tests/OperationChainSuite.lean` with three new chain families: (R-09) VSpace multi-ASID shared-page coherency and per-ASID permission independence checks (including post-unmap isolation), (R-10) endpoint IPC interleaved three-sender FIFO plus alternating send/receive ordering checks, and (R-11) lifecycle authority-degradation and CDT cascading-revoke chains (root→child→grandchild) validating descendant cleanup and non-amplification of rights.

### 5.14 Deferred Operations (WS-F5/D3)

The following seL4 operations are intentionally deferred from the current model.
Each has a documented rationale and prerequisite milestone:

| Operation | seL4 Equivalent | Rationale | Prerequisite | Status |
|-----------|----------------|-----------|--------------|--------|
| `setPriority` | `seL4_TCB_SetPriority` | MCP authority validation, SchedContext-aware priority update, run queue migration | MCS scheduling (Z1–Z5) | **Implemented (D2, v0.24.1)** |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | MCP ceiling update with retroactive priority capping | MCS scheduling (Z1–Z5) | **Implemented (D2, v0.24.1)** |
| `suspend` | `seL4_TCB_Suspend` | Requires thread lifecycle state machine | WS-F6 (lifecycle invariants) | **Implemented (D1, v0.24.0)** |
| `resume` | `seL4_TCB_Resume` | Inverse of suspend; same prerequisite | WS-F6 (lifecycle invariants) | **Implemented (D1, v0.24.0)** |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | VSpace-validated IPC buffer address update | H3 (VSpace integration) | **Implemented (D3, v0.24.2–v0.24.3)** |

**D1 (v0.24.0):** Thread suspension and resumption are now fully implemented.
`suspendThread` performs the complete cleanup pipeline (IPC blocking cancellation,
SchedContext donation cleanup, run queue removal, pending state clearing, state
transition to Inactive). `resumeThread` transitions from Inactive to Ready with
conditional preemption. Both operations are wired into the API dispatch layer
(`SyscallId.tcbSuspend`, `.tcbResume`) as capability-only arms and have frozen-phase
equivalents. Transport lemmas prove scheduler, serviceRegistry, and lifecycle
preservation through all suspension sub-operations.

These operations are tracked in `SeLe4n/Kernel/API.lean` (stability table) and
`docs/CLAIM_EVIDENCE_INDEX.md` (evidence tracking).

**D2 (v0.24.1):** Priority management is now fully implemented. `setPriorityOp`
validates MCP authority, updates priority on SchedContext (if bound) or TCB
(if unbound), migrates run queue buckets, and triggers conditional reschedule.
`setMCPriorityOp` updates the MCP ceiling and retroactively caps the thread's
current priority if it exceeds the new MCP. Both operations are wired into
`dispatchWithCap` (`SyscallId.tcbSetPriority`, `.tcbSetMCPriority`) as
capability-only arms with frozen-phase equivalents. Preservation theorems
prove authority non-escalation (`setPriority_authority_bounded`,
`setMCPriority_authority_bounded`) and transport lemmas guarantee scheduler,
serviceRegistry, and lifecycle field preservation.

**D3 (v0.24.2):** IPC buffer configuration is now fully implemented.
`setIPCBufferOp` validates the buffer address through a 5-step pipeline
(alignment to 512 bytes, canonical address check, VSpace root validity,
mapping existence via VSpaceRoot.lookup, write permission) before updating
the TCB's `ipcBuffer` field. The operation is wired into `dispatchWithCap`
(`SyscallId.tcbSetIPCBuffer`) as a capability-only arm with a frozen-phase
equivalent (`frozenSetIPCBuffer`). Validation correctness theorems prove that
successful validation implies alignment and mapped-writable guarantees.
Frame preservation is trivial since `ipcBuffer` is not referenced by any
scheduler, IPC, cross-subsystem, or capability invariant predicate.

---

## 6. Hardware Target: Raspberry Pi 5

The first production hardware target is **Raspberry Pi 5** (ARM64, BCM2712).

### 6.1 Why Raspberry Pi 5

1. Practical ARM64 platform for repeated experiments and bring-up
2. Realistic interrupt/memory/boot profile for architecture-bound modeling
3. Broad tooling availability and community support
4. Good tradeoff between accessibility and systems realism

### 6.2 Path to Hardware

| Stage | Description | Status |
|-------|-------------|--------|
| **H0** | Architecture-neutral semantics and proofs | Complete (M1–M7, WS-B..E) |
| **H1** | Architecture-boundary interfaces and adapters | Complete (M6) |
| **H2** | Audit-driven proof deepening (close critical gaps) | Complete (WS-F and WS-H portfolios) |
| **H3** | Platform binding — map interfaces to Raspberry Pi 5 hardware | **H3-prep complete** |
| **H4** | Evidence convergence — connect proofs to platform assumptions | Planned |

**H3 preparation (structural):** The `Platform/` directory now provides the
organizational foundation for hardware binding:

- `PlatformBinding` typeclass (`SeLe4n/Platform/Contract.lean`)
- `MachineConfig` and `MemoryRegion` types (`SeLe4n/Machine.lean`)
- `VSpaceBackend` abstraction with permissions-enriched `hashMapVSpaceBackend` instance (WS-G6/WS-H11)
- `ExtendedBootBoundaryContract` with platform boot fields
- Simulation platform (`Platform/Sim/`) for testing
- RPi5 stubs (`Platform/RPi5/`) with BCM2712 memory map, GIC-400 constants,
  ARM64 machine config, and platform-specific runtime contract

The critical prerequisite for full H3 execution is closing the remaining WS-F
proof gaps. Untyped memory (WS-F2) and information-flow completeness (WS-F3)
are now complete.

### 6.3 Cache Coherency & Memory Ordering Assumptions (T6-G/M-NEW-8)

The seLe4n model makes the following cache coherency and memory ordering
assumptions for the initial single-core RPi5 target:

1. **Single-core assumption**: The RPi5 target uses one Cortex-A76 core.
   Single-core execution eliminates most cache coherency concerns — all loads
   and stores from the same core observe a consistent memory view without
   explicit cache maintenance.

2. **MMIO requires barriers**: Device register accesses (MMIO) are *not*
   subject to normal memory ordering guarantees. All MMIO operations must use
   explicit ARM64 memory barriers:
   - **Reads**: `DMB` (Data Memory Barrier) after read to ensure the value
     is visible before subsequent dependent accesses.
   - **Writes**: `DSB` (Data Synchronization Barrier) before write to ensure
     prior writes complete before the device register update.
   - **Configuration writes**: `ISB` (Instruction Synchronization Barrier)
     after writes to system configuration registers (e.g., MMU, GIC) to
     flush the instruction pipeline.

   The MMIO adapter (`Platform/RPi5/MmioAdapter.lean`) models these barriers
   as fields on `MmioOp`. The `MemoryBarrier` inductive (DMB, DSB, ISB)
   captures the three ARM64 barrier types.

3. **DMA coherency is out of scope**: Direct Memory Access (DMA) coherency
   requires explicit cache clean/invalidate operations and is not modeled.
   DMA is relevant only for device drivers (USB, SD, network), which are
   outside the kernel's formal boundary. DMA coherency will be addressed in
   WS-U if multicore or DMA-capable device drivers are targeted.

4. **TLB coherency**: TLB invalidation after page table modifications is
   modeled via `adapterFlushTlb` (full flush), `adapterFlushTlbByAsid`
   (per-ASID flush), and `adapterFlushTlbByVAddr` (per-page flush). The
   production dispatch path uses `vspaceMapPageCheckedWithFlush` which
   includes a full flush. Targeted flushes (`tlbFlushByASID`, `tlbFlushByPage`)
   are defined for future optimization but not yet wired into production paths.

---

## 7. Acceptance Expectations

### 7.1 Per-Workstream Acceptance Gates

Each workstream has defined entry/exit criteria. Common acceptance patterns:

1. implementation compiles and passes tiered validation,
2. new/modified theorems are non-tautological and non-trivial,
3. executable trace evidence captures semantic breadcrumbs,
4. documentation is synchronized across all canonical surfaces,
5. no regressions in previously-completed workstream contracts.

### 7.2 Milestone-Moving PR Requirements

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 8. Model Fidelity & Type Safety (WS-S Phase S4)

### 8.1 Object Capacity Bounds

The abstract model uses unbounded `Nat` for object indices. For the RPi5
hardware target, the expected maximum object count is `maxObjects = 65536`.

- **objectIndex growth**: The `objectIndex` list consumes at most
  `65536 × 8 = 512 KB` at maximum capacity — well within RPi5's 8 GB RAM.
- **Advisory predicate**: `objectIndexBounded st` asserts
  `st.objectIndex.length ≤ maxObjects` (defined in `Model/State.lean`).
- **Capacity enforcement**: `storeObject` returns `objectStoreCapacityExceeded`
  when the object count reaches `maxObjects`, preventing unbounded growth.

### 8.2 Word-Boundedness Invariants

The Lean model bridges abstract `Nat` semantics to 64-bit hardware:

- **Register values**: `RegValue` wraps `Nat` with `isWord64` validity predicate.
- **Badges**: `Badge.ofNatMasked` masks to `2^64` at construction, proven valid.
- **Access rights**: `AccessRightSet.ofNat` masks to `2^5` (5-bit field).
  `AccessRightSet.ofList` proven valid (`ofList_valid`, T2-A/H-1).
- **IPC messages**: `IpcMessage.registers` uses `Array RegValue` (typed values).
- **CPtr resolution**: `resolveSlot` masks input to 64 bits before guard extraction.
- **CNode guard bounds**: `CNode.guardBounded` predicate (`guardValue < 2^guardWidth`)
  integrated into `CNode.wellFormed`. `resolveSlot_guardMismatch_of_not_guardBounded`
  proves resolution always fails for out-of-bounds guards (T2-J/L-NEW-4).
- **CDT access control**: `CapDerivationTree` constructor is `private`; external
  construction requires `mk_checked` with `cdtMapsConsistent` witness (T2-B/C/H-2).
- **Frozen TLB**: `FrozenSystemState.tlb` field preserves TLB state across freeze;
  `freeze_preserves_tlb` correctness theorem (T2-D/E/F/M-NEW-1).
- **storeObject preservation**: Bundled `storeObject_preserves_allTablesInvExtK`
  theorem composing 16+ component proofs (T2-G/M-NEW-2). Uses `invExtK` kernel-level
  invariant bundle (V3-B) — eliminates separate `hSize`/`hCapGe4` threading.

### 8.3 Memory Alignment Model Gap

The abstract model uses `Memory := PAddr → UInt8` (byte-addressable). Real ARM64
hardware requires word-aligned access for register-width loads/stores:

- **Alignment predicates**: `alignedRead`/`alignedWrite` in `Machine.lean` document
  the word-alignment requirement.
- **Alignment faults**: Not modeled — the abstract `Memory` function accepts any
  address. Hardware binding (WS-T) must enforce alignment via the platform contract.
- This is a documented model gap, not a soundness issue: proofs about memory
  semantics hold for the abstract model; hardware binding adds the alignment
  constraint as an additional platform-level precondition.

### 8.4 Page-Alignment Requirement for VSpace-Bound Retype

`retypeFromUntyped` enforces page-aligned allocation bases (4 KiB) for object
types that require it. This applies to VSpace roots and CNodes, which must be
page-aligned for correct hardware page-table walks and CNode radix indexing.

- **`requiresPageAlignment`** -- predicate identifying `KernelObjectType` values
  that require page-aligned allocation (VSpace roots, CNodes).
- **`allocationBasePageAligned`** -- checks 4 KiB alignment of the allocation base
  (`base % 4096 == 0`).
- **`allocationMisaligned`** -- `KernelError` variant returned when the alignment
  check fails.
- **Lifecycle invariant preservation**: all existing lifecycle preservation proofs
  are updated to account for the new error branch. Error returns preserve the
  unchanged state trivially.

This enforcement closes the gap between the abstract model (which previously
accepted any allocation base) and hardware requirements for ARM64 page-table
structures. See `SeLe4n/Kernel/Lifecycle/Operations.lean` (S5-G/S5-H).

### 8.5 IPC Timeout Semantics (Z6)

seLe4n implements budget-driven timeout for IPC blocking operations (Z6),
extending seL4 MCS timeout semantics. When a thread's SchedContext budget
expires while blocked on send/receive/call/reply, the thread is unblocked
with timeout error code `0xFFFFFFFF` in register x0 and re-enqueued in the
RunQueue.

- **`timeoutThread`** (`Timeout.lean`): Removes thread from endpoint queue
  via `endpointQueueRemove`, resets IPC state to `.ready`, writes timeout
  error code, re-enqueues via `ensureRunnable`.
- **`timeoutBlockedThreads`** (`Core.lean`): Scans object store for TCBs
  bound to an exhausted SchedContext and calls `timeoutThread` on each.
- **`timeoutAwareReceive`** (`Timeout.lean`): Wrapper that detects prior
  timeout via error code in register context.
- **`blockedThreadTimeoutConsistent`** invariant: Threads with
  `timeoutBudget = some scId` must reference a valid SchedContext and be
  in a blocking IPC state.

The timeout scan is triggered in `timerTickBudget` on budget exhaustion,
using `schedContextBinding.scId?` to identify affected threads.

### 8.6 Memory Scrubbing on Delete (WS-S Phase S6)

When an object is deleted via `lifecycleRetypeWithCleanup`, the backing memory
region is zeroed using `scrubObjectMemory` before the memory is returned to the
untyped pool. This prevents information leakage between security domains when
memory is retyped for a different purpose.

- **`zeroMemoryRange`** (`Machine.lean`): Primitive that zeroes a contiguous
  range of physical memory addresses.
- **`memoryZeroed`** (`Machine.lean`): Postcondition predicate asserting all
  bytes in a range are zero after scrubbing.
- **`scrubObjectMemory`** (`Lifecycle/Operations.lean`): Applies `zeroMemoryRange`
  to the object's backing region during cleanup.
- **Invariant preservation**: `scrubObjectMemory` preserves lifecycle invariants
  trivially (only modifies `machine.memory`, not kernel state structures).
- **NI preservation**: `scrubObjectMemory` preserves `lowEquivalent` for
  non-observable targets — scrubbing memory outside an observer's domain does
  not affect their projected state.

### 8.7 TLB Flush Requirements for Production Paths (WS-S Phase S6)

All production VSpace operations must use TLB-flushing variants to ensure
hardware TLB consistency:

- **`vspaceMapPageCheckedWithFlush`**: Production path for mapping pages.
  Performs W^X checks, bounds validation, and TLB flush after insertion.
- **`vspaceUnmapPageWithFlush`**: Production path for unmapping pages.
  Flushes the TLB entry after removal.
- **Internal helpers**: The unflushed `vspaceMapPage`/`vspaceUnmapPage` are
  internal proof decomposition helpers only. They carry explicit warnings
  against direct use in production paths.
- **API dispatch**: `dispatchWithCap` routes VSpace syscalls through the
  `WithFlush` variants exclusively.

### 8.8 Frozen IPC Queue Semantics (WS-T Phase T1)

Frozen kernel operations now support blocking IPC paths with proper queue
management:

- **`frozenQueuePushTail`**: Appends a thread to a frozen endpoint queue with
  dual-queue invariant precondition checks (head/tail link integrity).
  Integrated into `frozenEndpointSend`, `frozenEndpointReceive`, and
  `frozenEndpointCall`.
- **7 preservation theorems** prove that enqueue operations maintain all frozen
  state invariants via `frozenQueuePushTail_only_modifies_objects`.
- **Commutativity**: `FrozenMap` set/get? roundtrip proofs ensure lookup
  consistency after frozen state mutations.

### 8.9 Object Well-Formedness Validation (WS-T Phase T5)

Every kernel object has a decidable well-formedness predicate:

- **`KernelObject.wellFormed`**: Validates structural constraints (CNode guard
  bounds, VSpace permission compliance, TCB register consistency, endpoint queue
  integrity).
- **`lifecycleRetypeWithCleanup`**: Enforces well-formedness at object creation
  via the decidable validator.
- **Intrusive queue cleanup**: `spliceOutMidQueueNode` patches predecessor and
  successor links when removing mid-queue nodes, maintaining doubly-linked list
  integrity.

### 8.10 Checked Dispatch and MMIO Adapter (WS-T Phase T6)

- **Checked dispatch**: `dispatchWithCapChecked`, `dispatchSyscallChecked`, and
  `syscallEntryChecked` gate all 7 policy-relevant operations through
  `securityFlowsTo` wrappers at runtime (endpointSend/Receive/Call,
  cspaceMint/Copy/Move, registerService). `checkedDispatch_flowDenied_preserves_state`
  proves state preservation on flow denial.
- **MMIO adapter**: `mmioRead`/`mmioWrite` in `Platform/RPi5/MmioAdapter.lean`
  validate device-region membership. `MemoryBarrier` inductive (DMB, DSB, ISB)
  models ARM64 memory ordering. `mmioAccessAllowed` runtime contract predicate
  gates access.
- **TLB flush operations**: `tlbFlushByASID`, `tlbFlushByPage`, `tlbFlushAll`
  with state frame proofs for targeted invalidation.

### 8.11 buildChecked Runtime Invariant Validation (WS-T Phase T7)

All test states use `BootstrapBuilder.buildChecked` instead of `build`:

- **Runtime structural validation**: No duplicate ObjIds, lifecycle type-tag
  matching, runnable threads reference existing TCBs, CNode capacity bounds,
  current thread in runnable list.
- **31 post-mutation invariant checks** in the trace harness covering all
  major transition families (IPC, VSpace, lifecycle, scheduler, capability).

### 8.12 Scheduling Context Objects (WS-Z)

A `SchedContext` is a first-class kernel object containing CPU budget, period,
priority, deadline, and domain parameters for CBS (Constant Bandwidth Server)
scheduling. Threads bind to SchedContexts via the `schedContextBinding` field
(unbound | bound | donated). The `threadSchedulingParams` accessor resolves
effective scheduling parameters from the bound SchedContext or falls back to
legacy TCB fields.

Key types: `Budget` (CPU time in ticks), `Period` (replenishment period),
`Bandwidth` (budget/period pair for admission control), `ReplenishmentEntry`
(CBS replenishment event), `SchedContextBinding` (thread ↔ SchedContext relationship).

#### 8.12.1 CBS Budget Engine (WS-Z Phase Z2)

The CBS budget engine (`Kernel/SchedContext/Budget.lean`) provides pure-function
budget management operations with machine-checked invariants:

- **Budget consumption**: `consumeBudget` decrements `budgetRemaining` with
  saturating arithmetic (cannot go negative). `isBudgetExhausted` detects
  zero remaining budget.
- **Replenishment scheduling**: `scheduleReplenishment` creates a
  `ReplenishmentEntry` eligible one period in the future and truncates the
  replenishment list to `maxReplenishments` (= 8).
- **Replenishment processing**: `processReplenishments` partitions the
  replenishment list by eligibility time, sums eligible amounts, and refills
  `budgetRemaining` capped at the configured `budget` ceiling via `applyRefill`.
  `applyRefill` also synchronizes `isActive` to reflect whether budget is positive.
- **CBS deadline rule**: `cbsUpdateDeadline` assigns `deadline := currentTime +
  period` when a SchedContext is replenished after budget exhaustion.
- **Combined entry point**: `cbsBudgetCheck` composes consume → exhaust check →
  replenishment scheduling → processing → deadline update into a single
  atomic step returning `(updatedSc, wasPreempted)`.
- **Admission control**: `admissionCheck` verifies that adding a new SchedContext
  does not exceed total utilization of 1000 per-mille (100% bandwidth).

Invariants (`Kernel/SchedContext/Invariant/Defs.lean`):
- `budgetWithinBounds`: `budgetRemaining ≤ budget ≤ period`
- `replenishmentListWellFormed`: bounded length, no zero-amount entries
- `replenishmentAmountsBounded`: each entry's amount ≤ configured budget
- `schedContextWellFormed`: 4-conjunct bundle (`wellFormed ∧ budgetWithinBounds ∧
  replenishmentListWellFormed ∧ replenishmentAmountsBounded`)

16 preservation theorems (4 operations × 4 sub-invariants) prove that all CBS
operations maintain the invariant bundle, composed into
`cbsBudgetCheck_preserves_schedContextWellFormed` (bundled) and
`cbsBudgetCheck_preserves_replenishmentAmountsBounded` (standalone).
Bandwidth isolation theorems (`cbs_single_period_bound`, `cbs_bandwidth_bounded`)
bound total consumption by `maxReplenishments × budget`.

#### 8.12.2 Replenishment Queue (WS-Z Phase Z3)

The system-wide `ReplenishQueue` (`Kernel/SchedContext/ReplenishQueue.lean`)
tracks when each SchedContext's budget becomes eligible for refill. The queue
is a sorted list of `(SchedContextId, eligibleAt)` pairs with a cached `size`
field, enabling O(1) `peek`/`hasDue` and O(k) `popDue` (prefix split).

Operations: `insert` (sorted O(n)), `popDue` (prefix split O(k)), `remove`
(filter O(n)). Invariants: `pairwiseSortedBy` (recursive adjacency predicate),
`replenishQueueSorted`, `replenishQueueSizeConsistent`, `replenishQueueConsistent`
(parameterized by object store lookup). 13 preservation/membership theorems
including `insert_preserves_sorted`, `popDue_preserves_sorted`,
`splitDue_length_additive`, `mem_insertSorted`.

#### 8.12.3 Scheduler Integration (WS-Z Phase Z4)

The CBS budget engine and replenishment queue are wired into the scheduler via
`effectivePriority` (resolves scheduling params from SchedContext if bound, TCB
fields if unbound), `hasSufficientBudget` (budget eligibility predicate),
`chooseThreadEffective` (budget-filtered selection chain), and `timerTickBudget`
(3-branch: unbound legacy / bound decrement / bound exhaustion+preempt).

6 new invariants: `budgetPositive`, `currentBudgetPositive`,
`schedContextsWellFormed`, `replenishQueueValid`, `schedContextBindingConsistent`,
`effectiveParamsMatchRunQueue`. Extended bundle:
`schedulerInvariantBundleExtended` (15-tuple: original 9 + 6 new). Backward
compatible: existing `chooseThread`/`schedule`/`timerTick`/`handleYield`
preserved unchanged.

#### 8.12.4 Capability-Controlled Thread Binding (WS-Z Phase Z5)

3 new `SyscallId` variants: `.schedContextConfigure` (17), `.schedContextBind`
(18), `.schedContextUnbind` (19). Capability-gated operations:
`validateSchedContextParams`, `schedContextConfigure` (validate + admit + store),
`schedContextBind` (bidirectional TCB↔SchedContext binding + RunQueue
re-insertion), `schedContextUnbind` (unbind + preemption guard + RunQueue
removal), `schedContextYieldTo` (kernel-internal budget transfer). 7
preservation theorems including `schedContextBind_output_bidirectional` and
`schedContextConfigure_admission_excludes_eq`. API dispatch via
`dispatchCapabilityOnly` shared path.

#### 8.12.5 API Surface & Syscall Wiring (WS-Z Phase Z8)

3 error-exclusivity theorems (`decodeSchedContextConfigureArgs_error_iff`,
`decodeSchedContextBindArgs_error_iff`, `decodeSchedContextUnbindArgs_error_iff`).
4 frozen SchedContext operations (`frozenSchedContextConfigure`,
`frozenSchedContextBind`, `frozenSchedContextUnbind`, `frozenTimerTickBudget`).
`enforcementBoundary` expanded 22→25 entries (3 new `.capabilityOnly` SchedContext
operations). `frozenOpCoverage_count` increased 12→15.

#### 8.12.6 Invariant Composition & Cross-Subsystem (WS-Z Phase Z9)

3 new cross-subsystem predicates: `schedContextStoreConsistent` (every
SchedContext in the object store satisfies `schedContextWellFormed`),
`schedContextNotDualBound` (no SchedContext simultaneously bound to two threads),
`schedContextRunQueueConsistent` (RunQueue threads have bound SchedContext with
positive budget or are legacy-unbound). `crossSubsystemInvariant` extended from
5 to 8 predicates. `proofLayerInvariantBundle` extended from 9 to 10 conjuncts
(added `schedulerInvariantBundleExtended`). `bootSafeObject` extended with
SchedContext `schedContextWellFormed` requirement (6th conjunct). Field-
disjointness: 16 pairwise witnesses for 8 predicates, 3 new frame lemmas.

### 8.7 SchedContext Donation (Z7)

SchedContext donation enables **passive servers** — threads that consume zero
CPU when idle by borrowing the client's SchedContext during IPC Call/Reply.

**Protocol**: (1) Client calls server via `endpointCall`. If server is passive
(`.unbound`), client's SchedContext is donated via `donateSchedContext`. (2)
Server executes on client's budget. (3) Server replies via `endpointReply` —
`returnDonatedSchedContext` returns the SC to the original owner. (4) Server
becomes passive (`.unbound`, removed from RunQueue).

**Architecture**: Donation is implemented as post-processing in the API dispatch
layer (`API.lean`), preserving all existing IPC invariant proofs unchanged. Core
IPC functions (`endpointCall`, `endpointReply`, `endpointReplyRecv`) are not
modified. Key helpers: `donateSchedContext`, `returnDonatedSchedContext`,
`applyCallDonation`, `applyReplyDonation`, `cleanupPreReceiveDonation`.

**Invariants** (`ipcInvariantFull` extended from 10 to 14 conjuncts):
- `donationChainAcyclic`: no circular donation chains (A→B and B→A)
- `donationOwnerValid`: donated bindings reference valid objects with
  bidirectional consistency (`sc.boundThread = some server`,
  `owner.schedContextBinding = .bound scId`, `owner.ipcState = .blockedOnReply`)
- `passiveServerIdle`: unbound non-runnable threads are ready/receiving
- `donationBudgetTransfer`: at most one thread per SchedContext

**Lifecycle**: `cleanupDonatedSchedContext` in `lifecyclePreRetypeCleanup`
returns donated SchedContexts before TCB destruction.

**Defense-in-depth**: `donateSchedContext` validates `sc.boundThread = some
clientTid` before transferring ownership.

### 8.13 Priority Inheritance Protocol (WS-AB Phase D4)

Priority inversion via Call/Reply IPC is mitigated by a deterministic Priority
Inheritance Protocol (PIP). When a client blocks on a server via `Call`, the
server's effective scheduling priority is transiently elevated to match the
highest-priority client transitively waiting on it.

**TCB field**: `pipBoost : Option Priority := none`. When `some p`, the
thread's effective priority is `max(SchedContext.priority, p)`.

**Blocking graph**: `blockedOnThread` (direct blocking via `blockedOnReply`),
`waitersOf` (all direct waiters), `blockingChain` (transitive upward walk).
Acyclicity is a system-level invariant (`blockingAcyclic`); chain depth is
bounded by `objectIndex.length`.

**Operations**:
- `computeMaxWaiterPriority`: maximum effective priority among direct waiters
- `updatePipBoost`: single-thread pipBoost recompute + conditional run queue migration
- `propagatePriorityInheritance`: chain walk applying updatePipBoost at each step
- `revertPriorityInheritance`: structurally identical to propagation (same updatePipBoost)

**Integration points**:
- `endpointCallWithDonation`: propagates PIP after Call completes (D4-L)
- `endpointReplyWithDonation`: reverts PIP after Reply unblocks client (D4-M)
- `endpointReplyRecvWithDonation`: reverts PIP for ReplyRecv (D4-M)
- `suspendThread`: reverts PIP before cleanup pipeline (D4-N)

**Composition with SchedContext donation (Z7)**: `effectivePriority` computes
`max(scPrio, pipBoost)`, so PIP provides an additional boost when the transitive
client priority exceeds the donated SchedContext priority.

**Bounded inversion**: Priority inversion is bounded by
`objectIndex.length × WCRT(effectivePriority)` ticks (parametric in WCRT).

---

## 9. Non-Negotiable Baseline Contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. domain-aware scheduling semantics (`schedule` is active-domain-only; no cross-domain fallback),
4. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
5. theorem discoverability through stable naming,
   - canonical IPC/lifecycle composition surfaces: `coreIpcInvariantBundle`, `ipcSchedulerCouplingInvariantBundle`, `lifecycleCompositionInvariantBundle`,
   - canonical trace helper surfaces: `runCapabilityIpcTrace`, `runSchedulerTimingDomainTrace`,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: `SeLe4n/Kernel/API.lean` is the canonical aggregate API surface.
9. syscall capability-checking: `SyscallGate` + `syscallLookupCap` model the seL4 CSpace-lookup + rights-check pattern; production path `syscallEntry` -> `dispatchSyscall` -> `syscallInvoke` -> `dispatchWithCap` (S5-A: deprecated `api*` wrappers removed); 3 soundness theorems prove capability requirements; 17 `SyscallId` variants (V2: added `notificationSignal`=14, `notificationWait`=15, `replyRecv`=16); `MessageInfo` label bounded to 20 bits (seL4 convention).
10. HashMap-backed equality for `VSpaceRoot` and `CNode` is order-independent (size + fold containment), and the migrated state stores (`services`, `irqHandlers`, `capabilityRefs`, `cdtSlotNode`, `cdtNodeSlot`) are `Std.HashMap`-backed (no closure-chain metadata stores).

---

## 10. Audit Baselines

### 10.1 Active Baselines

| Artifact | Path |
|----------|------|
| Codebase audit v1 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md`](../dev_history/audits/AUDIT_CODEBASE_v0.12.2_v1.md) |
| Codebase audit v2 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md`](../dev_history/audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Execution baseline (WS-F) | [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) |

### 10.2 Prior Baselines (completed)

| Artifact | Path |
|----------|------|
| Findings baseline (v0.11.6) | [`docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md`](../dev_history/audits/AUDIT_CODEBASE_v0.11.6.md) |
| Execution baseline (WS-E) | [`docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |
| Findings baseline (v0.11.0) | [`docs/dev_history/audits/AUDIT_v0.11.0.md`](../dev_history/audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |

### 10.3 Historical Baselines

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/).

---

## 11. Security and Threat Model

Security assumptions and trust boundaries are documented in
[`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).

### 10.1 Trust Boundaries (WS-S/S1)

The following trust boundaries are documented as part of WS-S Phase S1:

**`ThreadId.toObjId` identity mapping** (`SeLe4n/Prelude.lean`): The conversion
from `ThreadId` to `ObjId` is an unchecked identity mapping. Callers must verify
the returned `ObjId` references a TCB by pattern-matching on `.tcb tcb` after
object store lookup. The checked variant `toObjIdChecked` additionally rejects
the sentinel value (ID 0). See `ThreadId.toObjId_injective` for the injectivity
proof.

**Badge forging via Mint** (`SeLe4n/Kernel/Capability/Operations.lean`): Any
holder of a capability with Mint authority on an endpoint can mint a derived
capability with an arbitrary badge value. This matches seL4 semantics — badge
values are opaque sender identifiers, not cryptographic authenticators.
Authentication relies on the CDT tracking which entity performed the mint.

**`MemoryRegion.wellFormed`** (`SeLe4n/Machine.lean`): Converted from a runtime
`Bool` check to a `Prop` proof obligation in WS-S/S1-B. Callers must provide
evidence that `size > 0 ∧ endAddr ≤ 2^physAddrWidth`. A `Decidable` instance
enables `decide`/`native_decide` and `if`-expressions.

**`AccessRightSet.valid`** (`SeLe4n/Model/Object/Types.lean`): Added in
WS-S/S1-G. The well-formedness predicate `bits < 2^5` ensures no spurious
upper bits exist. `AccessRightSet.ofNat` masks inputs to the valid 5-bit range.
