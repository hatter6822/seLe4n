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
8. [Non-Negotiable Baseline Contracts](#8-non-negotiable-baseline-contracts)
9. [Audit Baselines](#9-audit-baselines)
10. [Security and Threat Model](#10-security-and-threat-model)

---

## 1. Project Identity

**seLe4n** is a novel microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked — zero
`sorry`, zero `axiom` across the entire production proof surface.

The project keeps four concerns in one engineering loop:

1. deterministic transition semantics (executable pure functions),
2. machine-checked invariant preservation (1,086 theorem/lemma declarations),
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
| **Package version** | `0.15.7` (`lakefile.toml`) |
| **Lean toolchain** | `v4.28.0` (`lean-toolchain`) |
| **Production LoC** | 35,009 across 68 Lean files |
| **Test LoC** | 3,459 across 4 Lean test suites |
| **Proved declarations** | 1,126 theorem/lemma declarations (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_CODEBASE_v0.13.6.md`](../audits/AUDIT_CODEBASE_v0.13.6.md) — zero critical issues |
| **Next workstreams** | WS-J1 register-indexed authoritative namespaces — J1-A completed (v0.15.4, typed `RegName`/`RegValue` wrappers), J1-B completed (v0.15.5, register decode layer with `RegisterDecode.lean`), J1-C completed (v0.15.6, syscall entry point and dispatch; v0.15.7, audit refinements), J1-D completed (v0.15.8, invariant/NI integration), J1-E..F pending (testing, CdtNodeId cleanup) + Raspberry Pi 5 hardware binding |
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
| **WS-F6** | Invariant quality: `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (tautological predicates removed); `blockedOnNotificationNotRunnable` added to `ipcSchedulerContractPredicates` (6-tuple); `runnableThreadsAreTCBs` in `schedulerInvariantBundleFull` (6-tuple) with sorry-free preservation for all scheduler ops; `vspaceCrossAsidIsolation` in `vspaceInvariantBundle` (6-tuple); `default_serviceCountBounded` and `default_serviceGraphInvariant` proved; zero sorry/axiom | WS-F6 completed |
| **WS-H13** (v0.14.4) | CSpace, lifecycle & service model enrichment: `cspaceDepthConsistent` invariant in `capabilityInvariantBundle` (8-tuple → 6-tuple after WS-F6), `resolveCapAddress` theorems (`_deterministic`, `_zero_bits`, `_result_valid_cnode`), `serviceStop` backing-object verification (A-29), `serviceGraphInvariant` preservation proofs (`serviceRegisterDependency`, `serviceStart`, `serviceStop`), `cspaceMove` error-path atomicity theorem (A-21); CNode field migration (`depth`/`guardWidth`/`guardValue`/`radixWidth`); addresses H-01, A-21, A-29, A-30, M-17/A-31 | WS-H13 completed |
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
- Policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `serviceRestartChecked`) exercised by default in trace and probe harnesses.
- **WS-G1:** All 13 typed identifiers and the composite `SlotRef` key have `Hashable` instances with `@[inline]` for zero overhead. `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, enabling O(1) hash-based data structures for kernel performance optimization (WS-G2..G9).

---

## 4. Architectural Improvements over seL4

seLe4n is not a 1:1 formalization of seL4. It preserves seL4's capability-based
security model while introducing improvements that the Lean 4 proof framework enables:

| Area | seL4 | seLe4n Improvement |
|------|------|-------------------|
| **Service lifecycle** *(seLe4n extension)* | No kernel-level service concept | Service orchestration layer with dependency graphs, acyclic policy enforcement (novel seLe4n extension — not present in seL4) |
| **CDT representation** | Mutable doubly-linked list | Node-stable CDT with O(1) slot transfer via pointer/backpointer fixup |
| **IPC queuing** | Intrusive linked list | Dual-queue model (`sendQ`/`receiveQ`) with O(1) arbitrary removal; `blockedOnCall` state for call/reply semantics; reply-target scoping for confused-deputy prevention; formal `dualQueueSystemInvariant` with doubly-linked integrity (WS-H5) |
| **Information flow** | Binary high/low partition | Parameterized N-domain labels with per-endpoint flow policies |
| **Scheduling** | Priority-based round-robin | Priority + EDF scheduling with dequeue-on-dispatch semantics, per-TCB register context with inline context switch, and domain-aware partitioning |
| **Revocation** | Silent error swallowing | Strict variant (`cspaceRevokeCdtStrict`) reporting first failure with context |
| **Syscall boundary** *(WS-J1-A/B/C/D completed)* | C code extracts args from registers | Typed register wrappers (J1-A) + total decode layer with `RegisterDecode.lean`, round-trip lemmas, determinism proof, and error exclusivity (J1-B) + `syscallEntry` register-sourced entry point with capability-gated dispatch to all 13 kernel operations, soundness theorems (J1-C) + invariant preservation and NI coverage for decode/dispatch path with `registerDecodeConsistent` predicate and 2 new `NonInterferenceStep` constructors (J1-D) |

These are not abstract research extensions — they are design decisions that will be
carried forward into the production kernel.

---

## 5. Completed Workstream Portfolio (WS-G) and Next Steps

The WS-G portfolio addressed kernel performance optimization findings from the
[v0.12.5 performance audit](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All 9 workstreams completed (v0.12.6–v0.12.15), closing all 14 findings.

Authoritative detail:
[`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).

### 5.1 Completed — Data Structure Optimization

- **WS-G1:** ~~Typed identifier Hashable instances~~ **COMPLETED** — `Hashable` + `LawfulHashable` for all 13 typed identifiers; `Std.HashMap`/`Std.HashSet` imports; zero-overhead foundation for O(1) lookups (v0.12.6)
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

| Operation | seL4 Equivalent | Rationale | Prerequisite |
|-----------|----------------|-----------|--------------|
| `setPriority` | `seL4_TCB_SetPriority` | Requires MCS scheduling context model | MCS scheduling (long-horizon) |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | Same MCS prerequisite | MCS scheduling (long-horizon) |
| `suspend` | `seL4_TCB_Suspend` | Requires thread lifecycle state machine | WS-F6 (lifecycle invariants) |
| `resume` | `seL4_TCB_Resume` | Inverse of suspend; same prerequisite | WS-F6 (lifecycle invariants) |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | Requires VSpace validation via page walk | H3 (VSpace integration) |

These operations are tracked in `SeLe4n/Kernel/API.lean` (stability table) and
`docs/CLAIM_EVIDENCE_INDEX.md` (evidence tracking).

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

## 8. Non-Negotiable Baseline Contracts

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
9. syscall capability-checking: `SyscallGate` + `syscallLookupCap` model the seL4 CSpace-lookup + rights-check pattern; 13 `api*` wrappers gate user-space invocations; 3 soundness theorems prove capability requirements.
10. HashMap-backed equality for `VSpaceRoot` and `CNode` is order-independent (size + fold containment), and the migrated state stores (`services`, `irqHandlers`, `capabilityRefs`, `cdtSlotNode`, `cdtNodeSlot`) are `Std.HashMap`-backed (no closure-chain metadata stores).

---

## 9. Audit Baselines

### 9.1 Active Baselines

| Artifact | Path |
|----------|------|
| Codebase audit v1 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) |
| Codebase audit v2 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Execution baseline (WS-F) | [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) |

### 9.2 Prior Baselines (completed)

| Artifact | Path |
|----------|------|
| Findings baseline (v0.11.6) | [`docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md`](../dev_history/audits/AUDIT_CODEBASE_v0.11.6.md) |
| Execution baseline (WS-E) | [`docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |
| Findings baseline (v0.11.0) | [`docs/dev_history/audits/AUDIT_v0.11.0.md`](../dev_history/audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |

### 9.3 Historical Baselines

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/).

---

## 10. Security and Threat Model

Security assumptions and trust boundaries are documented in
[`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
