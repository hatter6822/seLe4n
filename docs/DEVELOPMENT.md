# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current project state**:

- **active workstream:** **WS-Y Phase Y1 COMPLETE** (v0.22.23). Phases Y2–Y3 planned. **WS-X PORTFOLIO COMPLETE** (v0.22.18–v0.22.22). All prior portfolios complete: WS-W (v0.22.11–v0.22.17), WS-V (v0.22.0–v0.22.9), WS-U (v0.21.0–v0.21.7), WS-T (v0.20.0–v0.20.7), WS-S–WS-B (see `docs/WORKSTREAM_HISTORY.md`),
- **recently completed:** WS-J1-C audit refinements (v0.15.7 — CSpace/lifecycle/VSpace dispatch returns `illegalState` for MR-dependent ops, `syscallEntry` accepts `regCount` parameter, `syscallEntry_implies_capability_held` strengthened to full capability-resolution chain; zero sorry/axiom), WS-J1-C (v0.15.6, syscall entry point and dispatch — `syscallEntry` top-level entry point, `lookupThreadRegisterContext` TCB register extraction, `dispatchSyscall` routing through `SyscallGate`/`syscallInvoke` to 13 internal kernel operations, `dispatchWithCap` per-syscall routing, `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to field; 5 soundness theorems; zero sorry/axiom), WS-J1-B (v0.15.5, register decode layer — `SyscallId` inductive with 13 syscalls, `MessageInfo` bit-field structure, `SyscallDecodeResult`, total deterministic decode functions in `RegisterDecode.lean`, round-trip/determinism/error-exclusivity theorems, `SyscallRegisterLayout` with ARM64 default, 3 new `KernelError` variants; zero sorry/axiom), WS-J1-A (v0.15.4, typed register wrappers — replaced `abbrev RegName/RegValue := Nat` with typed wrapper structures, full instance suites, all 10 machine lemmas re-proved, downstream compilation fixed across Architecture/Platform/Testing; zero sorry/axiom), WS-H15 (v0.14.7, platform & API hardening — `InterruptBoundaryContract` decidability, RPi5 contract hardening with substantive predicates, 13 capability-gated syscall wrappers, `AdapterProofHooks` concrete instantiation for Sim/RPi5, MMIO disjointness proof; closes A-33, A-41, A-42, M-13), WS-H14 (v0.14.6, type safety & Prelude foundations — `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal for type-safety enforcement, sentinel predicate completion), Module restructuring (v0.14.5, decomposed 9 monolithic files into 24 focused submodules via re-export hub pattern; zero code loss, 50 new helper theorems extracted, 209 Tier 3 anchor checks updated), WS-H13 (v0.14.4, CSpace/service model enrichment — `cspaceDepthConsistent` invariant, `resolveCapAddress` theorems, `serviceGraphInvariant` preservation, `cspaceMove` atomicity; addresses H-01, A-21, A-29, A-30, M-17/A-31; WS-Q1: `serviceStop` backing-object verification removed), WS-H12f (v0.14.3, test harness update & documentation sync — dequeue-on-dispatch, context switch, and bounded message trace scenarios; legacy `endpointInvariant` comment cleanup; expected fixture updated; Tier 3 anchors added; documentation synchronized), WS-H12e (v0.14.2, cross-subsystem invariant reconciliation), WS-H12d (v0.14.1, IPC message payload bounds — A-09 closed), WS-H12c (v0.14.0, per-TCB register context with inline context switch — H-03 closed), WS-H12b (v0.13.9, dequeue-on-dispatch scheduler semantics — H-04 closed), WS-H12a (v0.13.8, legacy endpoint removal), WS-H11 (v0.13.7, VSpace & architecture enrichment), End-to-end audit (v0.13.6), WS-H10 (v0.13.6, security model foundations), WS-H7/H8/H9 gaps closed (v0.13.5), WS-H9 (v0.13.4, NI coverage >80%), WS-H8 (v0.13.2, enforcement-NI bridge), WS-H6 (v0.13.1, scheduler proof completion), WS-H5 (v0.12.19, IPC dual-queue invariant), WS-H4 (v0.12.18, capability invariant redesign), WS-H3 (v0.12.17, build/CI), WS-H2 (v0.12.16, lifecycle safety), WS-H1 (v0.12.16, IPC call-path fix), WS-G (v0.12.15, kernel performance), WS-F1..F4 (critical audit remediation),
- **findings baseline:** [`AUDIT_CODEBASE_v0.12.2_v1.md`](dev_history/audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](dev_history/audits/AUDIT_CODEBASE_v0.12.2_v2.md),
- **latest audit:** [`AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`](dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md) and [`AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md`](dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md) — dual comprehensive audits (115+ findings, 0 Critical),
- **hardware target:** Raspberry Pi 5 (ARM64).

Canonical planning sources:
[`docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md) for WS-X (all 5 phases complete),
[`docs/dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) for WS-U (Phase U8 complete — all 8 phases delivered),
[`docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md) for WS-T (complete),
[`docs/dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md) for WS-S (completed),
[`docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md) for WS-R (completed),
[`docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md) for WS-Q (completed), and
[`docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) for completed WS-H remediation lineage.

---

## 2) Non-negotiable baseline contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
4. domain-aware scheduling semantics (`schedule` only chooses from `activeDomain`; `scheduleDomain` switch/tick behavior is regression-tested),
5. theorem discoverability through stable naming,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: keep `SeLe4n.lean` free of duplicate/redundant subsystem imports by relying on `SeLe4n/Kernel/API.lean` as the canonical aggregate surface.

---

## 3) Next workstreams

The WS-F portfolio (v0.12.2 audit) is fully complete — all 33 findings closed.
The WS-J1 portfolio (v0.14.10) is fully complete — all 6 phases closed.
The **WS-K** portfolio (v0.16.0–v0.16.8) is **fully complete** — all 8 phases
(K-A through K-H) delivered: full syscall dispatch with message register
extraction, per-syscall argument decode, 13/13 dispatch, service policy
configuration, IPC message population, 44+ theorems, 34 NI step constructors,
comprehensive testing, and documentation sync. See
[`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md).

The **WS-L** portfolio (IPC subsystem audit & remediation) is **fully complete**
(v0.16.9–v0.16.13) — all 5 phases delivered: L1 (performance), L2 (code quality),
L3 (proof strengthening), L4 (test coverage), L5 (documentation & closeout).
12 of 13 findings resolved, 1 intentionally deferred (L-T03: cap transfer requires
CSpace IPC integration not yet modeled). All 4 WS-I5 deferred items resolved.
See [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md).

The **WS-M** portfolio (Capability subsystem audit & remediation) is **fully
complete** (v0.16.14–v0.17.0) — all 5 phases delivered: M1 (proof strengthening,
v0.16.14), M2 (performance optimization, v0.16.15), M3 (IPC capability transfer,
v0.16.17), M4 (test coverage expansion, v0.16.18), M5 (streaming BFS revocation
+ documentation sync, v0.16.19), plus v0.17.0 (shared `processRevokeNode` helper
extraction, unified BFS revocation proofs, edge-case test expansion). All 14
audit findings resolved. Zero sorry/axiom.
See [`AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md).

The **WS-Q** portfolio (Kernel State Architecture) is **fully complete**
(v0.17.7–v0.17.14) — a multi-phase plan unifying two-phase state architecture,
service interface simplification, and Rust syscall wrappers into a single execution path.
**WS-Q1** (v0.17.7) — service interface simplification — **COMPLETED**:
stateless registry model replacing lifecycle-based `ServiceStatus`/`ServiceConfig`.
**WS-Q2** (v0.17.8) — universal RHTable migration — **COMPLETED**: replaced
every `Std.HashMap` and `Std.HashSet` in kernel state (16 map fields + 2 set
fields across 6 structures, 30+ files) with formally verified `RHTable`/`RHSet`.
10 atomic subphases (Q2-A through Q2-J) including `RHSet` type definition,
`allTablesInvExt` global invariant predicate, and `invExt` proof threading
across all subsystem invariant files.
**WS-Q3** (v0.17.9) — IntermediateState formalization — **COMPLETED**:
`IntermediateState` type wrapping `SystemState` with four machine-checked
invariant witnesses (`allTablesInvExt`, `perObjectSlotsInvariant`,
`perObjectMappingsInvariant`, `lifecycleMetadataConsistent`). 7 builder
operations (`registerIrq`, `registerService`, `addServiceGraph`,
`createObject`, `deleteObject`, `insertCap`, `mapPage`). Boot sequence
(`bootFromPlatform`) with master validity theorem. Zero sorry/axiom, 1,479
proved declarations, all tests pass.
**WS-Q4** (v0.17.10) — CNode radix tree (verified) — **COMPLETED**:
`CNodeRadix` flat radix array for CNode capability slots with O(1) zero-hash
lookup via `extractBits` + direct array indexing. 24 correctness proofs
(lookup roundtrip, WF preservation, parameter invariance, size bounds,
toList completeness/noDup, fold coverage). `buildCNodeRadix` equivalence
bridge (RHTable → CNodeRadix), `freezeCNodeSlots` Q5 integration, 12-scenario
test suite (43 checks). Zero admitted proofs, 1,527 proved declarations,
all tests pass.
**WS-Q5** (v0.17.11) — FrozenSystemState + freeze — **COMPLETED**:
`FrozenMap`/`FrozenSet` types, per-object frozen representations (`FrozenCNode`
with `CNodeRadix`, `FrozenVSpaceRoot` with `FrozenMap`), `freeze` function
(IntermediateState → FrozenSystemState), capacity planning. 20+ theorems,
15-scenario test suite (49 checks). Zero sorry/axiom, 1,558 proved declarations.
**WS-Q6** (v0.17.12) — Freeze correctness proofs — **COMPLETED**:
machine-checked proofs that `freeze` preserves lookup semantics and kernel
invariants. Core `freezeMap_get?_eq` theorem + 13 per-field lookup equivalence
theorems (Q6-A). CNode radix lookup equivalence via generic fold helpers (Q6-B).
5 structural property theorems (Q6-C). Invariant transfer with keystone
`freeze_preserves_invariants` theorem (Q6-D). 31 theorems in
`SeLe4n/Model/FreezeProofs.lean`, 22-scenario test suite (60 checks). Zero
sorry/axiom.
**WS-Q7** (v0.17.13) — Frozen kernel operations — **COMPLETED**:
`FrozenKernel` monad with 14 per-subsystem frozen operations across 5 subsystems
(Scheduler, IPC, Capability, VSpace, Service). FrozenMap set/get? commutativity
proofs, 18 frozenStoreObject preservation theorems. 15-scenario test suite
covering TPH-005 through TPH-014. Zero sorry/axiom.
**WS-Q8** (v0.17.13) — Rust syscall wrappers — **COMPLETED**:
`libsele4n` — 3 `no_std` Rust crates (`sele4n-types`, `sele4n-abi`, `sele4n-sys`)
encoding the finalized ABI surface (17 syscalls, V2-A/D). 14 newtype identifiers,
34-variant `KernelError`, `MessageInfo` bitfield, ARM64 `svc #0` trap (single
`unsafe` block), safe high-level wrappers for all syscalls, phantom-typed
`Cap<Obj, Rts>` handles with sealed traits. 64 unit tests + 25 conformance tests.
Lean trace harness cross-validation (XVAL-001..004). Zero Lean regression.
**WS-Q9** (v0.17.14) — Integration testing + documentation — **COMPLETED**:
`TwoPhaseArchSuite.lean` with 14 integration tests (41 checks) covering the full
builder→freeze→execution pipeline (TPH-001 through TPH-014). Commutativity
property verified. Rust conformance XVAL-001..019 verified. SRG-001..010
verified. Full documentation sync across 15+ files. Scenario registry updated.
**WS-Q portfolio is now COMPLETE** (all 9 phases, 45 atomic units of work).
See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md).

The **WS-N** portfolio (Robin Hood hashing verified implementation) is **fully
complete** (v0.17.0–v0.17.5) — 5 phases (N1–N5, 122 subtasks): core types +
operations (N1, v0.17.1), invariant proofs (N2, v0.17.2), kernel API bridge
(N3, v0.17.3), CNode.slots integration (N4, v0.17.4), test coverage +
documentation (N5, v0.17.5). ~4,655 LoC, zero sorry/axiom.
See [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md).

The **WS-S** portfolio (Pre-Benchmark Strengthening) is **fully complete**
(v0.19.0–v0.19.6) — 7 phases (S1–S7), 83 sub-tasks addressing all findings from
dual comprehensive v0.18.7 audits (115+ findings, 0 Critical). All 5 High, 29
Medium, and 19 Low findings resolved. Closure report:
[`WS_S_CLOSURE_REPORT.md`](dev_history/audits/WS_S_CLOSURE_REPORT.md).

**WS-S testing practices introduced (S2):**
- **Structural assertions**: test determinism checks use `BEq Except` structural
  equality instead of `toString`-based string comparison. All 101 `reprStr`
  occurrences replaced with `toString`.
- **Builder-based test states**: `buildChecked` enforces 8 runtime invariant
  checks during test state construction; primary test states (`baseState`,
  `f2UntypedState`, `f2DeviceState`) use `buildChecked`.
- **Error-path coverage**: 11 error-path tests covering capability failures
  (rights attenuation, full CNode, deep CDT revoke) and lifecycle failures
  (region exhaustion, child ID collision, device untyped rejection).
- **Golden-output fixture management**: `test_tier2_trace.sh` provides enhanced
  diff reporting when `tests/fixtures/main_trace_smoke.expected` drifts.
- **Shared test helpers**: `Testing/Helpers.lean` module with `expectCond`,
  `expectError`, `expectOk` shared across test suites.
- **SimRestrictive platform variant** (S5-D): substantive contracts with timer
  monotonicity, 256 MiB RAM bound, and register write denial for testing.

The **WS-R** portfolio (Comprehensive Audit Remediation) is **fully complete**
(v0.18.0–v0.18.7) — 8 phases (R1–R8), 111 sub-tasks addressing all 82 findings from
[`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md).

The **next major milestone** is **Raspberry Pi 5 hardware binding**:
populating RPi5 platform stubs with hardware-validated contracts, implementing
ARMv8 multi-level page table walk, GIC-400 interrupt routing, ARM Generic Timer
binding, and verified boot sequence construction.

**S5-F: Pre-hardware-binding gate — BCM2712 address validation.** Before H3
begins, every address constant in `SeLe4n/Platform/RPi5/Board.lean` must be
cross-referenced against the BCM2712 ARM Peripherals datasheet. A validation
checklist is maintained in `Board.lean` (see the "BCM2712 Address Validation
Checklist" section). The gate requires all 14 constants to be marked "Validated"
with exact datasheet references (document title, revision, page number).

**WS-J1 (completed):** register-indexed authoritative
namespace migration with typed register wrappers, syscall argument decode layer,
and `CdtNodeId` cleanup (6 phases: J1-A through J1-F). **WS-J1-A completed (v0.15.4):**
replaced `RegName`/`RegValue` `abbrev Nat` definitions with typed wrapper structures,
added full instance suites, re-proved all machine lemmas, fixed downstream compilation.
**WS-J1-B completed (v0.15.5):** added `SyscallId`, `MessageInfo`, `SyscallDecodeResult`
types, total decode functions in `RegisterDecode.lean`, round-trip and determinism proofs,
`SyscallRegisterLayout` with ARM64 default, `MachineConfig.registerCount`, 3 new `KernelError`
variants.
**WS-J1-C completed (v0.15.6):** added `syscallEntry` top-level user-space entry point,
`lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing
through `SyscallGate`/`syscallInvoke`, `dispatchWithCap` per-syscall routing for all 13
syscalls, `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted
to configurable field; 5 soundness theorems proved.
**WS-J1-C audit refinements (v0.15.7):** CSpace/lifecycle/VSpace dispatch returns `illegalState`
for MR-dependent ops (full MR extraction deferred to WS-J1-E), `syscallEntry` accepts
`regCount` parameter for architectural bounds, `syscallEntry_implies_capability_held`
strengthened to full capability-resolution chain.
**WS-J1-D completed (v0.15.8):** invariant and information-flow integration for
decode path; `decodeSyscallArgs_preserves_lowEquivalent` NI theorem; capability
invariant preservation through `syscallEntry`; scheduler invariant preservation
through register decode; bridge theorems in Enforcement/Soundness and
InformationFlow/Invariant/Composition.
**WS-J1-E completed (v0.15.9):** testing and trace evidence — 18 negative
decode tests in `NegativeStateSuite.lean`; 5 register-decode trace scenarios
(RDT-002 through RDT-010) in `MainTraceHarness.lean`; 2 operation-chain tests
(`chain10RegisterDecodeMultiSyscall`, `chain11RegisterDecodeIpcTransfer`) in
`OperationChainSuite.lean`; fixture updates; 13 Tier 3 invariant surface
anchors for RegisterDecode definitions and theorems.
**WS-J1-F completed (v0.15.10):** CdtNodeId cleanup and documentation sync —
replaced `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat`,
added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
`LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`), fixed downstream
compilation in `SystemState` defaults and test literals, documentation synchronized.
**WS-J1 portfolio fully completed.** All 16 kernel identifiers are now typed wrappers.
WS-I1..WS-I4 are completed; WS-I5 Part A (R-12) is superseded by WS-J1.

### 3.1 WS-H11..H16 — v0.12.15 audit remediation status (completed)

See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-H11** | VSpace & architecture enrichment (PagePermissions, W^X, TLB model) | Medium | **Completed** |
| **WS-H12a** | Legacy endpoint field & operation removal | Medium | **Completed** |
| **WS-H12b** | Dequeue-on-dispatch scheduler semantics | Medium | **Completed** |
| **WS-H12c** | Per-TCB register context with inline context switch | Medium | **Completed** |
| **WS-H12d** | IPC message payload bounds | Medium | **Completed** |
| **WS-H12e** | Cross-subsystem invariant reconciliation | Medium | **Completed** |
| **WS-H12f** | Test harness update & documentation sync | Medium | **Completed** |
| **WS-H13** | CSpace/service model enrichment (multi-level resolution, backing-object verification, serviceCountBounded) | Medium | **Completed** |
| **WS-H14** | Type safety hardening: EquivBEq/LawfulBEq instances, LawfulMonad proofs, isPowerOfTwo verification, OfNat removal, sentinel completion | Low | **Completed** |
| **WS-H15** | Platform & API hardening (RPi5 contracts, syscall capability wrappers, AdapterProofHooks) | Low | **Completed** |
| **WS-H16** | Testing and documentation expansion | Low | Planned |

### 3.2 WS-F5..F8 — Remaining v0.12.2 audit remediation

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | **Completed** |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | **Completed** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | **Completed** |
| **WS-F8** | Cleanup (dead type constructors, extension labeling, finding closure) | Low | **Completed** |

### 3.3 Completed portfolios

- **WS-I3:** completed (v0.15.2). Test coverage expansion — new `tests/OperationChainSuite.lean` adds 6 multi-operation chain tests (retype→mint→revoke, send/send/receive FIFO, map/lookup/unmap/lookup, service start/stop dependency sequencing, copy/move/delete, notification badge accumulation), scheduler stress coverage (16-thread repeated scheduling, same-priority determinism, multi-domain isolation), and Tier 2 integration via `scripts/test_tier2_negative.sh`; `tests/InformationFlowSuite.lean` now includes declassification runtime checks for authorized downgrade, normal-flow rejection, policy-denied rejection, and 3-domain lattice behavior. Closes R-06/R-07/R-08. Declassification policy denial now reports a distinct `declassificationDenied` error in `declassifyStore` and suite expectations.
- **WS-I4:** completed (v0.15.3). Subsystem coverage expansion — `tests/OperationChainSuite.lean` now includes VSpace multi-ASID shared-page coherency and per-ASID-permission checks (R-09), IPC interleaved send ordering checks with three-sender FIFO + alternating send/receive validation (R-10), and lifecycle cascading revoke/authority-degradation chains over CDT-linked root→child→grandchild caps (R-11).
- **WS-I1:** completed (v0.15.0). Critical testing infrastructure — 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation (R-02), scenario ID traceability with 121 tagged trace lines, pipe-delimited fixture format, scenario registry YAML with Tier 0 validation (R-03). Phase 1 of the WS-I improvement portfolio. Closes R-01/R-02/R-03.
- **WS-F8:** completed. Cleanup — removed dead `ServiceStatus.failed`/`isolated` constructors, labeled Service subsystem as seLe4n extension with module docstrings (MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised — finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04, MED-17, F-01, F-14, F-19.
- **WS-F7:** completed. Testing expansion — 4 new runtime invariant checks (`blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`, `currentThreadInActiveDomain`, `uniqueWaiters`) added to `InvariantChecks.lean`; `TraceSequenceProbe` extended from 3 to 7 operation families (+ notification signal/wait, schedule, capability lookup) with blocked-thread guard; `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` fixtures exercised in `MainTraceHarness` with 6 deterministic trace assertions; CDT `childMapConsistentCheck` confirmed already delivered. Zero sorry, zero axiom. Closes MED-08, F-24, F-25, F-26.
- **WS-F6:** completed (v0.14.9). Invariant quality — tautology reclassification, cross-subsystem coupling, adapter proof hooks. `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (removed tautological `cspaceInvariant`/`badgeInvariant`); `blockedOnNotificationNotRunnable` predicate added to `ipcSchedulerContractPredicates` (6-conjunct); `runnableThreadsAreTCBs` predicate added to `schedulerInvariantBundleFull` (6-conjunct) with 4 preservation theorems (`switchDomain`, `schedule`, `handleYield`, `timerTick`); `vspaceCrossAsidIsolation` added to `vspaceInvariantBundle` (6-conjunct) with `mapPage`/`unmapPage` proofs; `default_serviceCountBounded` and `default_serviceGraphInvariant` proved for service graph; bundle coherence verified across all subsystems. Zero sorry, zero axiom.
- **WS-H12f:** completed (v0.14.3). Test harness update & documentation sync — `runDequeueOnDispatchTrace` (dequeue-on-dispatch lifecycle with preemption re-enqueue), `runInlineContextSwitchTrace` (inline context save/restore verification through `handleYield` → `schedule`), `runBoundedMessageExtendedTrace` (zero-length, sub-boundary, max-caps acceptance); legacy `endpointInvariant` comment cleanup; expected fixture updated (108 lines); 9 new Tier 3 anchors; documentation synchronized. Completes WS-H12 composite workstream.
- **WS-H12e:** completed (v0.14.2). Cross-subsystem invariant reconciliation — `coreIpcInvariantBundle` upgraded from `ipcInvariant` to `ipcInvariantFull` (includes `dualQueueSystemInvariant` and `allPendingMessagesBounded`); `schedulerInvariantBundleFull` extended with `contextMatchesCurrent` (5-conjunct); `ipcSchedulerCouplingInvariantBundle` extended with `contextMatchesCurrent` and `currentThreadDequeueCoherent`; `proofLayerInvariantBundle` uses `schedulerInvariantBundleFull` (full bundle) instead of bare `schedulerInvariantBundle`; extraction theorems added; `switchDomain_preserves_contextMatchesCurrent` new preservation theorem; 8 `allPendingMessagesBounded` frame lemmas for primitive ops; 3 compound `*_preserves_allPendingMessagesBounded` theorems (notificationSignal, notificationWait, endpointReply); 7 composed `*_preserves_ipcInvariantFull` theorems for all IPC operations; all `*_preserves_schedulerInvariantBundleFull` theorems updated; default state proofs extended; Tier 3 invariant surface anchors updated. Completes deferred WS-H12d preservation theorems. Closes systemic invariant composition gaps from WS-H12a–d.
- **WS-H12d:** completed (v0.14.1). IPC message payload bounds — `IpcMessage` registers/caps migrated from `List` to `Array` with `maxMessageRegisters`(120)/`maxExtraCaps`(3), bounds enforcement at all 4 send boundaries, 4 `*_message_bounded` theorems, `allPendingMessagesBounded` system invariant, A-09 closed.
- **WS-H12c:** completed (v0.14.0). Per-TCB register context with inline context switch — `registerContext` field on TCB, `saveOutgoingContext`/`restoreIncomingContext` in `schedule`, information-flow projection strips register context, `endpointInvariant` removed, H-03 closed.
- **WS-H12b:** completed (v0.13.9). Dequeue-on-dispatch scheduler semantics — `queueCurrentConsistent` inverted from `current ∈ runnable` to `current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue`. `schedule` dequeues chosen thread before dispatch; `handleYield` inserts+rotates current thread before scheduling; `timerTick` re-enqueues on preemption; `switchDomain` re-enqueues before domain switch. Added `currentTimeSlicePositive` predicate to `schedulerInvariantBundleFull`; added `schedulerPriorityMatch` with `RunQueue.insert_preserves_wellFormed` and `insert_threadPriority` theorems. IPC predicates added: `currentThreadIpcReady`, `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, `currentThreadDequeueCoherent`. Helper lemmas `ensureRunnable_not_mem_of_not_mem`, `removeRunnable_not_mem_of_not_mem`, `ThreadId.ext`. ~1800 lines of preservation proofs re-proved. Closes H-04 (HIGH).
- **WS-H11:** completed (v0.13.7). VSpace & architecture enrichment — `PagePermissions` structure with `read`/`write`/`execute`/`user`/`cacheable` fields and `wxCompliant` W^X enforcement; `VSpaceRoot.mappings` enriched from `HashMap VAddr PAddr` to `HashMap VAddr (PAddr × PagePermissions)`; `vspaceMapPage` enforces W^X at insertion (`policyDenied` on violation); `vspaceLookupFull` returns `(PAddr × PagePermissions)`; `vspaceInvariantBundle` extended from 3 to 5 conjuncts (`wxExclusiveInvariant`, `boundedAddressTranslation` integrated); `VSpaceBackend` typeclass enriched with permissions; `MemoryRegion.wellFormed` and `MachineConfig.wellFormed` enforce `endAddr ≤ 2^physicalAddressWidth`; `TlbState`/`TlbEntry` abstract TLB model with `adapterFlushTlb`/`adapterFlushTlbByAsid` operations; `tlbConsistent` invariant with flush-restoration and composition theorems. Closes H-02/A-32 (HIGH), H-10 (HIGH), A-05/M-12 (HIGH), A-12 (HIGH), M-14 (MEDIUM).
- **WS-H10:** completed (v0.13.6). Security model foundations — `ObservableState` extended with `machineRegs` (domain-gated register file projection); machine timer excluded as covert timing channel; `bibaIntegrityFlowsTo`/`bibaSecurityFlowsTo`/`bibaPolicy` standard BIBA alternatives with refl/trans proofs; `DeclassificationPolicy` with `declassifyStore` enforcement operation (5 theorems) and `declassifyStore_NI` non-interference proof; `endpointFlowPolicyWellFormed` predicate with reflexivity/transitivity inheritance proofs; `InformationFlowConfigInvariant` bundle. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL), A-39 (MEDIUM), M-16 (MEDIUM). 866 proved declarations.
- **WS-H7/H8/H9 gap closure:** completed (v0.13.5). Comprehensive audit remediation — `VSpaceRoot.beq_sound`/`CNode.beq_sound` BEq soundness lemmas (WS-H7), `endpointReceiveDualChecked_NI` enforcement bridge (WS-H8), `endpointReceiveDual_preserves_lowEquivalent`/`endpointCall_preserves_lowEquivalent`/`endpointReplyRecv_preserves_lowEquivalent` hypothesis-based IPC NI theorems (WS-H9), `NonInterferenceStep` extended to 31 constructors with `endpointReceiveDualHigh`/`endpointCallHigh`/`endpointReplyRecvHigh`. 840 proved declarations.
- **WS-H9:** completed (v0.13.4). Non-interference coverage extension >80% of kernel operations — 27 new NI preservation theorems, `NonInterferenceStep` extended from 11 to 28 constructors, scheduler/IPC/CSpace/VSpace/observable-state NI proofs, `switchDomain_preserves_lowEquivalent` two-sided proof, `composedNonInterference_trace` covers all constructors. Closes C-02/A-40 (CRITICAL), M-15 (MEDIUM).
- **WS-H8:** completed (v0.13.2). Enforcement-NI bridge & missing wrappers — enforcement soundness meta-theorems connecting `securityFlowsTo` checks to non-interference; 4 new policy-checked wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`); `ObservableState` extended with domain timing metadata (`domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`); NI bridge theorems for all new wrappers. Closes A-35/H-07 (CRITICAL), H-07 (HIGH), A-36/A-37/H-11 (HIGH). 26 new theorems; 779 total.
- **WS-H6:** completed (v0.13.1). Scheduler proof completion — `timeSlicePositive` preservation proven for all 6 scheduler operations (`setCurrentThread`, `chooseThread`, `schedule`, `handleYield`, `switchDomain`, `timerTick`); `edfCurrentHasEarliestDeadline` fixed to be domain-aware (closing false-assurance gap); `chooseBestRunnableBy_optimal` (fold-based candidate optimality), `noBetter_implies_edf` (bridge to EDF invariant), `isBetterCandidate_not_better_trans` (negation transitivity); `schedulerInvariantBundleFull` (5-tuple bundle with projection and composition); plus earlier Part D/E work (`flat_wf_rev`, `mem_toList_iff_mem`, `isBetterCandidate_transitive`, `bucketFirst_fullScan_equivalence`).
- **WS-H7:** completed (v0.12.21). HashMap equality + state-store migration — `BEq VSpaceRoot`/`BEq CNode` switched from `toList` order-sensitive checks to size+fold order-independent checks; `services`, `irqHandlers`, `lifecycle.capabilityRefs`, `cdtSlotNode`, and `cdtNodeSlot` migrated from closure functions to `Std.HashMap`, removing O(k) closure-chain accumulation.
- **WS-H5:** completed (v0.12.19). IPC dual-queue structural invariant — `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems for all dual-queue operations. Closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H4:** completed (v0.12.18). Capability invariant redesign — `capabilityInvariantBundle` extended from trivially-true 4-tuple to meaningful 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`. All preservation theorems re-proved. C-03, M-08/A-20, M-03. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H3:** completed (v0.12.17). Build/CI infrastructure fixes — `run_check` return value fix (H-12), `test_docs_sync.sh` CI integration (M-19), Tier 3 `rg` availability guard with `grep -P` fallback (M-20). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H2:** completed (v0.12.16). Lifecycle safety guards — childId collision/self-overwrite guards, TCB scheduler cleanup on retype, CNode CDT detach, atomic retype. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H1:** completed (v0.12.16). IPC call-path semantic fix — `blockedOnCall` variant, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates`. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G1..G9:** all completed (v0.12.6–v0.12.15). See [`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).
- **WS-F1..F4:** completed. See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).
- **WS-E1..E6:** all completed (historical archive).
- **WS-D1..D4:** completed (historical archive).
- **WS-C1..C8:** completed (historical archive).

### 3.4 PR-to-workstream discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 4) Security hardening defaults

- IPC thread-state updates now fail with `objectNotFound` when the target TCB is missing (including reserved thread ID `0`), preventing ghost queue entries in endpoint/notification paths.
- Sentinel ID `0` is rejected at IPC TCB lookup/update boundaries (`lookupTcb`/`storeTcbIpcState`) rather than silently treated as a valid runtime thread identity.
- Trace and probe harnesses now exercise policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `registerServiceChecked`) by default; unchecked operations remain available for research experiments. `enforcementBoundary` classifies 17 operations (3 policy-gated in base, 7 in extended). (WS-Q1: `serviceRestartChecked` removed, `registerServiceChecked` added — service lifecycle simplified to registry-only model; SRG-001 through SRG-010 test scenarios added.)
- WS-E4 dual-queue endpoint operations (`endpointSendDual`/`endpointReceiveDual`) use intrusive-list queue boundaries (`sendQ`/`receiveQ`) with per-thread links stored in `TCB.queuePrev`/`TCB.queuePPrev`/`TCB.queueNext`; invariant checks now include `intrusiveQueueWellFormed` validation for both endpoint queues (including head/tail shape, cycle-free traversal, and per-node `queuePrev`/`queuePPrev`/`queueNext` linkage), and `negative_state_suite` adds runtime queue-link assertions for both send-queue and receive-queue FIFO/dequeue paths alongside enqueue/block, rendezvous/dequeue, queue drain, O(1) middle removal via `endpointQueueRemoveDual`, malformed-`queuePPrev` rejection (`illegalState`), and dual-queue double-wait rejection (`alreadyWaiting`).
- WS-E4 CDT representation is node-stable: derivation edges are over stable node IDs and slots map to nodes via bidirectional maps (`cdtSlotNode`, `cdtNodeSlot`). `cspaceMove` updates slot→node ownership/backpointers instead of rewriting every CDT edge, `cspaceDeleteSlot` detaches stale slot↔node mappings on deletion, the observed slot-level CDT is defined as projection of node edges through the slot mapping (`SystemState.observedCdtEdges`), and strict revoke (`cspaceRevokeCdtStrict`) now reports the first descendant deletion failure with offending slot context.

## 5) Daily contributor loop

1. Sync branch and choose one coherent slice from the active plans (currently Raspberry Pi 5 hardware binding prep — WS-J1 register-namespace migration is fully completed).
2. Implement the minimal semantic/proof/doc delta.
3. Run smallest relevant check first, then higher tiers.
4. Update docs in the same commit range.
5. Re-run validation before commit.

Recommended command loop:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Optional nightly/staged checks:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Environment note for `./scripts/setup_lean_env.sh` on apt-based systems:

- if a third-party apt mirror is temporarily unavailable, the setup script now retries `apt-get update` with primary distro sources only so required tool installs (`shellcheck`, `ripgrep`) remain reproducible.

---

## 6) Proof engineering standards

1. Keep proofs local-first; compose afterward.
2. Prefer explicit theorem statements and stable names.
3. Keep invariant bundles factored and named.
   - Current canonical IPC composition names:
     - `coreIpcInvariantBundle`
     - `ipcSchedulerCouplingInvariantBundle`
     - `lifecycleCompositionInvariantBundle`
   - Current canonical trace helper names for these slices:
     - `runCapabilityIpcTrace`
     - `runSchedulerTimingDomainTrace`
4. Avoid hidden global simplification behavior.
5. Never add `axiom`/`sorry` to core proof surfaces.
6. BFS completeness proof (TPI-D07-BRIDGE): formally resolved. The core
   completeness theorem (CP1), its equational lemmas (EQ1-EQ5), and closure
   lemmas (CB1-CB4) are all proved. The prerequisite lemma hierarchy in
   [`M2_BFS_SOUNDNESS.md §6`](dev_history/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md)
   and its sub-documents ([M2A](dev_history/audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)–[M2D](dev_history/audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md))
   is fully discharged. No further work is required for this tracking item.

---

## 7) Documentation synchronization rules

For changes that alter behavior, theorem surfaces, or slice status, update in the same PR:

1. `README.md`
2. `docs/spec/SELE4N_SPEC.md` (and `docs/spec/SEL4_SPEC.md` if seL4 reference material changes)
3. `docs/DEVELOPMENT.md`
4. impacted GitBook chapter(s) and `docs/gitbook/SUMMARY.md` if IA changes
5. any directly affected audit/workstream status document

Use [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](./DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
for cross-document synchronization expectations.

Before touching any `Current state` numbers, run `./scripts/report_current_state.py`
and propagate the output verbatim to README/spec/GitBook mirrors in the same PR.
At minimum keep these attributes synchronized across all three surfaces: version,
Lean toolchain, production/test LoC, theorem+lemma count, build jobs, active
findings/audit references, and completed/next workstream status.

For codebase-map synchronization, run `./scripts/generate_codebase_map.py --pretty`
whenever Lean module/declaration surfaces change, then validate with
`./scripts/generate_codebase_map.py --pretty --check`. The generated
`docs/codebase_map.json` contains:

- **`readme_sync`** — project-level metrics (version, LoC, theorem count,
  hardware target) used by README.md, SELE4N_SPEC.md, and GitBook chapters.
- **`source_sync`** — stable `source_digest` (SHA256 over Lean source paths +
  contents) plus volatile `repository.head` git metadata.
- **`modules`** — per-module declaration inventory. Each declaration record
  includes an additive `called` array listing in-module declaration references
  (or `[]` when none are detected).

Website clients should invalidate local cache entries on
`source_sync.source_digest` changes. `--check` compares only the stable subset,
keeping CI robust across branch/merge-only commits while still detecting real
declaration-surface drift. Post-merge enforcement runs in
`.github/workflows/codebase_map_sync.yml`, which auto-regenerates and commits
the map on `main` when drift is detected.

### Test fixture update process (WS-L5-B)

When adding new trace scenarios to `MainTraceHarness.lean`:

1. Add `IO.println` calls with `[PREFIX-NNN]` scenario IDs.
2. Rebuild: `lake build`.
3. Run `lake exe sele4n` and verify new output lines appear.
4. Add fixture expectations to `tests/fixtures/main_trace_smoke.expected` using
   the format: `PREFIX-NNN | SUBSYSTEM | expected_trace_fragment`.
5. Add scenario registry entries to `tests/fixtures/scenario_registry.yaml` with
   `source`, `function`, `subsystem`, and `description` fields.
6. If the inter-transition invariant check count changes (ITR-001), update the
   count in both the fixture file and the scenario registry.
7. Validate: `./scripts/test_smoke.sh` (includes Tier 0 registry validation +
   Tier 2 fixture comparison).

### Golden-output fixture management (S2-D)

The `tests/fixtures/main_trace_smoke.expected` file is the golden fixture for
the kernel's executable trace output. Changes to this file require explicit
rationale because they indicate behavioral changes in kernel transitions.

**When to update the fixture:**
- Adding new trace scenarios (new kernel operations or test paths)
- Changing kernel transition semantics that affect trace output
- Modifying the trace format (e.g., scenario ID prefixes)

**When NOT to update the fixture:**
- A test fails unexpectedly — investigate the root cause first
- Cosmetic changes to non-trace output (e.g., `Repr` instances)

**Update procedure:**
1. Run `lake exe sele4n > /tmp/actual_trace.log` to capture actual output
2. Compare: `diff tests/fixtures/main_trace_smoke.expected /tmp/actual_trace.log`
3. Review each changed line — every difference should correspond to an
   intentional behavioral change
4. Update the fixture with the new expected output
5. Document the rationale in the commit message (e.g., "Update fixture: added
   S3-F RunQueue.remove well-formedness trace scenario")
6. Run `./scripts/test_smoke.sh` to verify the updated fixture passes

**Test assertions:** All test suites use structural equality (`BEq`/`DecidableEq`)
for comparison logic, not `reprStr` or `toString`. The `reprStr` function is
used only in diagnostic error messages when a test fails, not in the comparison
itself (S2-A). This ensures test stability across `Repr` instance changes.

### Metrics regeneration process (WS-L5-C)

When modifying production Lean source files:

1. Run `./scripts/report_current_state.py` to get updated metrics.
2. Update metrics in `README.md`, `docs/spec/SELE4N_SPEC.md`, and
   `docs/gitbook/05-specification-and-roadmap.md` — all three must match.
3. Run `./scripts/generate_codebase_map.py --pretty --output docs/codebase_map.json`
   to regenerate the machine-readable map.
4. Validate with `./scripts/generate_codebase_map.py --pretty --check`.
5. Verify: `./scripts/test_docs_sync.sh` (checks codebase map freshness).

---

## 8) Definition of done (milestone-moving changes)

A change is done when all are true:

- implementation compiles,
- trace/fixture behavior is intentionally stable or intentionally updated with rationale,
- theorem/invariant surface remains coherent and discoverable,
- tiered checks pass for the claimed scope,
- docs reflect exact current state (not intended future state).

---

## 9) Quick checklist (copy into PRs)

- [ ] Workstream ID(s) identified.
- [ ] Scope is one coherent slice.
- [ ] Transition semantics are explicit and deterministic.
- [ ] Invariant/theorem updates are paired with implementation changes.
- [ ] Required validation commands were run.
- [ ] Documentation was synchronized.
