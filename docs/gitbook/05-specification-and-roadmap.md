# Specification & Roadmap

This chapter summarizes the project specification. For the normative document:
[`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md).

## Project identity

seLe4n is a **production-oriented microkernel** written in Lean 4 with
machine-checked proofs, improving on seL4 architecture. First hardware target:
**Raspberry Pi 5** (ARM64).

## Current state

| Attribute | Value |
|-----------|-------|
| Version | `0.16.19` |
| Lean toolchain | `v4.28.0` |
| Production LoC | 39,444 across 71 files |
| Test LoC | 4,231 across 4 suites |
| Proved declarations | 1,248 theorem/lemma declarations (zero sorry/axiom) |
| Latest audit | [`AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md) — Capability subsystem end-to-end audit |
| Next workstreams | **WS-M** Capability subsystem audit & remediation — **PORTFOLIO COMPLETE** (v0.16.14–v0.16.19). All 5 phases (M1–M5) delivered. See [workstream plan](../audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md). **WS-L** IPC subsystem audit & remediation — **PORTFOLIO COMPLETE** (v0.16.9–v0.16.13). WS-K **PORTFOLIO COMPLETE** (v0.16.0–v0.16.8). **Next: Raspberry Pi 5 hardware binding** |
| Workstream history | [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) |
| Metrics source of truth | [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key) |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..F1-F4 (5 audit portfolios, all completed) → WS-G
(performance optimization, completed) → WS-H1 (IPC call-path semantic fix, completed) →
WS-H2 (lifecycle safety guards, completed) → WS-H3 (build/CI infrastructure, completed) →
WS-H4 (capability invariant redesign, completed) → WS-H5 (IPC dual-queue structural
invariant, completed) → WS-H6 (scheduler proof completion, completed) →
WS-H8 (enforcement-NI bridge & missing wrappers, completed) →
WS-H9 (non-interference coverage extension, completed) →
WS-H7/H8/H9 gap closure (comprehensive audit, v0.13.5) →
WS-H10 (security model foundations, v0.13.6) →
End-to-end codebase audit (v0.13.6) →
WS-H11 (VSpace & architecture enrichment, v0.13.7) →
WS-H12a (legacy endpoint removal, v0.13.8) →
WS-H12b (dequeue-on-dispatch scheduler semantics, v0.13.9) →
WS-H12c (per-TCB register context, v0.14.0) →
WS-H12d (IPC message payload bounds, v0.14.1) →
WS-H12e (cross-subsystem invariant reconciliation, v0.14.2) →
WS-H12f (test harness & docs sync, v0.14.3) →
WS-H13 (CSpace/service enrichment, v0.14.4) →
Module restructuring (24 focused submodules, v0.14.5) →
WS-H14 (type safety & Prelude foundations, v0.14.6) →
WS-H15 (platform/API hardening, v0.14.7) →
WS-H16 (testing/documentation cleanup, v0.14.8) →
WS-F5..F8 (model fidelity, invariant quality, testing, cleanup, v0.14.9) →
WS-I1 (critical testing infrastructure, v0.15.0) →
WS-J1-A (typed register wrappers, v0.15.4) →
WS-J1-B (register decode layer, v0.15.5) →
WS-J1-C (syscall entry point and dispatch, v0.15.6; audit refinements, v0.15.7) →
WS-J1-D (invariant/NI integration, v0.15.8) →
WS-J1-E (testing and trace evidence, v0.15.9) →
WS-J1-F (CdtNodeId cleanup + documentation sync, v0.15.10) →
**WS-K (full syscall dispatch completion, v0.16.0–v0.16.8) — PORTFOLIO COMPLETE.** →
WS-L1 (IPC performance optimization, v0.16.9) →
WS-L2 (code quality — HashMap.fold migration, v0.16.10) →
WS-L3 (proof strengthening — 22 theorems, v0.16.11) →
WS-L4 (test coverage expansion, v0.16.12) →
**WS-L5 (documentation & closeout, v0.16.13) — WS-L PORTFOLIO COMPLETE.** →
**WS-M1 (proof strengthening, v0.16.14) — COMPLETED.** →
**WS-M2 (performance optimization, v0.16.15) — COMPLETED.** →
**WS-M3 (IPC cap transfer, v0.16.17) — COMPLETED.** →
**WS-M4 (test coverage expansion, v0.16.18) — COMPLETED.** →
**WS-M5 (streaming BFS optimization, v0.16.19) — COMPLETED. WS-M PORTFOLIO COMPLETE.**

## Completed: WS-M Capability Subsystem Audit & Remediation (v0.16.13–v0.16.19, PORTFOLIO COMPLETE)

End-to-end audit of the Capability subsystem (3,520 LoC, 5 files) identified
14 findings across 4 categories: 5 performance optimizations (M-P01–P05),
4 proof gaps (M-G01–G04), 3 test coverage gaps (M-T01–T03), and 2 documentation
items (M-D01–D02). Also resolves deferred L-T03 (IPC capability transfer model).
All 5 phases (M1–M5) delivered across v0.16.14–v0.16.19. All 14 findings resolved.
Phase 1 (WS-M1, proof strengthening) completed at v0.16.14: 7 new proved
declarations including `resolveCapAddress_guard_match`, `cdtMintCompleteness`,
`addEdge_preserves_edgeWellFounded_fresh`, `cspaceRevokeCdt_swallowed_error_consistent`.
Phase 2 (WS-M2, performance optimization) completed at v0.16.15:
- M2-A: fused revoke (`revokeAndClearRefsState` single-pass replacing the prior two-pass fold),
- M2-B: CDT `parentMap` index for O(1) `parentOf` lookup (replacing O(E) edge scan),
- M2-C: reply lemma extraction and new field preservation lemmas for NI proofs,
- `parentMapConsistent` runtime check added to invariant surface.
Findings M-P01, M-P02, M-P03, M-P05 resolved at v0.16.15.
Phase 3 (WS-M3, IPC capability transfer) completed at v0.16.17:
- 20 atomic subtasks across 7 tasks: types, slot scanning, single-cap transfer, batch unwrap, IPC wrappers, API wiring, tests
- seL4-aligned architecture: cap unwrapping on receive side, Grant-right gate, CDT `.ipcTransfer` edge tracking
- Wrapper pattern preserves all existing IPC operation signatures and proofs
- `ipcTransferSingleCap`/`ipcUnwrapCaps` operations with preservation proofs
- `endpointSendDualWithCaps`/`endpointReceiveDualWithCaps`/`endpointCallWithCaps` wrappers
- IPC invariant preservation proofs for all wrappers; `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`
- `decodeExtraCapAddrs`/`resolveExtraCaps` API wiring, 4 test scenarios (basic, no-grant, full-CNode, badge+cap combined)
- Resolves L-T03 (capability transfer during IPC); 12+ new proved declarations
Phase 4 (WS-M4, test coverage expansion) completed at v0.16.18: 8 new test
scenarios addressing M-T01/M-T02.
Phase 5 (WS-M5, streaming BFS optimization) completed at v0.16.19:
`streamingRevokeBFS`/`cspaceRevokeCdtStreaming` operations with
`streamingRevokeBFS_step_preserves`, `streamingRevokeBFS_preserves`,
`cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` preservation
theorems. Resolves M-P04.
See [WS-M workstream plan](../audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md).

## Completed: WS-K Full Syscall Dispatch Completion (v0.16.0–v0.16.8)

Completed the syscall surface established by WS-J1. Extended
`SyscallDecodeResult` with message register values (x2–x5), defined per-syscall
argument structures with total decode functions, wired all 13 syscalls through
`dispatchWithCap` (replacing 7 `.illegalState` stubs), replaced service policy
stubs with configuration-sourced predicates, populated IPC message bodies from
decoded registers, and proved round-trip correctness, invariant preservation,
and NI coverage for all new paths. All 8 phases (K-A through K-H) completed
(v0.16.0–v0.16.8). See
[workstream plan](../dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md).

## Active: WS-L IPC Subsystem Audit & Remediation (v0.16.8)

A comprehensive end-to-end audit of the IPC subsystem (9,195 LoC, 12 files)
found zero critical issues and zero sorry/axiom, but identified 3 performance
optimization opportunities, 5 proof strengthening opportunities, and 5 test
coverage gaps. WS-L also resolves all deferred WS-I5 items.

| Phase | Focus | Priority | Status |
|-------|-------|----------|--------|
| **WS-L1** | IPC performance optimization (redundant TCB lookups) | HIGH | Planned |
| **WS-L2** | Code quality: HashMap.fold migration | MEDIUM | Planned |
| **WS-L3** | Proof strengthening: round-trip, consistency, preservation | MEDIUM | Planned |
| **WS-L4** | Test coverage: ReplyRecv, blocked-thread, interleaving | MEDIUM | Partially complete |
| **WS-L5** | Documentation: IF readers' guide, fixture process, metrics | LOW | In progress |

See [WS-L workstream plan](../audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md).

## Next: Raspberry Pi 5 Hardware Binding

The next major milestone is populating the RPi5 platform stubs with
hardware-validated contracts:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

## Completed: WS-J1-F CdtNodeId Cleanup and Documentation Sync (v0.15.10)

Final cleanup phase of WS-J1. Replaced `abbrev CdtNodeId := Nat` with
`structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`,
matching the typed wrapper pattern used by all other kernel identifiers. Added
full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
`LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`) co-located with
the type definition. Fixed downstream compilation: `SystemState` field defaults
(`cdtNextNode := ⟨0⟩`), monotone allocator (`⟨node.val + 1⟩`), test literals
in `NegativeStateSuite.lean`. All documentation synchronized across canonical
sources and GitBook chapters. Codebase map regenerated. All 16 kernel identifiers
are now typed wrappers. Zero sorry/axiom. Closes WS-J1 Phase F.
**WS-J1 portfolio fully completed.**

## Completed: WS-J1-E Testing and Trace Evidence (v0.15.9)

Testing and trace evidence for the register decode layer. 18 negative decode
tests in `NegativeStateSuite.lean` covering `validateRegBound`, `decodeSyscallId`,
`decodeMsgInfo`, `decodeCapPtr`, `decodeSyscallArgs`, and `syscallEntry` error
paths. 5 register-decode trace scenarios (RDT-002 through RDT-010) in
`MainTraceHarness.lean`: standalone decode success, full `syscallEntry` send via
register decode, invalid syscall number, malformed message info, out-of-bounds
register layout. 2 operation-chain tests (`chain10RegisterDecodeMultiSyscall`,
`chain11RegisterDecodeIpcTransfer`) in `OperationChainSuite.lean`. Fixture and
scenario registry updates. 13 Tier 3 invariant surface anchors for
RegisterDecode definitions and theorems. Zero sorry/axiom. Closes WS-J1 Phase E.

## Completed: WS-J1-D Invariant and NI Integration (v0.15.8)

Invariant and information-flow integration for the register decode path.
`registerDecodeConsistent` predicate bridging the decode layer to the kernel
object store. Invariant preservation through `syscallEntry` (compositional:
decode is pure, lookup is read-only). Non-interference: `decodeSyscallArgs_preserves_lowEquivalent`,
`lookupThreadRegisterContext_preserves_lowEquivalent/projection`,
`syscallEntry_preserves_projection`. Two new `NonInterferenceStep` constructors:
`syscallDecodeError` and `syscallDispatchHigh`. Bridge theorems connecting
`syscallEntry` outcomes to NI steps. Zero sorry/axiom. Closes WS-J1 Phase D.

## Completed: WS-J1-C Syscall Entry Point and Dispatch (v0.15.6; refinements v0.15.7)

Wired the register decode layer into a register-sourced syscall entry point.
`syscallEntry` reads the current thread's saved register context via
`lookupThreadRegisterContext`, decodes raw register values via `decodeSyscallArgs`
(with configurable `regCount` parameter, default 32 for ARM64), and dispatches
through capability-gated `syscallInvoke` to the appropriate internal kernel
operation. `dispatchSyscall` constructs a `SyscallGate` from the caller's TCB and
CSpace root CNode, while `dispatchWithCap` routes all 13 modeled syscalls: IPC
ops (send/receive/call/reply) and service ops extract targets from the resolved
capability, while CSpace ops (mint/copy/move/delete), lifecycle retype, and
VSpace ops (map/unmap) return `illegalState` as they require message-register
data not yet available in the decode path (full MR extraction deferred to
WS-J1-E). `syscallRequiredRight` provides a total mapping from `SyscallId` to
`AccessRight`. `MachineConfig.registerCount` promoted from computed def to
configurable structure field (default 32 for ARM64). Five soundness theorems
proved: `syscallEntry_requires_valid_decode`,
`syscallEntry_implies_capability_held` (full capability-resolution chain from
TCB/CSpace lookup to resolved cap with required right),
`dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`,
`syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C.

## Completed: WS-J1-B Register Decode Layer (v0.15.5)

Register decode layer closing the gap between raw machine registers and typed
kernel operations. `SyscallId` inductive (13 modeled syscalls with injective
encoding and round-trip proofs), `MessageInfo` structure (seL4 message-info
bit-field layout with `encode`/`decode`), `SyscallDecodeResult` typed output,
total deterministic decode functions (`decodeCapPtr`, `decodeMsgInfo`,
`decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`) in self-contained
`RegisterDecode.lean` module, `SyscallRegisterLayout` with `arm64DefaultLayout`
(x0–x7 convention), `MachineConfig.registerCount`, 3 new `KernelError` variants
(`invalidRegister`, `invalidSyscallNumber`, `invalidMessageInfo`), round-trip
lemmas, determinism theorem, error exclusivity theorems. Zero sorry/axiom.
Closes WS-J1 Phase B.

## Completed: WS-H12e Cross-Subsystem Invariant Reconciliation (v0.14.2)

Reconciled all subsystem invariant compositions after WS-H12a–d changes.
`coreIpcInvariantBundle` upgraded from `ipcInvariant` to `ipcInvariantFull`
(3-conjunct: `ipcInvariant ∧ dualQueueSystemInvariant ∧ allPendingMessagesBounded`);
`schedulerInvariantBundleFull` extended from 4 to 5 conjuncts (+ `contextMatchesCurrent`);
`ipcSchedulerCouplingInvariantBundle` extended with `contextMatchesCurrent` and
`currentThreadDequeueCoherent`; `proofLayerInvariantBundle` uses full scheduler bundle;
8 frame lemmas + 3 compound preservation theorems + 7 composed `ipcInvariantFull`
preservation theorems; all `*_preserves_schedulerInvariantBundleFull` theorems updated;
default state proofs extended. Closes systemic invariant composition gaps from WS-H12a–d.

## Completed: WS-H12d IPC Message Payload Bounds (v0.14.1)

`IpcMessage` registers/caps migrated from `List` to `Array` with
`maxMessageRegisters`(120)/`maxExtraCaps`(3). Bounds enforcement at all 4 send
boundaries (`endpointSendDual`/`endpointCall`/`endpointReply`/`endpointReplyRecv`).
4 `*_message_bounded` theorems. `allPendingMessagesBounded` system invariant
integrated into `ipcInvariantFull` 3-conjunct bundle. `checkBounds_iff_bounded`
decidability bridge. Information-flow enforcement updated with bounds-before-flow
ordering. Closes A-09 (HIGH).

## Completed: WS-I3 Operations Coverage Expansion (v0.15.2)

Phase 3 (operations-focused) of the WS-I improvement portfolio:

- `tests/OperationChainSuite.lean` adds six compositional chain tests spanning lifecycle, CSpace, IPC, VSpace, service sequencing, and notifications.
- Scheduler stress section adds 16-thread repeated scheduling, same-priority deterministic selection checks, and multi-domain isolation checks with `switchDomain` + `schedule`.
- Tier 2 negative gate now executes `OperationChainSuite` via `scripts/test_tier2_negative.sh`.
- `tests/InformationFlowSuite.lean` adds declassification runtime coverage for authorized downgrade, normal-flow rejection, policy-denied rejection, and a 3-domain lattice scenario; policy-denied downgrade now reports distinct `declassificationDenied`.

## Completed: WS-I1 Critical Testing Infrastructure (v0.15.0)

Phase 1 of the WS-I improvement portfolio, addressing three critical testing
infrastructure recommendations from the v0.14.9 audit:

- **R-01 (inter-transition assertions):** 17 `checkInvariants` calls across all
  13 trace functions, invoking 17 invariant check families (scheduler, CSpace, IPC,
  lifecycle, service, VSpace, CDT, ASID, untyped, notification, blocked-thread, domain)
  after every major transition group. `IO.Ref Nat` counter tracking with `[ITR-001]`
  summary output.
- **R-02 (mandatory determinism):** `test_tier2_determinism.sh` runs trace twice
  and diffs output, integrated into `test_smoke.sh` Tier 2 gate. Determinism is now
  a mandatory CI property rather than an optional Tier 4 extension.
- **R-03 (scenario ID traceability):** 121 trace lines tagged with unique IDs
  across 15 prefix families. Pipe-delimited fixture format. Scenario registry YAML
  with bidirectional Tier 0 validation.

## Completed: WS-H12f Test Harness Update & Documentation Sync (v0.14.3)

Three new trace scenarios added to `MainTraceHarness.lean`:
`runDequeueOnDispatchTrace` (dequeue-on-dispatch lifecycle with preemption
re-enqueue), `runInlineContextSwitchTrace` (inline context save/restore through
`handleYield` → `schedule`), `runBoundedMessageExtendedTrace` (zero-length,
sub-boundary, max-caps message acceptance). Legacy `endpointInvariant` comments
cleaned up in `IPC/Invariant.lean`. Expected fixture updated (108 lines, 11 new
output lines). 9 new Tier 3 anchors. Documentation synchronized across all
canonical sources and GitBook chapters. Completes WS-H12 composite workstream.

## Completed: WS-H12c Per-TCB Register Context (v0.14.0)

Per-TCB `registerContext` field on TCB with inline `saveOutgoingContext`/
`restoreIncomingContext` in `schedule`. `contextMatchesCurrent` invariant with
preservation proofs for all scheduler and IPC operations. Information-flow
projection strips register context. `endpointInvariant` removed (vacuous since
WS-H12a). Closes H-03 (HIGH).

## Completed: WS-H12b Dequeue-on-Dispatch Scheduler Semantics (v0.13.9)

Inverted `queueCurrentConsistent` from `current ∈ runnable` to
`current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue`
dequeue-on-dispatch semantics. `schedule` dequeues chosen thread before
dispatch; `handleYield` inserts+rotates current thread; `timerTick`
re-enqueues on preemption; `switchDomain` re-enqueues before domain switch.
Added `currentTimeSlicePositive`, `schedulerPriorityMatch`, and IPC coherence
predicates. ~1800 lines of proofs re-proved. Closes H-04 (HIGH).

## Completed: WS-H12a Legacy Endpoint Removal (v0.13.8)

Deleted `EndpointState` type and legacy endpoint fields (`state`, `queue`,
`waitingReceiver`). Removed legacy IPC operations (`endpointSend`,
`endpointReceive`, `endpointAwaitReceive`) and ~60 associated dead theorems.
All IPC now uses exclusively the O(1) dual-queue path. `endpointReplyRecv`
migrated from legacy `endpointAwaitReceive` to `endpointReceiveDual`. Tests
and tier-3 anchors updated. Closes A-08 (HIGH), M-01 (MEDIUM), A-25 (MEDIUM).

## Completed: WS-H11 VSpace & Architecture Enrichment (v0.13.7)

PagePermissions struct with W^X enforcement at insertion time. Address bounds
checking via `vspaceMapPageChecked` (ARM64 52-bit PA bound). TLB/cache
maintenance model with `TlbState`, `adapterFlushTlb`, and `adapterFlushTlbByAsid`.
`VSpaceBackend` typeclass for platform-agnostic page table operations.
Per-VAddr TLB flush (`adapterFlushTlbByVAddr`) and cross-ASID TLB isolation
theorem. `vspaceInvariantBundle` extended to 5-conjunct preservation across all
VSpace transitions. 889 proved declarations, zero sorry/axiom.

## Completed: WS-H10 Security Model Foundations (v0.13.6)

Extended `ObservableState` with domain-gated machine register file projection
(`machineRegs`). Machine timer deliberately excluded to prevent covert timing
channels. Added standard BIBA security lattice alternatives (`bibaPolicy`,
`bibaSecurityFlowsTo`) with reflexivity/transitivity proofs. Introduced
`DeclassificationPolicy` with `declassifyStore` enforcement operation (5
theorems). Added `endpointFlowPolicyWellFormed` predicate with reflexivity and
transitivity inheritance proofs. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL),
A-39 (MEDIUM), M-16 (MEDIUM). Added `declassifyStore_NI` (non-interference for
controlled declassification) and `InformationFlowConfigInvariant` bundle. 866
proved declarations.

## Completed: WS-H7/H8/H9 Audit Gap Closure (v0.13.5)

Comprehensive codebase audit identified and closed remaining gaps in WS-H7, WS-H8,
and WS-H9: BEq soundness lemmas (`VSpaceRoot.beq_sound`, `CNode.beq_sound`),
`endpointReceiveDualChecked_NI` enforcement bridge theorem, 3 IPC NI theorems
(`endpointReceiveDual_preserves_lowEquivalent`, `endpointCall_preserves_lowEquivalent`,
`endpointReplyRecv_preserves_lowEquivalent`), and `NonInterferenceStep` extended
to 31 constructors. Zero sorry/axiom. All tests pass.

## Completed: WS-H9 Non-Interference Coverage Extension (v0.13.4)

WS-H9 extends NI coverage from ~25% to >80% of kernel operations (C-02/A-40 CRITICAL),
adding 27 new NI preservation theorems across scheduler, IPC, CSpace, VSpace, and
observable-state operations. `NonInterferenceStep` inductive extended from 11 to 28
constructors. `composedNonInterference_trace` covers all constructors. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H5 IPC Dual-Queue Structural Invariant (v0.12.19)

WS-H5 defines and proves a formal structural well-formedness invariant for the
intrusive dual-queue IPC implementation, closing C-04/A-22 (CRITICAL), A-23
(HIGH), and A-24 (HIGH). Core predicates: `intrusiveQueueWellFormed` (head/tail
emptiness iff, boundary link consistency, TCB existence), `dualQueueSystemInvariant`
(all endpoints well-formed + `tcbQueueLinkIntegrity` doubly-linked forward/reverse
consistency). 13 preservation theorems cover all dual-queue operations. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H3 Build/CI Infrastructure Fixes (v0.12.17)

WS-H3 addresses build and CI infrastructure gaps identified in the v0.12.15
audit: `run_check` return value fix (H-12) so failure is correctly signaled in
continue mode, `test_docs_sync.sh` integration into the smoke CI job and
`test_smoke.sh` entrypoint (M-19), and a `rg` availability guard with `grep -P`
fallback in Tier 3 (M-20). See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H2 Lifecycle Safety Guards (v0.12.16)

WS-H2 addresses lifecycle safety gaps identified in the v0.12.15 audit:
childId self-overwrite and collision guards in `retypeFromUntyped`, TCB scheduler
cleanup on retype via `lifecycleRetypeWithCleanup`, CNode CDT slot detach, and
atomic dual-store retype. Proved `lifecycleRetypeWithCleanup_ok_runnable_no_dangling`
— no dangling run queue entries after TCB retype. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H1 IPC call-path semantic fix (v0.12.16)

WS-H1 addresses the IPC call-path semantic gap identified in the v0.12.15 audit:
`blockedOnCall` state for call/reply semantics, reply-target scoping to prevent
confused-deputy attacks, and 5-conjunct `ipcSchedulerContractPredicates` with full
invariant proof maintenance. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-G kernel performance optimization

The WS-G portfolio (v0.12.6–v0.12.15) closed all 14 findings from the
[v0.12.5 performance audit](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md),
migrating every kernel hot path to O(1) hash-based structures. All proofs
re-verified — zero sorry/axiom.

See [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
for the full technical breakdown.

## Next: WS-J1 and Raspberry Pi 5 hardware binding

All WS-F and WS-H remediation workstreams are completed. The active
workstream was **WS-J1** (register-indexed authoritative namespace migration).
All 6 phases (J1-A through J1-F) are completed (v0.15.4–v0.15.10): typed register
wrappers, decode layer, syscall entry point, invariant/NI integration, testing/trace
evidence, and CdtNodeId cleanup. **WS-J1 portfolio fully completed.**

See [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md),
[`docs/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md),
and [Next Development Path](../dev_history/gitbook/22-next-slice-development-path.md).

## Hardware roadmap

H0 (neutral semantics, complete) → H1 (boundary interfaces, complete) →
H2 (proof deepening, complete) → H3 (Raspberry Pi 5 binding) →
H4 (evidence convergence).

See [Path to Real Hardware](10-path-to-real-hardware-mobile-first.md).

## Non-negotiable baseline contracts

1. Deterministic transition semantics (explicit success/failure).
2. IPC-scheduler handshake coherence.
3. Domain-aware scheduling (active-domain-only).
4. Local + composed invariant layering.
5. Stable theorem naming.
6. Fixture-backed executable evidence.
7. Tiered validation commands.
8. Import hygiene (`API.lean` as canonical aggregate).
