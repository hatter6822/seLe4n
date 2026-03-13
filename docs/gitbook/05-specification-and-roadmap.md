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
| Version | `0.14.10` |
| Lean toolchain | `v4.28.0` |
| Production LoC | 34,171 across 67 files |
| Test LoC | 2,886 across 3 suites |
| Proved declarations | 1,086 theorem/lemma declarations (zero sorry/axiom) |
| Total declarations | 2,006 across 70 modules |
| Latest audit | [`AUDIT_CODEBASE_v0.13.6.md`](../audits/AUDIT_CODEBASE_v0.13.6.md) — zero critical issues |
| Next workstreams | WS-I4+ (v0.14.10 improvement portfolio; WS-I1/WS-I3 completed); Raspberry Pi 5 hardware binding |
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
WS-I1 (critical testing infrastructure, v0.15.0).

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
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H5 IPC Dual-Queue Structural Invariant (v0.12.19)

WS-H5 defines and proves a formal structural well-formedness invariant for the
intrusive dual-queue IPC implementation, closing C-04/A-22 (CRITICAL), A-23
(HIGH), and A-24 (HIGH). Core predicates: `intrusiveQueueWellFormed` (head/tail
emptiness iff, boundary link consistency, TCB existence), `dualQueueSystemInvariant`
(all endpoints well-formed + `tcbQueueLinkIntegrity` doubly-linked forward/reverse
consistency). 13 preservation theorems cover all dual-queue operations. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H3 Build/CI Infrastructure Fixes (v0.12.17)

WS-H3 addresses build and CI infrastructure gaps identified in the v0.12.15
audit: `run_check` return value fix (H-12) so failure is correctly signaled in
continue mode, `test_docs_sync.sh` integration into the smoke CI job and
`test_smoke.sh` entrypoint (M-19), and a `rg` availability guard with `grep -P`
fallback in Tier 3 (M-20). See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H2 Lifecycle Safety Guards (v0.12.16)

WS-H2 addresses lifecycle safety gaps identified in the v0.12.15 audit:
childId self-overwrite and collision guards in `retypeFromUntyped`, TCB scheduler
cleanup on retype via `lifecycleRetypeWithCleanup`, CNode CDT slot detach, and
atomic dual-store retype. Proved `lifecycleRetypeWithCleanup_ok_runnable_no_dangling`
— no dangling run queue entries after TCB retype. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H1 IPC call-path semantic fix (v0.12.16)

WS-H1 addresses the IPC call-path semantic gap identified in the v0.12.15 audit:
`blockedOnCall` state for call/reply semantics, reply-target scoping to prevent
confused-deputy attacks, and 5-conjunct `ipcSchedulerContractPredicates` with full
invariant proof maintenance. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-G kernel performance optimization

The WS-G portfolio (v0.12.6–v0.12.15) closed all 14 findings from the
[v0.12.5 performance audit](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md),
migrating every kernel hot path to O(1) hash-based structures. All proofs
re-verified — zero sorry/axiom.

See [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
for the full technical breakdown.

## Next: WS-H11..H16 and WS-F5..F8 (WS-F5 completed)

### Remaining v0.12.15 audit remediation (WS-H11..H16)

WS-H1..H11 are completed. The remaining workstreams address Phases 4–5:
scheduler/IPC alignment (H12), CSpace/service
enrichment (H13), type safety (H14), platform hardening (H15), and
testing/docs expansion (H16). WS-H11 added `PagePermissions` with W^X enforcement,
abstract TLB model, bounded address translation checks, and extended
`vspaceInvariantBundle` to 5 conjuncts.

See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
and [Next Development Path](22-next-slice-development-path.md).

### Remaining v0.12.2 audit remediation (WS-F7..F8)

WS-F1..F6 (critical/high/medium priority) are completed. The remaining workstreams
address low findings from the v0.12.2 audits:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low — **COMPLETED** |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

See [v0.12.2 Audit Remediation (WS-F)](24-comprehensive-audit-2026-workstream-planning.md).

## Hardware roadmap

H0 (neutral semantics, complete) → H1 (boundary interfaces, complete) →
H2 (proof deepening, WS-F remaining) → H3 (Raspberry Pi 5 binding) →
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
