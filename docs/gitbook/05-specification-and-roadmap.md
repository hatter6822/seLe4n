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
| Version | `0.13.8` |
| Lean toolchain | `4.28.0` |
| Production LoC | 28,083 across 41 files |
| Test LoC | 2,257 across 3 suites |
| Proved declarations | 838 theorem/lemma declarations (zero sorry/axiom) |
| Build jobs | 86 |
| Active findings | [`AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Active audit | [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) (14 findings tracked to completion in WS-G) |
| Latest audit | [`AUDIT_CODEBASE_v0.13.6.md`](../audits/AUDIT_CODEBASE_v0.13.6.md) — comprehensive end-to-end audit, zero critical issues |
| Recently completed | WS-H12a (v0.13.8, legacy endpoint removal), WS-H11 (v0.13.7, VSpace & architecture enrichment), End-to-end audit (v0.13.6), WS-H10 (v0.13.6, security model foundations), WS-H7/H8/H9 gaps closed (v0.13.5), WS-H9 (NI coverage extension, v0.13.4), WS-H8 (enforcement-NI bridge, v0.13.2), WS-H6 (scheduler proof completion, v0.13.1), WS-H5 (IPC dual-queue invariant, v0.12.19), WS-H4 (capability invariant redesign, v0.12.18), WS-H3 (build/CI, v0.12.17), WS-H2 (lifecycle safety guards, v0.12.16), WS-H1 (IPC call-path fix, v0.12.16), WS-G (kernel performance) |
| Next workstream | WS-H12b–f, H13..H16 (remaining v0.12.15 audit remediation) |
| Metrics source of truth | `./scripts/report_current_state.py` |

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
WS-H12a (legacy endpoint removal, v0.13.8).

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

## Next: WS-H11..H16 and WS-F5..F8

### Remaining v0.12.15 audit remediation (WS-H11..H16)

WS-H1..H11 are completed. The remaining workstreams address Phases 4–5:
scheduler/IPC alignment (H12), CSpace/service
enrichment (H13), type safety (H14), platform hardening (H15), and
testing/docs expansion (H16). WS-H11 added `PagePermissions` with W^X enforcement,
abstract TLB model, bounded address translation checks, and extended
`vspaceInvariantBundle` to 5 conjuncts.

See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
and [Next Development Path](22-next-slice-development-path.md).

### Remaining v0.12.2 audit remediation (WS-F5..F8)

WS-F1..F4 (critical/high priority) are completed. The remaining workstreams
address medium/low findings from the v0.12.2 audits:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
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
