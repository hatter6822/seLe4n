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
| Version | `0.13.0` |
| Lean toolchain | `4.28.0` |
| Production LoC | 25,648 across 40 files |
| Test LoC | 1,854 across 3 suites |
| Proved declarations | 734 theorem/lemma declarations (zero sorry/axiom) |
| Build jobs | 84 |
| Active findings | [`AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Active audit | [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) (14 findings tracked to completion in WS-G) |
| Recently completed | WS-H5 (IPC dual-queue structural invariant, v0.12.19), WS-H4 (capability invariant redesign, v0.12.18), WS-H3 (build/CI infrastructure, v0.12.17), WS-H2 (lifecycle safety guards, v0.12.16), WS-H1 (IPC call-path semantic fix, v0.12.16), WS-G (kernel performance optimization) |
| Next workstream | WS-F5..F8 (remaining v0.12.2 audit remediation) |
| Metrics source of truth | `./scripts/report_current_state.py` |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..F1-F4 (5 audit portfolios, all completed) → WS-G
(performance optimization, completed) → WS-H1 (IPC call-path semantic fix, completed) →
WS-H2 (lifecycle safety guards, completed) → WS-H3 (build/CI infrastructure, completed) →
WS-H4 (capability invariant redesign, completed) → WS-H5 (IPC dual-queue structural
invariant, completed).

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

## Next: remaining WS-F workstreams (F5–F8)

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
