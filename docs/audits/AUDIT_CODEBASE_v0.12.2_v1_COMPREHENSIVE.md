# seLe4n Comprehensive Codebase Audit — v0.12.2

**Date**: 2026-02-28
**Scope**: All 33 `.lean` files (14,708 LoC), 21 shell scripts, all documentation
**Build**: Passes (62 jobs) | **Smoke tests**: All pass

---

## Executive Summary

seLe4n is a Lean 4 formalization of seL4 microkernel semantics with **zero
`sorry`, `axiom`, or unsound constructs** across the entire codebase. Every
theorem is fully machine-checked. The project demonstrates serious engineering
discipline with clean typed identifiers, a deterministic monad, and
well-structured Operations/Invariant separation across all subsystems.

However, significant gaps exist between what the codebase proves and what it
could be interpreted as claiming. The model omits several foundational seL4
mechanisms (Untyped memory, per-thread register context, multi-level CSpace,
message transfer in IPC), and the information-flow proofs cover only 5 of 30+
operations with an incomplete state projection.

**Overall**: Solid foundations, clean engineering, early-stage formalization.
Should be described as "partially verified executable semantics" rather than a
comprehensive seL4 formalization.

---

## Proof Soundness

| Pattern              | Count | Severity |
|----------------------|-------|----------|
| `sorry`              | 0     | None     |
| `axiom`              | 0     | None     |
| `native_decide`      | 0     | None     |
| `admit`/`unsafe`     | 0     | None     |
| `partial` functions  | 2     | Low (test-only) |
| Panicking operations | 0     | None     |
| Debug artifacts      | 0     | None     |

---

## Critical Findings

### CRIT-01: No Message Transfer in IPC

`IpcMessage` (registers, caps, badge) is defined but never referenced by any
IPC operation. All endpoint send/receive operations manipulate thread
scheduling state only — zero data flows between threads. Capability transfer
through IPC is completely unmodeled.

### CRIT-02: Incomplete State Projection

`ObservableState` projects 4 of 10+ `SystemState` fields. Not projected:
`machine`, `irqHandlers`, `lifecycle`, `cdt`, `objectIndex`, `activeDomain`,
`domainSchedule`, `domainTimeRemaining`. Operations modifying unprojected
fields trivially "preserve" low-equivalence.

### CRIT-03: Non-Interference Covers 5 of 30+ Operations

Only `endpointSend`, `chooseThread`, `cspaceMint`, `cspaceRevoke`, and
`lifecycleRetypeObject` have proofs. All IPC receive/reply, notification,
VSpace, architecture, service, and capability copy/move/delete operations
are uncovered. Only "high step" unwinding; no "low step."

### CRIT-04: No Untyped Memory Model

No `UntypedObject`, no retype-from-untyped, no memory accounting. The
fundamental seL4 memory safety property cannot be stated or proved.

### CRIT-05: Dual-Queue IPC Operations Unverified

Five newer IPC operations (`endpointSendDual`, `endpointReceiveDual`,
`endpointCall`, `endpointReplyRecv`, `endpointQueueRemoveDual`) have zero
preservation theorems.

### CRIT-06: Notification Badge Semantics

`Notification.pendingBadge` is `Option Badge` (at most one). Real seL4 uses
word-sized bitmask with OR-accumulation across multiple signals.

---

## High-Severity Findings

- **HIGH-01**: Single-level CSpace resolution (no multi-level CNode walk)
- **HIGH-02**: No per-thread register context (one global `MachineState.regs`)
- **HIGH-03**: No invariant linking `ThreadIpcState` to scheduler queue membership
- **HIGH-04**: Capability rights as ordered `List` (order-sensitive equality)
- **HIGH-05**: Dual endpoint queues without consistency invariant
- **HIGH-06**: `serviceCountBounded` is assumed, never discharged
- **HIGH-07**: No intransitive non-interference (transitive-only policies)
- **HIGH-08**: `AdapterProofHooks` never instantiated (open proof obligation)

---

## Medium-Severity Findings

- **MED-01**: Invariant inflation (universally-true properties in state bundles)
- **MED-02**: `timeSlicePositive`/`edfCurrentHasEarliestDeadline` defined but never preserved
- **MED-03**: Missing operations (setPriority, suspend/resume, CNode_Rotate, etc.)
- **MED-04**: Generic domain lattice is dead code
- **MED-05**: `schedulerWellFormed` misleadingly named (only 1 of 4 components)
- **MED-06**: No `runnableThreadsAreTCBs` invariant
- **MED-07**: VSpace missing cross-ASID isolation theorem
- **MED-08**: Tier 3 tests are source-text grep, not compiled verification

---

## Low-Severity Findings

- No `setSP` function (asymmetry with `setPC`)
- `RegValue`/`UInt8` mismatch
- `OfNat` instances undermine identifier opacity
- `valid` predicate inconsistency across identifier types
- `ServiceStatus.failed`/`isolated` are dead states
- No `serviceUnregisterDependency`
- `irqRoutingTotality` assumption too strong
- `isBetterCandidate` lacks transitivity proof
- CDT acyclicity not maintained after `addEdge`

---

## Documentation Findings

- `CLAUDE.md`/`AGENTS.md` claim v0.12.0 (actual: v0.12.2)
- Workstream status stale in agent config files
- `SELE4N_SPEC.md` has duplicate section "3.1" and broken ToC anchor
- File size estimates in CLAUDE.md significantly stale
- All CLAIM_EVIDENCE_INDEX theorem references verified correct (20/20)

---

## Testing Assessment

| Layer | Quality | Notes |
|-------|---------|-------|
| Tier 0 | Good | Hygiene checks |
| Tier 1 | Good | Build passes |
| Tier 2 | **Excellent** | NegativeStateSuite + randomized probe |
| Tier 3 | Weak | Source grep only |
| Info-flow | Good | Non-tautological witness |

---

## Strengths

1. Zero `sorry`/`axiom` — clean proof surface
2. Deterministic semantics — all transitions are pure functions
3. Operations/Invariant separation — consistent across 7 subsystems
4. BFS completeness proof with loop invariant and termination
5. VSpace round-trip algebra fully proved
6. Badge routing end-to-end proof (mint → signal → wait)
7. CDT node-stable design handles capability moves correctly
8. NegativeStateSuite with corruption testing

---

## Top Recommendations

1. Integrate `IpcMessage` into IPC operations
2. Extend `ObservableState` to cover all security-relevant fields
3. Prove non-interference for all API operations + "low step"
4. Add Untyped memory model with watermark tracking
5. Prove preservation for dual-queue IPC operations
6. Add per-thread register context
7. Implement recursive CSpace resolution
8. Add `runnableThreadsAreReady` invariant
9. Replace `List AccessRight` with order-independent representation
10. Remove legacy endpoint fields or add consistency invariant
