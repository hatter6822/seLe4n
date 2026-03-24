# Comprehensive Pre-Release Audit: seLe4n v0.20.7

**Date**: 2026-03-24
**Scope**: Full kernel — 97 Lean modules (61,525 lines) + 3 Rust crates (3,715 lines)
**Auditor**: Claude Opus 4.6 (8-agent parallel deep-read audit)
**Status**: Pre-release audit for benchmarking milestone

---

## Executive Summary

This audit reviewed every line of production code across the seLe4n verified
microkernel: 97 Lean 4 source files and 26 Rust source files spanning 8
subsystems. Eight parallel audit agents performed independent deep reads,
examining every definition, function, theorem, and invariant.

### Key Metrics

| Metric | Value |
|--------|-------|
| Lean source lines | 61,525 |
| Rust source lines | 3,715 |
| Files audited | 123 |
| `sorry` found | **0** |
| `axiom` found | **0** |
| `unsafe` blocks (Rust) | **1** (svc #0 trap — expected) |
| `native_decide` uses | ~10 (all on finite bounded arithmetic) |
| External Rust dependencies | **0** (zero supply-chain risk) |

### Finding Summary

| Severity | Count | Description |
|----------|-------|-------------|
| CRITICAL | 0 | No soundness holes or exploitable vulnerabilities |
| HIGH | 13 | Semantic gaps, fragile assumptions, missing access control |
| MEDIUM | 37 | Design trade-offs, proof obligation gaps, spec divergences |
| LOW | 43 | Minor gaps, documentation issues, hardening opportunities |
| INFO | 72+ | Architecture observations, positive verification notes |

**Overall Assessment**: The kernel is in strong shape for its first major
release. The proof surface is clean — zero sorry/axiom across 61,525 lines of
Lean. All kernel transitions are deterministic and return explicit
success/failure. The Rust userspace library is minimal, no_std, and has zero
external dependencies. The findings below are primarily semantic gaps vs
hardware reality, proof obligation patterns that externalize hypotheses, and
access control on internal primitives.

---

## Table of Contents

1. [Global Findings (Cross-Cutting)](#1-global-findings)
2. [Prelude, Machine, and Model Layer](#2-prelude-machine-and-model-layer)
3. [Scheduler Subsystem](#3-scheduler-subsystem)
4. [Capability Subsystem](#4-capability-subsystem)
5. [IPC Subsystem](#5-ipc-subsystem)
6. [Information Flow and Service Subsystems](#6-information-flow-and-service)
7. [Robin Hood, Radix Tree, and Frozen Operations](#7-data-structures-and-frozen-ops)
8. [Architecture, Platform, and Lifecycle](#8-architecture-platform-and-lifecycle)
9. [Rust Userspace Library](#9-rust-userspace-library)
10. [Recommendations](#10-priority-recommendations)

---

## 1. Global Findings

These findings apply across multiple subsystems and represent systemic
architectural characteristics.

### G-01 [HIGH] Unbounded Nat for All Identifiers and Register Values

**Affected files**: `Prelude.lean`, `Machine.lean`, `Object/Types.lean`

Every typed identifier (`ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
`Priority`, `Deadline`, etc.) and `RegValue` wraps `Nat` with no upper bound.
The `machineWordBounded` invariant constrains registers to `< 2^64` but is not
type-enforced. On ARM64 hardware, all values must fit in 64 bits.

A transition that produces an ID > 2^64 would violate the hardware model
silently. The model relies entirely on invariant predicates and transition-level
bounds checking, not types.

**Impact**: Semantic gap with real hardware. No formal correctness issue (proofs
hold for all Nat values), but Priority/Deadline have no upper bound enforcement
— a value set to an astronomically large number would always win scheduling.

**Recommendation**: Add `Priority.isValid` (0 ≤ val ≤ 255) and `Deadline`
bound predicates. Enforce at the API layer.

### G-02 [MEDIUM] `native_decide` Usage (~10 occurrences)

**Affected files**: `Machine.lean`, `Object/Types.lean`, `Object/Structures.lean`,
`Board.lean`, `Invariant.lean`, `RunQueue.lean`, `SyscallArgDecode.lean`,
`FrozenOps/Operations.lean`

All uses are on concrete bounded arithmetic (bitfield extraction, small
enumeration properties, empty-state bounds). These are trusted by Lean's native
code evaluator, not the proof kernel. Each occurrence is a minimal TCB expansion
point. Risk is very low but non-zero.

**Recommendation**: Accept as standard Lean 4 practice. Document as known TCB
boundary.

### G-03 [MEDIUM] Non-Lawful BEq Instances

**Affected files**: `Machine.lean:196`, `Object/Types.lean:357`

`BEq RegisterFile` and `BEq TCB` are explicitly non-lawful (documented). They
compare function types by exhaustive enumeration over all constructors. While
no proofs currently depend on `LawfulBEq` for these types, the instances exist
in scope and could be accidentally used in a proof expecting lawful behavior.

**Recommendation**: Consider adding negative instances to catch misuse at
compile time.

### G-04 [INFO] Zero sorry/axiom Across Entire Lean Codebase

Confirmed via codebase-wide grep. Every theorem in all 97 Lean files is
machine-checked. This is a significant achievement for a kernel of this
complexity.

### G-05 [INFO] Zero External Rust Dependencies

All three Rust crates depend only on each other. No supply-chain attack surface.
All crates are `#![no_std]` with `#![deny(unsafe_code)]` (single targeted
`#[allow]` for the trap module).

---

## 2. Prelude, Machine, and Model Layer

**Files**: `Prelude.lean` (1,258 lines), `Machine.lean` (656 lines),
`Object/Types.lean` (992 lines), `Object/Structures.lean` (2,257 lines),
`State.lean` (1,407 lines), `IntermediateState.lean` (106 lines),
`Builder.lean` (357 lines), `FrozenState.lean` (542 lines),
`FreezeProofs.lean` (1,134 lines)

### Positive Findings

- All typed IDs have roundtrip/injectivity proofs.
- `Badge.ofNatMasked` correctly truncates to 64-bit with machine-checked proof.
- `KernelM` monad has proven `LawfulMonad` instance.
- RHTable bridge lemmas (get/insert/erase) complete with `invExt` preconditions.
- `zeroMemoryRange` has frame + postcondition proofs.
- `UntypedObject` watermark allocator has extensive well-formedness proofs.
- `CapDerivationTree` has private constructor (forced construction through
  verified paths).
- `addEdge_preserves_edgeWellFounded_noParent` is a ~120 line cycle detection
  proof — complete and sound.
- `freezeMap_get?_eq` keystone theorem proves lookup equivalence between
  mutable RHTable and frozen dense array + index.
- `apiInvariantBundle_frozenDirect` survives post-freeze mutations (improved
  over existential formulation).

### Findings

| ID | Severity | Location | Finding |
|----|----------|----------|---------|
| ML-01 | MEDIUM | `Structures.lean:989` | `descendantsOf` transitive closure fuel sufficiency not proven — only depth-1 children guaranteed. Revocation completeness for deep derivation trees is formally open. Deferred to WS-U. |
| ML-02 | MEDIUM | `FrozenState.lean:85` | `FrozenMap.get?` bounds-checks index against data array size. Post-freeze `.set` mutations could create inconsistencies if index and data array diverge. Correctness at freeze time is proven, but post-mutation requires caller-supplied compatibility witness. |
| ML-03 | MEDIUM | `FreezeProofs.lean:1033` | `apiInvariantBundle_frozen` uses existential witness that becomes unprovable after mutation. The `frozenDirect` formulation (line 1089) is the correct one for post-mutation reasoning. |
| ML-04 | LOW | `Machine.lean:144` | `Memory := PAddr → UInt8` is pure and total. Cannot represent MMIO side effects or out-of-bounds access. Appropriate for abstract model; refinement needed for RPi5. |
| ML-05 | LOW | `State.lean:276` | `allTablesInvExt` manually enumerates 16 RHTable fields. A new field could be silently omitted. No automated enforcement. |
| ML-06 | LOW | `IntermediateState.lean:58` | `IntermediateState` carries `allTablesInvExt` but not `lifecycleMetadataConsistent`. Gap bridged at freeze time but no compile-time guarantee during builder phase. |


---

## 3. Scheduler Subsystem

**Files**: `Operations/Selection.lean` (249 lines), `Operations/Core.lean`
(395 lines), `Operations/Preservation.lean` (2,931 lines),
`Invariant.lean` (489 lines), `RunQueue.lean` (1,094 lines)

### Positive Findings

- Zero sorry/axiom. 7 `native_decide` on empty-state bounds (safe).
- EDF scheduling with domain partitioning correctly models seL4 MCS semantics.
- `chooseBestRunnableBy` implements priority-first, EDF tie-breaking.
- `schedule` re-validates after `chooseThread` (defense-in-depth).
- `rotateToBack`/`rotateHead` correctly preserve RunQueue size.
- Complete preservation theorems for schedule, handleYield, timerTick.

### Findings

| ID | Severity | Location | Finding |
|----|----------|----------|---------|
| SC-01 | **HIGH** | `Core.lean:373-380` | **switchDomain does not save outgoing register context.** Sets `current := none` before `schedule`, making `saveOutgoingContext` a no-op. The outgoing thread's register state at domain switch is lost. `contextMatchesCurrent` is preserved vacuously (current = none). **This is a correctness bug.** Fix: insert `saveOutgoingContext` before setting `current := none`. |
| SC-02 | HIGH | `Selection.lean:160` | Non-TCB in runnable list causes scheduler abort (`.schedulerInvariantViolation`). Under `runnableThreadsAreTCBs` invariant this is unreachable, but creates hard dependency on ALL other subsystems preserving that invariant. A single lifecycle bug could cause permanent scheduler DoS. |
| SC-03 | MEDIUM | `Invariant.lean:72` | Vacuous truth for non-TCB current thread in `currentThreadInActiveDomain`. Composed with `currentThreadValid` this is safe, but standalone use would have a hole. |
| SC-04 | MEDIUM | `Selection.lean:177-189` | Bucket-first vs full-scan functional equivalence unproven. EDF property is proven (sufficient for invariants), but optimality guarantee relies on unproven equivalence. |
| SC-05 | MEDIUM | `Core.lean:371` | `switchDomain` silently drops non-TCB current thread (doesn't re-enqueue). Under invariant, unreachable. |
| SC-06 | MEDIUM | All files | No starvation prevention mechanism. Matches seL4 (fixed-priority by design), but no formal starvation-freedom analysis for specific configurations. |
| SC-07 | LOW | `Preservation.lean:2117,2199` | `maxHeartbeats` overrides (1.6M, 800K) in EDF preservation proofs. Build performance concern. |


---

## 4. Capability Subsystem

**Files**: `Operations.lean` (1,338 lines), `Invariant/Defs.lean` (732 lines),
`Invariant/Authority.lean` (667 lines), `Invariant/Preservation.lean`
(2,072 lines)

### Positive Findings

- Zero sorry/axiom/native_decide across all 5 files.
- All 18+ capability-modifying operations have preservation theorems.
- Authority monotonicity proved for mint (rights attenuation), delete (slot
  clearance), revoke (local target reduction).
- Badge-override safety explicitly proved.
- Guard correctness: bidirectional characterization (reject/match).
- Three revocation variants (local, CDT, streaming BFS) all have preservation.
- CDT acyclicity via edge-well-founded with private constructor.

### Findings

| ID | Severity | Location | Finding |
|----|----------|----------|---------|
| CP-01 | MEDIUM | `Operations.lean:76-108` | `resolveCapAddress` does not check intermediate capability rights during multi-level CSpace walk. In seL4, traversal requires at least read right. seLe4n permits traversal through zero-rights capabilities. Rights enforcement happens at the operation layer instead. Semantic gap vs seL4. |
| CP-02 | MEDIUM | `Preservation.lean:417-535` | CDT-modifying operations (copy, move, mint+CDT, IPC transfer) take `cdtCompleteness ∧ cdtAcyclicity` as hypothesis rather than proving from pre-state. Proof obligation pushed to caller. Well-documented design choice but means composition is conditional. |
| CP-03 | MEDIUM | `Operations.lean:591-605` | Local revoke (`cspaceRevoke`) does not clear CDT edges for revoked slots. Stale CDT entries accumulate. `cspaceRevokeCdt` handles cleanup; direct `cspaceRevoke` use leaves CDT inconsistent. |
| CP-04 | LOW | `Operations.lean:634-651` | `cspaceMove` insert-before-delete creates transient dual-capability state. Monadic semantics ensure atomicity at caller boundary. Not exploitable. |


---

## 5. IPC Subsystem

**Files**: 14 files, ~16,500 lines total across `Operations/*`, `DualQueue/*`,
`Invariant/*`

### Positive Findings

- Zero sorry/axiom/native_decide across all 14 files.
- Complete preservation coverage for all IPC operations across all key invariants.
- Correct seL4 semantics for endpoint send/receive, call/reply, notification
  signal/wait, and badge accumulation (bitwise OR with `ofNatMasked`).
- Grant-right gating for cap transfer; replyTarget authorization for
  confused-deputy prevention.
- Robust dual-queue with doubly-linked integrity, acyclicity proofs, O(1) ops.
- FIFO ordering for endpoint queues (enqueue at tail, pop from head).
- Messages are immutable Lean values — no TOCTOU or race conditions possible.
- Message bounds enforced at all send boundaries.

### Findings

| ID | Severity | Location | Finding |
|----|----------|----------|---------|
| IP-01 | HIGH | `DualQueue/Transport.lean:1577` | `endpointReceiveDual` reads pending message from pre-dequeue TCB. Correct because `endpointQueuePopHead` only modifies queue links, but fragile — any future change to `tcbWithQueueLinks` that modifies `pendingMessage` would silently break this. |
| IP-02 | HIGH | `DualQueue/WithCaps.lean:116` | Missing sender CSpace root falls back to `senderId.toObjId` as CNode root. Unreachable in practice (sender TCB must exist), but fallback silently proceeds rather than returning error. Could mask bugs. |
| IP-03 | MEDIUM | `Endpoint.lean:159-175` | `notificationSignal` wake path unconditionally overwrites waiter's `pendingMessage`. If waiter had stale message from previous IPC, it's lost. Invariant chain prevents this in practice. |
| IP-04 | MEDIUM | `CapTransfer.lean:51` | Sender CSpace root slot hardcoded to `Slot.ofNat 0`. Model simplification — real seL4 uses actual slot address from message info. |
| IP-05 | MEDIUM | `Structural.lean:2984-3037` | `ipcInvariantFull` preservation for Send/Receive/Call/ReplyRecv requires caller-supplied `dualQueueSystemInvariant`. Individual proofs exist; composition is not self-contained for these 4 operations. |
| IP-06 | LOW | General | No IPC buffer memory model. Messages via `pendingMessage` TCB field instead of memory-mapped buffer. Acceptable for abstract model; relevant for hardware binding. |
| IP-07 | LOW | General | No notification binding model (bound-notification signal-during-receive optimization not present). |

