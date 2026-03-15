# Comprehensive Codebase Audit — seLe4n v0.12.15

**Date:** 2026-03-02
**Scope:** Full codebase audit — all 44 Lean source files, build infrastructure, test
harnesses, documentation accuracy, and cross-cutting security analysis.
**Method:** Systematic file-by-file reading of every production and test module,
automated scans for forbidden markers, and structural analysis of proof coverage.

---

## Executive Summary

seLe4n v0.12.15 is a formally verified microkernel written in 23,455 lines of Lean 4
across 44 source files, containing **574 machine-checked theorems with zero `sorry`,
zero `axiom`, and zero `native_decide`**. The kernel models capability-based access
control, IPC, scheduling, lifecycle management, service orchestration, virtual memory,
and information flow — all as pure executable functions with preservation proofs.

**Overall Assessment: STRONG with actionable gaps.**

The codebase demonstrates exceptional discipline in maintaining a zero-sorry proof
surface and deterministic transition semantics. However, this audit identifies
**8 critical findings, 14 high-priority findings, and 19 medium-priority findings**
across proof coverage gaps, model fidelity limitations, documentation inaccuracies,
and architectural debt. None are exploitable vulnerabilities in the current abstract
model, but several represent gaps that must be closed before hardware deployment.

---

## Table of Contents

1. [Project Vital Statistics](#1-project-vital-statistics)
2. [Cross-Cutting Analysis](#2-cross-cutting-analysis)
3. [Foundations: Prelude and Machine](#3-foundations-prelude-and-machine)
4. [Model Layer: Object and State](#4-model-layer-object-and-state)
5. [Scheduler Subsystem](#5-scheduler-subsystem)
6. [Capability Subsystem](#6-capability-subsystem)
7. [IPC Subsystem](#7-ipc-subsystem)
8. [Lifecycle and Service Subsystems](#8-lifecycle-and-service-subsystems)
9. [Architecture Subsystem](#9-architecture-subsystem)
10. [Information Flow Subsystem](#10-information-flow-subsystem)
11. [Platform Bindings and API](#11-platform-bindings-and-api)
12. [Testing Infrastructure](#12-testing-infrastructure)
13. [Build and CI Scripts](#13-build-and-ci-scripts)
14. [Documentation Accuracy](#14-documentation-accuracy)
15. [Consolidated Findings Table](#15-consolidated-findings-table)
16. [Recommendations](#16-recommendations)

---

## 1. Project Vital Statistics

| Metric | Documented | Actual | Status |
|--------|-----------|--------|--------|
| Version | 0.12.15 | 0.12.15 | Correct |
| Lean toolchain | 4.28.0 | 4.28.0 | Correct |
| Production Lean LoC | 16,485 | 21,650 (prod) / 23,455 (total) | **INACCURATE** |
| Source files | 34 | 41 (prod) / 44 (total) | **INACCURATE** |
| Proved theorems | 400+ | 574 | **UNDERSTATED** |
| Build jobs | 64 | 84 | **INACCURATE** |
| `sorry` count | 0 | 0 | Correct |
| `axiom` count | 0 | 0 | Correct |
| `native_decide` | 0 | 0 | Correct |
| `unsafe` | 0 | 0 | Correct |

---

## 2. Cross-Cutting Analysis

### 2.1 Forbidden Marker Scan

A comprehensive scan of all 44 `.lean` files confirms:

- **`sorry`**: 0 occurrences. The entire proof surface is complete.
- **`axiom`**: 0 occurrences. No unproven axioms beyond Lean's core.
- **`native_decide`**: 0 occurrences. No opaque kernel decisions.
- **`unsafe`**: 0 occurrences. No escape hatches.

This is exceptional for a codebase of this size and represents genuine formal verification
discipline.

### 2.2 Inhabited Instance Analysis

21 `Inhabited` instances found across the codebase. All 13 typed identifier wrappers
(ObjId, ThreadId, DomainId, etc.) derive `Inhabited`, generating default instances
with sentinel value 0. This creates a subtle risk: any use of `default` in production
code silently produces semantically invalid sentinel IDs.

**Finding A-01 (MEDIUM):** `Inhabited` defaults generate sentinel values without guard.
Code using `default : ObjId` gets the sentinel (0) with no compiler warning.

### 2.3 Theorem Coverage Distribution

574 theorems distributed across 26 files. Top theorem-density files:

| File | Theorems | Lines | Density |
|------|----------|-------|---------|
| IPC/Invariant.lean | 62 | 3,858 | 1.6% |
| Capability/Invariant.lean | 55 | 1,861 | 3.0% |
| Service/Invariant.lean | 45 | 1,179 | 3.8% |
| IPC/Operations.lean | 44 | 1,116 | 3.9% |
| Model/Object.lean | 44 | 1,066 | 4.1% |
| Model/State.lean | 44 | 898 | 4.9% |
| Scheduler/Operations.lean | 35 | 877 | 4.0% |
| Prelude.lean | 34 | 780 | 4.4% |

---

## 3. Foundations: Prelude and Machine

### 3.1 Typed Identifiers (Prelude.lean)

**Strengths:**
- 13 distinct wrapper types (ObjId, ThreadId, CPtr, Slot, DomainId, Priority,
  Deadline, Irq, ServiceId, Badge, ASID, VAddr, PAddr) prevent type confusion.
- Each derives `DecidableEq`, `Repr`, `Inhabited`.
- Sentinel value conventions documented. Forward injectivity theorems provided
  (e.g., `ThreadId.toObjId_injective`).
- `LawfulHashable` instances enable sound HashMap/HashSet usage.

**Finding A-02 (HIGH):** Typed identifier wrappers are bypassable. All structures have
public `val` fields. Any code can construct arbitrary IDs via `⟨n⟩` syntax or access
raw values via `.val`, bypassing any validation. There is no mechanism to prevent
allocation or use of sentinel IDs in production paths.

**Recommendation:** Make `val` fields private; expose only `ofNat`/`toNat` converters.

**Finding A-03 (MEDIUM):** Missing `EquivBEq` instances. The `LawfulHashable` instances
and HashMap bridge lemmas require `[EquivBEq α]`, but no explicit instances are
declared. Lean may synthesize them via `DecidableEq`, but this resolution chain is
not documented or tested.

### 3.2 Monad System (Prelude.lean)

`KernelM σ ε` is a state-error monad `σ → Except ε (α × σ)` with correct `pure`
and `bind`. However:

**Finding A-04 (MEDIUM):** No `LawfulMonad` instance is provided. The three monad laws
(left identity, right identity, associativity) are not proven. While the implementation
appears correct by inspection, downstream code that depends on monad laws via typeclass
resolution will fail.

### 3.3 Machine State (Machine.lean, 251 lines)

Models register files, memory regions, timer, and machine configuration.

**Finding A-05 (HIGH):** `MemoryRegion.endAddr` does not check for address overflow.
`endAddr = base.toNat + size` can exceed hardware address width (52-bit on RPi5).
The `wellFormed` predicate checks region overlap and page-size validity but does not
enforce that `endAddr ≤ 2^physicalAddressWidth`.

**Finding A-06 (MEDIUM):** `isPowerOfTwo` correctness is unproven. The bitwise check
`n > 0 && (n &&& (n - 1)) == 0` is standard but has no accompanying theorem
`isPowerOfTwo n ↔ ∃ k, n = 2^k`.

---

## 4. Model Layer: Object and State

### 4.1 Kernel Objects (Object.lean, 1,066 lines)

Defines six kernel object types: TCB, Endpoint, Notification, CNode, VSpaceRoot,
UntypedObject. All use modern HashMap-backed data structures (WS-G5 migration).

**Finding A-07 (CRITICAL):** BEq instances for VSpaceRoot and CNode rely on
`HashMap.toList` iteration order, which is implementation-defined. The pattern
`a.mappings.toList.all (fun (k,v) => b.mappings[k]? == some v)` may produce
false inequality for semantically equal HashMaps if iteration order differs.

**Recommendation:** Replace with bidirectional size+entry verification using key
iteration, not `toList`.

**Finding A-08 (HIGH):** Endpoint has redundant legacy + dual-queue fields. Both
`(state, queue, waitingReceiver)` and `(sendQ, receiveQ)` coexist in the same
structure. No invariant enforces consistency between them, and the IPC invariant
(`endpointQueueWellFormed`) only validates legacy fields, not dual-queue fields.

**Recommendation:** Either prove equivalence between legacy and dual-queue
representations, or deprecate/remove legacy fields.

**Finding A-09 (HIGH):** IpcMessage has unbounded payload size. `registers : List Nat`
and `caps : List Capability` have no size limits, creating potential for unbounded
memory allocation in the abstract model.

### 4.2 System State (State.lean, 898 lines)

**Finding A-10 (CRITICAL):** `capabilityRefs` in `LifecycleMetadata` is function-typed
(`SlotRef → Option CapTarget`) rather than HashMap-typed. This creates closure chains
on repeated updates — each `storeCapabilityRef` call wraps the previous function in
a new lambda, creating O(n) nested closures after n updates. This is both inefficient
and fragile for large-scale usage.

**Finding A-11 (HIGH):** CDT slot-node cleanup is incomplete. When a CNode is replaced
via `storeObject`, `cdtSlotNode` and `cdtNodeSlot` mappings for orphaned slots are
not cleaned up. This leaves dangling CDT node references that can cause stale revoke
behavior.

**Finding A-12 (HIGH):** No global invariant for ASID uniqueness. The `asidTable`
maps ASID → ObjId, but there is no proof that two different VSpaceRoots cannot claim
the same ASID simultaneously.

**Finding A-13 (MEDIUM):** `objectIndex` grows monotonically without bounds. Deleted
objects remain in the index, and no proof connects `id ∈ objectIndex` to
`objects[id]? = some _` (liveness).

---

## 5. Scheduler Subsystem

### 5.1 Architecture

Three-level scheduling: Priority > EDF (Earliest Deadline First) > FIFO.
RunQueue uses a multi-index design (priority-bucketed HashMap + membership HashSet +
flat list) with cached `maxPriority` for O(1) bucket-first selection (WS-G4).
Domain scheduling supports round-robin domain switching with per-domain time budgets.

### 5.2 Findings

**Finding A-14 (CRITICAL):** EDF invariant (`edfCurrentHasEarliestDeadline`) is defined
but has **zero preservation theorems**. The property is never proven to be maintained by
`schedule`, `timerTick`, `handleYield`, or any other operation. The scheduler claims
"EDF + priority scheduling" but provides no formal assurance of EDF correctness.

**Finding A-15 (CRITICAL):** `timeSlicePositive` invariant is defined but unproven. No
theorem shows that all runnable threads have `timeSlice > 0`. If a thread enters the
run queue with `timeSlice = 0`, the `timerTick` decrement path produces underflow
(mitigated by Lean's saturating subtraction, but semantically wrong).

**Finding A-16 (HIGH):** `maxPriority` cache correctness is unproven. The cached
`maxPriority` value is updated by `recomputeMaxPriority` (a HashMap fold), but no
theorem proves the result equals the actual maximum priority. If stale, the bucket-first
optimization could skip higher-priority threads.

**Finding A-17 (HIGH):** `chooseBestRunnableBy` optimality is unproven. No theorem
states that the function returns the best candidate. The algorithm looks correct by
inspection (fold with accumulator), but formal assurance is missing.

**Finding A-18 (MEDIUM):** O(n) membership check in `schedule`. The safety guard
`tid ∈ st'.scheduler.runnable` uses O(n) list membership despite O(1) HashSet
available via `RunQueue.contains`. Acknowledged in comments as deferred.

**Finding A-19 (MEDIUM):** `threadPriority` consistency in RunQueue is implicit. The
invariant that every thread in `membership` has a corresponding entry in
`threadPriority` is documented but not type-enforced. Direct structure construction
could violate it.

---

## 6. Capability Subsystem

### 6.1 Architecture

HashMap-backed CSpace with O(1) slot operations. Full capability lifecycle: lookup,
insert, mint (with rights attenuation), copy, move, mutate, delete, local revoke,
cross-CNode CDT revoke. 55 theorems across Operations + Invariant files.

### 6.2 Findings

**Strengths:**
- **Zero sorry/axiom** in all 2,348 lines of capability code.
- **Rights attenuation is ironclad**: `mintDerivedCap_attenuates` proven, with
  `rightsSubset_sound` grounding the boolean check in logic.
- **Authority reduction after delete**: `cspaceDeleteSlot_authority_reduction` proves
  the slot is empty after deletion.
- **Badge safety proven**: Badge override cannot escalate authority
  (`mintDerivedCap_target_preserved_with_badge_override`).
- **HashMap slot uniqueness is structural** (trivially true by `Std.HashMap` semantics).

**Finding A-20 (HIGH):** CDT completeness is not proven. Vanilla `cspaceMint` does
not add CDT edges, only `cspaceMintWithCdt` does. No invariant prevents creating
"orphaned" capabilities that CDT-based revoke will miss.

**Recommendation:** Either prove CDT completeness or document that CDT revoke is
advisory (not total).

**Finding A-21 (MEDIUM):** Move operation is not atomic. `cspaceMove` performs
insert-then-delete, creating a brief window where the capability exists in both
slots. If insert succeeds but delete fails, the capability is duplicated.
Mitigated by `storeObject` error semantics, but no formal atomicity proof.

---

## 7. IPC Subsystem

### 7.1 Architecture

Legacy O(n) endpoint operations + modern O(1) intrusive dual-queue operations
(WS-G6/G7). Notification operations with badge merging via bitwise OR. 62 theorems
in IPC/Invariant alone — the largest proof file at 3,858 lines.

### 7.2 Findings

**Strengths:**
- **Zero sorry/axiom** across all 6,650 lines of IPC code.
- **Full IPC invariant preservation** for all legacy and dual-queue operations.
- **Scheduler-IPC contract predicates** (runnableThreadIpcReady,
  blockedOnSendNotRunnable, blockedOnReceiveNotRunnable) are non-vacuously proven.
- **Compositional proof architecture** decomposes complex operations into
  storeObject chains with per-step preservation.
- **Badge notification routing consistency** proven end-to-end.

**Finding A-22 (CRITICAL):** `endpointQueueWellFormed` only validates legacy fields.
The `sendQ`/`receiveQ` intrusive dual-queue fields are **not checked** by the IPC
invariant predicate. If code accidentally mixes legacy and dual-queue operations on
the same endpoint, invariants break silently.

**Finding A-23 (HIGH):** Unvalidated queue link dereference in dual-queue operations.
`endpointQueuePopHead` directly dereferences `headTcb.queueNext` without validating
link consistency. Corrupted queue links would cause silent undefined behavior in the
model.

**Finding A-24 (HIGH):** Message extraction after `popHead` can silently lose messages.
`endpointReceiveDual` (line 1569) calls `lookupTcb st' sender` after dequeue. If the
lookup fails, the message is silently `none` rather than returning an error. Relies
on external lifecycle enforcement to prevent this.

**Finding A-25 (MEDIUM):** Legacy O(n) operations retained alongside O(1) dual-queue.
No migration guide or deprecation path documented. Potential confusion about which
API to use.

---

## 8. Lifecycle and Service Subsystems

### 8.1 Lifecycle Operations

Implements `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype`, and
`retypeFromUntyped`. Metadata consistency invariants prove type safety across retype
operations.

**Finding A-26 (HIGH):** `retypeFromUntyped` does not verify `childId ≠ untypedId`.
The invariant proof requires this as a precondition, but the operation itself is blind.
If `childId = untypedId`, the untyped is overwritten with the new typed object.

**Finding A-27 (HIGH):** `retypeFromUntyped` does not verify child ID freshness. No
check that `childId` is globally unused. If it collides with an existing object, that
object is silently overwritten.

**Finding A-28 (MEDIUM):** Non-atomic dual-store in `retypeFromUntyped`. Two sequential
`storeObject` calls (untyped update + child creation) lack transactional semantics.
If the second fails, the untyped watermark is advanced but no child was created.

### 8.2 Service Orchestration

Implements `serviceStart`, `serviceStop`, `serviceRestart`, and
`serviceRegisterDependency` with BFS-based cycle detection.

**Finding A-29 (HIGH):** Service operations do not verify backing-object existence.
`serviceStart` succeeds if the policy predicate returns true, even if
`svc.identity.backingObject` has been deleted from the object store.

**Finding A-30 (MEDIUM):** Service restart has partial-failure semantics. If stop
succeeds but start fails, the service remains stopped with no rollback mechanism
and no audit trail.

**Finding A-31 (MEDIUM):** `serviceCountBounded` assumption is never established.
The BFS fuel-based cycle detection requires a proof that the service graph fits
within the fuel budget, but no theorem in the codebase establishes this.

---

## 9. Architecture Subsystem

### 9.1 Overview

Models hardware/architecture assumptions (`Assumptions.lean`), virtual address space
operations (`VSpace.lean`), architecture adapter (`Adapter.lean`), and VSpace backend
abstraction (`VSpaceBackend.lean`).

**Finding A-32 (MEDIUM):** VSpace uses a flat HashMap translation (`VAddr → PAddr`).
Real ARM64 has hierarchical multi-level page tables with permission bits, page sizes,
caching attributes. The model cannot represent TLB semantics or page table walks.

**Finding A-33 (MEDIUM):** Architecture adapter operations (`adapterAdvanceTimer`,
`adapterWriteRegister`, `adapterReadMemory`) have preservation proofs but depend on
a `RuntimeBoundaryContract` that is parameterized, not concrete. The correctness of
the adapter layer is contingent on the platform binding providing correct contracts.

---

## 10. Information Flow Subsystem

### 10.1 Architecture

Implements a projection-based non-interference framework (Goguen-Meseguer style) with
security labels, state projection, enforcement gating, and trace-level composition.
All proofs mechanically verified with zero sorry/axiom.

### 10.2 Findings

**Finding A-34 (CRITICAL):** Non-standard security lattice (M-13). The integrity
dimension flows **upward** (untrusted → trusted is permitted), contrary to standard
BIBA model where integrity flows downward. This is documented as intentional but no
threat model justifies why untrusted data flowing to trusted destinations is safe.

**Finding A-35 (CRITICAL):** Enforcement-NI bridge is disconnected (F-20). There is
**no theorem** connecting the `securityFlowsTo` check (enforcement) to the
domain-separation hypotheses (non-interference). You cannot automatically conclude
"if the checked operation succeeds, NI is preserved" — manual domain-separation
verification is required for every scenario.

**Finding A-36 (HIGH):** `activeDomain` is always observable. The scheduling domain
is exposed to all observers without filtering, enabling timing-channel attacks where
low-domain threads observe when high-domain computation is active.

**Finding A-37 (HIGH):** TCB fields (priority, timeSlice, ipcState, domain) are fully
visible in projections. This exposes scheduling and IPC metadata that can be
weaponized for timing and side-channel attacks.

**Finding A-38 (MEDIUM):** No covert channel analysis. Timing, scheduling, cache, and
microarchitectural side channels are not addressed. The model assumes perfect
abstraction of hardware timing.

**Finding A-39 (MEDIUM):** No declassification model. No explicit declassification
points identified; no mechanism for controlled information downgrade.

**Finding A-40 (MEDIUM):** Coverage is ~5-10% of published seL4 information-flow scope.
11 operation families proved (out of 30+ in seL4). Missing: dynamic capability
authority, physical memory model, partition-aware scheduling, side-channel resistant
scheduling.

---

## 11. Platform Bindings and API

### 11.1 Platform Contract System

`PlatformBinding` typeclass defines boot and runtime contracts. Sim and RPi5 platforms
implement this typeclass. The RPi5 binding includes BCM2712 board constants (UART,
GPIO base addresses, interrupt controller configuration).

**Finding A-41 (MEDIUM):** RPi5 platform stubs are minimal. Boot and runtime contracts
use placeholder validators (e.g., `interruptRoutingValid` simply checks for non-empty
routing table). Significant work remains before real hardware interaction.

### 11.2 Kernel API (API.lean)

Single file that re-exports all kernel subsystem operations. Serves as the public
interface. Contains 1 theorem (`kernelAPI_deterministic`).

**Finding A-42 (MEDIUM):** No capability-checking wrapper at the API boundary. The
API directly exposes raw kernel operations without verifying that the caller holds
the necessary capability for each operation. In real seL4, every syscall validates
capabilities first.

---

## 12. Testing Infrastructure

### 12.1 Test Harness Architecture

Four-tier validation system:
- **Tier 0** (Hygiene): Forbidden marker scan, structure anchors, shellcheck
- **Tier 1** (Build): `lake build` success
- **Tier 2** (Trace + Negative): Executable trace comparison + negative-state tests
- **Tier 3** (Invariant Surface): 300+ `rg` checks verifying theorem/definition anchors
- **Tier 4** (Nightly): Determinism replay, trace sequence probing

**Finding A-43 (MEDIUM):** Tier 3 tests are anchor-based, not proof-based. They verify
that specific definitions and theorems *exist* (via `rg` pattern matching) but do not
verify what those theorems *prove*. A theorem could be renamed or its statement
weakened without breaking Tier 3.

### 12.2 Negative State Suite

976 lines testing error paths. Covers IPC errors, capability errors, lifecycle errors,
scheduling errors, and service errors.

### 12.3 Information Flow Suite

650 lines testing projection, low-equivalence, enforcement checks, and label
consistency.

### 12.4 Trace Fixture System

Main trace output compared against `tests/fixtures/main_trace_smoke.expected` via
substring matching. This is fragile — any output formatting change breaks the test.

---

## 13. Build and CI Scripts

### 13.1 Script Quality

All 21 scripts pass `shellcheck` compliance (verified by Tier 0). Consistent use of
`set -euo pipefail`. Good library factoring via `test_lib.sh`.

**Finding A-44 (LOW):** The Tier 3 invariant surface script (`test_tier3_invariant_surface.sh`)
is 53KB and 400+ lines of `rg` checks. This is inherently fragile: any refactoring
that changes function/theorem names breaks the test without indicating whether the
underlying property is preserved.

### 13.2 CI Integrity

SHA-pinned GitHub Actions (verified by Tier 0 hygiene check). Elan installer has
SHA256 verification. Good security posture for CI supply chain.

---

## 14. Documentation Accuracy

### 14.1 README.md Discrepancies

| Claim | README Value | Actual Value | Delta |
|-------|-------------|-------------|-------|
| Lean LoC | 16,485 | 21,650 (prod) | +31% |
| Source files | 34 | 41 (prod) | +7 |
| Theorems | 400+ | 574 | +44% |
| Build jobs | 64 | 84 | +31% |
| Next workstream | WS-F5..F8 | WS-G completed (v0.12.15) | **STALE** |
| Active findings ref | v0.12.2 audits | v0.12.5 perf audit is active | **STALE** |

**Finding A-45 (MEDIUM):** README documentation is significantly outdated. Line counts,
file counts, theorem counts, and workstream references all lag behind the actual
codebase state.

### 14.2 CLAUDE.md Discrepancies

The CLAUDE.md instruction file is generally accurate but lists incorrect line counts
for several files (reflecting older versions). For example, `IPC/Invariant.lean` is
listed as ~3750 lines but is actually 3858.

---

## 15. Consolidated Findings Table

### Critical (8 findings)

| ID | Finding | Location | Impact |
|----|---------|----------|--------|
| A-07 | BEq for VSpaceRoot/CNode relies on HashMap.toList order | Object.lean | False inequality for equal maps |
| A-10 | capabilityRefs is function-typed, creating O(n) closure chains | State.lean | Performance degradation, fragility |
| A-14 | EDF invariant defined but zero preservation theorems | Scheduler/Invariant | EDF correctness unproven |
| A-15 | timeSlicePositive invariant defined but unproven | Scheduler/Invariant | Potential arithmetic underflow |
| A-22 | endpointQueueWellFormed only validates legacy fields | IPC/Invariant | Dual-queue invariants unchecked |
| A-34 | Non-standard security lattice (untrusted → trusted allowed) | IF/Policy | Security model deviation from BIBA |
| A-35 | Enforcement-NI bridge disconnected | IF/Enforcement + Invariant | Cannot prove end-to-end security |
| F-18 | AdapterProofHooks never instantiated | Arch/Invariant | Cannot prove adapter preservation |

### High (14 findings)

| ID | Finding | Location |
|----|---------|----------|
| A-02 | Typed identifier wrappers are bypassable (public val) | Prelude |
| A-05 | MemoryRegion.endAddr has no address overflow check | Machine |
| A-08 | Endpoint has redundant legacy + dual-queue fields | Object |
| A-09 | IpcMessage has unbounded payload size | Object |
| A-11 | CDT slot-node cleanup incomplete on CNode replacement | State |
| A-12 | No global ASID uniqueness invariant | State |
| A-16 | maxPriority cache correctness unproven | Scheduler/RunQueue |
| A-17 | chooseBestRunnableBy optimality unproven | Scheduler/Operations |
| A-20 | CDT completeness not proven (orphaned capabilities) | Capability/Invariant |
| A-23 | Unvalidated queue link dereference in dual-queue | IPC/DualQueue |
| A-24 | Message extraction after popHead can silently lose data | IPC/DualQueue |
| A-26 | retypeFromUntyped: no childId ≠ untypedId check | Lifecycle/Operations |
| A-27 | retypeFromUntyped: no child ID freshness check | Lifecycle/Operations |
| A-29 | Service operations don't verify backing-object existence | Service/Operations |
| A-36 | activeDomain always observable (timing channel) | IF/Projection |
| A-37 | TCB scheduling metadata fully visible in projections | IF/Projection |

### Medium (19 findings)

| ID | Finding | Location |
|----|---------|----------|
| A-01 | Inhabited defaults generate sentinel values without guard | Prelude |
| A-03 | Missing explicit EquivBEq instances | Prelude |
| A-04 | No LawfulMonad instance for KernelM | Prelude |
| A-06 | isPowerOfTwo correctness unproven | Machine |
| A-13 | objectIndex grows monotonically without bounds | State |
| A-18 | O(n) membership check in schedule (HashSet available) | Scheduler |
| A-19 | threadPriority consistency implicit, not type-enforced | Scheduler/RunQueue |
| A-21 | cspaceMove is not atomic (insert-then-delete) | Capability/Operations |
| A-25 | Legacy O(n) IPC operations retained without migration path | IPC/Operations |
| A-28 | Non-atomic dual-store in retypeFromUntyped | Lifecycle/Operations |
| A-30 | Service restart has partial-failure without rollback | Service/Operations |
| A-31 | serviceCountBounded assumption never established | Service/Invariant |
| A-32 | VSpace uses flat HashMap (no hierarchical page tables) | Architecture/VSpace |
| A-33 | Adapter depends on parameterized, not concrete, contracts | Architecture/Adapter |
| A-38 | No covert channel analysis | InformationFlow |
| A-39 | No declassification model | InformationFlow |
| A-40 | IF coverage ~5-10% of seL4 scope | InformationFlow |
| A-41 | RPi5 platform stubs are minimal placeholders | Platform/RPi5 |
| A-42 | No capability-checking wrapper at API boundary | API |
| A-43 | Tier 3 tests are anchor-based, not proof-based | Testing |
| A-45 | README documentation significantly outdated | Documentation |

---

## 16. Recommendations

### Tier 1: Before Hardware Deployment (Blocking)

1. **Prove EDF and timeSlice invariant preservation** (A-14, A-15). Add
   `timerTick_preserves_edfCurrentHasEarliestDeadline` and
   `schedule_preserves_timeSlicePositive`. Without these, the scheduler's
   claimed EDF semantics have no formal backing.

2. **Fix BEq for HashMap-backed types** (A-07). Replace `toList.all` pattern
   with bidirectional entry verification using key iteration. This affects
   VSpaceRoot and CNode equality, which are used in proof automation.

3. **Bridge enforcement to non-interference** (A-35, F-18). Instantiate
   `AdapterProofHooks` for at least the Sim platform. Add bridge theorems
   connecting `securityFlowsTo` checks to domain-separation hypotheses.

4. **Resolve non-standard security lattice** (A-34). Either formally justify
   the "both dimensions upward" semantics with a threat model, or correct
   the integrity dimension to standard BIBA (deny untrusted → trusted).

5. **Migrate capabilityRefs to HashMap** (A-10). Replace the function-typed
   `SlotRef → Option CapTarget` with `Std.HashMap SlotRef CapTarget` to
   eliminate O(n) closure chain accumulation.

### Tier 2: Before Stable Release (High Priority)

6. **Add dual-queue invariant validation** (A-22). Extend `endpointInvariant`
   to cover `sendQ`/`receiveQ` fields, or prove equivalence with legacy fields
   and deprecate the legacy representation (A-08).

7. **Prove maxPriority cache and chooseBest optimality** (A-16, A-17). These
   are the scheduler's correctness backbone. Proofs are tractable given the
   existing infrastructure.

8. **Add childId validation to retypeFromUntyped** (A-26, A-27). Check
   `childId ≠ untypedId` and `objects[childId]? = none` at the operation level,
   not just as proof preconditions.

9. **Clean up CDT slot-node mappings on CNode replacement** (A-11). Add
   `detachSlotFromCdt` calls in the `storeObject` path when replacing a CNode
   with a non-CNode object.

10. **Prove CDT completeness or document it as advisory** (A-20). Either add an
    invariant that all derived capabilities are captured in the CDT, or
    explicitly document that CDT revoke is not total.

### Tier 3: Ongoing Improvement (Medium Priority)

11. **Update README statistics** (A-45). Correct LoC, file count, theorem count,
    build jobs, and workstream references to match v0.12.15 reality.

12. **Encapsulate typed identifiers** (A-02). Make `val` fields private and
    expose only validated construction/conversion functions.

13. **Add semantic test assertions** (A-43). Replace output-driven trace tests
    with assertions that validate post-transition invariants and semantic
    properties. This is the single highest-value testing improvement.

14. **Address scheduling transparency** (A-36). If `activeDomain` must be
    visible to all observers, document this as a deliberate security assumption.
    If not, filter it like other projections.

15. **Bound IpcMessage payload** (A-09). Add size limits to `registers` and
    `caps` fields (e.g., `Array 256 Nat` instead of `List Nat`).

---

## Conclusion

seLe4n v0.12.15 is a remarkable achievement: a 23,000-line formally verified
microkernel with 574 machine-checked theorems and zero proof holes. The
architecture is clean, the invariant-operations split is disciplined, and the
proof coverage across capability, IPC, lifecycle, and service subsystems is
genuinely impressive.

The gaps identified in this audit are overwhelmingly **proof obligations that
should exist but don't yet** (EDF, timeSlice, maxPriority cache, CDT
completeness, enforcement-NI bridge) rather than **design errors or
vulnerabilities**. The model's deterministic transition semantics and explicit
error handling provide a strong foundation. The information-flow subsystem,
while early-stage relative to published seL4 proofs, establishes a correct
mathematical framework that can be extended.

The most critical path to hardware readiness is closing the scheduler proof
gaps (EDF + timeSlice), bridging enforcement to non-interference, and migrating
the state model's function-typed capabilityRefs to HashMap.

This kernel deserves the care it's receiving. The findings above are offered
in the spirit of making something strong even stronger.

---

*End of audit — AUDIT_CODEBASE_v0.12.15.md*
