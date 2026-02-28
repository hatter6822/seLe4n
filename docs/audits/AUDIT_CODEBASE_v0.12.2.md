# End-to-End Codebase Audit — seLe4n v0.12.2

**Date:** 2026-02-27
**Scope:** Full codebase — 14,708 lines of Lean across 33 files
**Toolchain:** Lean 4.28.0, Lake build system
**Build status:** All 62 compilation units pass. `test_smoke.sh` passes.

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Codebase Statistics](#2-codebase-statistics)
3. [Foundation Layer Audit](#3-foundation-layer-audit)
4. [Kernel Subsystem Audits](#4-kernel-subsystem-audits)
5. [Information Flow Subsystem Audit](#5-information-flow-subsystem-audit)
6. [Testing and CI Audit](#6-testing-and-ci-audit)
7. [Documentation Accuracy Audit](#7-documentation-accuracy-audit)
8. [Cross-Cutting Findings](#8-cross-cutting-findings)
9. [Classified Finding Register](#9-classified-finding-register)
10. [Recommendations](#10-recommendations)

---

## 1. Executive Summary

seLe4n v0.12.2 is a **genuine, sorry-free Lean 4 formalization** of core seL4
microkernel semantics with machine-checked invariant preservation proofs. The
project has zero `sorry` and zero `axiom` in its production proof surface — every
theorem is fully machine-checked by the Lean kernel. This is a meaningful
achievement.

**Strengths:**
- Zero sorry/axiom in production code — all proofs are machine-checked
- Clean architectural separation (Operations/Invariant split per subsystem)
- Compositional proof architecture with well-chosen factoring lemmas
- Tiered CI testing (4 tiers) with hygiene, trace, negative, and invariant gates
- SHA-pinned CI dependencies, secret scanning, and security baseline workflow
- Thorough negative state test suite with per-mutation invariant checking
- Well-documented sentinel convention (ID 0 reserved, mirrors seL4_CapNull)

**Weaknesses (detailed below):**
- Significant proof gaps: several defined operations lack invariant preservation theorems
- The dual-queue IPC model (the more seL4-accurate model) has zero formal proofs
- Information flow covers ~5-10% of what published seL4 proofs establish
- The Service orchestration layer is a novel abstraction not present in real seL4
- Several "invariant components" are tautologically true regardless of state
- VSpace model is highly abstract (flat list, no page tables, no TLB, no permissions)
- No Untyped memory model — lifecycle retype is "replace object" not "carve from untyped"

---

## 2. Codebase Statistics

| Metric | Value |
|--------|-------|
| Total Lean lines | 14,708 |
| Production modules | 26 files |
| Test modules | 7 files |
| `sorry` count | 0 |
| `axiom` count | 0 |
| Defined operations | ~50 |
| Proved theorems | ~200+ |
| CI workflows | 4 (lean_action_ci, platform_security, nightly_determinism, toolchain_update) |
| Shell test scripts | 16 |
| Test tiers | 5 (Tier 0–4) |
| Trace fixture expectations | 68 lines |

---

## 3. Foundation Layer Audit

### 3.1 Prelude (460 lines)

**Assessment: Solid.**

Typed wrapper structures for all identifiers (`ObjId`, `ThreadId`, `CPtr`, `Slot`,
`DomainId`, `Priority`, `Deadline`, `Irq`, `ServiceId`, `Badge`, `ASID`, `VAddr`,
`PAddr`) — preventing Nat-aliasing bugs. Sentinel convention (ID 0 = reserved)
is consistently applied with `isReserved`, `sentinel`, and `valid` predicates.
`ThreadId.toObjId_injective` is a key lemma used downstream in IPC proofs.

The `KernelM` state/error monad is correctly defined with `pure`, `bind`, `get`,
`set`, `modify`, `throw`, `liftExcept`, each with correctness theorems proven by `rfl`.

**Minor issue:** `DomainId`, `Priority`, `Irq`, `Badge`, `ASID` lack `isReserved`/
`sentinel` predicates — only `ObjId`, `ThreadId`, `ServiceId`, `CPtr` have them.
This is inconsistent but may be intentional (not all ID spaces need sentinels).

### 3.2 Machine (138 lines)

**Assessment: Solid.**

Clean abstract machine model: `RegisterFile` (pc, sp, gpr), `Memory` (PAddr → UInt8),
`MachineState` with timer. All read-after-write and frame lemmas proven by `rfl`.
Zero-initialization proofs anchor the deterministic boot assumption.

**Observation:** `Memory` is total (`PAddr → UInt8`) — every physical address
is accessible. This cannot model unmapped memory or MMIO regions. Documented as
a known limitation with migration path to `PAddr → Option UInt8`.

### 3.3 Model/Object (707 lines)

**Assessment: Strong.**

Models `TCB`, `Endpoint`, `Notification`, `CNode`, `VSpaceRoot` as variants of
`KernelObject`. The `CNode` has comprehensive slot-index uniqueness infrastructure
(`slotsUnique`, with preservation through `insert`, `remove`, `revokeTargetLocal`).
`VSpaceRoot` has genuine non-overlap proofs and round-trip map/unmap/lookup theorems.

The Capability Derivation Tree (CDT) model uses stable node IDs with edge-based
forest representation. `descendantsOf` uses bounded BFS with `edges.length` as
fuel. The `acyclic` definition and `empty_acyclic` theorem are sound.

**Finding F-01 (LOW):** The `Endpoint` structure carries both legacy fields
(`state`, `queue`, `waitingReceiver`) and dual-queue fields (`sendQ`, `receiveQ`).
These are redundant and can diverge — no invariant constrains their relationship.

### 3.4 Model/State (756 lines)

**Assessment: Strong.**

`SystemState` correctly models the global kernel state with functional maps
(`ObjId → Option KernelObject`, etc.). `storeObject` atomically updates objects,
lifecycle metadata, and objectIndex. Monotonic objectIndex is well-documented
and formally verified (`storeObject_objectIndex_monotone`).

Bidirectional CDT slot↔node attachment (`attachSlotToCdtNode`, `detachSlotFromCdt`)
with stale-link cleanup is well-implemented. The `ensureCdtNodeForSlot` allocator
uses a monotonic counter.

Lifecycle metadata consistency (`objectTypeMetadataConsistent`,
`capabilityRefMetadataConsistent`) is maintained by construction in `storeObject` —
see Finding F-02.

---

## 4. Kernel Subsystem Audits

### 4.1 Scheduler (909 lines)

**Operations defined:** `isBetterCandidate`, `chooseThread`, `schedule`,
`handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`, `filterByDomain`.

**Proved invariants:** Core triad (`queueCurrentConsistent`, `runQueueUnique`,
`currentThreadValid`) plus `currentThreadInActiveDomain` — fully proved for
`schedule`, `handleYield`, `chooseThread`, `switchDomain`, `scheduleDomain`.

**Finding F-03 (HIGH):** `timerTick` has **zero preservation theorems**. It
modifies the object store (updating `tcb.timeSlice`) and potentially reschedules,
but no invariant (`queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`,
`currentThreadInActiveDomain`) is proved preserved. This is the most significant
gap in the scheduler proof surface.

**Finding F-04 (MEDIUM):** `timeSlicePositive` and `edfCurrentHasEarliestDeadline`
are defined but have zero theorems connecting them to any operation. They are
aspirational invariants with no proof evidence.

**Finding F-05 (LOW):** `chooseBestRunnableBy` (the fold that selects the best
thread) is not proved to return the optimal candidate. The comparator's
irreflexivity and asymmetry are proved, but the fold's optimality is not.

**seL4 fidelity:** Domain scheduling correctly mirrors seL4's `dschedule[]`.
Priority scheduling and EDF tie-breaking are structurally correct. Missing: MCP
(maximum controlled priority), per-priority ready queues, sporadic server
budgets, and scheduling context objects.

### 4.2 Capability (2,034 lines)

**Operations defined:** `cspaceLookupSlot`, `cspaceResolvePath`, `cspaceLookupPath`,
`cspaceInsertSlot`, `cspaceMint`, `cspaceDeleteSlot`, `cspaceRevoke`, `cspaceCopy`,
`cspaceMove`, `cspaceMutate`, `cspaceMintWithCdt`, `cspaceRevokeCdt`,
`cspaceRevokeCdtStrict`.

**Invariant bundle:** `capabilityInvariantBundle` = `cspaceSlotUnique` ∧
`cspaceLookupSound` ∧ `cspaceAttenuationRule` ∧ `lifecycleAuthorityMonotonicity`.

**Fully proved preservation for:** `cspaceLookupSlot`, `cspaceInsertSlot`,
`cspaceMint`, `cspaceDeleteSlot`, `cspaceRevoke`, `cspaceCopy`, `cspaceMove`,
`cspaceMintWithCdt`, plus cross-subsystem IPC operations.

**Finding F-06 (HIGH):** `cspaceMutate`, `cspaceRevokeCdt`, and
`cspaceRevokeCdtStrict` have **zero invariant preservation theorems**. These are
defined operations that modify CNode state but have no formal verification.

**Finding F-07 (MEDIUM):** `cspaceAttenuationRule` and
`lifecycleAuthorityMonotonicity` are **state-independent tautologies**. They are
universally true regardless of system state — they add no state-dependent
assurance to the bundle. They inflate the apparent proof strength.

**Finding F-08 (MEDIUM):** `cspaceRevokeCdt` silently swallows errors during
descendant deletion (line 386). When `cspaceDeleteSlot` fails for a descendant,
the CDT node is removed anyway, creating potential CDT/CSpace inconsistency.

**Finding F-09 (MEDIUM):** Revocation is limited to single-CNode scope in the
proved theorems. Real seL4 `cteRevoke` walks the CDT across all CNodes. The
CDT-based `cspaceRevokeCdt` attempts cross-CNode revocation but is unproved.

**seL4 fidelity:** Core CSpace operations (lookup, mint, copy, move, delete) are
well-modeled. Guard/radix resolution is structurally present but disconnected
from the proof surface. Missing: multi-level CSpace walk, CTE type resolution,
recycling.

### 4.3 IPC (2,571 lines)

**Operations defined:** `endpointSend`, `endpointAwaitReceive`, `endpointReceive`,
`notificationSignal`, `notificationWait`, `endpointSendDual`, `endpointReceiveDual`,
`endpointQueueRemoveDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`.

**Invariant predicates:** `endpointQueueWellFormed`, `endpointObjectValid`,
`ipcInvariant`, `notificationQueueWellFormed`, `runnableThreadIpcReady`,
`blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`, `uniqueWaiters`.

**Fully proved preservation for:** Legacy `endpointSend`, `endpointAwaitReceive`,
`endpointReceive`, `endpointReply` — covering `ipcInvariant`,
`schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`.

**Finding F-10 (CRITICAL):** The dual-queue operations (`endpointSendDual`,
`endpointReceiveDual`, `endpointQueueRemoveDual`) have **zero invariant
preservation theorems**. These are the more seL4-accurate endpoint model (intrusive
FIFO queues), yet they are completely unverified formally. All formal proofs target
the legacy single-queue model.

**Finding F-11 (HIGH):** `endpointCall` and `endpointReplyRecv` (compound
operations listed as stable API) have **zero invariant preservation theorems**.

**Finding F-12 (HIGH):** `notificationSignal` and `notificationWait` have result
well-formedness theorems but **no full `ipcInvariant` or
`schedulerInvariantBundle` preservation**. Only `uniqueWaiters` preservation for
`notificationWait` exists.

**Finding F-13 (MEDIUM):** `ipcSchedulerContractPredicates` does not cover
`blockedOnNotification` or `blockedOnReply` states. Threads in these states
should also not be runnable, but no predicate enforces this.

**Finding F-14 (LOW):** The `endpointInvariant` definition (line 79) is defined
but never referenced — dead code.

**seL4 fidelity:** Control flow is well modeled (blocking, unblocking, queue
management). Badge OR-merge for notifications matches seL4 semantics. Missing:
message register transfer, capability transfer during IPC, fault IPC.

### 4.4 Lifecycle (543 lines)

**Operations defined:** `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype`.

**Invariant bundle:** `lifecycleInvariantBundle` = `lifecycleIdentityAliasingInvariant`
∧ `lifecycleCapabilityReferenceInvariant`.

**Fully proved:** `lifecycleRetypeObject_preserves_lifecycleInvariantBundle`,
plus stale-reference and identity-stale-reference variants.

**Finding F-15 (MEDIUM):** `lifecycleIdentityNoTypeAliasConflict` is trivially
true for any deterministic state model (same function applied to same input
yields same output). It is a structural placeholder, not meaningful assurance.

**Finding F-16 (LOW):** Lifecycle metadata consistency is maintained by
construction in `storeObject` — the model cannot represent metadata
desynchronization, which reduces the significance of the preservation proofs.

**seL4 fidelity:** Only retype (object replacement) is modeled. Missing: Untyped
memory model (watermark tracking, region bounds), object creation from untyped,
object deletion / memory reclamation, TCB configuration
(`TCB_Configure`/`TCB_SetSpace`/etc.).

### 4.5 Service (~1,300 lines)

**Operations defined:** `serviceStart`, `serviceStop`, `serviceRestart`,
`serviceRegisterDependency`, `serviceHasPathTo`.

**Invariant bundle:** `serviceLifecycleCapabilityInvariant` =
`servicePolicySurfaceInvariant` ∧ `serviceCountBounded` ∧ `serviceExistenceValid`
∧ `serviceDependencyAcyclic`.

**Finding F-17 (MEDIUM):** The Service orchestration layer is a **novel
abstraction not present in real seL4**. The `ServiceGraphEntry` with dependency
edges, isolation edges, and runtime status is not a seL4 concept. While
potentially useful for modeling higher-level system composition, it should be
clearly labeled as a project-specific extension rather than a seL4 formalization.

**seL4 fidelity:** None — this is pure project extension. seL4 has no concept of
services, service dependencies, or service lifecycle management at the kernel level.

### 4.6 Architecture (1,118 lines)

**Operations defined:** `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup`,
`adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory`.

**Invariant bundle:** `vspaceInvariantBundle` = `vspaceAsidRootsUnique` ∧
`vspaceRootNonOverlap`. Plus `proofLayerInvariantBundle` composing all subsystems.

**Fully proved:** VSpace map/unmap success preservation, four round-trip theorems
(map-then-lookup, map-other, unmap-then-lookup, unmap-other), adapter error
characterization, default state satisfies all invariants.

**Finding F-18 (MEDIUM):** `AdapterProofHooks` is **never instantiated**. The
composed adapter preservation theorems are conditional on proof obligations that
remain open. The entire adapter-to-invariant connection has an unresolved hole.

**Finding F-19 (LOW):** `BootBoundaryContract`, `InterruptBoundaryContract`,
and `boundedAddressTranslation` are forward-declared stubs with no consumers.

**seL4 fidelity:** VSpace is highly abstract — flat mapping list instead of
multi-level page tables. No frame objects, no page permissions (R/W/X), no TLB
model, no ASID pool hierarchy. The VSpace round-trip theorems are genuine but
limited in scope. Timer/register/memory adapters correctly gate behind
runtime contracts.

---

## 5. Information Flow Subsystem Audit (1,628 lines)

**Assessment: Architecturally sound but early-stage.**

The projection-based non-interference approach (Goguen-Meseguer style) is correct
and aligns with published seL4 information-flow methodology. The `lowEquivalent`
relation is an equivalence (reflexivity, symmetry, transitivity proven). Five core
non-interference theorems are machine-checked:
- `endpointSend_preserves_lowEquivalent`
- `chooseThread_preserves_lowEquivalent`
- `cspaceMint_preserves_lowEquivalent`
- `cspaceRevoke_preserves_lowEquivalent`
- `lifecycleRetypeObject_preserves_lowEquivalent`

Trace-level composition is proven (`composedNonInterference_trace`).

**Finding F-20 (HIGH):** The enforcement layer and non-interference layer are
**not formally connected**. Enforcement wrappers check flow policy; non-interference
theorems assume domain separation via hypotheses. No theorem proves "if a checked
operation succeeds, the domain-separation hypotheses are satisfied."

**Finding F-21 (MEDIUM):** `notificationSignal` has no non-interference theorem
despite modifying shared state (the notification word).

**Finding F-22 (MEDIUM):** The `ObservableState` projection does not project
CSpace internals — observable CNodes expose their full slot contents, potentially
leaking high-domain capability information to low-domain observers.

**Finding F-23 (LOW):** The `enforcementBoundary` classification table (17
operations) is not verified to be exhaustive or consistent with the actual API.

**Maturity relative to published seL4 info-flow proofs:** ~5-10% of scope.
Published proofs cover ~30+ syscalls, dynamic authority model, partitioned
scheduler timing channels, physical frame memory model, and whole-execution
unwinding — all absent here. The architecture is correct for extension; the
coverage is narrow.

---

## 6. Testing and CI Audit

### 6.1 Test Infrastructure

**Tier 0 (Hygiene):** Scans for `sorry`/`axiom`/`TODO` in production surface,
checks typed-ID wrapper regression, validates doc sync, spot-checks trivial
rfl-only proofs in invariant files, verifies SHA-pinned GitHub Actions, runs
shellcheck. **Assessment: Thorough.**

**Tier 1 (Build):** `lake build`. **Assessment: Standard.**

**Tier 2 (Trace + Negative):** Fixture-diff trace harness (68 expectations) +
`negative_state_suite` + `information_flow_suite`. **Assessment: The negative
state suite is excellent** — it tests specific error codes, runs invariant oracle
after every mutation, and covers deliberate corruption scenarios for intrusive
queue pointers.

**Tier 3 (Invariant Surface):** 533-line script with ~200+ `rg`-based anchor
checks verifying that specific theorem names, structure definitions, and
documentation anchors exist. **Assessment: Good regression net.**

**Finding F-24 (MEDIUM):** The runtime invariant oracle (`InvariantChecks.lean`)
does **not check** the following formal invariants:
- `blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`
- `currentThreadInActiveDomain`
- `timeSlicePositive`, `edfCurrentHasEarliestDeadline`
- CDT structural integrity (no runtime oracle at all)
- `uniqueWaiters`

**Finding F-25 (LOW):** `runtimeContractTimerOnly` and
`runtimeContractReadOnlyMemory` fixtures are defined but never exercised.

**Finding F-26 (LOW):** The `TraceSequenceProbe` fuzzer only covers 3 IPC
operations (`send`, `awaitReceive`, `receive`). Extending to dual-queue,
notification, scheduler, and capability operations would significantly strengthen
coverage.

### 6.2 CI Workflows

Four GitHub Actions workflows with SHA-pinned dependencies:
- `lean_action_ci.yml`: docs→fast→smoke→full pipeline
- `platform_security_baseline.yml`: ARM64 cross-compile + Gitleaks + Trivy + CodeQL
- `nightly_determinism.yml`: Tier 0-4 + flake probe (3x smoke retry)
- `lean_toolchain_update_proposal.yml`: Weekly check for upstream Lean releases

**Assessment: Well-structured CI.** SHA pinning, artifact upload, telemetry
capture, and concurrency groups are all present. The security baseline includes
secret scanning and vulnerability scanning — uncommon for a formal verification
project and commendable.

---

## 7. Documentation Accuracy Audit

**Version consistency:** lakefile.toml says `0.12.2`, README says `0.12.2`,
SELE4N_SPEC says `0.12.2` — consistent.

**Finding F-27 (MEDIUM):** SELE4N_SPEC.md (Section 2) says "Active portfolio:
WS-E1..WS-E6" while README says "Current active portfolio: In-Planning" and
"Prior completed: WS-E1..WS-E6". The spec document has not been updated to
reflect WS-E completion. Section 4 header says "Active Workstream Portfolio
(WS-E)" when these are completed.

**Finding F-28 (LOW):** The CLAUDE.md says version "0.12.0" in the project
description while the actual version is 0.12.2.

**Trace fixture:** All 68 expected trace lines match actual output — verified by
running `lake exe sele4n` during this audit.

---

## 8. Cross-Cutting Findings

### 8.1 Proof Coverage Gap Analysis

Of ~50 defined kernel operations, invariant preservation is proved for ~25.
Operations lacking formal proofs:

| Operation | Severity | Notes |
|-----------|----------|-------|
| `timerTick` | HIGH | Modifies object store + reschedules |
| `endpointSendDual` | CRITICAL | More seL4-accurate model, exercised by tests |
| `endpointReceiveDual` | CRITICAL | Same as above |
| `endpointQueueRemoveDual` | HIGH | O(1) removal from intrusive queue |
| `endpointCall` | HIGH | Compound send + block-for-reply |
| `endpointReplyRecv` | HIGH | Compound reply + receive |
| `notificationSignal` (full) | HIGH | Result WF only, no system-level preservation |
| `notificationWait` (full) | HIGH | Same as above |
| `cspaceMutate` | HIGH | In-place rights attenuation |
| `cspaceRevokeCdt` | MEDIUM | Cross-CNode CDT revocation |
| `cspaceRevokeCdtStrict` | MEDIUM | Variant with error reporting |

### 8.2 The Legacy vs. Dual-Queue Divergence

This is the most architecturally significant issue. The codebase maintains two
parallel endpoint models:
- **Legacy** (`endpointSend`/`endpointAwaitReceive`/`endpointReceive`): Simple
  state machine with list-based queue. **All formal proofs target this model.**
- **Dual-queue** (`endpointSendDual`/`endpointReceiveDual`): Intrusive
  linked-list with `sendQ`/`receiveQ`. **Zero formal proofs, but better models
  real seL4.**

The invariant definitions (`endpointQueueWellFormed`) only inspect legacy fields
(`ep.queue`, `ep.waitingReceiver`). Even if dual-queue preservation theorems were
added, the invariant definitions would need extension.

### 8.3 State-Independent "Invariants"

Several components of invariant bundles are universally true regardless of state:
- `cspaceAttenuationRule` — property of `mintDerivedCap`, not of any state
- `lifecycleAuthorityMonotonicity` — property of operations, not of any state
- `lifecycleIdentityNoTypeAliasConflict` — tautological for deterministic lookup

These inflate the apparent invariant surface without providing state-dependent
assurance. They should be reclassified as operation correctness lemmas rather
than state invariants.

---

## 9. Classified Finding Register

| ID | Severity | Subsystem | Finding |
|----|----------|-----------|---------|
| F-01 | LOW | Model | Legacy and dual-queue endpoint fields are redundant and unconstrained |
| F-02 | — | Model | Lifecycle metadata consistency is by-construction (design note, not a finding) |
| F-03 | **HIGH** | Scheduler | `timerTick` has zero preservation theorems |
| F-04 | MEDIUM | Scheduler | `timeSlicePositive` and `edfCurrentHasEarliestDeadline` defined but unproved |
| F-05 | LOW | Scheduler | `chooseBestRunnableBy` fold optimality unproved |
| F-06 | **HIGH** | Capability | `cspaceMutate`, `cspaceRevokeCdt`, `cspaceRevokeCdtStrict` lack proofs |
| F-07 | MEDIUM | Capability | Two bundle components are state-independent tautologies |
| F-08 | MEDIUM | Capability | `cspaceRevokeCdt` silently swallows descendant deletion errors |
| F-09 | MEDIUM | Capability | Proved revocation is single-CNode only |
| F-10 | **CRITICAL** | IPC | Dual-queue operations have zero formal proofs |
| F-11 | **HIGH** | IPC | `endpointCall` and `endpointReplyRecv` lack proofs |
| F-12 | **HIGH** | IPC | Notification ops lack full system-level preservation proofs |
| F-13 | MEDIUM | IPC | Scheduler contract missing `blockedOnNotification`/`blockedOnReply` |
| F-14 | LOW | IPC | `endpointInvariant` definition is dead code |
| F-15 | MEDIUM | Lifecycle | `lifecycleIdentityNoTypeAliasConflict` is trivially true |
| F-16 | LOW | Lifecycle | Metadata consistency is by-construction |
| F-17 | MEDIUM | Service | Novel abstraction not present in seL4 — should be clearly labeled |
| F-18 | MEDIUM | Architecture | `AdapterProofHooks` never instantiated — open proof obligation |
| F-19 | LOW | Architecture | Forward-declared stubs with no consumers |
| F-20 | **HIGH** | InfoFlow | Enforcement and non-interference layers not formally connected |
| F-21 | MEDIUM | InfoFlow | `notificationSignal` non-interference missing |
| F-22 | MEDIUM | InfoFlow | Projection leaks CNode internals to observers |
| F-23 | LOW | InfoFlow | Enforcement boundary table not verified exhaustive |
| F-24 | MEDIUM | Testing | Runtime oracle missing several formal invariant checks |
| F-25 | LOW | Testing | Unused runtime contract fixtures |
| F-26 | LOW | Testing | TraceSequenceProbe covers only 3 operations |
| F-27 | MEDIUM | Docs | SELE4N_SPEC.md workstream status stale |
| F-28 | LOW | Docs | CLAUDE.md version string outdated |

**Summary:** 1 CRITICAL, 6 HIGH, 12 MEDIUM, 9 LOW

---

## 10. Recommendations

### Priority 1 — Close Critical Proof Gaps

1. **Prove dual-queue IPC invariant preservation** (F-10). Either:
   - Extend `endpointQueueWellFormed` to cover `sendQ`/`receiveQ` and prove
     preservation for `endpointSendDual`/`endpointReceiveDual`, or
   - Formally bridge the dual-queue operations to the legacy invariants by
     proving a simulation/refinement relation.

2. **Prove `timerTick` preservation** (F-03). This is the highest-value scheduler
   proof work — `timerTick` modifies objects and reschedules.

### Priority 2 — Close High-Severity Gaps

3. **Prove notification full-system preservation** (F-12). The building blocks
   (result well-formedness) exist — composing them into `ipcInvariant` and
   `schedulerInvariantBundle` preservation should be tractable.

4. **Prove `endpointCall`/`endpointReplyRecv` preservation** (F-11). These are
   composed from already-proved primitives.

5. **Prove `cspaceMutate` preservation** (F-06). Uses `cn.insert` which already
   has `insert_slotsUnique` — should be straightforward.

6. **Connect enforcement to non-interference** (F-20). Add a theorem proving that
   if `endpointSendChecked` succeeds, the domain-separation hypotheses of
   `endpointSend_preserves_lowEquivalent` are satisfied.

### Priority 3 — Architectural Improvements

7. **Reclassify state-independent tautologies** (F-07, F-15). Move
   `cspaceAttenuationRule`, `lifecycleAuthorityMonotonicity`, and
   `lifecycleIdentityNoTypeAliasConflict` out of state-invariant bundles into
   a separate "operation correctness" namespace.

8. **Extend `ipcSchedulerContractPredicates`** (F-13) to cover all five
   `ThreadIpcState` constructors.

9. **Resolve the legacy/dual-queue divergence** at the architectural level —
   either deprecate legacy operations or maintain a formal refinement bridge.

10. **Extend the runtime invariant oracle** (F-24) to check
    `currentThreadInActiveDomain`, `blockedOnSendNotRunnable`, etc.

### Priority 4 — Documentation and Cleanup

11. Update SELE4N_SPEC.md section 2/4 to reflect WS-E completion (F-27).
12. Update CLAUDE.md version string (F-28).
13. Remove dead `endpointInvariant` definition (F-14).
14. Label the Service subsystem as a project extension, not seL4 formalization (F-17).
