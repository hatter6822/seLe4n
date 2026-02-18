# Independent Repository Audit — February 2026

**Date**: 2026-02-18
**Scope**: Full codebase — architecture, source, proofs, tests, CI/CD, documentation
**Version under audit**: 0.9.32

---

## Executive Summary

seLe4n is a Lean 4 formal model of the seL4 microkernel covering scheduler, capability/CSpace, IPC, lifecycle/retype, service orchestration, VSpace memory, architecture-boundary contracts, and information-flow security labels. At ~1,278 lines of Lean across 30 files, it is compact with extensive invariant-preservation proofs and a multi-tiered test framework.

The project demonstrates careful engineering discipline — typed identifiers, explicit error paths, layered invariant bundles, deterministic transitions. However, this audit identified **critical semantic gaps** between code and real seL4, **proof obligations that are tautologies**, **tests starting from invariant-violating states**, and a **documentation corpus vastly outweighing the code**.

### Severity Summary

| Severity | Count | Category |
|----------|-------|----------|
| Critical | 5 | Semantic fidelity, proof gaps |
| High | 7 | Missing functionality, test validity |
| Medium | 8 | Code quality, CI, architecture |
| Low | 6 | Style, documentation, minor issues |

---

## 1. Architecture Assessment

### 1.1 Strengths

- **Clean layered module hierarchy**: Prelude > Machine > Model.Object > Model.State > Kernel.* with clear dependency ordering.
- **Typed identifiers**: ObjId, ThreadId, DomainId, Priority, etc. are all structure wrappers around Nat, preventing accidental mixing.
- **Explicit error paths**: Every kernel operation returns Except KernelError with 14 distinct error constructors. No silent failures.
- **Operations/Invariant separation**: Each subsystem cleanly separates executable definitions from proof obligations.
- **BootstrapBuilder DSL**: StateBuilder.lean is well-designed for composing test states.

### 1.2 Architectural Criticisms

**MEDIUM -- Function-encoded state limits scalability.**
SystemState.objects uses `ObjId -> Option KernelObject` (total function from all naturals). This means every Nat is a valid ObjId (no finite object store), linear scans are required for enumeration (see vspaceDiscoveryWindow of 4096), and equality of SystemState requires function extensionality. Migrate to finite maps.

**MEDIUM -- ServiceId breaks type-wrapper discipline.**
Prelude.lean wraps every identifier as a structure. But Model/Object.lean:6 defines `abbrev ServiceId := Nat` -- a transparent alias, not a typed wrapper. This violates the project's own design principle.

**MEDIUM -- No do-notation in kernel code.**
The Kernel type has a Monad instance via KernelM, but all kernel operations use raw lambda functions with manual pattern matching. This produces deeply nested match pyramids (MainTraceHarness.lean reaches 15+ nesting levels).

**LOW -- VSpace discovery window is a linear-scan hack.**
Architecture/VSpace.lean:11 defines vspaceDiscoveryWindow as 4096. ASID resolution scans object IDs 0-4095 linearly. O(n) and architecturally fragile.

---

## 2. Source Code -- Semantic Fidelity Issues

These compare the model against real seL4 behavior.

### 2.1 CRITICAL -- IPC send-to-waiting-receiver does not complete the handshake

IPC/Operations.lean:31-36: When a sender meets a waiting receiver (the IPC fast-path in seL4), the code clears the endpoint back to idle but does NOT identify or return the receiver, does NOT add the receiver back to the runnable queue, and does NOT transfer any message payload. In real seL4 this is the most important IPC path -- the sender's message is copied directly to the receiver's registers and the receiver is made runnable. The model silently drops the receiver.

Impact: Any reasoning about IPC completeness is unsound for the fast-path case.

### 2.2 CRITICAL -- IPC operations never update TCB ipcState

Model/Object.lean:61-66 defines ThreadIpcState with blockedOnSend, blockedOnReceive, blockedOnNotification states. But no IPC operation ever updates the TCB's ipcState field:

- endpointSend never sets sender to blockedOnSend
- endpointAwaitReceive never sets receiver to blockedOnReceive
- notificationWait never sets waiter to blockedOnNotification
- endpointReceive/notificationSignal never reset TCBs to ready

The ipcState field is dead data. The 16 IPC/scheduler contract theorems in IPC/Invariant.lean (runnableThreadIpcReady, blockedOnSendNotRunnable, blockedOnReceiveNotRunnable preservations) are vacuously true because no operation ever changes ipcState.

Impact: The entire ipcSchedulerContractPredicates proof track provides no actual assurance.

### 2.3 CRITICAL -- Notification badge semantics are wrong

IPC/Operations.lean:90-96: When signaling a notification that is already active, seL4 bitwise-ORs the new badge with the existing pending badge. This model overwrites the pending badge entirely. Multiple signals lose information; the receiver sees only the last badge.

Additionally, signaling an already-active notification should OR badges rather than transition state. The model doesn't handle the active->active case at all -- it only handles the case where waitingThreads is non-empty (wakes a waiter) or empty (sets to active). If the notification is already active with a pending badge and no waiters, the signal overwrites rather than accumulates.

### 2.4 CRITICAL -- Scheduler ignores priorities entirely

Scheduler/Operations.lean:8-12: chooseThread always picks the first thread in the runnable list, ignoring TCB.priority completely. seL4 uses a strict priority scheduler with 256 levels. The Priority type exists but is never consulted.

Impact: Any scheduling fairness or priority-inversion reasoning is meaningless.

### 2.5 HIGH -- handleYield is an unconditional alias for schedule

Scheduler/Operations.lean:26-27: A yield in seL4 moves the current thread to the end of its priority queue, then reschedules. This model's yield just re-runs the scheduler without modifying the queue. The current thread is immediately re-selected. No round-robin semantics exist.

---

## 3. Source Code -- Proof Quality Issues

### 3.1 CRITICAL -- Tautological determinism proofs

Architecture/VSpace.lean:57-61:
```
theorem vspaceLookup_deterministic ... :
    vspaceLookup asid vaddr st = vspaceLookup asid vaddr st := rfl
```

This proves f(x) = f(x) -- definitional equality for any function. It says nothing about determinism. Same issue in InformationFlow/Projection.lean:65-70 with projectState_deterministic. These theorems inflate the proof count without semantic value.

### 3.2 HIGH -- lowEquivalent proofs are structural properties of Eq

Projection.lean:72-94 proves reflexivity, symmetry, and transitivity of lowEquivalent. But lowEquivalent is defined as `projectState ctx observer s1 = projectState ctx observer s2`. So the proofs are just properties of `=`, which hold for any projection function including `fun _ => ()`.

The actual noninterference property -- "if two states are low-equivalent and we execute an operation, the results are still low-equivalent" -- is completely absent. Zero `_preserves_lowEquivalent` theorems exist anywhere.

### 3.3 HIGH -- Service projection leaks through observer clearance

Projection.lean:57-59: projectState passes service status through unfiltered:
```
services := projectServiceStatus st  -- NOT filtered by observer clearance
```

A low-clearance observer sees the same service graph as a high-clearance observer. This is a built-in covert channel. InformationFlowSuite.lean:86-87 tests this as a feature, but it is an information-flow bug.

### 3.4 HIGH -- No notification invariant preservation proofs

notificationSignal and notificationWait modify scheduler state (ensureRunnable, removeRunnable in IPC/Operations.lean:89,121). But there are ZERO invariant preservation theorems for notification operations. The ipcInvariant is only proven preserved for endpoint operations (endpointSend, endpointAwaitReceive, endpointReceive) but not for notificationSignal or notificationWait. Notification operations could break scheduler invariants with no proof coverage.

### 3.5 MEDIUM -- Duplicate theorems across files

These theorems are identical in IPC/Invariant.lean and Lifecycle/Operations.lean:
- storeObject_objects_eq / lifecycle_storeObject_objects_eq
- storeObject_objects_ne / lifecycle_storeObject_objects_ne
- storeObject_scheduler_eq / lifecycle_storeObject_scheduler_eq

Should be consolidated into Model/State.lean.

---

## 4. Testing Audit

### 4.1 HIGH -- bootstrapState contains unreachable thread in runnable queue

MainTraceHarness.lean:100: `withRunnable [1, 2]` puts ThreadId 2 in the runnable queue, but no TCB with tid := 2 exists. Object ID 2 doesn't exist at all. The scheduler correctly falls through to setCurrentThread none, but this masks potential bugs and the initial state doesn't represent a reachable kernel state.

### 4.2 HIGH -- NegativeStateSuite starts from invariant-violating state

NegativeStateSuite.lean:50: `withObject sendEmptyEndpointId (.endpoint { state := .send, queue := [], waitingReceiver := none })` -- an endpoint in .send state with an empty queue violates endpointQueueWellFormed, which requires .send to have a non-empty queue. Testing error paths from states the kernel can never reach doesn't validate real error handling.

### 4.3 HIGH -- No runtime invariant verification

All 3 test executables check operation results (success/error, return values) but never verify kernel invariants hold after operations. There is no test that runs an operation then checks schedulerInvariantBundle, ipcInvariant, or endpointQueueWellFormed on the result state. Invariants exist only at proof level.

### 4.4 MEDIUM -- Tests are deterministic snapshots, not property tests

All testing is snapshot-based: run a fixed trace, compare output strings against main_trace_smoke.expected. No property-based testing, no randomized state exploration, no fuzzing, no invariant-based random testing. For a formal verification project, this is a significant gap.

### 4.5 MEDIUM -- InformationFlowSuite doesn't test noninterference

Tests check label comparison and projection visibility but never test whether any operation preserves low-equivalence. The lowEquivalent proof witness at line 75 compares sampleState to itself -- trivially true.

### 4.6 MEDIUM -- TraceSequenceProbe has no expected-output validation

tests/TraceSequenceProbe.lean takes a seed argument but has no expected-output fixtures. The nightly tier-4 script runs probes but only checks they don't crash, not that output is correct.

### 4.7 LOW -- Deep nesting in MainTraceHarness reduces readability

runLifecycleAndEndpointTrace chains ~20 operations in a deeply nested match pyramid reaching 15+ indentation levels. This is fragile and hard to review. Using do-notation with the Kernel monad or a test combinator would flatten this dramatically.

---

## 5. CI/CD Assessment

### 5.1 MEDIUM -- Missing runner.arch in x86 cache keys

lean_action_ci.yml and nightly_determinism.yml use cache keys without runner.arch while platform_security_baseline.yml correctly includes it. Risk of cross-architecture cache contamination if GitHub's runner pool changes.

### 5.2 MEDIUM -- Toolchain update workflow has injection risk

lean_toolchain_update_proposal.yml:46 interpolates the upstream release tag (latestTag) into a GitHub search query without sanitization. Defense-in-depth requires validating the tag format.

### 5.3 LOW -- Tier-0 hygiene regex has false-positive risk

test_tier0_hygiene.sh:12 matches the literal string TODO anywhere, including in docstrings or comments explaining intentional deferrals. Should use word-boundary anchors.

### 5.4 LOW -- Nightly flake probe uses only 2 iterations

ci_flake_probe.sh runs tests twice. Two iterations can only detect flakes with >50% reproduction rate. Industry standard is 3-5 iterations.

### 5.5 Positive CI findings

- Fork handling in platform_security_baseline.yml is correct
- Dependabot configured
- Workflow permissions properly scoped
- No secrets leaked in workflows
- ARM64 testing is genuine (runs full test_fast.sh)

---

## 6. Documentation Assessment

### 6.1 HIGH -- Documentation-to-code ratio is extreme

~57 markdown files (~10,000+ lines) for ~1,278 lines of Lean. This is roughly 8:1. The 29-chapter GitBook, 5 audit documents, and extensive workstream tracking create navigational overhead disproportionate to the codebase. Many documents describe intentions and future work rather than current state.

### 6.2 MEDIUM -- Documentation claims unverified properties

Several documents claim properties the code doesn't establish:
- "Noninterference proofs" -- no noninterference theorem exists
- "IPC-scheduler handshake semantics" -- IPC ops don't update TCB ipcState
- "Priority-based scheduling" -- priorities are ignored
- WS-B6 "notification-object IPC completion" -- badge OR semantics missing
- WS-B7 "information-flow proof-track start" -- only Eq properties proven

### 6.3 LOW -- CHANGELOG tracks micro-level changes

Version 0.9.32 has dozens of entries that are internal refactoring steps, making it hard to identify actual functional changes.

---

## 7. Security Posture

### Positive findings

- No axiom or sorry in proof surface. Tier-0 hygiene enforces this and manual review confirms.
- RuntimeContractFixtures properly quarantined in SeLe4n/Testing/ with hygiene checks preventing leakage into SeLe4n/Kernel/.
- Apache 2.0 licensing with complete LICENSE file.
- CI permissions properly scoped.

### Concerns

- Tier-0 sorry/axiom scan only covers SeLe4n/ and Main.lean. Files in tests/ are not checked.
- .gitignore mentions .env patterns but no .env.example or documented secret requirements exist.

---

## 8. Recommendations (Prioritized)

### Immediate (blocks correctness claims)

1. **Fix IPC fast-path**: endpointSend in the .receive case must return/wake the waiting receiver.
2. **Wire ipcState**: IPC operations must update TCB.ipcState so scheduler/IPC contract proofs are non-vacuous.
3. **Fix notification badge OR**: Signal to active notification must OR badges, not overwrite.
4. **Remove tautological proofs**: vspaceLookup_deterministic and projectState_deterministic prove f(x)=f(x). Remove or honestly relabel.
5. **Implement noninterference theorem**: Add at least one operation_preserves_lowEquivalent theorem.

### High Priority (blocks testing validity)

6. **Fix test initial states**: NegativeStateSuite's sendEmptyEndpointId should start from a valid state. MainTraceHarness should add a TCB for thread 2 or remove it from runnable.
7. **Add runtime invariant checks**: After each operation in test traces, assert invariant bundles hold.
8. **Add notification invariant proofs**: notificationSignal and notificationWait need preservation theorems.
9. **Add property-based testing**: Generate random valid states and operations, check invariant preservation.

### Medium Priority (code quality)

10. **Implement priority-aware scheduling**: chooseThread should select the highest-priority runnable thread.
11. **Wrap ServiceId as a structure**: Align with typed-identifier discipline.
12. **Consolidate duplicate theorems**: Move shared storeObject lemmas to Model/State.lean.
13. **Filter services in IF projection**: projectState should filter service status through observer clearance.
14. **Add runner.arch to CI cache keys**: Consistent cache isolation across all workflows.

### Low Priority (polish)

15. **Implement yield semantics**: handleYield should move current thread to end of queue.
16. **Consolidate documentation**: Prune 29-chapter GitBook and 5 audit docs to match code surface.
17. **Tighten hygiene regex**: Use word boundaries for sorry/axiom/TODO matching.
18. **Increase flake probe iterations**: From 2 to 3-5.

---

## 9. Conclusion

seLe4n demonstrates strong engineering discipline in its layered architecture, typed identifiers, explicit error handling, and proof infrastructure. The CI/CD pipeline and tiered testing framework show thoughtful process design.

However, the model has critical semantic gaps relative to seL4 -- particularly in IPC message transfer, notification badge accumulation, and scheduler priority handling. The information-flow proof track proves structural properties of equality rather than meaningful noninterference. Several tests start from invariant-violating states, and no test verifies invariant preservation at runtime.

The documentation is comprehensive but disproportionate to the code, and in several places claims properties the code does not establish. The gap between documentation ambition and code reality is the single most important issue to address.

Before advancing beyond v0.9.x, the five immediate recommendations should be resolved, as they affect fundamental correctness claims.
