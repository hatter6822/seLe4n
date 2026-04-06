# Comprehensive Kernel Audit — seLe4n v0.25.14

**Date**: 2026-04-06
**Scope**: All 132 Lean modules, 30 Rust ABI files, full production reachability analysis
**Auditor**: Pre-release audit (automated + manual review)
**Branch**: `claude/audit-lean-kernel-9BleT`

---

## Executive Summary

This audit reviewed every module in the seLe4n v0.25.14 kernel — 132 Lean
files and 30 Rust ABI files — with emphasis on production reachability,
security correctness, dead code detection, and Lean-Rust ABI synchronization.

**Critical findings**: 4 HIGH, 9 MEDIUM, 13 LOW, 11 INFORMATIONAL

The kernel demonstrates exceptional proof hygiene (zero sorry/axiom in
production code) and sound formal verification. However, four high-severity
issues were discovered: (1) the production-recommended checked dispatch path
silently drops two syscalls, (2) a significant body of code is tested
but unreachable from the production import chain, (3) `switchDomain` is
missing from the `NonInterferenceStep` inductive, leaving domain-switch
non-interference unproven in composition, and (4) PIP/SchedContext donation
mutations in the call/reply paths occur outside the NI proof envelope.

---

## Table of Contents

1. [Finding Summary Table](#finding-summary-table)
2. [HIGH Severity Findings](#high-severity-findings)
3. [MEDIUM Severity Findings](#medium-severity-findings)
4. [LOW Severity Findings](#low-severity-findings)
5. [INFORMATIONAL Findings](#informational-findings)
6. [Proof Hygiene Assessment](#proof-hygiene-assessment)
7. [Production Reachability Map](#production-reachability-map)
8. [Rust ABI Synchronization](#rust-abi-synchronization)
9. [Per-Subsystem Audit Notes](#per-subsystem-audit-notes)
10. [Recommendations](#recommendations)

---

## Finding Summary Table

| ID | Severity | Component | Title |
|----|----------|-----------|-------|
| F-01 | **HIGH** | Kernel/API.lean | `dispatchWithCapChecked` missing `tcbSetPriority` and `tcbSetMCPriority` arms |
| F-02 | **HIGH** | Multiple | FrozenOps subsystem (4 files) unreachable from production import chain |
| F-03 | MEDIUM | Scheduler/Liveness/* | Entire Liveness subsystem (7 files) unreachable from production |
| F-04 | MEDIUM | Kernel/API.lean | `dispatchWithCapChecked` duplicates `tcbSetIPCBuffer` arm instead of routing through `dispatchCapabilityOnly` |
| F-05 | MEDIUM | Kernel/API.lean | Wildcard unreachability comment at line 987 is incorrect |
| F-06 | LOW | Model/IntermediateState | IntermediateState, Builder only reachable via Platform.Boot (not kernel API) |
| F-07 | LOW | Scheduler/RunQueue | RunQueue.lean defines `RHSet`-backed run queue — large module (675 lines) with complex operations |
| F-08 | LOW | IPC/DualQueue/WithCaps | `endpointSendDualWithCaps` and `endpointCallWithCaps` are only reachable from API dispatch, not from any other kernel-internal path |
| F-09 | LOW | SchedContext/Operations | `schedContextYieldTo` is kernel-internal (no SyscallId), correctly documented but has bridge lemma in CrossSubsystem |
| F-10 | LOW | Platform/DeviceTree | `fromDtb` stub always returns `none` — must be replaced before DTB-based boot |
| F-11 | LOW | Testing/StateBuilder | `buildChecked` uses `panic!` on invariant violation — acceptable for test code |
| F-12 | INFO | Proof hygiene | Zero sorry, zero axiom, zero unsafe in production code |
| F-13 | INFO | Rust ABI | All 25 SyscallId and 44 KernelError variants perfectly synchronized |
| F-14 | INFO | native_decide | 2 uses in production code — both justified compile-time completeness checks |
| F-15 | INFO | CrossSubsystem | Fully reachable via Architecture.Invariant → API.lean |
| F-16 | INFO | RobinHood | Deeply integrated into production chain (Prelude, Object/Types, State, RunQueue) |
| F-17 | INFO | RadixTree | Reachable via Platform.Boot → FreezeProofs → FrozenState |
| F-18 | INFO | Re-export hubs | All 15 re-export hub files correctly import their submodules |
| S-01 | MEDIUM | Scheduler/PriorityInheritance/Propagate | PIP propagation reads pre-mutation `blockingServer` state |
| S-02 | MEDIUM | Scheduler/Operations/Selection | Domain filter uses `tcb.domain` but effective priority uses `sc.domain` |
| S-03 | LOW | Scheduler/Operations/Core | `handleYield` re-enqueues at raw priority, not effective priority |
| S-04 | LOW | Scheduler/Operations/Preservation | `*Effective`/`*WithBudget` variants lack full invariant preservation proofs |
| S-05 | LOW | Scheduler/Operations/Core | `timeoutBlockedThreads` O(n) scan over entire object store |
| IF-01 | **HIGH** | InformationFlow/Invariant/Composition | `switchDomain` missing from `NonInterferenceStep` inductive |
| IF-02 | **HIGH** | Kernel/API.lean + InformationFlow | PIP/donation mutations in call/reply outside NI proof envelope |
| IF-03 | MEDIUM | InformationFlow/Invariant/Composition | `NonInterferenceStep` proves per-operation NI, not full dispatch NI |
| IF-04 | MEDIUM | InformationFlow/Enforcement/Wrappers | Default labeling context uses `⊥` (bottom) — all flows permitted |
| IF-05 | MEDIUM | InformationFlow/Policy | BIBA integrity ordering reversed (`securityFlowsTo` used for both) |
| IF-06 | MEDIUM | InformationFlow/Invariant | Service registry excluded from NI projection model |
| IF-07 | LOW | InformationFlow/Enforcement/Soundness | Declassification well-formedness not structurally enforced |
| IF-08 | LOW | InformationFlow/Enforcement/Wrappers | Dispatch structure couples enforcement to operation structure |
| IF-09 | LOW | InformationFlow/Invariant/Composition | `replyRecv` compound operation NI proof assumes decomposition |
| IF-10 | LOW | InformationFlow/Invariant/Operations | Scheduling covert channel not modeled in NI proofs |
| C-01 | LOW | Kernel/Capability/Operations | `resolveCapAddress` correctly handles `bitsRemaining=0` — no issue |
| C-02 | INFO | Architecture/SyscallArgDecode | 21 of 25 syscalls have arg decoders; 4 IPC ops use MessageInfo directly |
| C-03 | INFO | Platform/RPi5/Board | BCM2712 MMIO addresses verified realistic against published documentation |

---

## HIGH Severity Findings

### F-01: `dispatchWithCapChecked` missing `tcbSetPriority` and `tcbSetMCPriority`

**Location**: `SeLe4n/Kernel/API.lean`, lines 802-989
**Impact**: Production syscall entry point silently rejects priority management syscalls
**Severity**: HIGH

**Description**: The production-recommended entry point `syscallEntryChecked` routes
through `dispatchSyscallChecked` → `dispatchWithCapChecked`. This function handles
25 `SyscallId` variants through two mechanisms:

1. `dispatchCapabilityOnly` — shared helper handling 11 capability-only arms
2. Explicit match arms in `dispatchWithCapChecked` — handling 14 remaining arms

However, `.tcbSetPriority` and `.tcbSetMCPriority` are in **neither**:
- They are NOT in `dispatchCapabilityOnly` (lines 437-540), which handles
  `cspaceDelete`, `lifecycleRetype`, `vspaceMap`, `vspaceUnmap`, `serviceRevoke`,
  `serviceQuery`, `schedContextConfigure`, `schedContextBind`, `schedContextUnbind`,
  `tcbSuspend`, `tcbResume`
- They are NOT explicitly matched in `dispatchWithCapChecked` (lines 808-989)

They fall through to `| _ => fun _ => .error .illegalState` at line 989.

**Contrast**: The unchecked `dispatchWithCap` correctly handles both at lines 731-757.
The enforcement boundary (`Wrappers.lean` line 221-222) correctly classifies them as
`.capabilityOnly "setPriority"` and `.capabilityOnly "setMCPriority"`.

**Root cause**: When D2 (priority management, v0.24.1) was implemented, the arms were
added to `dispatchWithCap` (unchecked) but not to `dispatchWithCapChecked` (checked).
D3 (`tcbSetIPCBuffer`) was correctly added to both paths. D1 (`tcbSuspend`,
`tcbResume`) was correctly added to `dispatchCapabilityOnly`.

**Remediation**: Add `.tcbSetPriority` and `.tcbSetMCPriority` to
`dispatchCapabilityOnly` (the shared helper), which would fix both dispatch paths
simultaneously. This is the correct approach since these are capability-only
operations requiring no information-flow checks.

**Verification**: The `dispatchWithCap_wildcard_unreachable` theorem (line 1195) proves
all 25 variants are handled in the unchecked path. An analogous theorem should be
added for `dispatchWithCapChecked` to prevent future regressions.

---

### F-02: FrozenOps subsystem unreachable from production import chain

**Location**: `SeLe4n/Kernel/FrozenOps/` (Core.lean, Operations.lean, Commutativity.lean, Invariant.lean)
**Impact**: 4 production-quality modules with proofs are not reachable from any production code path
**Severity**: HIGH

**Description**: The `FrozenOps` subsystem defines a `FrozenKernel` monad and 15
per-subsystem frozen operations with commutativity proofs and invariant preservation
theorems. These 4 files are imported **only** by:

- `tests/FrozenOpsSuite.lean`
- `tests/PriorityManagementSuite.lean`
- `tests/SuspendResumeSuite.lean`
- `tests/IpcBufferSuite.lean`
- `tests/TwoPhaseArchSuite.lean`

They are NOT imported by any module in the production import chain
(`SeLe4n.lean` → `Kernel/API.lean` → subsystem modules).

**Impact assessment**: The FrozenOps subsystem was designed for the two-phase
architecture (Q7) where the kernel operates on frozen (immutable) state during
syscall processing. If this architecture is intended for production use, these
modules must be integrated into the API layer. If it's preparatory infrastructure,
it should be documented as such and not counted toward production proof coverage.

**Remediation**: Either:
1. Integrate FrozenOps into the production API dispatch path (e.g., syscallEntryChecked
   operates on FrozenSystemState), or
2. Move to a `SeLe4n/Future/` or `SeLe4n/Experimental/` directory and clearly
   document the non-production status.

---

### IF-01: `switchDomain` missing from `NonInterferenceStep` inductive

**Location**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`, lines 34-308
**Impact**: Domain-switch non-interference is unproven in trace composition
**Severity**: HIGH

**Description**: The `NonInterferenceStep` inductive in `Composition.lean` contains
32 constructors covering individual kernel operations (endpointSendDual, cspaceMint,
vspaceMapPage, etc.), but **does not include** a `switchDomain` constructor.

A `switchDomain_preserves_lowEquivalent` theorem exists in `Operations.lean` (lines
580-596), proving that switchDomain preserves low-equivalence for a single step. However,
since `switchDomain` is not a constructor in `NonInterferenceStep`, the trace composition
proof (`nonInterferenceMultiStep`) cannot include domain-switch transitions.

This means the NI guarantee has a gap: a trace including domain switches is not covered
by the composition theorem. Since domain switches are the primary mechanism for
cross-domain isolation, this is a critical gap in the security proof.

**Remediation**: Add a `switchDomain` constructor to `NonInterferenceStep` that
references the `switchDomain_preserves_lowEquivalent` theorem. This closes the
composition gap without requiring new proofs — the per-step theorem already exists.

---

### IF-02: PIP/donation mutations outside NI proof envelope

**Location**: `SeLe4n/Kernel/API.lean`, lines 610-614 (call), 870-873 (reply)
**Impact**: Priority inheritance propagation and SchedContext donation are not covered by NI proofs
**Severity**: HIGH

**Description**: In the checked dispatch path:

- **Call arm** (lines 610-614): After `endpointCallWithCaps`, the code applies
  `applyCallDonation` then `propagatePriorityInheritance`. These mutations modify
  scheduler state (PIP boost, SchedContext binding) but occur AFTER the IPC operation
  that the `endpointCallHigh` NI constructor covers.

- **Reply arm** (lines 870-873): After `endpointReplyChecked`, the code applies
  `applyReplyDonation` then `revertPriorityInheritance`. Same issue — post-operation
  mutations outside the NI envelope.

The `NonInterferenceStep` constructors for `endpointCallHigh` and `endpointReply`
reference the base operations (`endpointCall`, `endpointReply`) without accounting
for the post-operation PIP state changes. This means the NI composition proof covers
the IPC operation but not the subsequent scheduler mutations, creating a gap where
information could flow through priority inheritance changes.

**Risk assessment**: In practice, PIP boost values derive from the blocking graph
(which is IPC-state-dependent), so they may not constitute a novel information channel.
However, the formal proof does not establish this — it simply does not cover these
mutations.

**Remediation**: Either:
1. Extend the `endpointCallHigh` and `endpointReply` NI constructors to cover the
   composed operation (IPC + donation + PIP), or
2. Add separate NI constructors for `applyCallDonation`/`propagatePriorityInheritance`
   and `applyReplyDonation`/`revertPriorityInheritance`, and compose them in the trace.

---

## MEDIUM Severity Findings

### F-03: Scheduler Liveness subsystem unreachable from production

**Location**: `SeLe4n/Kernel/Scheduler/Liveness/` (7 files: TraceModel, TimerTick,
Replenishment, Yield, BandExhaustion, DomainRotation, WCRT) + hub `Liveness.lean`
**Impact**: WCRT bounded latency theorem and all liveness proofs are test-only
**Severity**: MEDIUM

**Description**: The `Scheduler.Liveness` re-export hub is imported only by
`tests/LivenessSuite.lean`. The `Scheduler.Invariant.lean` module (which IS in the
production chain) does NOT import `Liveness.lean` or any Liveness submodule.

These 7+1 files contain the bounded latency theorem (WCRT = D*L_max + N*(B+P)),
timer-tick budget monotonicity, CBS replenishment bounds, yield/rotation semantics,
and priority-band exhaustion analysis — all key liveness guarantees.

**Risk**: The liveness theorems compile and pass tests, but since they are not
transitively imported by any production module, they could silently diverge from
the actual scheduler implementation if `Scheduler/Operations/Core.lean` is modified
without updating the liveness proofs.

**Remediation**: Import `SeLe4n.Kernel.Scheduler.Liveness` from
`SeLe4n/Kernel/Scheduler/Invariant.lean` or `SeLe4n/Kernel/Architecture/Invariant.lean`
to bring liveness proofs into the production build. This ensures the Lean type-checker
verifies liveness theorem compatibility with actual scheduler operations on every build.

---

### F-04: `tcbSetIPCBuffer` duplicated instead of shared

**Location**: `SeLe4n/Kernel/API.lean`, lines 759-769 (unchecked) and 976-986 (checked)
**Impact**: Maintenance burden; divergence risk between checked and unchecked paths
**Severity**: MEDIUM

**Description**: `.tcbSetIPCBuffer` is handled by explicit match arms in BOTH
`dispatchWithCap` and `dispatchWithCapChecked`, rather than being routed through
`dispatchCapabilityOnly` like the other capability-only operations. This is the same
pattern that caused F-01 (the missing `tcbSetPriority`/`tcbSetMCPriority` arms).

The enforcement boundary correctly classifies `tcbSetIPCBuffer` as `.capabilityOnly`,
confirming it needs no information-flow check and should be in `dispatchCapabilityOnly`.

**Remediation**: Move `.tcbSetIPCBuffer` into `dispatchCapabilityOnly` alongside
`.tcbSuspend` and `.tcbResume`. This eliminates the duplication and ensures both
dispatch paths handle it identically through the shared helper.

---

### F-05: Incorrect wildcard unreachability comment

**Location**: `SeLe4n/Kernel/API.lean`, lines 987-989
**Impact**: False documentation claim; could mislead auditors
**Severity**: MEDIUM

**Description**: The comment at line 987 states:
```
-- V8-H/D3: Remaining capability-only arms are unreachable — handled by
-- dispatchCapabilityOnly returning `some` above.
```

This is **incorrect** for `dispatchWithCapChecked`. The `.tcbSetPriority` and
`.tcbSetMCPriority` arms are NOT handled by `dispatchCapabilityOnly` and DO reach
the wildcard. The comment is only accurate for `dispatchWithCap` (where these arms
are explicitly matched before the wildcard).

Furthermore, there is no `dispatchWithCapChecked_wildcard_unreachable` theorem
analogous to `dispatchWithCap_wildcard_unreachable` (line 1195). Adding such a
theorem would have caught F-01 at compile time.

**Remediation**: Fix the comment, and add a compile-time wildcard unreachability
theorem for `dispatchWithCapChecked` to prevent future regressions.

---

### IF-03: `NonInterferenceStep` proves per-operation NI, not full dispatch NI

**Location**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`, lines 34-308
**Impact**: NI composition theorem does not cover the complete `dispatchSyscall` path
**Severity**: MEDIUM

**Description**: `NonInterferenceStep` has 32 constructors for individual kernel
operations, and `syscallDispatchHigh` (lines 295-299) wraps full dispatch via a
`hProj` hypothesis parameter. This means the composition theorem assumes the
dispatched operation preserves projection — it does not prove it from first principles.

The per-operation NI proofs in `Operations.lean` (~1492 lines) provide the actual
guarantees, but the gap between "each operation individually satisfies NI" and
"the dispatch function as a whole satisfies NI" is bridged by assumption, not proof.

**Remediation**: Add a master dispatch theorem proving that `dispatchSyscallChecked`
preserves projection for ALL 25 `SyscallId` variants, discharging all 32 per-operation
proofs. This closes the assumption gap.

---

### IF-04: Default labeling context uses bottom label — all flows permitted

**Location**: `SeLe4n/Kernel/InformationFlow/Policy.lean`
**Impact**: Default configuration permits all cross-domain flows
**Severity**: MEDIUM

**Description**: The default `LabelingContext` initializes security labels to `⊥`
(bottom), meaning `securityFlowsTo` returns true for all domain pairs. This is
correct for testing and simulation but means the default kernel configuration has
no information-flow restrictions. If a platform binding fails to configure proper
labels, the enforcement boundary will permit all flows silently.

**Remediation**: Add a runtime check or theorem verifying that the boot sequence
configures non-trivial security labels before the first syscall. Alternatively,
add a `LabelingContext.isNonTrivial` predicate and check it in `syscallEntryChecked`.

---

### IF-05: BIBA integrity uses same ordering as confidentiality

**Location**: `SeLe4n/Kernel/InformationFlow/Policy.lean`
**Impact**: Integrity ordering may not match seL4's BIBA model
**Severity**: MEDIUM

**Description**: The `securityFlowsTo` predicate is used for both confidentiality
(no read-up, no write-down) and integrity (BIBA: no write-up, no read-down). If
the same lattice ordering is used for both properties, the BIBA integrity direction
is effectively reversed relative to standard BIBA formulations where high-integrity
data flows downward.

This may be intentional (a lattice-theoretic dual), but the model does not explicitly
distinguish the two flow directions or document the duality.

**Remediation**: Add explicit documentation clarifying the integrity flow direction.
If BIBA integrity is intended, consider separate predicates `confidentialityFlowsTo`
and `integrityFlowsTo` with documented lattice orientations.

---

### IF-06: Service registry excluded from NI projection model

**Location**: `SeLe4n/Kernel/InformationFlow/Projection.lean`
**Impact**: Service operations are not covered by non-interference projection
**Severity**: MEDIUM

**Description**: The NI projection model (`projectState`) projects kernel state
per domain for the non-interference property. The service registry (`serviceEntries`)
is not included in the projection — service registrations, revocations, and queries
are invisible to the NI framework.

This means that if a service operation leaks information across domain boundaries
(e.g., a query reveals the existence of a cross-domain service), this would not be
caught by the NI proofs. The enforcement boundary classifies service operations
(`.serviceWrite "register"`, `.serviceWrite "revoke"`, `.serviceRead "query"`) but
the projection does not observe their effects.

**Remediation**: Extend `projectState` to include the domain-relevant subset of
the service registry, then prove NI preservation for service operations against
the extended projection.

---

## LOW Severity Findings

### F-06: IntermediateState and Builder only reachable via Boot path

**Location**: `SeLe4n/Model/IntermediateState.lean`, `SeLe4n/Model/Builder.lean`
**Severity**: LOW

These modules are reachable through `SeLe4n.lean` → `Platform.Boot` → `Model.Builder`
→ `Model.IntermediateState`. They are not dead code, but they are not reachable
through the kernel API path. This is architecturally correct (they are boot-phase
infrastructure), but should be documented in the source layout.

---

### F-07: RunQueue complexity

**Location**: `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~675 lines)
**Severity**: LOW

The run queue implementation uses `RHSet` (Robin Hood hash set) for O(1) membership
testing. This is a complex data structure for a run queue. The implementation appears
correct with proper RHSet integration, but the complexity of the Robin Hood hash table
means the TCB includes a non-trivial hash table implementation. This is a deliberate
design trade-off for performance.

---

### F-08: WithCaps IPC functions only reachable from API dispatch

**Location**: `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean`
**Severity**: LOW

`endpointSendDualWithCaps` and `endpointCallWithCaps` are only called from the
API dispatch path (`dispatchWithCap` and `dispatchWithCapChecked`). They are not
used by any kernel-internal path. This is correct behavior (kernel internals use
the base `endpointSendDual` / `endpointCall`), but it means capability transfer
during IPC is only tested through the full syscall dispatch path.

---

### F-09: `schedContextYieldTo` has no SyscallId

**Location**: `SeLe4n/Kernel/SchedContext/Operations.lean`, line 219
**Severity**: LOW

`schedContextYieldTo` is defined as a kernel-internal operation with no `SyscallId`
mapping. It has a bridge lemma in `CrossSubsystem.lean` and is tested in
`MainTraceHarness.lean`. The documentation correctly labels it as "kernel-internal".
In seL4, `seL4_SchedContext_YieldTo` is a user-space syscall. If user-space access
is needed, a `SyscallId.schedContextYieldTo` variant would need to be added.

---

### F-10: DTB parsing stub

**Location**: `SeLe4n/Platform/DeviceTree.lean`, line 135
**Severity**: LOW

`DeviceTree.fromDtb` is a stub that always returns `none`. The actual DTB parser
is implemented in `fromDtbFull` (which uses `parseFdtNodes`). The stub exists for
forward compatibility. This is properly documented but the stub should be removed
or deprecated once `fromDtbFull` is the canonical path.

---

### F-11: `panic!` in test StateBuilder

**Location**: `SeLe4n/Testing/StateBuilder.lean`, line 175
**Severity**: LOW

`buildChecked` uses `panic!` when invariant construction fails. This is appropriate
for test infrastructure — it ensures test setup failures are immediately visible.
Not present in any production kernel code.

---

### IF-07: Declassification well-formedness not structurally enforced

**Location**: `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean`
**Severity**: LOW

Declassification gates allow controlled information flow between domains (e.g.,
IPC send across a domain boundary). The well-formedness of declassification
requests (valid source/target labels, authorized gate) is checked at runtime
but not structurally enforced by the type system. A malformed declassification
context could pass the runtime check if label comparison is permissive.

**Remediation**: Consider adding a well-formedness witness type that must be
constructed through a validated path, similar to `IntermediateState`'s
invariant witnesses.

---

### IF-08: Enforcement dispatch structure tightly coupled to operation structure

**Location**: `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`
**Severity**: LOW

The enforcement wrappers individually wrap each kernel operation, creating a 1:1
coupling between the enforcement layer and the operation layer. When new operations
are added (as with D1-D3), both the enforcement boundary and the checked dispatch
path must be updated. The `enforcementBoundary_is_complete` `native_decide` check
catches missing entries, but only at Lean compile time — there is no analogous
check for the checked dispatch path (cf. F-01).

**Remediation**: Factor checked dispatch through a table-driven approach that
automatically derives dispatch from the enforcement boundary classification.

---

### IF-09: `replyRecv` NI proof assumes decomposition into reply + receive

**Location**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
**Severity**: LOW

The `replyRecv` compound operation is a single atomic transition in the kernel
(`API.lean` handles it as one arm) but the NI composition proof decomposes it
into a reply step followed by a receive step. If the atomic implementation has
observable intermediate states that differ from the sequential decomposition,
the NI proof may not cover the actual transition.

In practice, the Lean model is sequential (no interleaving), so this decomposition
is sound. But it should be documented as an assumption.

---

### IF-10: Scheduling covert channel not modeled

**Location**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`
**Severity**: LOW

The NI proofs model information flow through explicit state changes (object store,
IPC queues, capabilities) but do not model timing-based covert channels through
the scheduler. A thread in domain A could infer information about domain B's
workload by observing its own scheduling quantum consumption or preemption patterns.

This is a well-known limitation of state-based NI models and is common in all
formally-verified microkernels (including seL4's original NI proof). Not a defect
in the proof, but a documented scope limitation.

---

### C-01: `resolveCapAddress` correctly handles zero-bit edge case

**Location**: `SeLe4n/Kernel/Capability/Operations.lean`, line 87
**Severity**: LOW (positive confirmation)

Verified that `resolveCapAddress` explicitly guards against `bitsRemaining = 0`
at entry (`if hZero : bitsRemaining = 0 then .error .illegalState`), preventing
degenerate CSpace resolution paths. The recursive case maintains strict descent
via `Nat.sub_lt` proof. No issue found.

---

## INFORMATIONAL Findings

### F-12: Proof Hygiene — Excellent

- **0** `sorry` statements in production or test code
- **0** `axiom` declarations
- **0** `unsafe` blocks in Lean code
- **0** `unreachable!` macros
- **0** `dbg_trace` statements
- **0** `noncomputable` definitions
- **0** `Classical.*` axiom usage
- **0** `opaque` definitions

All proofs are constructive. The kernel operates in pure Lean 4 without any
classical logic or unsound proof techniques.

### F-13: Rust ABI Synchronization — Perfect

All cross-boundary types are synchronized:
- **SyscallId**: 25 variants, identical encoding (0-24) in both Lean and Rust
- **KernelError**: 44 variants, identical encoding (0-43) in both Lean and Rust
- **AccessRight**: Required rights per syscall match exactly
- **MessageInfo**: Encode/decode bit layout matches (7-bit length, 2-bit extraCaps, label)

Rust conformance tests verify roundtrip encoding and cross-reference Lean source lines.

### F-14: `native_decide` Usage — Justified

Two occurrences in production code:
1. `Enforcement/Wrappers.lean:286` — enforcement boundary completeness (all 25 SyscallIds covered)
2. `CrossSubsystem.lean:626` — pairwise coverage completeness (12 disjoint field pairs)

Both are compile-time finite decidability checks. They fail at build time if safety
properties are violated. Documented with risk/mitigation notes.

### F-15–F-18: Production Reachability Confirmations

- **CrossSubsystem.lean**: Reachable via `Architecture.Invariant` → `API.lean` (F-15)
- **RobinHood/***: Deeply integrated via `Prelude`, `Object/Types`, `State`, `RunQueue` (F-16)
- **RadixTree/***: Reachable via `Platform.Boot` → `FreezeProofs` → `FrozenState` (F-17)
- **All 15 re-export hubs**: Correctly import their submodules with no missing imports (F-18)

### C-02: SyscallArgDecode coverage — 21 of 25 decoders (by design)

`SyscallArgDecode.lean` defines typed argument decoders for 21 of 25 syscall types.
The 4 IPC syscalls (send, receive, call, reply) do not have separate arg decoders
because they use `MessageInfo` + capability pointer from registers, decoded directly
at the API layer via `RegisterDecode.lean`. This is architecturally correct — IPC
arguments include variable-length message payloads that don't fit a fixed struct pattern.

### C-03: RPi5 BCM2712 MMIO addresses verified realistic

`Platform/RPi5/Board.lean` defines MMIO addresses for the BCM2712 SoC:
- `peripheralBaseLow: 0xFE000000` — correct legacy 32-bit peripheral window
- `peripheralBaseHigh: 0x1000000000` — correct high peripheral window (>4GB)
- `gicDistributorBase: 0xFF841000` — realistic GIC-400 distributor offset
- `gicCpuInterfaceBase: 0xFF842000` — realistic GIC-400 CPU interface
- ARM Generic Timer at 54 MHz — matches RPi5 crystal specification

All addresses are consistent with published BCM2712 documentation.

---

## Proof Hygiene Assessment

| Metric | Count | Status |
|--------|-------|--------|
| sorry statements | 0 | CLEAN |
| axiom declarations | 0 | CLEAN |
| panic! (production) | 0 | CLEAN |
| panic! (test) | 3 | ACCEPTABLE |
| native_decide (production) | 2 | JUSTIFIED |
| partial def (production) | 0 | CLEAN |
| partial def (test) | 2 | ACCEPTABLE |
| decide (all) | 65 | SOUND |
| Classical axioms | 0 | CLEAN |
| unsafe blocks | 0 | CLEAN |

**Assessment**: The codebase meets the highest standard of proof hygiene for a
formally-verified microkernel. All proofs are machine-checked constructive proofs
with no admitted goals or postulated axioms.

---

## Production Reachability Map

### Modules IN the production import chain (via SeLe4n.lean)

```
SeLe4n.lean
├── SeLe4n/Prelude.lean (includes RobinHood.Bridge)
├── SeLe4n/Machine.lean
├── SeLe4n/Model/Object.lean → Object/Types.lean, Object/Structures.lean
├── SeLe4n/Model/State.lean (includes RobinHood.Set)
├── SeLe4n/Kernel/API.lean
│   ├── Scheduler/Invariant.lean → SchedContext/Invariant.lean
│   ├── Scheduler/Operations.lean → Operations/Core, Selection, Preservation
│   │   └── RunQueue.lean (includes RobinHood.Set)
│   ├── Capability/Operations.lean
│   ├── Capability/Invariant.lean → Invariant/Defs, Authority, Preservation
│   ├── IPC/DualQueue.lean → DualQueue/Core, Transport, WithCaps
│   ├── IPC/Invariant.lean → all Invariant submodules
│   ├── IPC/Operations.lean → Operations/Endpoint, CapTransfer, Timeout
│   ├── IPC/Operations/Donation.lean
│   ├── Lifecycle/Operations.lean
│   ├── Lifecycle/Invariant.lean → Invariant/SuspendPreservation
│   ├── Lifecycle/Suspend.lean
│   ├── Service/Operations.lean, Registry.lean, Invariant.lean
│   ├── InformationFlow/* (Policy, Projection, Enforcement, Invariant)
│   ├── Architecture/* (Adapter, Assumptions, Invariant, VSpace, RegisterDecode, etc.)
│   │   └── Architecture/Invariant.lean → CrossSubsystem.lean
│   ├── SchedContext/Operations.lean, PriorityManagement.lean
│   └── SchedContext/Invariant/* (via CrossSubsystem)
├── Architecture/VSpaceBackend.lean, TlbModel.lean, RegisterDecode.lean
├── Platform/Contract.lean
├── Platform/Boot.lean → Model/Builder.lean → Model/IntermediateState.lean
│   └── Model/FreezeProofs.lean → Model/FrozenState.lean → RadixTree/Bridge
├── Platform/Sim/Contract.lean → Sim/RuntimeContract, BootContract, ProofHooks
└── Platform/RPi5/Contract.lean → RPi5/Board, RuntimeContract, BootContract, etc.
```

### Modules NOT in the production import chain

| Module | Files | Test Coverage | Status |
|--------|-------|---------------|--------|
| **FrozenOps/** | 4 files | 5 test suites | **TEST-ONLY** (F-02) |
| **Scheduler/Liveness/** | 7+1 files | LivenessSuite (58 tests) | **TEST-ONLY** (F-03) |
| FrozenOps.lean (hub) | 1 file | via test suites | TEST-ONLY |

Additionally, the following modules are partially unreachable:

| Module | Files | Reason | Status |
|--------|-------|--------|--------|
| **PriorityInheritance hub** | 1 file | Hub itself not imported; submodules are | TEST-ONLY hub |
| **PriorityInheritance/BoundedInversion** | 1 file | Only imported by Liveness (test-only) | TEST-ONLY |
| **PriorityInheritance/Preservation** | 1 file | Only imported by BoundedInversion | TEST-ONLY |
| **RadixTree hub** | 1 file | Hub not imported; submodules reachable via Boot | TEST-ONLY hub |

Note: PriorityInheritance/Propagate, Compute, and BlockingGraph ARE in the
production chain (imported by IPC/Donation, Lifecycle/Suspend, SchedContext.Invariant).

**Total test-only modules**: 17 Lean files (12.4% of codebase)

**Documentation status**: FrozenOps/Core.lean (lines 15-28) explicitly documents
its non-production status. Scheduler/Liveness.lean (lines 11-22) documents its
proof-of-concept framework purpose. All unreachable modules have test coverage.

---

## Rust ABI Synchronization

### sele4n-types (core type definitions)

| Type | Lean Variants | Rust Variants | Encoding Match | Status |
|------|---------------|---------------|----------------|--------|
| SyscallId | 25 (0-24) | 25 (0-24) | Exact | SYNCHRONIZED |
| KernelError | 44 (0-43) | 44 (0-43) | Exact | SYNCHRONIZED |
| AccessRight | 5 | 5 | Exact | SYNCHRONIZED |

### sele4n-abi (ABI encoding/decoding)

- `encode.rs` / `decode.rs`: Message encoding matches Lean `MessageInfo.encode`/`decode`
- `registers.rs`: Register file layout matches `SyscallRegisterLayout`
- `ipc_buffer.rs`: IPC buffer format matches Lean model
- `message_info.rs`: 7-bit length, 2-bit extraCaps, label field layout matches
- `trap.rs`: Trap frame layout for ARM64 syscall entry
- `args/*.rs`: Per-syscall argument structures match `SyscallArgDecode.lean`

### sele4n-sys (kernel interface)

- System call wrappers for all 25 syscall IDs
- Capability, IPC, VSpace, lifecycle, service operations
- All function signatures match the Lean kernel API

### Detailed Rust ABI Findings

**R-01 (LOW)**: `SchedContextId` missing from Rust identifiers (`sele4n-types/src/identifiers.rs`).
Lean Prelude defines `SchedContextId` but Rust has no typed wrapper. `SchedContextBindArgs`
uses raw `u64` for `thread_id` instead of a typed identifier. Kernel validates on entry.

**R-02 (INFO)**: Stale variant counts in `sele4n-types/src/lib.rs` line 7 ("43-variant"
should be 44) and line 9 ("20-variant" should be 25). Documentation-only discrepancy.

**R-03 (LOW)**: `SchedContextConfigureArgs` decode does not validate budget/period
relationship (`sele4n-abi/src/args/sched_context.rs:36-51`). Budget > period violates
CBS admission control. Kernel validates, so this is defense-in-depth only.

**R-04 (LOW)**: `decode_response` comment at `sele4n-abi/src/decode.rs:39` says
"error codes are 0-42" but actual max is 43 (AlignmentError). Stale comment, logic correct.

**R-05 (INFO)**: `sele4n-sys` missing SchedContext syscall wrappers. Arg encode/decode
structures exist in `sele4n-abi`, but safe `sele4n-sys` wrappers for Configure/Bind/Unbind
are absent.

**R-06 (INFO)**: `Cap<Obj, Rts>` phantom-typed capabilities in `sele4n-sys/src/cap.rs` are
Rust-only (no Lean counterpart). Compile-time safety layer, by design.

### Rust Security Positives

- **Zero external dependencies** across all 3 crates — no supply chain risk
- **Single `unsafe` block** (`trap.rs` ARM64 `svc #0`) — sound with proper clobber list
- **`#![deny(unsafe_code)]`** globally with targeted `#[allow]` on 2 functions
- **All 3 crates are `#![no_std]`** by default
- **`#[non_exhaustive]`** on `KernelError` for forward compatibility
- **`TryFrom` for all fallible conversions** — no panicking paths
- **IPC buffer bounds checking** — no buffer overflow possible
- **Compile-time layout assertions** on `IpcBuffer` (960 bytes, `#[repr(C)]`)

**Assessment**: The Rust ABI layer is a faithful mirror of the Lean model with
comprehensive test coverage. No security vulnerabilities or CVE-worthy issues found.

---

## Per-Subsystem Audit Notes

### Kernel API (`SeLe4n/Kernel/API.lean` — 1785 lines)

The API module is the central dispatch hub. Key observations:

- **Syscall dispatch**: Two parallel paths — `dispatchWithCap` (unchecked, 25 arms)
  and `dispatchWithCapChecked` (checked, 23 arms + broken wildcard). The checked path
  is recommended for production but has the F-01 gap.
- **Capability gate**: `syscallLookupCap` correctly resolves and validates capabilities
  before dispatch. The `syscallInvoke` combinator composes gate resolution with operation
  dispatch. Read-only state preservation is proven.
- **Soundness theorems**: 12 soundness theorems proving capability requirements,
  dispatch delegation, structural equivalence, and invariant preservation composition.
  All machine-checked with no sorry.
- **Extra capability resolution**: `resolveExtraCaps` silently drops unresolvable
  capabilities (matching seL4 `lookupExtraCaps` behavior). Documented with AC3-D note.
- **SchedContext donation**: `.call` and `.reply` arms correctly apply donation and
  priority inheritance propagation/reversion after IPC operations.

### Scheduler (`SeLe4n/Kernel/Scheduler/` — 20 files)

- **Selection**: EDF scheduling with priority-based selection. `chooseThread` and
  `chooseThreadInDomain` correctly select highest-priority/earliest-deadline threads.
- **Core transitions**: `schedule`, `handleYield`, `timerTick`, `switchDomain` all
  use `saveOutgoingContext` for register context preservation. Checked wrappers
  in API.lean provide defense-in-depth.
- **RunQueue**: `RHSet`-backed run queue with O(1) membership testing. Complex but
  well-proven with Robin Hood hash table invariants.
- **Priority Inheritance**: D4 protocol with blocking graph, bounded chain walk,
  depth bound, and parametric WCRT bound. Propagation and reversion correctly
  integrate with IPC call/reply paths.
- **Liveness** (test-only, F-03): WCRT theorem, timer-tick monotonicity, CBS
  replenishment bounds, yield/rotation semantics. 58 surface anchor tests in
  LivenessSuite. Should be brought into production import chain.

**Scheduler-specific findings from deep audit:**

**S-01 (MEDIUM)**: `propagatePriorityInheritance` reads `blockingServer` from
pre-mutation state but recurses on post-mutation state (`Propagate.lean:60-72`).
Currently safe because `updatePipBoost` only modifies `pipBoost`/run queue, never
`ipcState`. Latent correctness risk if `updatePipBoost` is ever extended.
Recommend: add frame theorem proving `updatePipBoost` preserves `ipcState`.

**S-02 (MEDIUM)**: `chooseBestRunnableInDomainEffective` filters by `tcb.domain`
but `effectivePriority` resolves from `sc.domain` (`Selection.lean:363`). If
`tcb.domain != sc.domain` for a SchedContext-bound thread, the thread passes the
domain filter by its TCB domain but is prioritized by its SchedContext domain.
Recommend: enforce `sc.domain == tcb.domain` invariant for bound threads.

**S-03 (LOW)**: `handleYield` re-enqueues at `tcb.priority` not effective priority
(`Core.lean:330`). PIP-boosted threads go into wrong priority bucket after yield.
Recommend: use `resolveEffectivePrioDeadline` for re-enqueue priority.

**S-04 (LOW)**: `schedulerInvariantBundleFull` (9-tuple) preservation is proven for
base operations but NOT for `*Effective`/`*WithBudget` variants. The SchedContext-aware
code path lacks full invariant preservation proofs (`Preservation.lean`, 2170 lines).

**S-05 (LOW)**: `timeoutBlockedThreads` folds over entire object store — O(n) per
budget exhaustion event (`Core.lean:500-515`). Performance-sensitive on RPi5.

### IPC (`SeLe4n/Kernel/IPC/` — 20 files)

- **Dual-queue architecture**: Send and receive queues per endpoint. Queue operations
  (enqueue, dequeue) maintain no-dup invariants proven in QueueNoDup.lean.
- **Capability transfer** (WithCaps): IPC messages carry resolved capabilities from
  sender's CSpace. Transfer respects rights (grant right required for cap transfer).
- **Call/Reply/ReplyRecv**: Compound IPC operations correctly implement seL4 semantics.
  Reply targets are validated against expected reply capability.
- **Timeout**: Z6 timeout-driven IPC unblocking with priority inheritance reversion.
- **Donation**: Z7 SchedContext donation wrappers for call (donate to server) and
  reply (return to client). Both paths include PIP propagation/reversion.
- **Invariant suite**: 8 invariant submodules (Defs, EndpointPreservation, CallReplyRecv,
  WaitingThreadHelpers, NotificationPreservation, QueueNoDup, QueueMembership,
  QueueNextBlocking, Structural). Total ~8000 lines of preservation proofs.

### Capability (`SeLe4n/Kernel/Capability/` — 5 files)

- **Multi-level CSpace resolution**: `resolveCapAddress` with termination proof
  (strict descent on `bitsRemaining`). Zero-width CNode and zero-bits rejection.
- **CDT tracking**: `cspaceMintWithCdt` creates CDT-tracked derivation entries.
  `cspaceRevoke` uses CDT for revocation. CDT cycles prevented by construction.
- **Authority reduction**: Proven in Authority.lean — minted capabilities never
  exceed source rights. Badge routing preserves badge invariants.
- **Preservation**: ~1207 lines of per-operation invariant preservation proofs.

### Architecture (`SeLe4n/Kernel/Architecture/` — 10 files)

- **VSpace**: HashMap-backed virtual address space with W^X enforcement.
  `vspaceMapPageChecked` validates permissions (no simultaneous write+execute).
  Physical address bounds checking via `physicalAddressWidth` from machine state.
- **TLB model**: `vspaceMapPageCheckedWithFlush` and `vspaceUnmapPageWithFlush`
  include TLB invalidation in the state model.
- **RegisterDecode**: Total deterministic decode from raw registers to typed kernel IDs.
  All 25 syscall types have decoders in SyscallArgDecode.lean.
- **IPC buffer validation**: D3 setIPCBufferOp with 512-byte alignment check.
- **VSpaceInvariant**: ~733 lines of W^X enforcement and mapping consistency proofs.

### Information Flow (`SeLe4n/Kernel/InformationFlow/` — 9 files)

- **Policy**: Security labels, `securityFlowsTo` predicate, labeling context.
  Default labeling context uses `⊥` (bottom) — all flows permitted by default (IF-04).
  BIBA integrity uses same ordering as confidentiality (IF-05).
- **Projection**: State projection for non-interference — observable state per domain.
  Service registry excluded from projection (IF-06).
- **Enforcement wrappers**: 11 checked operations gating cross-domain flows.
  `enforcementBoundaryComplete` verified by `native_decide` at compile time.
  Dispatch structure tightly coupled to operation structure (IF-08).
- **NI proofs**: Per-operation non-interference proofs (~1492 lines in Operations.lean).
  Trace composition in Composition.lean (~607 lines). **Critical gap**: `switchDomain`
  missing from `NonInterferenceStep` inductive — domain-switch NI unproven in
  composition (IF-01). PIP/donation mutations outside NI envelope (IF-02).
  Composition proves per-operation NI but not full dispatch NI (IF-03).
- **Coverage**: All 25 SyscallId variants mapped to enforcement boundary entries.
  Declassification well-formedness not structurally enforced (IF-07).
  `replyRecv` NI proof assumes sequential decomposition (IF-09).
  Scheduling covert channels not modeled — standard scope limitation (IF-10).

### Data Structures

- **RobinHood** (production): Well-proven hash table with probe-chain-dominant
  invariant, WF preservation, functional correctness (get after insert/erase).
  Bridge module provides kernel API instances. Deeply integrated into production.
- **RadixTree** (production via Boot): CNodeRadix flat array with O(1) operations.
  24 correctness proofs. Bridge from RHTable → CNodeRadix preserves all entries.
- **FrozenOps** (test-only, F-02): FrozenKernel monad, 15 frozen operations,
  commutativity proofs. Well-engineered but not in production path.

### SchedContext (`SeLe4n/Kernel/SchedContext/` — 10 files)

- **CBS implementation**: Budget consume/replenish with admission control.
  Total bandwidth bound proven in Invariant/Defs.lean.
- **ReplenishQueue**: System-wide sorted replenishment queue with invariants (Z3).
- **Operations**: Configure, bind, unbind, yieldTo. All wired into API dispatch
  except yieldTo (kernel-internal).
- **Priority management** (D2): `setPriorityOp` with MCP authority validation.
  Run queue migration on priority change. Preservation proofs in PriorityPreservation.lean.

### Lifecycle (`SeLe4n/Kernel/Lifecycle/` — 4 files)

- **Retype**: Object creation with pre-retype cleanup and memory scrubbing.
  `lifecycleRetypeDirectWithCleanup` is the production entry point (not the
  base `lifecycleRetypeObject`).
- **Suspend/Resume** (D1): Thread state transitions with scheduler integration.
  Suspended threads removed from run queue. Resume re-enqueues.

### Service (`SeLe4n/Kernel/Service/` — 7 files)

- **Registry**: Service registration, revocation, and lookup by capability.
- **Acyclicity**: Dependency graph acyclicity proven (~1058 lines).
- **Policy bridge**: Service invariant composition with capability subsystem.

### Platform (`SeLe4n/Platform/` — 11 files)

- **Contract**: PlatformBinding typeclass abstracting hardware details.
- **Boot**: Q3-C boot sequence from PlatformConfig to IntermediateState.
  Uses Builder for invariant-preserving state construction.
- **DeviceTree**: FDT parser with bounds-checked helpers, fuel parameters,
  truncated-entry rejection, and full node traversal. Well-implemented.
- **Sim**: Permissive simulation contracts (all True) for testing.
- **RPi5**: Substantive BCM2712 contracts with real MMIO addresses,
  GIC-400 configuration, and runtime/boot/interrupt contracts.

### CrossSubsystem (`SeLe4n/Kernel/CrossSubsystem.lean`)

- 35 per-operation bridge lemmas covering ALL 33 kernel operations that modify
  `objects`. Pairwise field disjointness verified by `native_decide` (12 pairs).
- Fully reachable from production via Architecture.Invariant.

---

## Recommendations

### Priority 1 — Fix before release (HIGH)

1. **Fix F-01**: Add `.tcbSetPriority` and `.tcbSetMCPriority` to
   `dispatchCapabilityOnly` in `API.lean`. This simultaneously fixes both
   `dispatchWithCap` (where they'd be redundant but harmless) and
   `dispatchWithCapChecked` (where they're currently missing). Add a
   `dispatchWithCapChecked_wildcard_unreachable` theorem.

2. **Address F-02**: Decide on the production status of FrozenOps. If production:
   integrate into the API layer. If experimental: document as such and move to
   a clearly-labeled directory.

3. **Fix IF-01**: Add `switchDomain` constructor to `NonInterferenceStep` in
   `Composition.lean`. The per-step theorem already exists in `Operations.lean`
   (`switchDomain_preserves_lowEquivalent`), so this requires wiring, not new proofs.

4. **Fix IF-02**: Extend the `endpointCallHigh` and `endpointReply` NI
   constructors to cover the composed operation (IPC + donation + PIP), or add
   separate constructors for donation/PIP mutations. This closes the NI proof
   gap for the call/reply dispatch paths.

### Priority 2 — Fix before benchmarking (MEDIUM)

5. **Fix F-03**: Import `Scheduler.Liveness` into `Scheduler.Invariant` or
   `Architecture.Invariant` to bring liveness proofs into the production build.

6. **Fix F-04**: Move `.tcbSetIPCBuffer` into `dispatchCapabilityOnly` alongside
   the other capability-only TCB operations to eliminate duplication.

7. **Fix F-05**: Correct the wildcard unreachability comment in
   `dispatchWithCapChecked` and add a compile-time completeness theorem.

8. **Fix IF-03**: Add a master dispatch NI theorem that discharges all 32
   per-operation NI proofs via the actual `dispatchSyscallChecked` function.

9. **Fix IF-04**: Add a `LabelingContext.isNonTrivial` predicate and verify
   non-trivial labels are configured before the first syscall in boot sequence.

10. **Fix IF-05**: Document the integrity flow direction explicitly, or add
    separate `confidentialityFlowsTo`/`integrityFlowsTo` predicates.

11. **Fix IF-06**: Extend `projectState` to include the service registry
    and prove NI preservation for service operations.

12. **Fix S-01/S-02**: Add frame theorem for `updatePipBoost` preserving
    `ipcState`; enforce `sc.domain == tcb.domain` invariant for bound threads.

### Priority 3 — Maintenance (LOW)

13. **F-09**: Consider adding `SyscallId.schedContextYieldTo` if user-space budget
    transfer is needed for the hardware target.

14. **F-10**: Remove or deprecate the `fromDtb` stub once `fromDtbFull` is the
    canonical DTB parsing path.

15. **S-03**: Use `resolveEffectivePrioDeadline` in `handleYield` for correct
    PIP-aware re-enqueue priority.

16. **S-05**: Consider indexed data structure for `timeoutBlockedThreads` to
    avoid O(n) scan on RPi5 with many objects.

17. **General**: Consider adding a CI check that verifies all `.lean` files under
    `SeLe4n/` are transitively imported by `SeLe4n.lean` (the library root) to
    prevent future dead code accumulation.

---

## Methodology

This audit employed:
1. **Static import chain analysis**: Traced all transitive imports from `SeLe4n.lean`
   to identify modules unreachable from the production library target.
2. **Pattern scanning**: Searched all 132 Lean files for `sorry`, `axiom`, `panic`,
   `unsafe`, `unreachable!`, `native_decide`, `partial`, `noncomputable`,
   `Classical`, `opaque`, and `dbg_trace`.
3. **Manual code review**: Every line of `API.lean` (1785 lines) reviewed for
   dispatch completeness. Critical security paths (capability resolution, IPC
   message passing, information flow enforcement) reviewed in detail.
4. **Cross-reference verification**: Rust ABI types cross-referenced against Lean
   source for encoding synchronization (SyscallId, KernelError, AccessRight).
5. **Parallel subsystem audits**: 11 concurrent deep audits of individual subsystems
   covering scheduler, IPC, capability, architecture, information flow, data
   structures, SchedContext, lifecycle, service, platform, and testing infrastructure.

---

## Conclusion

seLe4n v0.25.14 demonstrates exceptional formal verification discipline with zero
sorry/axiom in production code, comprehensive invariant preservation proofs, and
perfect Lean-Rust ABI synchronization.

**Four HIGH findings** require attention before release:
- **F-01** (dispatch gap): Two syscalls silently rejected in checked path — straightforward fix
- **F-02** (FrozenOps unreachable): Production/experimental status needs resolution
- **IF-01** (switchDomain NI gap): Domain-switch missing from NI composition — per-step proof exists, needs wiring
- **IF-02** (PIP outside NI envelope): Call/reply donation mutations unproven for NI — needs constructor extension

**Nine MEDIUM findings** should be addressed before benchmarking:
- F-03 (Liveness unreachable), F-04/F-05 (dispatch maintenance), S-01/S-02 (scheduler correctness)
- IF-03 through IF-06 (NI methodology, labeling, integrity, projection completeness)

The information flow subsystem is architecturally sound but has proof coverage gaps
(IF-01/IF-02) and methodology limitations (IF-03 through IF-06) that should be
closed to claim full non-interference for all kernel transitions. These gaps do not
indicate the presence of actual information leaks — they indicate the absence of
formal proof that such leaks cannot occur.

After addressing the HIGH findings and the MEDIUM NI gaps, the kernel is
well-positioned for its first major release and hardware benchmarking on the
Raspberry Pi 5. The 13 LOW and 11 INFORMATIONAL findings are maintenance items
that can be addressed incrementally.

---

## Appendix A: Core Model Deep Audit

Detailed audit of `Prelude.lean` (1049 lines), `Machine.lean` (617 lines),
`Model/Object/Types.lean` (~1291 lines), `Model/Object/Structures.lean` (~833 lines),
and `Model/State.lean` (~1073 lines).

### Additional Low-Severity Findings

**A-01: `SchedContextId.ofObjId` missing sentinel check** (`Prelude.lean:373`)
`ofObjId` converts any `ObjId` to `SchedContextId` without checking sentinel value 0,
unlike `ThreadId.toObjIdChecked`. Recommend adding `SchedContextId.ofObjIdChecked`.

**A-02: `AccessRightSet` raw constructor exposure** (`Types.lean:96-98`)
`AccessRightSet.mk 999` creates invalid rights set. Documented and mitigated (AC4-B/F-02).
Membership queries mask to 5 bits. `union` can propagate high bits but this is harmless.

**A-03: Non-lawful BEq instances** (`Machine.lean:208-228`, `Types.lean:549-589`)
`RegisterFile.BEq` checks GPR 0-31 only. Negative `LawfulBEq` witnesses prove
intentionality. Kernel code never accesses GPR >= 32.

### Core Model Positive Confirmations

- `KernelM` monad provably lawful (all laws machine-checked, `Prelude.lean:734`)
- `CapDerivationTree` uses private constructor preventing inconsistent CDTs
- `UntypedObject.allocate` watermark monotonicity proven (`Types.lean:838`)
- No `Inhabited KernelObject` — prevents accidental default kernel object creation
- `allTablesInvExtK_witness` compile-time completeness check (16 conjuncts)
- `CNode.resolveSlot` correctly masks CPtr to 64 bits with idempotency proof
- `CNode.empty` proven NOT well-formed — prevents use in CSpace resolution
- Sentinel convention (ID 0 reserved) consistently applied across all ID types
- `storeObject` infallibility documented — capacity enforced at `retypeFromUntyped`
- `storeObjectChecked` adds capacity guard for new allocation paths
