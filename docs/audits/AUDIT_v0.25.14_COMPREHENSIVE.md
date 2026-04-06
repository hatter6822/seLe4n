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

**Critical findings**: 4 HIGH, 23 MEDIUM, 38 LOW, 25 INFORMATIONAL (90 total)

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
| SC-01 | MEDIUM | SchedContext/Invariant/Defs | CBS bandwidth bound 8x weaker than claimed CBS guarantee |
| SC-02 | MEDIUM | SchedContext/Budget | Admission control integer truncation allows marginal over-admission |
| SC-03 | MEDIUM | SchedContext/Operations | `schedContextConfigure` resets budget but not replenishment queue entries |
| SC-04 | MEDIUM | Lifecycle/Suspend | `cancelDonation` for `.bound` does not set `isActive := false` |
| SC-05 | MEDIUM | Lifecycle/Suspend | `resumeThread` preemption check uses TCB priority, not effective priority |
| SC-06 | LOW | SchedContext/Types | `Budget.refill` has inverted semantics — dead code but misleading if used |
| SC-07 | LOW | Lifecycle/Suspend | `cancelDonation` for `.bound` does not remove SchedContext from replenish queue |
| SC-08 | LOW | SchedContext/ReplenishQueue | `popDue` size calculation trusts cached size, fragile under invariant violation |
| SC-09 | LOW | SchedContext/Operations | `schedContextBind` run queue re-insertion reads pre-update SchedContext |
| SC-10 | INFO | SchedContext/Budget | No double-replenishment risk — CBS cycle correctly sequenced |
| SC-11 | INFO | SchedContext/PriorityManagement | `setPriorityOp` cannot bypass MCP authority — machine-checked |
| T-01 | LOW | Testing/MainTraceHarness | Trace harness focuses on happy-path codecs; exception paths underrepresented |
| CAP-01 | MEDIUM | Capability/Operations | CPtr masking inconsistency between `resolveCapAddress` and `resolveSlot` |
| CAP-02 | MEDIUM | Capability/Invariant/Preservation | CDT acyclicity externalized as hypothesis — not machine-checked end-to-end |
| CAP-03 | LOW | Capability/Operations | No `cspaceRevoke` syscall ID — revocation not exposed to userspace |
| CAP-04 | LOW | Capability/Operations | `cspaceMove`/`cspaceCopy` same-slot returns error instead of no-op |
| CAP-05 | INFO | Capability subsystem | No capability forgery path — `capAttenuates` proven for all derivation paths |
| CAP-06 | INFO | Capability/Operations | No dead code — all operations reachable from API dispatch or internal composition |
| ARCH-01 | LOW | Architecture/VSpace | No physical address aliasing protection — consistent with seL4 design |
| ARCH-02 | LOW | Architecture/VSpace | `vspaceMapPageCheckedWithFlush` uses model-default PA bound, not platform bound |
| ARCH-03 | LOW | Architecture/SyscallArgDecode | `decodeVSpaceUnmapArgs` does not validate VAddr canonical (asymmetry with map) |
| ARCH-04 | INFO | Architecture/VSpace | W^X enforcement correct at 3 layers (decode, operation, invariant) |
| ARCH-05 | INFO | Architecture/TlbModel | TLB model sound — per-ASID flush, cross-ASID isolation, frame lemmas proven |
| ARCH-06 | INFO | Architecture/VSpaceBackend | VSpaceBackend typeclass unused — intentional H3 preparation |
| SVC-01 | MEDIUM | Service/Operations | `serviceHasPathTo` conflates self-reachability with self-loops — bridged by declarative definition |
| SVC-02 | MEDIUM | Service/Registry | `lookupServiceByCap` first-match depends on RHTable insertion order |
| PLT-01 | MEDIUM | Platform/Boot | Boot-to-runtime invariant bridge proven only for empty config |
| PLT-02 | MEDIUM | Kernel/CrossSubsystem | `collectQueueMembers` fuel exhaustion silently truncates queue |
| SVC-03 | LOW | Service/Invariant/Acyclicity | `serviceCountBounded` existential — no executable runtime check |
| SVC-04 | LOW | Kernel/CrossSubsystem | `registryInterfaceValid` not in `crossSubsystemInvariant` |
| PLT-03 | LOW | Platform/Sim/Contract | Simulation PA width (52) diverges from RPi5 (44) |
| PLT-04 | LOW | Platform/DeviceTree | `parseFdtNodes` fuel exhaustion returns partial results, not error |
| PLT-05 | LOW | Platform/Boot | `bootFromPlatform` (unchecked) silently overwrites duplicate objects |
| PLT-06 | LOW | Platform/RPi5/BootContract | Boot contract validates empty state, not hardware-derived state |
| PLT-07 | INFO | Kernel/CrossSubsystem | 8-predicate invariant with 28 pairwise analyses — exemplary |
| PLT-08 | INFO | Service/Invariant/Acyclicity | Acyclicity proof is genuine, not vacuous — fixed original BFS issue |
| IPC-01 | MEDIUM | IPC/Operations/Timeout | Timeout detection uses sentinel register value — collision risk with message data |
| IPC-02 | MEDIUM | IPC/DualQueue/Core | `endpointQueueRemove` silently absorbs queue link lookup failures |
| IPC-03 | LOW | IPC/Operations/Endpoint | Notification wait uses LIFO instead of FIFO — potential waiter starvation |
| T-06 | MEDIUM | Testing | PriorityInheritanceSuite compiled but never executed in any test tier |
| T-07 | LOW | Testing | SuspendResume/Priority/IpcBuffer suites use unchecked `builder.build` |
| T-02 | INFO | Testing/InvariantChecks | Runtime invariant checks are boolean predicates, not proofs — by design |
| T-03 | INFO | IPC subsystem | Deep audit: no security or correctness issues found across all 20 files |
| T-04 | INFO | Lifecycle subsystem | Deep audit: retype cleanup, suspend/resume, all invariants verified correct |
| T-05 | INFO | Service subsystem | Deep audit: capability-mediated registry, acyclicity proven, dependency cleanup sound |

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

### SC-01: CBS bandwidth bound 8x weaker than claimed CBS guarantee

**Location**: `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, lines 441-470
**Impact**: Bandwidth bound theorem proves 8*budget per window, not budget per period
**Severity**: MEDIUM

**Description**: The `cbs_single_period_bound` and `cbs_bandwidth_bounded` theorems
prove `totalConsumed <= maxReplenishments * budget` (i.e., 8 * budget with the default
maxReplenishments = 8). The true CBS guarantee is `budget` per period. While per-object
`budgetWithinBounds` prevents actual over-consumption at any single tick, the proven
bound is weaker than the CBS specification claims.

The admission control runtime check (`admissionCheck`) correctly sums utilization
fractions, but its correctness is not formally connected to the bandwidth bound theorems.

**Remediation**: Either tighten the bandwidth bound proof to `budget` per period, or
document the 8x gap and connect `admissionCheck` to the proven bound.

---

### SC-02: Admission control integer truncation allows marginal over-admission

**Location**: `SeLe4n/Kernel/SchedContext/Budget.lean`, lines 206-218
**Impact**: With 64 active SchedContexts, up to 6.4% over-admission possible
**Severity**: MEDIUM

**Description**: `admissionCheck` uses per-mille integer arithmetic
(`budget * 1000 / period`) which truncates down. Per-context error is at most 1 per-mille.
With n active contexts, aggregate error is at most n per-mille. For 64 SchedContexts,
total utilization could exceed 100% by up to 6.4%, causing deadline misses for all
contexts when total demand exceeds capacity.

The code comments note this is acceptable because `budgetWithinBounds` prevents
per-object overrun. This is correct for isolation but not for aggregate schedulability.

**Remediation**: Document as a known precision limit. Consider whether RPi5 workloads
could realistically hit 64+ active SchedContexts.

---

### SC-03: `schedContextConfigure` resets budget but not replenishment queue

**Location**: `SeLe4n/Kernel/SchedContext/Operations.lean`, lines 98-106
**Impact**: Stale replenishment entries may transiently violate `replenishmentAmountsBounded`
**Severity**: MEDIUM

**Description**: When reconfiguring a SchedContext, `budgetRemaining` is set to the new
budget but the `replenishments` list is not cleared. Old entries reference the previous
budget/period. If the new budget is **smaller** than the old, old entries may have
`amount > new_budget`, violating `replenishmentAmountsBounded` until those entries are
processed. The `min` in `applyRefill` caps actual refill to budget, preventing overrun,
but the invariant is transiently broken.

**Remediation**: Clear or rewrite the replenishment list during `schedContextConfigure`,
or prove that the transient invariant violation is harmless.

---

### SC-04: `cancelDonation` for `.bound` does not set `isActive := false`

**Location**: `SeLe4n/Kernel/Lifecycle/Suspend.lean`, lines 96-108
**Impact**: Orphaned SchedContext remains `isActive` with no bound thread
**Severity**: MEDIUM

**Description**: When `cancelDonation` processes a `.bound` SchedContext, it clears
`boundThread` to `none` but does not set `isActive := false`. Compare with
`schedContextUnbind` (Operations.lean:191) which correctly sets both. A SchedContext
with `isActive = true` but `boundThread = none` satisfies `replenishQueueConsistent`
(which checks `isActive`) while having no bound thread — replenishments are processed
for a SchedContext that cannot schedule anyone.

**Remediation**: Set `isActive := false` in `cancelDonation` for the `.bound` case,
matching `schedContextUnbind` behavior.

---

### SC-05: `resumeThread` preemption check uses TCB priority, not effective priority

**Location**: `SeLe4n/Kernel/Lifecycle/Suspend.lean`, lines 207-211
**Impact**: Missed preemptions when current thread's effective priority is SchedContext-derived
**Severity**: MEDIUM

**Description**: The preemption check at line 210 compares `tcb'.priority.val > curTcb.priority.val`.
If the current thread's effective priority is derived from a SchedContext (not its TCB
priority field), this comparison uses the wrong value. The `getCurrentPriority` helper
from `PriorityManagement.lean` resolves this correctly but is not used here.

This mirrors S-03 (`handleYield` uses raw priority) — the pattern of using `tcb.priority`
instead of effective priority appears in multiple locations.

**Remediation**: Use `resolveEffectivePrioDeadline` or `getCurrentPriority` for the
preemption comparison.

---

### CAP-01: CPtr masking inconsistency between `resolveCapAddress` and `resolveSlot`

**Location**: `SeLe4n/Kernel/Capability/Operations.lean`, line 96 vs
`SeLe4n/Model/Object/Structures.lean`, lines 500-501
**Impact**: Model-level inconsistency in CPtr bit extraction between single-level and multi-level paths
**Severity**: MEDIUM

**Description**: `resolveCapAddress` uses `addr.toNat` directly without masking to
64-bit word width:
```
let shiftedAddr := addr.toNat >>> (bitsRemaining - consumed)
```

In contrast, `CNode.resolveSlot` explicitly masks (S4-C):
```
let maskedAddr := cptr.toNat % SeLe4n.machineWordMax
```

Since Lean `Nat` is unbounded, if a `CPtr` value exceeds `2^64`, the two functions
will compute different guard/slot extractions for the same address. This creates a
model-level inconsistency where `resolveCapAddress` (multi-level walk) and
`resolveSlot` (single-level) could resolve to different slots.

In practice, CPtr values come from register decode which bounds them to word width,
but the model does not enforce this precondition on `resolveCapAddress`.

**Remediation**: Add `% SeLe4n.machineWordMax` masking at the entry of
`resolveCapAddress`, or prove that all CPtr values reaching the function are
bounded to 64 bits.

---

### CAP-02: CDT acyclicity externalized as post-state hypothesis

**Location**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`, lines 15-48, 470-513
**Impact**: CDT cycle-freedom not machine-checked end-to-end
**Severity**: MEDIUM

**Description**: CDT-modifying operations (`cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`)
take `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as a post-state hypothesis
(documented U4-L/U-M26) rather than proving acyclicity preservation. The preservation
proofs are conditional — they assume the CDT remains acyclic after `addEdge`.

There is no proven `addEdge_preserves_acyclicity` lemma with a reachability
precondition. If a cycle were to form, `descendantsOf` (which uses
fuel = `edges.length`) would terminate but potentially miss descendants, making
`cspaceRevokeCdt` incomplete — some derived capabilities would survive revocation.

**Remediation**: Either prove `addEdge_preserves_acyclicity` with an appropriate
reachability precondition (source not reachable from destination), or add a runtime
`addEdgeWouldBeSafe` check in CDT-modifying operations.

---

### SVC-01: `serviceHasPathTo` conflates self-reachability with self-loops

**Location**: `SeLe4n/Kernel/Service/Operations.lean`, line 149
**Impact**: Executable traversal semantics are asymmetric with declarative definition
**Severity**: MEDIUM

`serviceHasPathTo.go` checks `if node = target then true` before visited status.
When `src = target`, returns `true` immediately, conflating "A reaches A" with "A has
a self-loop." The declarative definition (`serviceDependencyAcyclic` via
`serviceNontrivialPath`) is correct. The mismatch is bridged by
`bfs_complete_for_nontrivialPath` requiring `hNe : a != b`. Not a soundness issue,
but makes the executable check harder to reason about independently.

---

### SVC-02: `lookupServiceByCap` first-match depends on hash table insertion order

**Location**: `SeLe4n/Kernel/Service/Registry.lean`, lines 89-100
**Impact**: Multiple services can register the same endpoint with nondeterministic lookup
**Severity**: MEDIUM

Uses `RHTable.fold` for first-match. If two services share the same endpoint, the
result depends on insertion order into the hash table. No `registryEndpointUnique`
invariant prevents this. Documented at lines 83-88 but not enforced.

**Remediation**: Add a `registryEndpointUnique` invariant (one service per endpoint)
or document the intentional multi-registration semantics.

---

### PLT-01: Boot-to-runtime invariant bridge proven only for empty config

**Location**: `SeLe4n/Platform/Boot.lean`, lines 286-345
**Impact**: Non-empty hardware boot lacks formal invariant guarantee
**Severity**: MEDIUM

`bootToRuntime_invariantBridge_empty` proves the 10-component `proofLayerInvariantBundle`
holds for the empty config only. For general configs (non-empty IRQ tables, objects),
the full bundle is not proven to hold after boot. Documented and deferred to WS-V.
This means any actual hardware boot with objects loaded will lack formal guarantees
that the initial state satisfies the full runtime invariant bundle.

**Remediation**: Prove `bootToRuntime_invariantBridge` for arbitrary well-formed
`PlatformConfig`, or add runtime invariant validation after boot.

---

### PLT-02: `collectQueueMembers` fuel exhaustion silently truncates

**Location**: `SeLe4n/Kernel/CrossSubsystem.lean`, lines 50-60
**Impact**: Stale endpoint queue references could be hidden by truncation
**Severity**: MEDIUM

When fuel is exhausted, `collectQueueMembers` returns `[]`, silently truncating the
remaining queue. This means `noStaleEndpointQueueReferences` could pass even if
interior queue members reference deleted TCBs, because they were never checked.
The fuel-sufficiency argument relies on `tcbQueueChainAcyclic` but this connection
is not formalized (TPI-DOC deferred at line 96-98).

**Remediation**: Formalize the fuel-sufficiency argument by proving that fuel ≥
queue length under the acyclicity invariant, or return an error on fuel exhaustion.

---

### IPC-01: Timeout detection uses sentinel register value — collision risk

**Location**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, lines 23, 111
**Impact**: False timeout detection if legitimate IPC message contains sentinel value
**Severity**: MEDIUM

`timeoutAwareReceive` detects prior timeouts by checking `gpr x0 = timeoutErrorCode
(0xFFFFFFFF) AND ipcState = .ready`. No mechanism prevents a sender from setting this
value in message register x0. A thread that received a legitimate message containing
`0xFFFFFFFF` could be misidentified as timed-out.

In practice, the IPC message is delivered via `pendingMessage` and `gpr x0` is only
written by `timeoutThread`, but the formal model does not prove that `gpr x0` cannot
contain the sentinel through non-timeout paths.

**Remediation**: Add a dedicated `wasTimedOut : Bool` field to TCB, or prove an
invariant that `gpr x0 = timeoutErrorCode` implies the thread was actually timed out.

---

### IPC-02: `endpointQueueRemove` silently absorbs queue link lookup failures

**Location**: `SeLe4n/Kernel/IPC/DualQueue/Core.lean`, lines 493-507
**Impact**: Queue corruption masked by defensive fallback
**Severity**: MEDIUM

When predecessor/successor TCB lookup fails during mid-queue removal, the fallback is
a no-op (`objs`). If this fallback IS reached (e.g., queue corruption from a bug
elsewhere), the predecessor's `queueNext` still points to the removed thread — a
dangling pointer. The `tcbQueueLinkIntegrity` invariant theoretically prevents this,
but the defensive fallback masks the symptom rather than failing loudly.

**Remediation**: Return an error on the fallback path, or prove formally that the
branch is unreachable under `dualQueueSystemInvariant`.

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

### T-01: Test harness focuses on happy-path codecs

**Location**: `SeLe4n/Testing/MainTraceHarness.lean` (~3114 lines)
**Severity**: LOW

The main trace harness and Rust cross-validation vectors (XVAL-001 through XVAL-005)
cover codec roundtrips and basic kernel scenarios. Exception paths (OOM during retype,
register corruption, timer underflow, capability exhaustion) are underrepresented in
the trace harness, though many are covered by individual test suites (NegativeStateSuite,
DecodingSuite). The `InvariantChecks.lean` runtime checks are boolean predicates, not
proofs — this is appropriate for runtime testing but should not be conflated with the
formal proof surface.

---

### T-06: PriorityInheritanceSuite compiled but never executed

**Location**: `tests/PriorityInheritanceSuite.lean`, `lakefile.toml` line 77
**Severity**: MEDIUM (promoted from testing subsystem)

`priority_inheritance_suite` is registered in `lakefile.toml` as a lean_exe target
and compiles successfully, but it is **not referenced in any test script**
(`test_tier2_negative.sh`, `test_smoke.sh`, `test_full.sh`, or `test_nightly.sh`).
The suite tests `propagatePriorityInheritance`/`revertPriorityInheritance` used in
the `.call`/`.reply` dispatch arms — critical production code paths.

**Remediation**: Add `lake exe priority_inheritance_suite` to `test_tier2_negative.sh`
or `test_full.sh`.

---

### T-07: Some test suites use unchecked `builder.build`

**Location**: `tests/SuspendResumeSuite.lean`, `PriorityManagementSuite.lean`,
`IpcBufferSuite.lean`, `PriorityInheritanceSuite.lean`
**Severity**: LOW

These suites use `builder.build` instead of `buildChecked`, constructing states
without validation. Could create unrealistic test states that mask bugs. Partially
by design (edge-case states like already-inactive threads), but reduces confidence
that test scenarios represent production-reachable states.

---

### SC-06: `Budget.refill` has inverted semantics — dead code

**Location**: `SeLe4n/Kernel/SchedContext/Types.lean`, line 49
**Severity**: LOW

`Budget.refill` is defined as `min b.val ceiling.val`, which caps down to the ceiling
rather than refilling up. The name suggests additive refill semantics but the
implementation only decreases or maintains the budget. This function is **unused** —
the actual refill logic is in `applyRefill` (Budget.lean:136). If any future code
calls `Budget.refill` expecting refill semantics, it would silently cap the budget.

**Remediation**: Delete `Budget.refill` or rename to `Budget.cap`.

---

### SC-07: `cancelDonation` for `.bound` does not remove from replenish queue

**Location**: `SeLe4n/Kernel/Lifecycle/Suspend.lean`, lines 96-108
**Severity**: LOW

Unlike `schedContextUnbind` (which calls `ReplenishQueue.remove`), `cancelDonation`
for the `.bound` case does not remove the SchedContext from the system replenish queue.
After unbinding, replenishments are processed for a SchedContext with no bound thread —
a harmless no-op but wasted work.

---

### SC-08: `popDue` size calculation trusts cached size

**Location**: `SeLe4n/Kernel/SchedContext/ReplenishQueue.lean`, line 110
**Severity**: LOW

`popDue` computes `size := rq.size - due.length` using Nat subtraction (saturates at 0).
If `replenishQueueSizeConsistent` is violated, size could underflow to 0 while entries
remain. Compare with `remove` (line 121) which recomputes `size := filtered.length`.
Safe under invariants but fragile if preconditions are weakened.

---

### SC-09: `schedContextBind` reads pre-update SchedContext for run queue insertion

**Location**: `SeLe4n/Kernel/SchedContext/Operations.lean`, lines 146-149
**Severity**: LOW

Run queue re-insertion uses `sc.priority` from the pre-update SchedContext. Since bind
does not change priority, this is currently correct. Pattern could become a bug if future
changes to bind modify priority. Preservation theorem confirms current correctness.

---

### CAP-03: No `cspaceRevoke` syscall ID — revocation not exposed to userspace

**Location**: `SeLe4n/Model/Object/Types.lean` (SyscallId), `SeLe4n/Kernel/API.lean`
**Severity**: LOW

The `SyscallId` enumeration has no `cspaceRevoke` variant. `cspaceDelete` returns
`.revocationRequired` when CDT children exist (U-H03 guard), but there is no
userspace-accessible syscall to invoke `cspaceRevokeCdt`. This means capabilities
with CDT children become effectively undeletable from userspace. The revocation
infrastructure exists internally but is not yet exposed via syscall. Likely
intentional design-in-progress for the hardware target milestone.

---

### CAP-04: `cspaceMove`/`cspaceCopy` same-slot returns error instead of no-op

**Location**: `SeLe4n/Kernel/Capability/Operations.lean`, lines 677-714
**Severity**: LOW

When `src == dst`, `cspaceMove` and `cspaceCopy` return `.targetSlotOccupied` rather
than succeeding as a no-op. This is safe (the error path produces no state change
by construction of the Kernel monad), but diverges from seL4 where same-slot operations
are no-ops. No security impact — behavioral difference only.

---

### ARCH-01: No physical address aliasing protection in VSpace

**Location**: `SeLe4n/Kernel/Architecture/VSpace.lean`, `VSpaceInvariant.lean`
**Severity**: LOW

The VSpace model enforces `noVirtualOverlap` (each VAddr maps to at most one PAddr)
but has no invariant preventing physical address aliasing — multiple VAddrs mapping
to the same PAddr. This is consistent with seL4's design (PA aliasing is managed by
frame capabilities, not VSpace), but means VSpace-level isolation alone is insufficient
without frame capability invariants. The gap is not explicitly documented.

---

### ARCH-02: `vspaceMapPageCheckedWithFlush` uses model-default PA bound

**Location**: `SeLe4n/Kernel/Architecture/VSpace.lean`, lines 192-197
**Severity**: LOW

Uses `physicalAddressBound` (2^52, ARM64 LPA maximum) not the platform-specific bound.
On RPi5 (44-bit PA), addresses in [2^44, 2^52) would pass this check. The production
dispatch path correctly uses `vspaceMapPageCheckedWithFlushFromState` (which reads
`st.machine.physicalAddressWidth`), so no actual vulnerability exists. Risk is that a
future developer uses the wrong entry point — the docstring misleadingly labels it
as a "production entry point."

---

### ARCH-03: `decodeVSpaceUnmapArgs` does not validate VAddr canonical

**Location**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, lines 228-237
**Severity**: LOW

`decodeVSpaceUnmapArgs` validates ASID range but not VAddr canonical-ness. By contrast,
`decodeVSpaceMapArgs` validates both. A non-canonical VAddr in an unmap request produces
a harmless `.translationFault` error (no mapping exists), so no security impact.
Asymmetry is a code smell.

---

### IPC-03: Notification wait uses LIFO instead of FIFO

**Location**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, lines 389-390, 418
**Severity**: LOW

`notificationWait` prepends waiters (`waiter :: ntfn.waitingThreads`) for O(1) enqueue.
`notificationSignal` wakes the first element. This produces LIFO order — the last
thread to wait is first to be woken. While the seL4 spec doesn't mandate FIFO, most
implementations use FIFO. LIFO can cause starvation of early waiters if new waiters
continuously arrive. Documented design choice.

---

### SVC-03: `serviceCountBounded` — existential with no executable check

**Location**: `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean`, lines 441-443
**Severity**: LOW

`serviceCountBounded` is a `Prop` (existential) with no executable `Bool` validator.
If the invariant were violated via an unverified boot path, there would be no runtime
detection. Inherent to the existential formulation.

---

### SVC-04: `registryInterfaceValid` not in `crossSubsystemInvariant`

**Location**: `SeLe4n/Kernel/CrossSubsystem.lean`, line 242
**Severity**: LOW

`crossSubsystemInvariant` includes `registryEndpointValid` but not `registryInterfaceValid`.
Coverage exists in `serviceLifecycleCapabilityInvariantBundle` (Policy.lean), so the gap
is in the cross-subsystem bundle only.

---

### PLT-03: Simulation PA width (52) diverges from RPi5 (44)

**Location**: `SeLe4n/Platform/Sim/Contract.lean` line 47 vs `RPi5/Board.lean` line 122
**Severity**: LOW

Address-width-sensitive code exercised under simulation may accept addresses that would
be out-of-range on RPi5. By design (simulation is "idealized"), but PA-width-dependent
proofs may not transfer without re-checking.

---

### PLT-04: `parseFdtNodes` fuel exhaustion returns partial results

**Location**: `SeLe4n/Platform/DeviceTree.lean`, line 585
**Severity**: LOW

When fuel reaches 0, returns `some ([], offset)` instead of `none`. A large DTB produces
a truncated tree without error indication. `extractInterruptController` falls back to
zeros, preventing crashes but potentially misconfiguring the platform.

---

### PLT-05: `bootFromPlatform` silently overwrites duplicate objects

**Location**: `SeLe4n/Platform/Boot.lean`, lines 119-128
**Severity**: LOW

Uses `RHTable.insert` with last-wins semantics. Duplicate ObjIds cause silent data loss.
The checked variant `bootFromPlatformChecked` validates uniqueness and is recommended.

---

### PLT-06: RPi5 boot contract validates empty state, not hardware-derived state

**Location**: `SeLe4n/Platform/RPi5/BootContract.lean`, lines 48-54
**Severity**: LOW

Asserts `(default : SystemState).objects.size = 0` — properties of the Lean default,
not of hardware-derived state. Will need re-evaluation when hardware bring-up populates
objects.

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

### CAP-05: No capability forgery path — machine-checked

Capabilities can only be created through `mintDerivedCap` (rights subset proven),
`cspaceInsertSlot` (requires pre-constructed Capability), `lifecycleRetypeObject`
(fresh objects), `cspaceCopy` (unchanged), and `cspaceMutate` (attenuates only).
The `capAttenuates` property is proven for all derivation paths. `syscallInvoke`
gate checks `cap.hasRight gate.requiredRight` before dispatch. Badge override
cannot escalate authority — proven by `mintDerivedCap_rights_attenuated_with_badge_override`
and `cspaceMint_badge_override_safe`.

### CAP-06: No dead code in capability subsystem

All operations defined in Operations.lean are reachable from either the API dispatch
layer, internal composition by other kernel operations, or information-flow enforcement
wrappers.

### SC-10: No double-replenishment risk — CBS cycle correctly sequenced

CBS cycle is: consume → if exhausted, schedule replenishment → process replenishments
→ update deadline. Replenishments scheduled at time T become eligible at T + period,
so they cannot be immediately processed in the same `cbsBudgetCheck` call. Verified
no double-replenishment is possible within a single tick.

### SC-11: `setPriorityOp` cannot bypass MCP authority — machine-checked

`validatePriorityAuthority` checks `targetPriority.val <= callerTcb.maxControlledPriority.val`
before any state mutation. The theorem `setPriority_authority_bounded` formally proves
no bypass is possible. Machine-checked with zero sorry.

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

- **Dual-queue architecture**: Send and receive queues per endpoint. `endpointSendDual`
  correctly handles both cases: dequeues receiver when receiveQ non-empty, enqueues
  sender to sendQ when empty. O(1) operations via intrusive doubly-linked lists.
  `endpointQueuePopHeadFresh` variant avoids stale TCB snapshot footgun.
- **Queue invariants**: K-1 (no self-loops) and K-2 (send/receive head disjointness)
  proven in QueueNoDup.lean. Structural invariants (WS-H5) ensure head/tail
  consistency, doubly-linked integrity, and boundary conditions.
- **Capability transfer** (WithCaps): Grant right checked at top-level boundary
  (`ipcUnwrapCaps`) — without Grant, all caps returned as `.grantDenied`. Per-cap
  transfer via `ipcTransferSingleCap`. Sender retains all transferred capabilities.
- **Timeout**: Z6 timeout correctly captures `maybeBlockingServer` before clearing
  `ipcState`, then calls `revertPriorityInheritance` to recompute server's pipBoost
  from remaining waiters only. Prevents stale priority boost after client timeout.
- **Donation**: Z7 SchedContext donation wrappers for call (donate to server) and
  reply (return to client). Both paths include PIP propagation/reversion.
- **Invariant suite**: 8 invariant submodules (Defs, EndpointPreservation, CallReplyRecv,
  WaitingThreadHelpers, NotificationPreservation, QueueNoDup, QueueMembership,
  QueueNextBlocking, Structural). Total ~8000 lines of preservation proofs.
- **Timeout**: Sentinel value collision risk (IPC-01) — `timeoutErrorCode` in gpr x0
  is convention-based, not invariant-enforced. `endpointQueueRemove` silently absorbs
  lookup failures (IPC-02). Notification wait uses LIFO (IPC-03) — documented choice.
- **Deep audit verdict**: Two MEDIUM findings (sentinel detection, silent fallback).
  Core IPC operations (send, receive, call, reply, replyRecv) verified correct.

### Capability (`SeLe4n/Kernel/Capability/` — 5 files)

- **Multi-level CSpace resolution**: `resolveCapAddress` with termination proof
  (strict descent on `bitsRemaining`). Zero-width CNode and zero-bits rejection.
  **CPtr masking inconsistency** with `resolveSlot` (CAP-01) — model-level gap.
- **CDT tracking**: `cspaceMintWithCdt` creates CDT-tracked derivation entries.
  `cspaceRevoke` uses CDT for revocation. CDT acyclicity externalized as hypothesis
  (CAP-02) — not machine-checked end-to-end. No `cspaceRevoke` syscall (CAP-03).
- **Authority reduction**: Proven in Authority.lean — minted capabilities never
  exceed source rights. Badge routing preserves badge invariants. No capability
  forgery path exists — `capAttenuates` proven for all derivation paths (CAP-05).
- **Preservation**: ~1207 lines of per-operation invariant preservation proofs.
  All operations reachable — no dead code (CAP-06).

### Architecture (`SeLe4n/Kernel/Architecture/` — 10 files)

- **VSpace**: HashMap-backed virtual address space with W^X enforcement at 3 layers:
  decode-time rejection, operation-time re-check, and invariant proof (ARCH-04).
  No PA aliasing protection (ARCH-01) — consistent with seL4. Model-default PA bound
  variant exists but production path uses platform-specific bound (ARCH-02).
- **TLB model**: Conservative and sound — per-ASID flush, cross-ASID isolation,
  frame lemmas all proven (ARCH-05). Atomic composition prevents TOCTOU.
- **RegisterDecode**: Total deterministic decode. Round-trip theorems proven.
  Register bounds validated before access. `isWord64Dec` rejects oversize Nat values.
- **SyscallArgDecode**: 15 decode structures covering all 25 SyscallId variants.
  VAddr canonical validation asymmetry between map and unmap decoders (ARCH-03).
- **IPC buffer validation**: 5-step pipeline (alignment, canonical, TCB lookup,
  mapping, write permission). All 5 checks proven necessary.
- **VSpaceBackend**: Typeclass declared but unused — H3 preparation (ARCH-06).
- **Deep audit verdict**: No security vulnerabilities. 3 LOW findings (PA aliasing
  gap, PA bound variant, decode asymmetry) — all mitigated by defense-in-depth.

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
  Bandwidth bound proven as 8*budget (SC-01) — weaker than CBS spec of budget/period.
  Admission control uses per-mille truncation (SC-02) — up to n/1000 aggregate error.
  No double-replenishment risk (SC-10). `Budget.refill` is dead code (SC-06).
- **ReplenishQueue**: System-wide sorted replenishment queue with invariants (Z3).
  `popDue` trusts cached size (SC-08) — safe under invariants.
- **Operations**: Configure resets budget but not replenishment entries (SC-03).
  Bind reads pre-update SchedContext for run queue insertion (SC-09 — currently safe).
  `yieldTo` is kernel-internal (F-09).
- **Priority management** (D2): `setPriorityOp` with MCP authority validation —
  machine-checked no-bypass (SC-11). Run queue migration on priority change.
- **Lifecycle integration**: `cancelDonation` for `.bound` has two gaps vs
  `schedContextUnbind`: does not set `isActive := false` (SC-04) and does not
  remove from replenish queue (SC-07). `resumeThread` preemption check uses raw
  TCB priority instead of effective priority (SC-05).

### Lifecycle (`SeLe4n/Kernel/Lifecycle/` — 4 files)

- **Retype**: `lifecycleRetypeDirectWithCleanup` orchestrates: (1) `wellFormed`
  validation (T5-D), (2) pre-retype cleanup (dequeue TCB, cancel IPC, detach CNode),
  (3) memory scrubbing (S6-C), (4) `lifecycleRetypeDirect` with authority check.
  Double-retype prevented via `lifecycle.objectTypes` type agreement. Proven theorem
  `lifecycleRetypeWithCleanup_ok_runnable_no_dangling` (H-05) guarantees no dangling
  run queue references after TCB retype.
- **Suspend/Resume** (D1): Suspend sequence: validate not already Inactive → cancel
  IPC blocking → cancel donation → `removeRunnable` → clear pending state → set
  Inactive → trigger reschedule if current. Resume: validate Inactive → set Ready
  → `ensureRunnable` → conditional preemption if resumed > current priority.

### Service (`SeLe4n/Kernel/Service/` — 7 files)

- **Registry**: Capability-mediated registration enforces `.write` right on endpoints
  (R4-C.1). `lookupServiceByCap` first-match depends on RHTable insertion order (SVC-02)
  — no `registryEndpointUnique` invariant. `registryInterfaceValid` not in cross-subsystem
  bundle (SVC-04).
- **Revocation**: `revokeService` erases registration AND cleans dependency graph.
  `removeDependenciesOf` uses `fold` snapshot semantics (correct but subtle).
- **Acyclicity**: Declarative property `serviceDependencyAcyclic` correctly captures
  absence of non-trivial self-loops. Executable `serviceHasPathTo` conflates self-
  reachability with self-loops (SVC-01) — bridged by declarative layer. Proof is
  genuine, not vacuous (PLT-08). `serviceCountBounded` is existential only (SVC-03).
- **Fuel bound**: Graph reachability uses fuel = `objectIndex.length + 256`, with
  HashSet membership ensuring each node visited at most once.

### Platform (`SeLe4n/Platform/` — 11 files)

- **Boot**: Invariant bridge proven only for empty config (PLT-01). Unchecked variant
  silently overwrites duplicate objects (PLT-05). Checked variant validates uniqueness.
  `ObjectEntry` carries proof obligations. Deterministic.
- **DeviceTree**: FDT parser with bounds-checked helpers. `parseFdtNodes` fuel
  exhaustion returns partial results without error (PLT-04). `fromDtb` stub (F-10).
- **Sim**: PA width 52 diverges from RPi5 44 (PLT-03). Three contracts (permissive,
  restrictive, substantive) for distinct testing purposes.
- **RPi5**: Verified-realistic BCM2712 addresses (C-03). Boot contract validates
  empty state only (PLT-06). H3-prep — not yet hardware-validated.
- **CrossSubsystem**: `collectQueueMembers` fuel exhaustion silently truncates
  (PLT-02). 8-predicate invariant with 28 pairwise analyses is exemplary (PLT-07).

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

13. **Fix SC-03**: Clear or rewrite replenishment list during `schedContextConfigure`
    to prevent transient `replenishmentAmountsBounded` violation.

14. **Fix SC-04**: Set `isActive := false` in `cancelDonation` for `.bound` case,
    matching `schedContextUnbind` behavior.

15. **Fix SC-05**: Use `getCurrentPriority` or `resolveEffectivePrioDeadline` in
    `resumeThread` preemption check instead of raw `tcb.priority`.

16. **Fix SC-01/SC-02**: Document CBS bandwidth bound gap (8x vs 1x) and admission
    control truncation as known precision limits. Connect `admissionCheck` to the
    proven bound theorem.

17. **Fix CAP-01**: Add `% SeLe4n.machineWordMax` masking at entry of
    `resolveCapAddress` to match `resolveSlot`, or prove CPtr values are bounded.

18. **Fix CAP-02**: Prove `addEdge_preserves_acyclicity` with reachability
    precondition, or add runtime cycle check in CDT-modifying operations.

19. **Fix PLT-01**: Prove `bootToRuntime_invariantBridge` for well-formed non-empty
    configs, or add runtime invariant validation after boot.

20. **Fix PLT-02**: Formalize fuel-sufficiency for `collectQueueMembers` under
    acyclicity invariant, or return error on fuel exhaustion.

21. **Fix SVC-02**: Add `registryEndpointUnique` invariant or document multi-registration.

### Priority 3 — Maintenance (LOW)

22. **F-09**: Consider adding `SyscallId.schedContextYieldTo` if user-space budget
    transfer is needed for the hardware target.

18. **F-10**: Remove or deprecate the `fromDtb` stub once `fromDtbFull` is the
    canonical DTB parsing path.

19. **S-03/SC-05**: Use `resolveEffectivePrioDeadline` in `handleYield` and
    `resumeThread` for correct PIP-aware re-enqueue/preemption priority.

20. **S-05**: Consider indexed data structure for `timeoutBlockedThreads` to
    avoid O(n) scan on RPi5 with many objects.

21. **SC-06**: Delete dead `Budget.refill` function or rename to `Budget.cap`.

22. **SC-07**: Add `ReplenishQueue.remove` to `cancelDonation` for `.bound` case.

23. **General**: Consider adding a CI check that verifies all `.lean` files under
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

**Twenty-three MEDIUM findings** should be addressed before benchmarking:
- F-03 (Liveness unreachable), F-04/F-05 (dispatch maintenance), S-01/S-02 (scheduler correctness)
- IF-03 through IF-06 (NI methodology, labeling, integrity, projection completeness)
- SC-01/SC-02 (CBS bandwidth bound gap, admission control truncation)
- SC-03 (stale replenishment entries after reconfigure)
- SC-04/SC-05 (`cancelDonation` incomplete vs `schedContextUnbind`, resume priority mismatch)
- CAP-01 (CPtr masking inconsistency), CAP-02 (CDT acyclicity hypothesis gap)
- SVC-01/SVC-02 (service traversal semantics, lookup ordering)
- PLT-01/PLT-02 (boot invariant bridge, queue truncation)

The information flow subsystem is architecturally sound but has proof coverage gaps
(IF-01/IF-02) and methodology limitations (IF-03 through IF-06) that should be
closed to claim full non-interference for all kernel transitions. These gaps do not
indicate the presence of actual information leaks — they indicate the absence of
formal proof that such leaks cannot occur.

After addressing the HIGH findings and the MEDIUM gaps (NI, CBS, scheduler,
capability), the kernel is well-positioned for its first major release and
hardware benchmarking on the Raspberry Pi 5. The 38 LOW and 25 INFORMATIONAL
findings are maintenance items that can be addressed incrementally. Deep audits
of the IPC and Architecture subsystems found no security issues. The Capability
subsystem has a model-level CPtr masking inconsistency (CAP-01) and a CDT
acyclicity proof gap (CAP-02) that should be closed. The SchedContext/Lifecycle
subsystems have real but non-critical correctness gaps (SC-03 through SC-05)
that should be closed before production deployment.

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
