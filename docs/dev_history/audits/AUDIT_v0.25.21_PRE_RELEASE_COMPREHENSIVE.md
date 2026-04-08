# seLe4n Pre-Release Comprehensive Audit Report

**Version**: v0.25.21  
**Date**: 2026-04-07  
**Scope**: All 132 Lean modules + 31 Rust source files (3 crates)  
**Auditor**: Claude Opus 4.6 (8 parallel audit agents, line-by-line review)  
**Classification**: Pre-release security and correctness audit

---

## Executive Summary

This audit performed a line-by-line review of the entire seLe4n microkernel
codebase: 132 Lean 4 source files (~100,000+ lines) and 31 Rust files across
3 userspace ABI crates. The review covered soundness, type safety, security,
determinism, logic errors, performance, invariant coverage, and dead code.

### Key Metrics

| Severity | Count |
|----------|-------|
| CRITICAL | 0     |
| HIGH     | 2     |
| MEDIUM   | 24    |
| LOW      | 53    |
| INFO     | 170+  |

### Headline Result

**Zero CRITICAL findings. Zero `sorry` or `axiom` in the entire production
Lean codebase.** All kernel transitions are deterministic pure functions with
explicit error handling. The two HIGH findings are in the Scheduler subsystem
and concern unproven assumptions (blocking graph acyclicity, tautological WCRT
theorem) rather than code defects. The 26 MEDIUM findings are predominantly
design-level concerns, documentation gaps, and proof-precision issues -- none
represent exploitable vulnerabilities.

**No CVE-worthy vulnerabilities were identified.**

---

## Methodology

Each of the 8 audit agents was assigned a disjoint set of modules:

1. **Prelude + Machine + Model** (10 files, ~9,500 lines)
2. **Scheduler** (20 files, ~8,500 lines)
3. **IPC** (20 files, ~25,000 lines)
4. **Capability + Architecture** (15 files, ~10,250 lines)
5. **InformationFlow + Service + Lifecycle** (20 files, ~14,000 lines)
6. **RobinHood + RadixTree + SchedContext** (22 files, ~9,500 lines)
7. **API + CrossSubsystem + FrozenOps + Platform** (20 files, ~12,000 lines)
8. **Rust ABI** (31 files + 4 Cargo.toml, ~5,000 lines)

Each agent read every file in 500-line chunks and examined each line for:
- Soundness: `sorry`, `axiom`, `native_decide`, unsafe coercions
- Type safety: unchecked conversions, potential overflow
- Security: capability leaks, privilege escalation, missing validation
- Determinism: non-deterministic branches, partial functions
- Logic errors: off-by-one, inverted conditions, wrong comparisons
- Performance: quadratic algorithms, unnecessary allocations
- Invariant gaps: missing pre/postconditions, unproven assumptions
- Dead code: unused definitions, unreachable branches


---

## HIGH Findings (2)

### HIGH-1: Unproven Blocking Graph Acyclicity

- **Location**: `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean`, lines ~120-140
- **Subsystem**: Scheduler / Priority Inheritance Protocol
- **Category**: Invariant gap

**Description**: `blockingAcyclic` is defined as a predicate (line 115) but
is **not part of any proven invariant bundle**. The docstring comments in
BlockingGraph.lean (lines 62, 74) claim it lives in `crossSubsystemInvariant`,
but inspection of CrossSubsystem.lean reveals the 9-predicate bundle does NOT
include `blockingAcyclic`. Furthermore, `blockingAcyclic` is never consumed
as a hypothesis by any downstream theorem -- the only consumer is
`blockingChain_acyclic` (line 119) which is a trivial restatement.

`propagatePriorityInheritance` uses fuel-bounded traversal (fuel =
`objectIndex.length`) which prevents infinite loops. If a cycle exists in the
blocking graph, propagation terminates at the fuel limit rather than looping,
but the chain walk is incomplete -- threads beyond the cycle point retain
stale priority boosts.

The key gap is twofold: (1) the predicate is defined but unintegrated into
the invariant framework, and (2) the code comments incorrectly claim it is
part of `crossSubsystemInvariant`, creating a false sense of coverage.

**Impact**: If a cycle exists in the blocking graph, PIP propagation is
incomplete (stale boosts). The fuel bound prevents non-termination but does
not ensure correctness. The misleading comments could cause maintainers to
believe this property is already verified.

**Recommendation**:
(a) Add `blockingAcyclic` to `crossSubsystemInvariant` and prove preservation
    for all kernel operations, or
(b) Prove it from existing IPC invariants (e.g., `tcbQueueChainAcyclic`), or
(c) Correct the misleading comments in BlockingGraph.lean to accurately state
    that `blockingAcyclic` is defined but not yet integrated.

---

### HIGH-2: Tautological WCRT Theorem

- **Location**: `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`, lines ~120-140
- **Subsystem**: Scheduler / Liveness
- **Category**: Misleading assurance

**Description**: `bounded_scheduling_latency` (line 132) proves
`wcrtBound D L_max N B P = D * L_max + N * (B + P)`. The proof is
`simp [wcrtBound]` -- it is **definitional unfolding** that provides zero
assurance beyond the definition of `wcrtBound` itself. The theorem name
suggests a proven scheduling latency bound, but it merely confirms the
formula equals its expansion.

**Correction from initial audit**: The companion theorem
`bounded_scheduling_latency_exists` (line 153) is **NOT** tautological.
It is a genuine composition theorem that takes `WCRTHypotheses`,
`hDomainActiveRunnable`, and `hBandProgress` hypotheses and composes them
via `Nat.add_le_add` to produce a concrete selection index within the bound.
This is real proof work, though the hypotheses are still externally provided.

The core gap remains: `WCRTHypotheses` must be instantiated externally for
a concrete system configuration, and neither `hDomainActiveRunnable` nor
`hBandProgress` are derived from the kernel invariants.

**Positive note**: `pip_enhanced_wcrt_le_base` (line 278) IS a genuine
inequality, and `countHigherOrEqual_mono_threshold` (line 238) proves
monotonicity of the priority counting function.

**Impact**: The `bounded_scheduling_latency` name is misleading for its
definitional content. The existential version does genuine composition
but relies on externalized hypotheses.

**Recommendation**: Rename `bounded_scheduling_latency` to
`wcrtBound_unfold` or similar. Document that `bounded_scheduling_latency_exists`
is the substantive theorem, and track the `WCRTHypotheses` instantiation
obligation as a future workstream item.

---

## MEDIUM Findings (24)

### Scheduler Subsystem (5 MEDIUM, 2 retracted)

**MED-S1**: `resolveEffectivePrioDeadline` permissive fallback  
_Location_: `Scheduler/Operations/Selection.lean`, lines ~280-310  
Falls back to TCB's own `basePriority`/`deadline` when no SchedContext is
bound. This is inconsistent with `hasSufficientBudget` (same file) which
returns `false` for unbound threads. The combination is safe because budget
check gates dispatch, but the priority fallback is misleading. Consider
having `resolveEffectivePrioDeadline` return `Option` for unbound threads.

**MED-S2**: O(n) scan in `timeoutBlockedThreads`  
_Location_: `Scheduler/Operations/Core.lean`, lines ~500-550  
Performs a linear scan over `st.objectIndex` on every budget exhaustion
event. Acknowledged in AE3/S-05 documentation. Consider maintaining an
index of budget-bound blocked threads.

**~~MED-S3~~**: RETRACTED. The `switchDomain` `| none =>` branch IS proven
unreachable by `switchDomain_index_in_bounds` (line 792) and
`switchDomain_index_lookup_isSome` (line 804) in the same file.

**MED-S3**: High heartbeat proofs (fragility risk)  
_Location_: `Scheduler/Operations/Preservation.lean`, lines 2409, 2494  
`handleYield_preserves_edfCurrentHasEarliestDeadline` requires 1,600,000
heartbeats (8x default). `timerTick` variant requires 800,000 (4x).
Maintenance risk: toolchain updates could break these proofs.

**MED-S4**: Tautological `pip_deterministic` theorem  
_Location_: `Scheduler/PriorityInheritance/BoundedInversion.lean`, lines 53-66  
Proves `f x = f x` given identical inputs. Follows from purity by `rfl`.
Name "deterministic" is misleading. Rename to `pip_congruence`.

**MED-S5**: `eventuallyExits` is an unproven hypothesis  
_Location_: `Scheduler/Liveness/BandExhaustion.lean`, lines ~30-45  
Assumes every thread eventually exits a priority band. Not enforced by the
kernel. A thread with sufficient budget could spin indefinitely. Should be
derived from CBS budget finiteness for bound threads.

**~~MED-S7~~**: RETRACTED. `bounded_scheduling_latency_exists` is a genuine
composition theorem that performs real proof work (combining domain rotation
and band exhaustion bounds via `Nat.add_le_add`), not a vacuous existential.
See corrected HIGH-2 description above.

### IPC Subsystem (3 MEDIUM)

**MED-I1**: Badge merge Nat round-trip  
_Location_: `IPC/Operations/Endpoint.lean`, line 372  
`Badge.ofNatMasked badge.toNat` round-trips through unbounded `Nat`.
Model-safe but hardware binding must ensure consistent masking.

**MED-I2**: Timeout sentinel fragility  
_Location_: `IPC/Operations/Timeout.lean`, lines 27-38  
Uses `gpr x0 = 0xFFFFFFFF` + `ipcState = .ready` for timeout detection.
Documented as fragile; migration to dedicated `timedOut : Bool` field
recommended for H3.

**MED-I3**: `endpointQueueRemove` bypasses `storeObject`  
_Location_: `IPC/DualQueue/Core.lean`, lines 492-517  
Uses direct `RHTable.insert` instead of `storeObject` abstraction. Proven
safe under `dualQueueSystemInvariant`, but the defensive fallback silently
does nothing on predecessor/successor lookup failure.


### Model Layer (3 MEDIUM)

**MED-M1**: `AccessRightSet` raw `mk` constructor accessible  
_Location_: `Model/Object/Types.lean`, lines ~90-130  
Lean 4 limitation: `structure` constructors are public. Arbitrary `Nat`
values can be wrapped as `AccessRightSet` bypassing validated constructors.
No exploitable path found in codebase but violates encapsulation intent.

**MED-M2**: CDT `descendantsOf` transitive closure completeness deferred  
_Location_: `Model/Object/Structures.lean`, lines ~1400-1500  
BFS traversal is structurally correct but formal completeness proof (that
BFS finds ALL descendants) is not yet provided. If used in security-critical
revocation, an incomplete traversal could leave dangling capabilities.

**MED-M3**: `storeObject` infallible without capacity check  
_Location_: `Model/State.lean`, lines ~400-500  
Unconditionally inserts into the `objects` table. Relies on
`storeObjectChecked` (with `maxObjects = 65536` gate) being used at
allocation boundaries. Defense-in-depth gap for internal callers.

### InformationFlow + Service (2 MEDIUM)

**MED-IF1**: `native_decide` in enforcement boundary completeness  
_Location_: `InformationFlow/Enforcement/Wrappers.lean`, line 286  
Only `native_decide` in the audited codebase. Bypasses proof kernel, relying
on compiled Lean code. Risk minimal for finite 33-element enumeration.
Replace with `decide` for stronger trust guarantee.

**MED-SV1**: `serviceHasPathTo` returns `true` on fuel exhaustion  
_Location_: `Service/Operations.lean`, lines 118-135  
Conservative for safety (prevents missed cycles) but means insufficient fuel
causes spurious dependency rejection. Correctness proven under
`serviceCountBounded` via `serviceBfsFuel_sound`/`_sufficient`.

### SchedContext (1 MEDIUM)

**MED-SC1**: CBS bandwidth bound has acknowledged 8x gap  
_Location_: `SchedContext/Invariant/Defs.lean`, lines ~460-487  
`cbs_single_period_bound` proves `totalConsumed <= 8 * budget`. Ideal CBS
bound is `1 * budget` per period. The 8x factor from `maxReplenishments = 8`
is a proof-precision issue, not a correctness bug.

### API + CrossSubsystem + Platform (6 MEDIUM)

**MED-A1**: ThreadId/ObjId identity conflation  
_Location_: `Kernel/API.lean`, lines 526-577  
`ThreadId.ofNat objId.toNat` round-trips through `Nat`. Correct today but
structurally fragile if encoding conventions ever diverge.

**MED-CS1**: `native_decide` in pairwise coverage proof  
_Location_: `Kernel/CrossSubsystem.lean`, line 705  
Second `native_decide` instance. Extends TCB to Lean runtime evaluator for
9-predicate pairwise field-disjointness check.

**MED-CS2**: `collectQueueMembers` fuel-sufficiency not formally connected  
_Location_: `Kernel/CrossSubsystem.lean`, def at lines 69-79, doc at 112-126  
Fuel-bounded traversal with fuel = object count. AE5-A already changed the
return type to `Option` (fuel exhaustion returns `none` instead of `[]`).
Documentation argues sufficiency follows from `tcbQueueChainAcyclic`, but
the argument is not formalized as a theorem.

**MED-D1**: `parseFdtNodes` silent truncation on fuel exhaustion  
_Location_: `Platform/DeviceTree.lean`, line 585  
Returns `some ([], offset)` (empty list) when fuel runs out. Caller gets no
indication of truncation. Malformed DTB could cause missed RAM/device
regions. Should return `none` on fuel exhaustion.

**MED-B1**: `natKeysNoDup` uses opaque `Std.HashSet`  
_Location_: `Platform/Boot.lean`, lines 66-72  
Correctness depends on unverified `Std.HashSet` internals. Transparent
alternative `listAllDistinct` exists but is not used in primary path.

**MED-MM1**: MMIO write-semantics model divergence  
_Location_: `Platform/RPi5/MmioAdapter.lean`, `mmioWrite` functions  
All MMIO writes use direct memory store in the abstract model. For W1C
(write-one-to-clear) regions, abstract model diverges from hardware
semantics. Only `mmioWrite32W1C` correctly models W1C. No `MmioWriteSafe`
witness type exists to gate correct usage.

### Rust ABI (4 MEDIUM)

**MED-R1**: Unrecognized kernel errors mapped to `InvalidSyscallNumber`  
_Location_: `rust/sele4n-abi/src/decode.rs`, line 42  
Semantic mismatch: an unrecognized error code is not an invalid syscall
number. If kernel adds error code 44+ before Rust update, all new errors are
misreported. Consider adding `UnknownKernelError` variant.

**MED-R2**: `endpoint_reply_recv` silently truncates to 3 registers  
_Location_: `rust/sele4n-sys/src/ipc.rs`, lines 180-188  
If user passes message with `length = 4`, the 4th register is silently
dropped. MR[0] consumed by `reply_target` leaves only MR[1]-MR[3]. Should
return error instead of silently truncating.

**MED-R3**: `tcb_set_priority` accepts raw u64 without validation  
_Location_: `rust/sele4n-sys/src/tcb.rs`, lines 49-99  
`tcb_set_priority`, `tcb_set_mcp`, `tcb_set_ipc_buffer` accept raw `u64`
without client-side validation. Kernel validates, so no security impact, but
inconsistent with `vspace_map` which pre-validates W^X.

**MED-R4**: `raw_syscall` x6 clobbered but not read back  
_Location_: `rust/sele4n-abi/src/trap.rs`, lines 48-49  
`lateout("x6") _` clobbers x6 without reading. Current ABI doesn't use x6
for return values. Future ABI extension risk.


---

## LOW Findings (53)

### Scheduler (8 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-S1 | RunQueue.lean ~60-70 | `size` field maintained but never consumed by scheduler decisions; dead state |
| LOW-S2 | Selection.lean ~150-180 | `chooseBestRunnableBy` tie-breaking semantics (FIFO) implicit, not documented |
| LOW-S3 | Invariant.lean ~400-450 | `schedulerInvariantBundleExtended` is a 16-tuple; unwieldy projections |
| LOW-S4 | BlockingGraph.lean ~80-100 | `waitersOf` O(n) scan per PIP chain link; O(n * depth) total |
| LOW-S5 | Compute.lean ~26-37 | Waiter with no SchedContext invisible to PIP; undocumented |
| LOW-S6 | BoundedInversion.lean ~39-43 | Chain depth bound uses total objects, not thread count (over-conservative) |
| LOW-S7 | Replenishment.lean ~40-55 | Dead-time bound assumes continuous time; discrete ticks add up to 1 tick |
| LOW-S8 | TraceModel.lean ~20-50 | Trace model disconnected from concrete operations; bridge hypotheses needed |

### IPC (7 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-I1 | Endpoint.lean ~329-336 | `pendingMessage = none` for waiting threads: structural argument, no formal invariant |
| LOW-I2 | Endpoint.lean ~184-208 | `donateSchedContext` is public `def`; could be misused outside IPC module |
| LOW-I3 | CapTransfer.lean ~100 | Slot base advancement uses unbounded Nat; H3 must enforce slot width |
| LOW-I4 | Timeout.lean ~118 | `_endpointId` parameter unused (reserved for future) |
| LOW-I5 | Donation.lean ~63-82 | `applyCallDonation` silently returns unchanged state on all error paths |
| LOW-I6 | WithCaps.lean ~138-139 | Receive-side cap transfer failure aborts entire receive; asymmetric with send |
| LOW-I7 | Invariant/Defs.lean ~960-967 | `donationChainAcyclic` only prevents 2-cycles; longer prevention by structural argument |

### Model Layer (6 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-ML1 | Prelude.lean ~250-300 | `Std.HashSet.contains` bridge layer unverified (trusted from Std) |
| LOW-ML2 | Machine.lean ~200-250 | `zeroMemoryRange` creates O(n) temporary list for memory scrubs |
| LOW-ML3 | Types.lean ~1050-1100 | `Notification.waitingThreads` removal is O(n) via `List.filter` |
| LOW-ML4 | Structures.lean ~700-800 | CNode guard comparison uses BEq on Nat (lawful, but noted) |
| LOW-ML5 | Structures.lean ~1500-1600 | `findFirstEmptySlot` O(n) linear scan |
| LOW-ML6 | State.lean ~600-700 | `revokeAndClearRefsState` fold order is deterministic but order-independent |

### Capability + Architecture (2 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-CA1 | Capability/Invariant/Defs.lean | CDT completeness/acyclicity externalized hypotheses (documented design) |
| LOW-CA2 | Architecture/VSpaceBackend.lean | `VSpaceBackend` typeclass not yet integrated (H3 forward declaration) |

### InformationFlow + Service + Lifecycle (5 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-IF1 | Policy.lean ~785-810 | `defaultLabelingContext` assigns public label to all entities (insecure bootstrap) |
| LOW-IF2 | Projection.lean ~200-230 | Register contents stripped from TCBs but TCB existence is observable |
| LOW-SV2 | Operations.lean ~85-100 | `removeDependenciesOf` O(n*m) scan; acceptable for bounded service counts |
| LOW-SV3 | Registry.lean ~150-175 | `lookupServiceByCap` first-match via fold; safe under `registryEndpointUnique` |
| LOW-SV4 | Acyclicity.lean ~547 | 800K maxHeartbeats for DFS completeness proof (10x default) |

### RobinHood + RadixTree + SchedContext (7 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-RH1 | RobinHood/Invariant/*.lean | High maxHeartbeats (420K-800K) across multiple proofs; fragility risk |
| LOW-RH2 | RobinHood/Core.lean | `resize` preserves `invExt` but `invExtK` requires going through `insert` |
| LOW-RT1 | RadixTree/Bridge.lean | `UniqueRadixIndices` assumed; `buildCNodeRadixChecked` validates but unchecked path does not |
| LOW-SC1 | ReplenishQueue.lean | `insertSorted` allows duplicate SchedContextId entries |
| LOW-SC2 | ReplenishQueue.lean | `popDue` size subtraction could underflow (Nat saturates to 0; invariant prevents) |
| LOW-SC3 | Budget.lean | `truncateReplenishments` drops oldest entries; some earned budget silently lost |
| LOW-SC4 | Operations.lean ~234-262 | `schedContextYieldTo` is pure function, not Kernel monad; cannot signal errors |

### API + CrossSubsystem + Platform (10 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-A1 | API.lean ~417-426 | `resolveExtraCaps` silently drops caps on resolution failure (seL4-compatible) |
| LOW-A2 | API.lean ~684-685 | Badge zero as "no badge" sentinel; implicit reserved value |
| LOW-CS1 | CrossSubsystem.lean ~79 | Non-TCB object in queue returns singleton list instead of error |
| LOW-F1 | FrozenOps/Core.lean ~216-244 | "Unreachable after Phase 1" comments without proofs |
| LOW-F2 | FrozenOps/Operations.lean | O(n) thread selection in frozenChooseThread (experimental module) |
| LOW-D2 | DeviceTree.lean ~317 | `classifyMemoryRegion` always returns `.ram` (TODO for WS-V) |
| LOW-D3 | DeviceTree.lean ~136 | `fromDtb` stub always returns `none` |
| LOW-B2 | Boot.lean | `bootSafeObject` excludes VSpaceRoots; post-boot construction needed |
| LOW-S01 | Sim/RuntimeContract.lean | Permissive contract with all-True predicates (testing only) |
| LOW-MM2 | RPi5/MmioAdapter.lean ~636 | `memoryRead_idempotent_nonMmio` is trivially `rfl` (vacuous) |

### Rust ABI (9 LOW)

| ID | Location | Description |
|----|----------|-------------|
| LOW-R1 | sele4n-types/src/lib.rs | Doc comment says "43-variant" instead of "44-variant" |
| LOW-R2 | sele4n-types/src/identifiers.rs | `From<u64>` allows constructing sentinel values without warning |
| LOW-R3 | sele4n-abi/src/decode.rs ~39 | Stale comment says error codes "0-42"; actual max is 43 |
| LOW-R4 | sele4n-abi/src/args/sched_context.rs | No client-side CBS constraint validation (budget <= period) |
| LOW-R5 | sele4n-abi/src/args/service.rs ~62 | Invalid `requires_grant` returns `InvalidMessageInfo` instead of `InvalidArgument` |
| LOW-R6 | sele4n-abi/tests/conformance.rs | Missing XVAL register-position tests for SchedContext/TCB operations |
| LOW-R7 | sele4n-sys/src/cap.rs | Missing `SchedContext` marker type for phantom-typed capabilities |
| LOW-R8 | sele4n-sys/src/ipc.rs ~50 | `IpcMessage.length` is public; can be set to invalid values externally |
| LOW-R9 | sele4n-sys/src/lifecycle.rs ~15 | Doc comment omits SchedContext from type tag list |


---

## Per-Subsystem Assessment

### 1. Prelude + Machine + Model

**Verdict: EXCELLENT**

Zero sorry/axiom across ~9,500 lines. All typed identifiers, monad
foundations, kernel objects, and state representations are machine-checked.
The freeze pipeline (IntermediateState -> FrozenSystemState) has complete
lookup equivalence proofs. Three MEDIUM findings are documented design
decisions (AccessRightSet encapsulation, CDT BFS completeness, storeObject
capacity). The `LawfulMonad` instance for `KernelM` and `LawfulBEq`/
`LawfulHashable` instances for all ID types provide strong algebraic
guarantees.

### 2. Scheduler

**Verdict: GOOD with notable gaps**

The scheduler operations are deterministic and well-structured. RunQueue
operations have comprehensive WF invariants. EDF thread selection is proven
correct with transitivity of the comparison predicate. However, two HIGH
findings (blocking acyclicity assumption, tautological WCRT) and the
`eventuallyExits` unproven hypothesis represent genuine proof gaps that
should be addressed before claiming formal scheduling guarantees. The PIP
implementation is functionally correct but its termination guarantee depends
on the unproven acyclicity assumption.

### 3. IPC

**Verdict: EXCELLENT**

The largest subsystem (~25,000 lines) with zero sorry/axiom. The 14-conjunct
`ipcInvariantFull` covers queue well-formedness, link integrity, acyclicity,
message bounds, badge bounds, blocking consistency, queue membership, head
disjointness, timeout consistency, and donation invariants. All core IPC
operations have preservation proofs. The `endpointQueueRemove` fallback
branches are proven unreachable under invariants. Three MEDIUM findings are
design-level concerns with documented mitigation paths.

### 4. Capability + Architecture

**Verdict: EXCELLENT**

Zero MEDIUM findings. All ~10,250 lines pass with only 2 LOW findings (both
documented forward-declarations). Complete round-trip proofs for all decode
paths. W^X enforcement at the map operation level. VSpace invariant bundle
has 7 conjuncts with full preservation coverage. The register decode pipeline
is total and deterministic with exhaustive bounds checking.

### 5. InformationFlow + Service + Lifecycle

**Verdict: EXCELLENT**

Non-interference coverage with 34 `NonInterferenceStep` constructors, trace-
level composition, and compile-time coverage enforcement. Service dependency
acyclicity has bi-directional correctness proofs. Lifecycle suspension
follows the documented 7-step sequence with PIP revert correctly placed. The
single `native_decide` (enforcement boundary completeness) is the only TCB
extension concern.

### 6. RobinHood + RadixTree + SchedContext

**Verdict: VERY GOOD**

All three data structure implementations are fully verified. RobinHood has
complete `invExtK` preservation for all operations. RadixTree has O(1)
operations with proven lookup equivalence to the source RHTable. SchedContext
CBS budget engine has sound admission control and bidirectional binding
consistency. The CBS 8x bandwidth gap (MED-SC1) is the only notable proof-
precision issue.

### 7. API + CrossSubsystem + FrozenOps + Platform

**Verdict: GOOD**

API dispatch has complete coverage with wildcard unreachability proofs. The
33-operation cross-subsystem bridge lemma suite is comprehensive. Boot
sequence proves all 10 components of `proofLayerInvariantBundle`. Platform
RPi5 has substantive contracts with BCM2712 datasheet cross-references. Six
MEDIUM findings include the DTB parser truncation risk and MMIO write-
semantics divergence, both of which should be addressed before hardware
deployment.

### 8. Rust ABI

**Verdict: VERY GOOD**

Zero `unsafe` code in sele4n-types and sele4n-sys. Single targeted `unsafe`
in sele4n-abi (inline `svc #0`). `deny(unsafe_code)` enforced crate-wide.
All enum variants (KernelError 44, SyscallId 25, TypeTag 7, AccessRight 5)
match Lean definitions exactly. Comprehensive conformance test suite (~1,350
lines). Four MEDIUM findings are ergonomics/error-reporting issues, not
safety violations.

---

## Cross-Cutting Observations

### Soundness

- **Zero `sorry`** across all 132 Lean production files
- **Zero `axiom`** in the production proof surface
- **Two `native_decide`** instances (MED-IF1, MED-CS1) -- finite decidable
  propositions, minimal risk but extend TCB
- **All transitions are pure functions** returning `Except KernelError` --
  no IO, no randomness, no non-determinism

### Type Safety

- All `.toNat`/`.ofNat` conversions are documented as requiring hardware-
  binding validation in WS-V/H3
- Lean's unbounded `Nat` eliminates overflow in the model; hardware binding
  must enforce word-width constraints
- Non-lawful `BEq` instances (RegisterFile, TCB, VSpaceRoot, CNode) are
  documented with formal negative witnesses

### Security

- **No capability leak paths found** across the entire codebase
- **No privilege escalation paths found**
- Capability authority is monotonically non-increasing (proven: mint
  attenuates, delete reduces, revoke reduces)
- Priority authority bounded by caller's MCP (proven)
- W^X enforcement at VSpace map level (proven)
- Non-interference for all 34 kernel operations (proven, with documented
  boundary exclusions for service orchestration)

### Performance

- Several O(n) scans exist (waitersOf, timeoutBlockedThreads,
  collectQueueMembers, lookupServiceByCap, removeFromAllEndpointQueues)
- These are acceptable for the microkernel's bounded object counts but should
  be reviewed for the hardware binding if object counts grow significantly
- High-heartbeat proofs (800K-1,600K) are a maintenance risk for CI

### Lean-Rust Consistency

- **KernelError**: 44 Lean variants = 44 Rust variants (0-43). MATCH.
- **SyscallId**: 25 Lean variants = 25 Rust variants (0-24). MATCH.
- **TypeTag/KernelObjectType**: 7 Lean variants = 7 Rust variants (0-6). MATCH.
- **AccessRight**: 5 Lean variants = 5 Rust variants (bits 0-4). MATCH.
- All `repr(C)`, `repr(transparent)`, and `repr(u32/u64/u8)` annotations are
  correctly applied

---

## Priority Recommendations

### Before Release (Recommended)

1. **Prove or bridge `blockingAcyclic`** (HIGH-1) -- PIP correctness depends
   on this unproven assumption
2. **Rename/document WCRT theorems** (HIGH-2) -- prevent misleading
   assurance claims for `bounded_scheduling_latency`
3. **Fix DTB parser truncation** (MED-D1) -- return `none` on fuel exhaustion
4. **Replace `native_decide` with `decide`** (MED-IF1, MED-CS1) -- reduce TCB
5. **Fix silent reply_recv truncation** (MED-R2) -- return error for >3 regs

### Before Hardware Binding (H3)

6. Formalize `collectQueueMembers` fuel sufficiency (MED-CS2)
7. Add `MmioWriteSafe` witness type (MED-MM1)
8. Replace timeout sentinel with dedicated `timedOut : Bool` field (MED-I2)
9. Add `ObjId.toThreadId` validated conversion (MED-A1)
10. Add client-side validation in `tcb_set_priority` et al. (MED-R3)

### Maintenance / Quality

11. Decompose high-heartbeat proofs (MED-S3, LOW-SV4, LOW-RH1)
12. Derive `eventuallyExits` from CBS budget finiteness (MED-S5)
13. Tighten CBS bandwidth bound from 8x to 1x (MED-SC1)
14. Add `SchedContext` marker type to Rust sele4n-sys (LOW-R7)
15. Add XVAL register-position tests for SchedContext/TCB (LOW-R6)

---

## Conclusion

The seLe4n microkernel is in strong shape for its first major release. The
codebase demonstrates exceptional engineering discipline: zero sorry/axiom
across 100,000+ lines of Lean 4, comprehensive invariant preservation proofs
for all kernel operations, and a well-structured Rust ABI layer with minimal
unsafe code.

The two HIGH findings are both in the Scheduler subsystem's formal assurance
claims rather than in operational code. The blocking acyclicity assumption
(HIGH-1) is the most significant gap -- PIP correctness depends on it and it
should be formally addressed. The WCRT theorem naming (HIGH-2) is a
documentation/assurance concern that can be resolved by renaming.

No security vulnerabilities warranting CVE designation were identified. The
kernel's capability-based security model is well-implemented with proven
authority reduction, and the non-interference framework provides comprehensive
coverage with clearly documented boundary exclusions.

**Overall assessment: PASS with 2 HIGH findings requiring attention before
formal verification claims are made about scheduling guarantees.**

---

## Errata (Post-Verification Corrections)

The following corrections were applied after independent line-by-line
verification of each finding against the source code:

1. **MED-S3 RETRACTED**: The `switchDomain` `| none =>` branch IS proven
   unreachable by `switchDomain_index_in_bounds` (line 792) and
   `switchDomain_index_lookup_isSome` (line 804) in Core.lean. The initial
   audit agent missed these theorems located directly below the function.

2. **MED-S7 RETRACTED**: `bounded_scheduling_latency_exists` is NOT vacuous.
   It is a genuine composition theorem that combines domain rotation and band
   exhaustion bounds via `Nat.add_le_add` with real hypotheses
   (`hDomainActiveRunnable`, `hBandProgress`). Only the definitional
   `bounded_scheduling_latency` (which proves `wcrtBound D L N B P =
   D * L + N * (B + P)` by `simp`) is tautological.

3. **HIGH-1 REFINED**: `blockingAcyclic` is not only unproven but also NOT
   part of `crossSubsystemInvariant` despite comments in BlockingGraph.lean
   (lines 62, 74) claiming otherwise. Additionally, `blockingAcyclic` is
   never consumed by any downstream proof. The misleading comments are an
   additional concern beyond the original finding.

4. **MED-CS2 LINE CORRECTION**: `collectQueueMembers` definition is at lines
   69-79 (not 118-126). The documentation at 112-126 discusses fuel
   sufficiency. AE5-A already changed the return type to `Option` (fuel
   exhaustion returns `none`).

5. **MEDIUM count adjusted**: 26 -> 24 (2 retracted).

All other 22 MEDIUM and 2 HIGH findings were independently confirmed against
the source code at their claimed locations.
