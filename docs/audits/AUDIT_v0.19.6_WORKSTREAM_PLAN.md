# WS-T Workstream Plan — Deep-Dive Audit Remediation (v0.19.6)

**Created**: 2026-03-23
**Baseline version**: 0.19.6
**Baseline audits**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.19.6_DEEP_DIVE.md` (17 new findings, 112+ confirmed)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.19.6_FULL_KERNEL_RUST.md` (3 HIGH, 40 MEDIUM, 52 LOW)
**Prior portfolios**: WS-B through WS-S (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Combined finding count**: 4 HIGH, 52 MEDIUM (deduplicated), 56 LOW, 97+ Info (confirmed + extended)

---

## 1. Executive Summary

Two comprehensive audits of seLe4n v0.19.6 were conducted on 2026-03-23: a full
kernel & Rust audit (multi-agent, 95+ findings) followed by a deep-dive audit
(14 parallel agents, line-by-line review of all 135+ source files). The deep
dive independently confirmed every predecessor finding and discovered **17 new
findings** (1 HIGH elevation, 12 MEDIUM, 4 LOW).

Neither audit found Critical vulnerabilities. The codebase has zero `sorry`,
zero `axiom`, and zero `unsafe` Rust beyond the single ARM64 `svc #0`
instruction. All 11 TPI-D tracked proof items are CLOSED.

The **4 HIGH findings** concentrate in three areas:
1. **Model integrity gaps** — `AccessRightSet.ofList` lacks `valid` postcondition
   (H-1), `CapDerivationTree` constructor bypasses verified mutation (H-2)
2. **Hardware-binding readiness** — RPi5 runtime contract cannot prove register-
   write invariant preservation (H-3)
3. **Rust ABI drift** — `KernelError` missing 4 Lean variants, causing silent
   error misidentification during hardware benchmarking (H-4)

The **52 deduplicated MEDIUM findings** cluster around eight themes:

1. **Frozen-phase IPC semantics** — Blocked threads not enqueued in frozen
   endpoint operations (M-FRZ-1/2/3), no `frozenQueuePushTail` primitive
2. **IPC proof coverage** — `ipcStateQueueConsistent` preservation gaps for
   compound operations (M-IPC-1/2/3), WithCaps wrappers unproven
3. **Model-hardware fidelity** — Unbounded identifiers (M-MOD-1), timer
   wrap-around (M-MOD-3), alignment modeling (M-MOD-5), frozen state
   TLB gap (M-NEW-1), storeObject invariant bundling (M-NEW-2/3)
4. **Lifecycle safety** — Retype functions bypass cleanup (M-NEW-4),
   no object well-formedness validation (M-NEW-5), mid-queue cleanup (M-LCS-1)
5. **Architecture & platform** — Default page permissions permissive (M-NEW-6),
   no MMIO adapter (M-NEW-7), no cache coherency model (M-NEW-8),
   VSpaceMapArgs raw Nat decode (M-ARCH-1), full TLB flush (M-ARCH-4)
6. **Rust ABI boundary** — MessageInfo label truncation (M-NEW-9), VSpaceMapArgs
   perms unvalidated (M-NEW-10), ServiceRegister bool permissive (M-NEW-11)
7. **Build infrastructure** — Pre-commit hook temp file race (M-NEW-12),
   toolchain download not SHA-verified (M-NEW-13), Rust tests not in CI
8. **Testing gaps** — `.build` not `.buildChecked` (M-TST-2), invariant checks
   on pre-state (M-TST-3), syscall dispatch 3/14 coverage (M-TST-4)

This workstream plan organizes all actionable findings into **8 phases** (T1–T8)
with **88 atomic sub-tasks**, explicit dependencies, gate conditions, and scope
estimates. The plan addresses all 4 HIGH findings, all 52 MEDIUM findings, the
4 new LOW findings, and selects 12 predecessor LOW findings for inclusion based
on security relevance, proof chain completeness, and hardware readiness.

---

## 2. Consolidated Finding Registry

### 2.1 HIGH Findings (4)

| ID | Source | Severity | Subsystem | Description |
|----|--------|----------|-----------|-------------|
| H-1 | Predecessor | HIGH | Model | `AccessRightSet.ofList` does not guarantee `valid` postcondition |
| H-2 | Predecessor | HIGH | Model | `CapDerivationTree` constructor not access-controlled; bypasses verified mutation |
| H-3 | Predecessor | HIGH | Platform | RPi5 runtime contract cannot prove register-write invariant preservation |
| H-4 | Deep-Dive (elevated) | HIGH | Rust | `KernelError` missing 4 Lean variants (discriminants 34-37) |

### 2.2 MEDIUM Findings — Frozen IPC (3)

| ID | Source | Description |
|----|--------|-------------|
| M-FRZ-1 | Predecessor | `frozenEndpointSend` marks sender `blockedOnSend` but does not enqueue into `sendQ` |
| M-FRZ-2 | Predecessor | `frozenEndpointReceive` marks receiver `blockedOnReceive` but does not enqueue into `receiveQ` |
| M-FRZ-3 | Predecessor | `frozenEndpointCall` marks caller `blockedOnCall` but does not enqueue into `sendQ` |

### 2.3 MEDIUM Findings — IPC Proof Coverage (3)

| ID | Source | Description |
|----|--------|-------------|
| M-IPC-1 | Predecessor | Missing `ipcStateQueueConsistent` preservation for `endpointCall`, `endpointReplyRecv`, notifications |
| M-IPC-2 | Predecessor | Missing `dualQueueSystemInvariant` preservation for `endpointQueueRemoveDual` |
| M-IPC-3 | Predecessor | Missing `ipcInvariantFull` preservation for `WithCaps` wrapper operations |

### 2.4 MEDIUM Findings — Model & State (10)

| ID | Source | Description |
|----|--------|-------------|
| M-MOD-1 | Predecessor | Unbounded `Nat` identifiers lack `isWord64` validity predicates |
| M-MOD-2 | Predecessor | `zeroMemoryRange` lacks `base + size <= machineWordMax` precondition |
| M-MOD-3 | Predecessor | `MachineState.timer` unbounded — no wrap-around modeling |
| M-MOD-6 | Predecessor | `Notification.waitingThreads` uses LIFO semantics (List.cons) |
| M-BLD-1 | Predecessor | `Builder.createObject` skips `objectIndex`/`objectIndexSet` updates |
| M-ST-1 | Predecessor | `storeObject` `capabilityRefs` rebuild is O(n) for CNode stores |
| M-NEW-1 | Deep-Dive | `FrozenSystemState` missing `tlb` field; freeze drops TLB state |
| M-NEW-2 | Deep-Dive | `storeObject` lacks bundled `allTablesInvExt` preservation theorem |
| M-NEW-3 | Deep-Dive | `capabilityRefs` filter-then-fold chain lacks `invExt` preservation proofs |
| M-ST-2 | Predecessor | `attachSlotToCdtNode` stale-link cleanup ordering fragile |

### 2.5 MEDIUM Findings — Scheduler (3)

| ID | Source | Description |
|----|--------|-------------|
| M-SCH-1 | Predecessor | `maxPriority` field consistency not formally proven after `insert` |
| M-SCH-2 | Predecessor | `recomputeMaxPriority` iterates via `fold` — hidden O(capacity) cost |
| M-SCH-3 | Predecessor | `threadPriority`/`membership` consistency is external hypothesis |

### 2.6 MEDIUM Findings — Capability (3)

| ID | Source | Description |
|----|--------|-------------|
| M-CAP-1 | Predecessor | `cspaceMutate` badge override untracked by CDT |
| M-CAP-2 | Predecessor | `descendantsOf` BFS fuel sufficiency for revocation completeness unproven |
| M-DS-3 | Predecessor | RadixTree bridge bidirectional lookup equivalence deferred |

### 2.7 MEDIUM Findings — Lifecycle & Service (4)

| ID | Source | Description |
|----|--------|-------------|
| M-LCS-1 | Predecessor | Intrusive queue cleanup only adjusts head/tail, not mid-queue nodes |
| M-LCS-2 | Predecessor | `lookupServiceByCap` fold uses implementation-defined first-match order |
| M-NEW-4 | Deep-Dive | `lifecycleRetypeObject`/`lifecycleRetypeDirect` bypass cleanup and scrub |
| M-NEW-5 | Deep-Dive | No validation of new object well-formedness in retype |

### 2.8 MEDIUM Findings — Architecture & Platform (7)

| ID | Source | Description |
|----|--------|-------------|
| M-ARCH-1 | Predecessor | `VSpaceMapArgs.perms` decoded as raw `Nat`, not `PagePermissions` |
| M-ARCH-2 | Predecessor | DTB parsing stub returns `none` for all inputs |
| M-ARCH-4 | Predecessor | TLB full-flush after every map/unmap — performance impact |
| M-NEW-6 | Deep-Dive | `vspaceMapPage` default permissions permissive |
| M-NEW-7 | Deep-Dive | No MMIO adapter for device-region access |
| M-NEW-8 | Deep-Dive | No cache coherency or memory ordering model |
| M-CS-1 | Predecessor | `noStaleEndpointQueueReferences` only checks head/tail, not interior |

### 2.9 MEDIUM Findings — InformationFlow & Cross-Subsystem (4)

| ID | Source | Description |
|----|--------|-------------|
| M-IF-1 | Predecessor | `dispatchWithCap` calls unchecked operations instead of policy-checked wrappers |
| M-IF-2 | Predecessor | Integrity flow direction allows write-up (documented deliberate design) |
| M-IF-3 | Predecessor | NI proofs for complex IPC accept projection as external hypothesis |
| M-DS-1 | Predecessor | `insertNoResize` silently drops entries on fuel exhaustion (mitigated by KMap) |

### 2.10 MEDIUM Findings — Rust ABI (4)

| ID | Source | Description |
|----|--------|-------------|
| M-RUST-1 | Predecessor (→ H-4) | Elevated to H-4; see section 2.1 |
| M-NEW-9 | Deep-Dive | `MessageInfo` label has no 55-bit bound check; encode silently truncates |
| M-NEW-10 | Deep-Dive | `VSpaceMapArgs.perms` unvalidated at ABI decode boundary |
| M-NEW-11 | Deep-Dive | `ServiceRegister` bool accepts any non-zero as true |

### 2.11 MEDIUM Findings — Testing & Build (7)

| ID | Source | Description |
|----|--------|-------------|
| M-TST-1 | Predecessor | `OperationChainSuite` not registered as lakefile executable |
| M-TST-2 | Predecessor | MainTraceHarness uses `.build` (unchecked) not `.buildChecked` |
| M-TST-3 | Predecessor | Trace harness invariant checks test pre-state, not mutated intermediates |
| M-TST-4 | Predecessor | Syscall dispatch tested for only 3 of 14 variants |
| M-NEW-12 | Deep-Dive | Pre-commit hook uses predictable `/tmp/lake-precommit-$$.log` temp path |
| M-NEW-13 | Deep-Dive | Lean toolchain download not SHA-256 verified |
| M-DS-2 | Predecessor | `erase` unconditionally decrements size (safe under WF invariant) |

### 2.12 Selected LOW Findings (16)

| ID | Source | Description | Inclusion Rationale |
|----|--------|-------------|---------------------|
| L-NEW-1 | Deep-Dive | `cleanupEndpointServiceRegistrations` orphans dependency edges | Service graph consistency |
| L-NEW-2 | Deep-Dive | Missing `cleanupEndpointServiceRegistrations` invariant proof | Proof chain completeness |
| L-NEW-3 | Deep-Dive | Notification `waitingThreads` references not checked by CrossSubsystem | Security boundary |
| L-NEW-4 | Deep-Dive | CNode `guardValue` not bounded by `guardWidth` | Model fidelity |
| L-P01 | Predecessor | No FrozenOps test coverage | Coverage gap |
| L-P02 | Predecessor | No deep CDT cascade test (3+ levels) | Proof confidence |
| L-P03 | Predecessor | Rust tests not run in CI | CI completeness |
| L-P04 | Predecessor | No `deregisterInterface` service operation | API completeness |
| L-P05 | Predecessor | RadixTree `lookup_insert_ne` extra precondition undocumented | Proof usability |
| L-P06 | Predecessor | `handleYield` with empty run queue not tested | Edge case coverage |
| L-P07 | Predecessor | IRQ handler dispatch not tested | Coverage gap |
| L-P08 | Predecessor | Boot sequence not tested | Coverage gap |
| L-P09 | Predecessor | `Builder.createObject` skips freeze test coverage | Coverage gap |
| L-P10 | Predecessor | IPC compound operation postconditions externalized | Proof ergonomics |
| L-P11 | Predecessor | Two CPtr resolution paths semantically consistent but undocumented | Documentation |
| L-P12 | Predecessor | Memory projection vacuous without MemoryDomainOwnership | Documentation |

---

## 3. Planning Principles

1. **Benchmarking-first ordering.** The v0.19.6 audit confirms the codebase is
   READY FOR BENCHMARKING with Priority 1 items addressed. Phase T1 eliminates
   all benchmarking blockers: frozen IPC queue semantics (M-FRZ-1/2/3), Rust
   `KernelError` drift (H-4), and test registration (M-TST-1). All subsequent
   phases can proceed while benchmarking runs.

2. **Model integrity before proof threading.** Structural changes to types and
   invariants (H-1, H-2, M-NEW-1, L-NEW-4) ship in T2 before proof closure
   phases (T4, T5) that must thread through updated type signatures. This
   prevents rework cascades.

3. **Rust ABI isolation.** All Rust changes (H-4, M-NEW-9/10/11) are grouped
   in T1 and T3. Rust files are disjoint from Lean proof files, enabling full
   parallelism with Lean-focused phases.

4. **Proof chain closure.** IPC and capability proof gaps (M-IPC-1/2/3,
   M-CAP-2, M-DS-3) are addressed in T4 after model stabilization (T2). Each
   preservation theorem is a self-contained sub-task that can be committed
   independently.

5. **Hardware preparation as late phase.** Architecture and platform changes
   (T6) depend on model fidelity (T2), lifecycle safety (T5), and API dispatch
   fixes (T6 includes M-IF-1). Grouping hardware preparation late minimizes
   rework from earlier model changes.

6. **Test coverage parallels code changes.** Phase T7 (test coverage) can run
   in parallel with T6 (hardware prep) on disjoint file sets. New tests
   exercise frozen operations, CDT cascades, and syscall dispatch added in
   earlier phases.

7. **Zero sorry/axiom invariant.** No phase may introduce `sorry`, `axiom`,
   `admit`, or `partial` in production Lean code. Every phase gate includes
   a `sorry`/`axiom` scan.

8. **Atomic sub-task discipline.** Each sub-task is scoped to a single logical
   change that can be committed independently. Sub-tasks within a phase may
   depend on earlier sub-tasks in the same phase but never on later phases.

9. **Design-intentional findings documented, not "fixed."** Findings that
   reflect deliberate design choices matching seL4 semantics (M-IF-2, M-CAP-1,
   M-CAP-3, M-DS-1, M-DS-2) are addressed through documentation, not code
   changes. The workstream adds explicit rationale at the definition site.

---

## 4. Phase Dependency Graph

```
T1 (Benchmarking Blockers)
 │
 ├──→ T2 (Model & CDT Integrity)
 │     │
 │     ├──→ T4 (IPC & Capability Proof Closure)
 │     │     │
 │     │     └──→ T5 (Lifecycle, Service & Cross-Subsystem)
 │     │           │
 │     │           ├──→ T6 (Architecture & Hardware Preparation)
 │     │           │     │
 │     │           │     └──→ T8 (Documentation & Closure) ← waits for T6+T7
 │     │           │
 │     │           └──→ T7 (Test Coverage & Build Infrastructure)  ← parallel with T6
 │     │
 │     └──→ T3 (Rust ABI Hardening)  ← parallel with T4 (disjoint files)
 │
 └──→ [BENCHMARKING CAN BEGIN after T1]
```

**Critical path**: T1 → T2 → T4 → T5 → T6 → T8
**Rust track**: T1 → T3 (runs in parallel with T2/T4, disjoint file sets)
**Test track**: T5 → T7 → T8 (runs in parallel with T6 after T5)

**Parallelism opportunities after T5:**
- **T6** owns: `Architecture/VSpace*.lean`, `Platform/RPi5/`, `InformationFlow/Enforcement/`,
  `Kernel/API.lean` (dispatch wrappers only)
- **T7** owns: `tests/`, `SeLe4n/Testing/`, `scripts/`, `lakefile.toml`,
  `rust/` (CI config only)

---

## 5. Phase Specifications

### Phase T1 — Benchmarking Blockers (v0.20.0)

**Scope**: Eliminate all benchmarking-blocking defects. Fix frozen IPC queue
enqueue semantics, add missing Rust `KernelError` variants, and register the
`OperationChainSuite` test target so it actually runs.

**Rationale**: The deep-dive audit confirms the codebase is READY FOR
BENCHMARKING with these 3 items resolved. The frozen IPC queue bug (M-FRZ-1/2/3)
means blocked threads are invisible to subsequent matching operations — IPC
rendezvous silently fails when sender and receiver arrive at different times.
The missing `KernelError` variants (H-4) cause hardware benchmarks to report
wrong errors for lifecycle operations. The unregistered test suite (M-TST-1)
means error-path tests may never run.

**Dependencies**: None (first phase).

**Gate**: `test_smoke.sh` passes. All Rust tests pass (`cargo test --workspace`).
Frozen IPC queue enqueue verified by new or existing tests. Zero `sorry`/`axiom`.
Specific module builds verified for every modified `.lean` file.

**Sub-tasks (10):**

**Intra-phase ordering constraints:**
- Frozen IPC chain: T1-A → T1-B/C/D (parallel) → T1-E
- Rust chain: T1-F → T1-G → T1-H (sequential)
- Testing: T1-I → T1-J (sequential)
- All three chains are independent of each other

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T1-A | M-FRZ-1/2/3 | Implement `frozenQueuePushTail` operation in `FrozenOps`. This is the missing primitive: given a frozen endpoint object and a `ThreadId`, append the thread to the endpoint's send or receive queue by updating the intrusive `queueNext`/`queuePrev` links via `FrozenMap.set`. Must maintain the dual-queue invariant (no thread in both queues). | `SeLe4n/Kernel/FrozenOps/Core.lean` | Medium |
| T1-B | M-FRZ-1 | **(Requires T1-A)** Fix `frozenEndpointSend` to call `frozenQueuePushTail` after marking the sender `blockedOnSend`. The enqueue must happen atomically with the TCB state update — both writes in the same `FrozenKernel` monadic chain. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| T1-C | M-FRZ-2 | **(Requires T1-A)** Fix `frozenEndpointReceive` to call `frozenQueuePushTail` after marking the receiver `blockedOnReceive`. Same pattern as T1-B but for the receive queue. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| T1-D | M-FRZ-3 | **(Requires T1-A)** Fix `frozenEndpointCall` to call `frozenQueuePushTail` after marking the caller `blockedOnCall`. Enqueue into the send queue (caller is a sender until reply). | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| T1-E | M-FRZ-1/2/3 | **(Requires T1-B/C/D)** Add `frozenQueuePushTail` preservation theorems: FrozenMap `set`/`get?` roundtrip for the enqueued thread, frame lemma proving other threads' state is unaffected, and `frozenStoreObject` preservation for the updated endpoint. | `SeLe4n/Kernel/FrozenOps/Commutativity.lean` | Medium |
| T1-F | H-4 | Add 4 missing `KernelError` variants to Rust enum: `ResourceExhausted` (34), `InvalidCapPtr` (35), `ObjectStoreCapacityExceeded` (36), `AllocationMisaligned` (37). Assign matching discriminant values. Update `Display` impl. | `rust/sele4n-types/src/error.rs` | Small |
| T1-G | H-4 | **(Requires T1-F)** Update `decode_response` to handle discriminants 34-37. Verify that the default/fallback arm maps truly unknown values (≥38) to `InvalidSyscallNumber`. | `rust/sele4n-types/src/error.rs` | Small |
| T1-H | H-4 | **(Requires T1-G)** Add cross-validation tests for new `KernelError` variants: roundtrip encode/decode, discriminant ordering, Lean-Rust enum correspondence check. | `rust/sele4n-types/tests/` | Small |
| T1-I | M-TST-1 | Register `OperationChainSuite` as a `lean_exe` target in `lakefile.toml`. Add the executable to `test_smoke.sh` so it runs as part of the standard test pipeline. | `lakefile.toml`, `scripts/test_smoke.sh` | Trivial |
| T1-J | M-TST-1 | **(Requires T1-I)** Run `OperationChainSuite` end-to-end and verify all test cases pass. Fix any failures discovered now that the suite actually executes. | `tests/OperationChainSuite.lean` | Small |

---

### Phase T2 — Model & CDT Integrity (v0.20.1)

**Scope**: Strengthen model-layer type safety and invariant coverage. Make the
CDT constructor private, add missing invariant fields to frozen state, bundle
storeObject preservation, and close capabilityRefs proof gaps.

**Rationale**: Model-layer changes affect every downstream subsystem. Completing
these changes early (T2) before proof threading (T4, T5) prevents cascading
rework. The CDT constructor bypass (H-2) is the most structurally impactful:
making it private forces all CDT mutations through verified operations, closing
a class of potential soundness gaps.

**Dependencies**: T1 (frozen IPC fixes may affect frozen state structure).

**Gate**: `test_full.sh` passes. All new theorems compile with `lake build
<Module.Path>`. Zero `sorry`/`axiom`. Every structural type change has at least
one downstream consumer verified.

**Sub-tasks (12):**

**Intra-phase ordering constraints:**
- CDT chain: T2-B → T2-C (constructor before smart constructor)
- Frozen chain: T2-D → T2-E → T2-F (field before transfer before proof)
- InvExt chain: T2-H → T2-I (filter before fold)
- Independent: T2-A, T2-G, T2-J, T2-K, T2-L have no intra-phase deps

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T2-A | H-1 | Add `AccessRightSet.ofList_valid` theorem: prove that `(ofList rs).valid` holds for all `rs : List AccessRight`. The proof should follow from `ofList` using bitwise OR of valid single-right values, each of which is < 2^5. | `SeLe4n/Model/Object/Types.lean` | Small |
| T2-B | H-2 | Make `CapDerivationTree` structure constructor `private`. This prevents external code from directly constructing CDT values with inconsistent `edges`/`childMap`/`parentMap` fields. All existing construction must go through verified operations. | `SeLe4n/Model/Object/Structures.lean` | Small |
| T2-C | H-2 | **(Requires T2-B)** Add `CapDerivationTree.empty` smart constructor with well-formedness proof obligation. Provide `CapDerivationTree.mk_checked` that requires `cdtMapsConsistent` witness. Update all construction sites (Builder, test fixtures) to use the verified constructors. | `SeLe4n/Model/Object/Structures.lean`, `SeLe4n/Model/Builder.lean`, `SeLe4n/Testing/StateBuilder.lean` | Medium |
| T2-D | M-NEW-1 | Add `tlb : TlbState` field to `FrozenSystemState` structure. This mirrors the `SystemState.tlb` field (State.lean:241) that is currently dropped during freeze. | `SeLe4n/Model/FrozenState.lean` | Small |
| T2-E | M-NEW-1 | **(Requires T2-D)** Update the `freeze` function to transfer `TlbState` from `IntermediateState` to `FrozenSystemState`. The TLB state is immutable (no frozen TLB operations), so transfer is a direct field copy. | `SeLe4n/Model/FrozenState.lean` | Small |
| T2-F | M-NEW-1 | **(Requires T2-E)** Add freeze-correctness theorem for TLB: `freeze_tlb_equiv : (freeze is).tlb = is.state.tlb`. Follow the pattern of existing per-field FreezeProofs (12 existing). | `SeLe4n/Model/FreezeProofs.lean` | Small |
| T2-G | M-NEW-2 | Add bundled `storeObject_preserves_allTablesInvExt` theorem. This composes the existing 16+ component preservation proofs (objects, objectIndex, objectIndexSet, lifecycle.objectTypes, lifecycle.capabilityRefs, asidTable, etc.) into a single theorem that callers can invoke instead of manually composing. | `SeLe4n/Model/State.lean` | Medium |
| T2-H | M-NEW-3 | Add `capabilityRefs_filter_preserves_invExt` proof: when `storeObject` filters out old CNode references via `RHTable.filter`, the resulting table's `invExt` invariant is preserved. Requires showing that filtering entries preserves the well-formedness of the underlying hash table. | `SeLe4n/Model/State.lean` | Medium |
| T2-I | M-NEW-3 | **(Requires T2-H)** Add `capabilityRefs_fold_preserves_invExt` proof: when `storeObject` inserts new CNode references via `fold`, the resulting table's `invExt` invariant is preserved. Requires showing that sequential `insert` operations on a well-formed table maintain well-formedness. | `SeLe4n/Model/State.lean` | Medium |
| T2-J | L-NEW-4 | Add `guardValue < 2^guardWidth` constraint to `CNode.wellFormed` predicate (or create it if absent). Add validation in `lifecycleRetypeObject` when constructing CNode objects. Prove that `resolveSlot` returns `none` for guards violating the bound. | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| T2-K | M-BLD-1 | Fix `Builder.createObject` to update `objectIndex` and `objectIndexSet` alongside `objects` table insertion. Verify that `IntermediateState` invariant witnesses still hold after the fix. | `SeLe4n/Model/Builder.lean` | Small |
| T2-L | M-ST-2 | Document `attachSlotToCdtNode` stale-link cleanup ordering rationale. Add inline documentation explaining why the current ordering (remove old link before inserting new link) is correct despite appearing fragile. Reference the CDT consistency invariant from WS-S S3-A. | `SeLe4n/Model/State.lean` | Trivial |

---

### Phase T3 — Rust ABI Hardening (v0.20.2)

**Scope**: Harden all Rust ABI boundary validation. Add missing bounds checks,
strict boolean parsing, and crate-level unsafe denial.

**Rationale**: The Rust ABI layer is the first code that touches raw register
values from userspace. Validation gaps here allow malformed data to propagate
into the kernel. While the Lean model validates at the kernel boundary, the
Rust layer should reject obviously invalid inputs at the earliest possible
point to provide defense-in-depth.

**Dependencies**: T1 (KernelError variants must exist for new error paths).

**Gate**: All Rust tests pass (`cargo test --workspace`). Encode/decode roundtrip
tests cover all new validation. Zero `unsafe` outside `svc #0`.

**Sub-tasks (8):**

**Intra-phase ordering constraints:**
- MessageInfo chain: T3-A → T3-B
- VSpace chain: T3-C → T3-D
- Service chain: T3-E → T3-F
- T3-G and T3-H are independent of all other tasks

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T3-A | M-NEW-9 | Add 55-bit bound check to `MessageInfo::encode()`. If `self.label >= (1u64 << 55)`, return `Err(InvalidMessageInfo)` instead of silently truncating. Update `encode` return type from `u64` to `Result<u64, KernelError>`. | `rust/sele4n-abi/src/message_info.rs` | Small |
| T3-B | M-NEW-9 | **(Requires T3-A)** Add MessageInfo label roundtrip conformance test: verify that `encode(decode(x)) == x` for boundary values (0, 2^55 - 1) and that `encode` returns error for 2^55 and u64::MAX. | `rust/sele4n-abi/tests/` | Small |
| T3-C | M-NEW-10 | Validate `VSpaceMapArgs.perms` at ABI decode boundary. Add a `PagePerms::try_from(u64)` validation in the `decode` method. Return `InvalidArgument` error for values outside the valid permission range. | `rust/sele4n-abi/src/args/vspace.rs` | Small |
| T3-D | M-NEW-10 | **(Requires T3-C)** Add VSpaceMapArgs perms roundtrip conformance test: verify valid permission values roundtrip correctly and invalid values (e.g., 0xFF) are rejected at decode. | `rust/sele4n-abi/tests/` | Small |
| T3-E | M-NEW-11 | Change `ServiceRegisterArgs` `requires_grant` decode from `regs[4] != 0` to `regs[4] == 1`, with `regs[4] > 1` returning `InvalidArgument` error. This prevents corrupted register contents from being silently accepted. | `rust/sele4n-abi/src/args/service.rs` | Small |
| T3-F | M-NEW-11 | **(Requires T3-E)** Add ServiceRegisterArgs conformance test: verify that `regs[4] = 0` decodes to `false`, `regs[4] = 1` decodes to `true`, and values 2, 0xFFFFFFFFFFFFFFFF are rejected. | `rust/sele4n-abi/tests/` | Small |
| T3-G | — | Add `#![deny(unsafe_code)]` crate-level attribute to `sele4n-abi`. Add a targeted `#[allow(unsafe_code)]` on the single `raw_syscall` function in `trap.rs` that contains the `svc #0` instruction. This ensures any new unsafe is rejected. | `rust/sele4n-abi/src/lib.rs`, `rust/sele4n-abi/src/trap.rs` | Small |
| T3-H | — | Run `cargo test --workspace` and verify all existing + new tests pass. Document any test infrastructure changes needed for the new `Result`-returning APIs. | `rust/` | Small |

---

### Phase T4 — IPC & Capability Proof Closure (v0.20.3)

**Scope**: Close all identified gaps in the IPC and capability proof chains.
Add missing preservation theorems for compound operations, prove BFS fuel
sufficiency, and complete RadixTree bridge equivalence.

**Rationale**: The IPC subsystem (12,424 lines) is the largest and most complex.
Its proof surface has structural gaps: `ipcInvariantFull` postconditions for
compound operations are externalized (callers supply 3 of 4 components), and
`WithCaps` wrappers lack any preservation proofs. These gaps create seams where
invariant violations could go undetected. Closing them makes the IPC proof
chain end-to-end compositional.

**Dependencies**: T2 (model type changes must be settled before proof threading).

**Gate**: `test_full.sh` passes. All new theorems compile with `lake build
<Module.Path>`. Zero `sorry`/`axiom`. Each new theorem has at least one
downstream consumer or is a terminal proof in the invariant chain.

**Sub-tasks (12):**

**Intra-phase ordering constraints:**
- IPC queue chain: T4-A → T4-B → T4-C (each builds on prior proof infrastructure)
- WithCaps chain: T4-E → T4-F (send before receive, shared proof structure)
- Independent: T4-D, T4-G, T4-H, T4-I, T4-J, T4-K, T4-L

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T4-A | M-IPC-1 | Prove `endpointCall_preserves_ipcStateQueueConsistent`. The call operation modifies both sender TCB (blocked) and endpoint queue (enqueue). Must show the queue-state consistency predicate holds across both mutations. | `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` | Medium |
| T4-B | M-IPC-1 | **(Requires T4-A)** Prove `endpointReplyRecv_preserves_ipcStateQueueConsistent`. The ReplyRecv operation dequeues a waiter, sends a reply, and re-blocks the replier. Must compose dequeue + state-change + re-enqueue preservations. | `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` | Medium |
| T4-C | M-IPC-1 | Prove `notificationSignal_preserves_ipcStateQueueConsistent` and `notificationWait_preserves_ipcStateQueueConsistent`. Notification operations modify waiting thread lists; must show these do not violate endpoint queue consistency. | `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` | Medium |
| T4-D | M-IPC-2 | Prove `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant`. The dual-queue removal operation must maintain the invariant that no thread appears in both send and receive queues simultaneously. | `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` | Medium |
| T4-E | M-IPC-3 | Prove `endpointSendWithCaps_preserves_ipcInvariantFull`. The WithCaps wrapper adds capability transfer to the base send operation. Must show that cap transfer (grant-gated) preserves all 4 components of `ipcInvariantFull`. | `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` | Large |
| T4-F | M-IPC-3 | **(Requires T4-E, shared proof infrastructure)** Prove `endpointReceiveWithCaps_preserves_ipcInvariantFull`. Same structure as T4-E but for the receive path. Can reuse capability-transfer lemmas from T4-E. | `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` | Medium |
| T4-G | M-CAP-2 | Prove `descendantsOf_fuel_sufficiency`: given a well-formed CDT with `n` nodes, `descendantsOf` with fuel `n` returns all descendants. This requires showing the BFS terminates within `n` steps because the CDT is acyclic and has at most `n` nodes. | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Medium |
| T4-H | M-CAP-1 | Document `cspaceMutate` badge override CDT tracking design. Add inline documentation explaining that badge mutation via `Mutate` is intentionally not tracked in the CDT (matching seL4 semantics). The badge is part of the capability *value*, not the derivation *relationship*. Reference the seL4 spec's `CNode_Mutate` semantics. | `SeLe4n/Kernel/Capability/Operations.lean` | Trivial |
| T4-I | M-DS-3 | Prove RadixTree bridge bidirectional lookup equivalence: `buildCNodeRadix_lookup_equiv` showing that `CNodeRadix.lookup k = RHTable.get k` for all keys after construction. This closes the deferred Q6-B proof. | `SeLe4n/Kernel/RadixTree/Bridge.lean` | Medium |
| T4-J | M-IF-3 | Document NI complex IPC projection hypothesis rationale. Add documentation at `nonInterference_ipc_complex` explaining that the projection hypothesis is unavoidable without a concrete `MemoryDomainOwnership` configuration, and that the hypothesis is discharged when the platform binding provides ownership. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | Small |
| T4-K | L-P10 | Add `ipcInvariantFull_compositional` helper: a convenience theorem that takes all 4 component proofs and produces the full bundle. This reduces boilerplate for callers that must compose the invariant manually. | `SeLe4n/Kernel/IPC/Invariant/Structural.lean` | Small |
| T4-L | M-SCH-1 | Prove `runQueueInsert_preserves_maxPriority_consistency`: after inserting a thread into a run queue, `maxPriority` is the maximum of the old `maxPriority` and the inserted thread's priority. | `SeLe4n/Kernel/Scheduler/RunQueue.lean` | Small |

---

### Phase T5 — Lifecycle, Service & Cross-Subsystem (v0.20.4)

**Scope**: Harden lifecycle retype safety, fix service graph cleanup, and
extend cross-subsystem invariants to cover notification references.

**Rationale**: The lifecycle subsystem exposes public retype functions that
bypass cleanup and scrubbing (M-NEW-4). Making these private or annotated
prevents misuse by future code. Object well-formedness validation (M-NEW-5)
prevents constructing invalid kernel objects. The cross-subsystem invariant
gap (L-NEW-3) means deleted TCB IDs can persist in notification wait lists
without detection.

**Dependencies**: T2 (CNode well-formedness from T2-J affects retype),
T4 (IPC proof infrastructure supports cross-subsystem proofs).

**Gate**: `test_full.sh` passes. All new theorems compile. Cross-subsystem
invariant includes notification predicate. Zero `sorry`/`axiom`.

**Sub-tasks (13):**

**Intra-phase ordering constraints:**
- Retype chain: T5-A/B → T5-C → T5-D (visibility before predicate before validation)
- Cross-subsystem chain: T5-H → T5-I → T5-J (predicate before extension before proof)
- Service chain: T5-F → T5-G (cleanup before invariant)
- Independent: T5-E, T5-K, T5-L, T5-M

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T5-A | M-NEW-4 | Make `lifecycleRetypeObject` `private` or add `@[deprecated "Use lifecycleRetypeWithCleanup instead"]` annotation. The function is an internal building block that skips `lifecyclePreRetypeCleanup` and `scrubObjectMemory`. External callers must use `lifecycleRetypeWithCleanup`. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| T5-B | M-NEW-4 | Make `lifecycleRetypeDirect` `private` or add safety annotation. Same rationale as T5-A — this function takes a pre-resolved `Capability` and bypasses cleanup. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| T5-C | M-NEW-5 | Define `KernelObject.wellFormed` predicate: for TCBs, `cspaceRoot` and `vspaceRoot` must reference valid object IDs; for CNodes, `guardValue < 2^guardWidth` (from T2-J); for VSpaceRoots, ASID must be valid. The predicate is parameterized by the current object store. | `SeLe4n/Model/Object/Structures.lean` or `Types.lean` | Medium |
| T5-D | M-NEW-5 | **(Requires T5-C)** Add `KernelObject.wellFormed` check in `lifecycleRetypeWithCleanup`. Return `invalidArgument` error if the new object fails well-formedness. Alternatively, document that the API layer (register decode + typed argument construction) is responsible for producing well-formed objects, and add a proof that the API layer satisfies this obligation. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Medium |
| T5-E | M-LCS-1 | Fix intrusive queue cleanup to handle mid-queue node links. Currently `cleanupIntrusive` only adjusts head/tail pointers. When a TCB is deleted, its `queueNext`/`queuePrev` links must be patched: the predecessor's `queueNext` must point to the successor, and vice versa. Add the mid-queue splice operation. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Medium |
| T5-F | L-NEW-1 | Add `removeDependenciesOf` call in `cleanupEndpointServiceRegistrations`. After filtering out registrations for the deleted endpoint, also remove all dependency edges that reference those services. This prevents orphaned edges in the service dependency graph. | `SeLe4n/Kernel/Service/Registry.lean` | Small |
| T5-G | L-NEW-2 | **(Requires T5-F)** Add `cleanupEndpointServiceRegistrations_preserves_registryEndpointValid` theorem. Prove that after filtering registrations by endpoint ID, remaining registrations still have valid endpoint references. | `SeLe4n/Kernel/Service/Invariant/Policy.lean` | Medium |
| T5-H | L-NEW-3 | Define `noStaleNotificationWaitReferences` predicate in CrossSubsystem: for every notification object, every `ThreadId` in `waitingThreads` references an existing TCB in the object store. Follow the pattern of `noStaleEndpointQueueReferences`. | `SeLe4n/Kernel/CrossSubsystem.lean` | Small |
| T5-I | M-CS-1 | **(Requires T5-H)** Extend `noStaleEndpointQueueReferences` to check interior queue members, not just head/tail. The current predicate misses mid-queue references. Change from checking `head`/`tail` to checking all threads reachable via `queueNext` traversal. | `SeLe4n/Kernel/CrossSubsystem.lean` | Medium |
| T5-J | L-NEW-3 | **(Requires T5-H, T5-I)** Add `noStaleNotificationWaitReferences` to `crossSubsystemInvariant` conjunction. Prove that `deleteObject` preserves the extended invariant (deleted TCB IDs are removed from notification wait lists). | `SeLe4n/Kernel/CrossSubsystem.lean` | Medium |
| T5-K | M-LCS-2 | Document `lookupServiceByCap` first-match semantics. Add inline documentation explaining that `fold` iteration order is deterministic for `RHTable` (insertion order within probe chains), and that the first-match convention is intentional for service resolution. | `SeLe4n/Kernel/Service/Registry.lean` | Trivial |
| T5-L | M-MOD-6 | Document `Notification.waitingThreads` LIFO semantics. Add inline documentation at the `waitingThreads : List ThreadId` field explaining that `List.cons` prepend creates LIFO ordering, matching seL4's notification wait semantics. Note the performance implication (O(n) scan for specific thread removal). | `SeLe4n/Model/Object/Types.lean` | Trivial |
| T5-M | M-SCH-3 | Prove `threadPriority_membership_consistent`: if a thread has `membership = some rqId`, then `rqId.threads` contains the thread with the matching priority. This closes the gap where the consistency is an external hypothesis. | `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | Medium |

---

### Phase T6 — Architecture & Hardware Preparation (v0.20.5)

**Scope**: Address all architecture-layer and platform-layer findings that
affect hardware-binding readiness. Change VSpace defaults, add MMIO and cache
coherency modeling, wire information-flow-checked dispatch, and design targeted
TLB flushes.

**Rationale**: The RPi5 hardware binding (next major milestone) requires formal
modeling of MMIO access, memory barriers, and TLB management. The current model
lacks all three. Additionally, the API dispatch layer bypasses policy-checked
wrappers (M-IF-1), meaning information-flow enforcement is proof-level only —
the runtime dispatch path uses unchecked operations. Fixing this before hardware
binding ensures the runtime path matches the proven model.

**Dependencies**: T5 (lifecycle safety settled), T4 (IPC proofs complete for
cross-subsystem composition).

**Gate**: `test_full.sh` passes. RPi5 platform binding compiles with
`lake build SeLe4n.Platform.RPi5.Contract`. All VSpace operations use typed
`PagePermissions`. Zero `sorry`/`axiom`.

**Sub-tasks (13):**

**Intra-phase ordering constraints:**
- VSpace perms chain: T6-A → T6-B (default change before caller update)
- MMIO chain: T6-E → T6-F (operations before contract)
- Cache chain: T6-G → T6-H (assumptions before model)
- IF dispatch chain: T6-I → T6-J (wrappers before proof)
- Independent: T6-C/D, T6-K, T6-L, T6-M

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T6-A | M-NEW-6 | Change `vspaceMapPage` default `perms` parameter from `default` (which may include write) to `PagePermissions.readOnly`. This enforces least-privilege: callers must explicitly request write or execute permissions. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Small |
| T6-B | M-NEW-6 | **(Requires T6-A)** Update all callers of `vspaceMapPage` that rely on the default parameter to explicitly specify permissions. Audit `MainTraceHarness.lean`, `API.lean` dispatch, and test suites. Verify each caller's intended permission level. | `SeLe4n/Testing/MainTraceHarness.lean`, `SeLe4n/Kernel/API.lean`, test files | Small |
| T6-C | M-ARCH-1 | Change `SyscallArgDecode.lean` to decode `VSpaceMapArgs.perms` as `PagePermissions` type instead of raw `Nat`. Add a `PagePermissions.ofNat?` partial function that returns `none` for invalid permission values. Wire through `dispatchSyscall`. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Medium |
| T6-D | M-ARCH-1 | **(Related to T6-C)** Add validation failure path: when `PagePermissions.ofNat?` returns `none`, the syscall returns `invalidArgument` error. Verify the error propagates correctly through the dispatch chain. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, `SeLe4n/Kernel/API.lean` | Small |
| T6-E | M-NEW-7 | Define MMIO adapter operations for device-region access. Create `MmioOp` inductive (read32, write32, read64, write64) with address and value fields. Define `mmioRead`/`mmioWrite` functions in the kernel monad with device-region validation (address must be in a `.device` memory region). | `SeLe4n/Platform/RPi5/MmioAdapter.lean` (new file) | Medium |
| T6-F | M-NEW-7 | **(Requires T6-E)** Extend RPi5 runtime contract `memoryAccessAllowed` to include MMIO device regions via the adapter. Add `mmioAccessAllowed` contract field that gates MMIO operations on region kind (`.device`). Update `PlatformBinding` instance. | `SeLe4n/Platform/RPi5/RuntimeContract.lean`, `SeLe4n/Platform/RPi5/Contract.lean` | Medium |
| T6-G | M-NEW-8 | Document cache coherency assumptions for ARM64 single-core RPi5. Create an explicit assumptions section in `docs/spec/SELE4N_SPEC.md` documenting: (1) single-core assumption eliminates most coherency concerns, (2) MMIO access still requires barriers (DMB/DSB/ISB), (3) DMA coherency is out of scope until multicore support. | `docs/spec/SELE4N_SPEC.md` | Small |
| T6-H | M-NEW-8 | **(Requires T6-G)** Add memory barrier modeling for MMIO operations. Define `MemoryBarrier` inductive (DMB, DSB, ISB) and `barrierBefore`/`barrierAfter` fields on `MmioOp`. The MMIO adapter (T6-E) must emit appropriate barriers. This is a modeling-only change — no runtime code generation yet. | `SeLe4n/Platform/RPi5/MmioAdapter.lean` | Medium |
| T6-I | M-IF-1 | Wire information-flow-policy-checked wrappers into `dispatchWithCap`. Replace the 14 unchecked operation calls in `dispatchWithCap` with their `Enforcement/Wrappers.lean` equivalents. Each wrapper validates that the caller's security label has `flowsTo` authorization before executing. | `SeLe4n/Kernel/API.lean` | Medium |
| T6-J | M-IF-1 | **(Requires T6-I)** Add non-interference preservation proof for checked dispatch: `syscallEntry_preserves_nonInterference_checked`. This proves that the checked dispatch path maintains NI, closing the gap where the unchecked path was used at runtime but only the checked path was proven. | `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` | Large |
| T6-K | H-3 | Implement context-switch-aware adapter stub for RPi5 register-write preservation. Define `RegisterWriteInvariant` predicate capturing which registers must be preserved across context switches. Add stub implementation that the hardware-binding phase (WS-U) will fill in with actual ARM64 context-switch code. | `SeLe4n/Platform/RPi5/RuntimeContract.lean` | Medium |
| T6-L | M-ARCH-4 | Design targeted TLB flush operations. Define `tlbFlushByASID`, `tlbFlushByPage`, and `tlbFlushByASIDPage` alongside existing `tlbFlushAll`. Add TLB invariant preservation proofs for each. Mark `tlbFlushAll` as the conservative fallback. Do not yet migrate callers (that is hardware-binding work). | `SeLe4n/Kernel/Architecture/VSpace.lean`, `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` | Medium |
| T6-M | M-ARCH-2 | Implement DTB parsing foundation. Extend the existing `parseDTB` stub to handle a minimal flattened device tree (FDT) structure: parse the FDT header, extract memory regions and their kinds. Return `Option PlatformConfig` with populated memory map. This enables future hardware bring-up without hardcoded addresses. | `SeLe4n/Platform/RPi5/Board.lean` | Large |

---

### Phase T7 — Test Coverage & Build Infrastructure (v0.20.6)

**Scope**: Expand test coverage for undertested subsystems (FrozenOps, CDT,
syscall dispatch), fix test harness issues, and harden the build pipeline.

**Rationale**: The deep-dive audit identified four significant testing gaps:
(1) zero test coverage for FrozenOps, (2) no CDT cascade beyond 2 levels,
(3) syscall dispatch tested for only 3 of 14 variants, and (4) the main trace
harness tests pre-state invariants instead of post-mutation state. Additionally,
the build infrastructure has supply-chain concerns (unverified toolchain
download) and a temp-file race condition.

**Dependencies**: T5 (lifecycle changes affect test states), T1 (frozen IPC
fixes must be exercised). Can run in parallel with T6 on disjoint file sets.

**Gate**: All test suites pass. `test_full.sh` green. `cargo test --workspace`
green. Pre-commit hook uses secure temp files. Toolchain SHA verification
integrated.

**Sub-tasks (12):**

**Intra-phase ordering constraints:**
- Harness chain: T7-A → T7-B → T7-J (buildChecked before invariants before fixture)
- Syscall coverage: T7-C is independent
- FrozenOps suite: T7-D → T7-F (suite before enqueue tests)
- Build infra: T7-G, T7-H, T7-I are all independent
- CDT test: T7-E is independent

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T7-A | M-TST-2 | Migrate `MainTraceHarness` from `.build` (unchecked) to `.buildChecked`. The unchecked builder skips `IntermediateState` invariant validation. Replace all `StateBuilder.build` calls with `StateBuilder.buildChecked`, handling the `Option` return. States that fail validation indicate test setup bugs. | `SeLe4n/Testing/MainTraceHarness.lean` | Medium |
| T7-B | M-TST-3 | **(Requires T7-A)** Fix trace harness invariant checks to test mutated intermediate states, not just the original `st1`. After each kernel operation, check `schedulerInvariantBundleFull`, `capabilityInvariantBundle`, and `crossSubsystemInvariant` on the result state. | `SeLe4n/Testing/MainTraceHarness.lean` | Medium |
| T7-C | M-TST-4 | Add syscall dispatch tests for remaining 11 variants. Currently tested: `Send`, `Recv`, `Call`. Missing: `Reply`, `ReplyRecv`, `Yield`, `NBSend`, `NBRecv`, `NotificationSignal`, `NotificationWait`, `CNodeMint`, `CNodeDelete`, `CNodeRevoke`, `Retype`. Add one end-to-end `syscallEntry` → `dispatchSyscall` test per missing variant. | `tests/OperationChainSuite.lean` or new test file | Large |
| T7-D | L-P01 | Create `FrozenOpsSuite` test file. Add tests for: `frozenSchedule`, `frozenNotificationSignal`/`Wait`, `frozenCspaceLookup`/`Mint`/`Delete`, `frozenVspaceLookup`, `frozenLookupServiceByCap`. Each test builds a frozen state from `IntermediateState`, executes the frozen operation, and verifies the result. | `tests/FrozenOpsSuite.lean` | Large |
| T7-E | L-P02 | Add deep CDT cascade test (3+ levels). Construct a capability derivation tree with root → child → grandchild → great-grandchild. Test `revokeCap` at the root level and verify all descendants are revoked. Test `deleteObject` at mid-tree and verify sub-tree cleanup. | `tests/OperationChainSuite.lean` | Medium |
| T7-F | M-FRZ-1/2/3 | **(Requires T7-D)** Add frozen IPC queue enqueue test cases to `FrozenOpsSuite`. Test: (1) `frozenEndpointSend` with no receiver — verify sender is enqueued in `sendQ`, (2) `frozenEndpointReceive` with no sender — verify receiver in `receiveQ`, (3) `frozenEndpointCall` — verify caller in `sendQ`. | `tests/FrozenOpsSuite.lean` | Medium |
| T7-G | M-NEW-12 | Replace pre-commit hook's PID-based temp file (`/tmp/lake-precommit-$$.log`) with `$(mktemp)`. Update the trap/cleanup handler to remove the mktemp-generated file on exit. This eliminates the symlink race condition. | `scripts/pre-commit-lean-build.sh` | Trivial |
| T7-H | M-NEW-13 | Add SHA-256 verification for Lean toolchain download in `setup_lean_env.sh`. Pin the expected hash for the v4.28.0 toolchain archive. After download, compute `sha256sum` and compare. Abort with clear error message on mismatch. Document hash update procedure for toolchain upgrades. | `scripts/setup_lean_env.sh` | Small |
| T7-I | L-P03 | Add Rust test stage to CI pipeline. The current CI skips Rust tests (exit cleanly). Add a `cargo test --workspace` step in the appropriate CI workflow, gated on Rust source changes. | `.github/workflows/` (CI config) | Small |
| T7-J | M-TST-2/3 | **(Requires T7-A/B)** Update `tests/fixtures/main_trace_smoke.expected` if trace output changes due to `.buildChecked` migration or invariant-check additions. Document rationale for fixture changes per WS-S S2-D. | `tests/fixtures/main_trace_smoke.expected` | Small |
| T7-K | L-P06/P07 | Add edge-case scheduler tests: (1) `handleYield` with empty run queue, (2) IRQ handler dispatch. Both are untested paths identified by the predecessor audit. | `tests/OperationChainSuite.lean` or `tests/NegativeStateSuite.lean` | Small |
| T7-L | L-P08 | Add boot sequence test. Exercise `Platform/Boot.lean` `bootKernel` function: construct a `PlatformConfig`, run boot, verify all 4 `IntermediateState` invariant witnesses are satisfied. | `tests/` (new or existing) | Medium |

---

### Phase T8 — Documentation & Closure (v0.20.7)

**Scope**: Final documentation synchronization, comprehensive verification
pass, workstream closure, and production of the WS-T closure report.

**Rationale**: Every prior phase introduces code, proof, type, and behavioral
changes that require documentation updates. This phase consolidates all
documentation work, runs the full test suite at all tiers, verifies zero
sorry/axiom, and produces the formal closure report.

**Dependencies**: All prior phases (T1–T7).

**Gate**: `test_full.sh` passes. `test_nightly.sh` passes. All documentation
files synchronized. Zero `sorry`/`axiom`. Website link manifest verified.
Cargo test suite passes.

**Sub-tasks (14):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| T8-A | — | Synchronize `README.md` metrics from `docs/codebase_map.json`. Update Lean file count, theorem count, proof line count to reflect WS-T additions. | `README.md` | Small |
| T8-B | — | Update `docs/spec/SELE4N_SPEC.md` with all spec changes from T1–T7: MMIO adapter specification (T6-E/F), cache coherency assumptions (T6-G), VSpace permission defaults (T6-A), object well-formedness predicates (T5-C), CNode guard bounds (T2-J), frozen IPC queue semantics (T1-A). | `docs/spec/SELE4N_SPEC.md` | Medium |
| T8-C | — | Update `docs/DEVELOPMENT.md` with new testing practices: FrozenOps test suite usage, .buildChecked migration rationale, syscall dispatch test patterns, CI Rust test stage. | `docs/DEVELOPMENT.md` | Small |
| T8-D | — | Update `docs/CLAIM_EVIDENCE_INDEX.md` with new claims from WS-T: frozen IPC queue enqueue correctness, CDT constructor access control, storeObject bundled preservation, notification stale reference detection, object well-formedness validation, MMIO adapter formal model. | `docs/CLAIM_EVIDENCE_INDEX.md` | Small |
| T8-E | — | Update `docs/WORKSTREAM_HISTORY.md` with WS-T summary (8 phases, 88 sub-tasks, version range v0.20.0–v0.20.7). Include finding coverage metrics and key outcomes. | `docs/WORKSTREAM_HISTORY.md` | Small |
| T8-F | — | Regenerate `docs/codebase_map.json` to reflect new and modified Lean source files from WS-T. | `docs/codebase_map.json` | Trivial |
| T8-G | — | Update affected GitBook chapters to mirror canonical doc changes. Priority chapters: proof-and-invariant-map (chapter 12), hardware-binding (RPi5 MMIO), information-flow (checked dispatch). | `docs/gitbook/*.md` | Medium |
| T8-H | — | Verify `scripts/website_link_manifest.txt` — ensure no protected paths were renamed or removed during WS-T. Run `scripts/check_website_links.sh`. | `scripts/website_link_manifest.txt` | Trivial |
| T8-I | — | Run `test_full.sh` end-to-end validation. Capture and archive results. All 4 test tiers must pass. | scripts | Small |
| T8-J | — | Run `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` — full nightly validation including experimental checks. | scripts | Small |
| T8-K | — | Run `cargo test --workspace`. Verify all Rust tests pass including new ABI validation tests (T3), KernelError roundtrip tests (T1), and CI integration. | `rust/` | Small |
| T8-L | — | Final `sorry`/`axiom` scan across entire codebase. Verify zero sorry, zero axiom in production Lean. Document any new `native_decide` usages with rationale. | all `.lean` files | Trivial |
| T8-M | — | Update `CHANGELOG.md` with WS-T release notes for v0.20.0–v0.20.7. Include: frozen IPC queue fix, Rust ABI hardening, model integrity improvements, MMIO adapter, checked dispatch, test coverage expansion. | `CHANGELOG.md` | Small |
| T8-N | — | Produce WS-T closure report summarizing: all remediated findings (88 sub-tasks across 4 HIGH + 52 MEDIUM + 16 LOW), test results, residual items deferred to WS-U (hardware binding), and final codebase metrics. | `docs/dev_history/audits/WS_T_CLOSURE_REPORT.md` | Medium |

---

## 6. Scope Summary

### Sub-task Count by Phase

| Phase | Version | Sub-tasks | Estimated Complexity |
|-------|---------|-----------|---------------------|
| T1 — Benchmarking Blockers | v0.20.0 | 10 | Medium |
| T2 — Model & CDT Integrity | v0.20.1 | 12 | Medium |
| T3 — Rust ABI Hardening | v0.20.2 | 8 | Small–Medium |
| T4 — IPC & Capability Proof Closure | v0.20.3 | 12 | Large |
| T5 — Lifecycle, Service & Cross-Subsystem | v0.20.4 | 13 | Medium–Large |
| T6 — Architecture & Hardware Preparation | v0.20.5 | 13 | Large |
| T7 — Test Coverage & Build Infrastructure | v0.20.6 | 12 | Medium–Large |
| T8 — Documentation & Closure | v0.20.7 | 14 | Small–Medium |
| **Total** | | **94** | |

### Finding Coverage

| Severity | Total (deduplicated) | Addressed in WS-T | Deferred | Coverage |
|----------|---------------------|-------------------|----------|----------|
| High | 4 | 4 | 0 | 100% |
| Medium | 52 | 52 | 0 | 100% |
| Low | 56 | 16 | 40 | 29% |
| Info | 97+ | 0 (observational) | 97+ | N/A |

Note: All 4 HIGH and all 52 MEDIUM findings are addressed — either through
code/proof changes or explicit documentation of design-intentional behavior.
The 16 selected LOW findings were chosen for security relevance, proof chain
completeness, and test coverage gaps. The remaining 40 LOW findings are
observational or represent future-work opportunities (see Section 8).

### Files Impacted by Phase

| Phase | Lean Files Modified | Rust Files Modified | Script/Doc Files |
|-------|--------------------|--------------------|-----------------|
| T1 | ~4 | ~2 | ~2 |
| T2 | ~5 | 0 | 0 |
| T3 | 0 | ~5 | 0 |
| T4 | ~8 | 0 | 0 |
| T5 | ~7 | 0 | 0 |
| T6 | ~8 | 0 | ~2 |
| T7 | ~6 | 0 | ~5 |
| T8 | 0 | 0 | ~12 |

---

## 7. Risk Assessment

### Technical Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| CDT constructor privatization (T2-B/C) cascades through Builder, StateBuilder, and test fixtures | Medium | Medium — many construction sites to update | T2-C provides `mk_checked` and `empty` smart constructors; migrate one file at a time |
| `frozenQueuePushTail` (T1-A) introduces new FrozenMap mutations that interact with existing commutativity proofs | Medium | Medium — may require updating frame lemmas | T1-E is dedicated to proving preservation; limit PushTail to endpoint objects only |
| IPC `WithCaps` wrapper preservation proofs (T4-E/F) may require deep understanding of cap transfer semantics | Medium | High — IPC is the largest subsystem | Break into lemmas: (1) base op preserves, (2) cap transfer preserves, (3) compose |
| `dispatchWithCap` checked wrapper migration (T6-I) changes 14 dispatch arms simultaneously | Low | High — any arm regression affects all syscalls | Migrate one arm at a time, running `test_smoke.sh` after each. Keep unchecked fallback until all arms verified |
| `storeObject` bundled preservation (T2-G) requires composing 16+ individual proofs | Medium | Medium — proof may be complex but each component exists | Start with explicit `And.intro` composition; refactor to tactic-based later if needed |
| `lifecycleRetypeObject` privatization (T5-A/B) may break internal callers | Low | Low — all production callers use `WithCleanup` wrapper | Grep for all call sites before privatizing; leave `@[deprecated]` if internal use remains |
| MMIO adapter (T6-E/F/H) introduces new platform abstraction layer | Low | Medium — must integrate with existing PlatformBinding typeclass | Start with RPi5-specific implementation; generalize to typeclass in WS-U |
| DTB parsing (T6-M) scope may expand beyond minimal FDT header parsing | Medium | Medium — full DTB parsing is a large task | Scope to header + memory regions only; defer /chosen, /interrupts, /cpu nodes to WS-U |
| Cross-subsystem invariant extension (T5-H/I/J) requires updating all invariant composition sites | Low | Medium — composition is conjunction-based, so adding a conjunct is mechanical | T5-J is scoped to `crossSubsystemInvariant` only; downstream composition proofs propagate automatically if the invariant is threaded correctly |

### Schedule Risks

| Risk | Mitigation |
|------|------------|
| T4 (IPC proofs) takes longer than estimated due to compound operation complexity | T5 and T6 cannot start until T4 completes; buffer by allowing T3 (Rust) and T7 (testing) to proceed in parallel |
| T6 (architecture) reveals new model–hardware gaps during MMIO/barrier modeling | T6 includes documentation sub-tasks (T6-G) that discover gaps early; defer unplanned gaps to WS-U |
| T7 (test coverage) uncovers latent bugs in frozen operations or syscall dispatch | Re-enter T1 or relevant phase for bug fixes; T7 is intentionally late to catch regressions from earlier phases |
| Documentation drift during multi-phase work | T8 is dedicated to synchronization; intermediate phases include doc stubs where relevant |

---

## 8. Deferred Findings

### Deferred Low Findings (40)

The following Low findings from the predecessor audit are **not addressed** in
WS-T. They are either purely informational, already documented, represent
future-work opportunities, or have negligible impact on correctness or security.

| Category | Count | Description | Reason for Deferral |
|----------|-------|-------------|---------------------|
| Performance documentation | ~8 | O(n) operations in RunQueue, TlbState, noOverlapAux, RHTable; O(capacity) recomputeMaxPriority | Acceptable for target system (<256 threads). Performance benchmarking (WS-U) will validate. |
| Type-level alternatives | ~6 | RegisterFile array vs function, List vs intrusive queue for notifications, Array Nat vs Array RegValue | Model-level abstractions; hardware binding provides concrete types. Addressed by S4 items in WS-S or deferred. |
| Proof tactic improvements | ~5 | Case-enumeration proofs, verbose capability proofs, tactic automation | Correct as-is; automation is nice-to-have. |
| Documentation-only | ~8 | CPtr resolution path documentation, memory projection documentation, EDF tie-breaking FIFO, allocate prepend convention | Several already documented in WS-S; remainder are informational. |
| Design-intentional | ~6 | `cspaceCopy` full authority propagation, integrity write-up direction, `insertNoResize` fuel exhaustion, notification LIFO | Matches seL4 semantics; documented, not "bugs." |
| Hardware-binding scope | ~4 | Memory map 4GB-only, high peripheral window, timer rollover, alignment faults | Correctly scoped for current target; generalization is WS-U work. |
| Rust cosmetic | ~3 | Panic handler bare loop, `#[must_use]` coverage, test helper duplication | Low impact; address opportunistically. |

### Deferred Info Findings (97+)

All Info findings are observational — they document positive security
properties, implementation choices, and architecture notes. No action required.
Key positive findings are highlighted in the audit reports' subsystem summaries.

### Findings Addressed by Documentation (Design-Intentional)

The following MEDIUM findings are addressed through documentation rather than
code changes, because they reflect deliberate design choices matching seL4:

| ID | Documentation Action | Phase |
|----|---------------------|-------|
| M-IF-2 | Already documented as deliberate design. No additional action. | N/A |
| M-CAP-1 | Document badge-CDT independence rationale (T4-H) | T4 |
| M-DS-1 | Already mitigated by KMap invariant. Document in spec (T8-B). | T8 |
| M-DS-2 | Safe under WF invariant. Document in spec (T8-B). | T8 |
| M-LCS-2 | Document first-match semantics (T5-K) | T5 |
| M-MOD-6 | Document LIFO semantics (T5-L) | T5 |
| M-SCH-2 | Document O(capacity) cost and bound (T8-B) | T8 |
| M-ST-1 | Document O(n) CNode store cost and bound (T8-B) | T8 |
| M-ST-2 | Document cleanup ordering rationale (T2-L) | T2 |

---

## 9. Workstream Naming Convention

This workstream is designated **WS-T** (following the alphabetical sequence
after WS-S). The "T" can be read as "Thorough" — thorough remediation of the
deep-dive audit findings, strengthening every layer from model integrity to
hardware readiness.

| Workstream | Focus | Version Range |
|------------|-------|---------------|
| WS-S | Pre-Benchmark Strengthening | v0.19.0–v0.19.6 |
| **WS-T** | **Deep-Dive Audit Remediation** | **v0.20.0–v0.20.7** |
| WS-U (future) | Raspberry Pi 5 Hardware Binding | v0.21.0+ |

---

## 10. Acceptance Criteria

WS-T is complete when all of the following hold:

1. **All 4 HIGH findings remediated** — `AccessRightSet.ofList` has `valid`
   postcondition, CDT constructor is private with verified smart constructors,
   RPi5 register-write adapter defined, Rust `KernelError` has all 38 variants.
2. **All 52 MEDIUM findings remediated** — each finding either fixed in code/
   proof or documented with explicit rationale (for design-intentional findings).
3. **16 selected LOW findings remediated** — per sub-task specifications.
4. **Frozen IPC queue semantics correct** — `frozenQueuePushTail` implemented,
   all three frozen endpoint operations enqueue blocked threads, preservation
   proofs complete, test coverage in place.
5. **Rust ABI boundary validated** — MessageInfo label bounds, VSpaceMapArgs
   perms validated, ServiceRegister bool strict, all roundtrip tests passing.
6. **Information-flow dispatch checked** — `dispatchWithCap` uses policy-checked
   wrappers for all 14 syscall arms, with NI preservation proof.
7. **Cross-subsystem invariant complete** — notification stale references
   detected, endpoint queue interior members checked.
8. **MMIO adapter modeled** — device-region access operations defined with
   memory barrier support, RPi5 contract updated.
9. **Zero `sorry`/`axiom` in production Lean** — full codebase scan clean.
10. **Zero `unsafe` Rust** — outside `svc #0` in `trap.rs`.
11. **`test_full.sh` passes** — all 4 test tiers green.
12. **`test_nightly.sh` passes** — including experimental checks.
13. **All Rust tests pass** — `cargo test --workspace` green.
14. **FrozenOps test suite exists and passes** — non-trivial coverage of frozen
    operations including IPC queue enqueue.
15. **Syscall dispatch pipeline tested** — 14 of 14 variants exercised end-to-end.
16. **Documentation synchronized** — README, spec, development guide, claims
    index, workstream history, GitBook chapters all updated.
17. **Website links verified** — manifest check passes.
18. **Build infrastructure hardened** — pre-commit uses secure temp files,
    toolchain download SHA-verified, Rust tests in CI.
19. **Closure report produced** — comprehensive summary of remediation status.

---

## Appendix A: Finding Cross-Reference Matrix

This matrix maps each audit finding to its phase, sub-task(s), and source.

### HIGH Findings

| Finding | Phase | Sub-task(s) | Source Audit |
|---------|-------|-------------|-------------|
| H-1 | T2 | T2-A | Predecessor |
| H-2 | T2 | T2-B, T2-C | Predecessor |
| H-3 | T6 | T6-K | Predecessor |
| H-4 | T1 | T1-F, T1-G, T1-H | Deep-Dive (elevated from M-RUST-1) |

### MEDIUM Findings — Frozen IPC

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-FRZ-1 | T1 | T1-A, T1-B, T1-E |
| M-FRZ-2 | T1 | T1-A, T1-C, T1-E |
| M-FRZ-3 | T1 | T1-A, T1-D, T1-E |

### MEDIUM Findings — IPC Proof Coverage

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-IPC-1 | T4 | T4-A, T4-B, T4-C |
| M-IPC-2 | T4 | T4-D |
| M-IPC-3 | T4 | T4-E, T4-F |

### MEDIUM Findings — Model & State

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-MOD-1 | Deferred | — (WS-U hardware binding) |
| M-MOD-2 | Deferred | — (WS-U hardware binding) |
| M-MOD-3 | Deferred | — (timer rollover in 10,825 years) |
| M-MOD-6 | T5 | T5-L (documentation) |
| M-BLD-1 | T2 | T2-K |
| M-ST-1 | T8 | T8-B (documentation) |
| M-ST-2 | T2 | T2-L (documentation) |
| M-NEW-1 | T2 | T2-D, T2-E, T2-F |
| M-NEW-2 | T2 | T2-G |
| M-NEW-3 | T2 | T2-H, T2-I |

### MEDIUM Findings — Scheduler

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-SCH-1 | T4 | T4-L |
| M-SCH-2 | T8 | T8-B (documentation) |
| M-SCH-3 | T5 | T5-M |

### MEDIUM Findings — Capability & Data Structures

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-CAP-1 | T4 | T4-H (documentation) |
| M-CAP-2 | T4 | T4-G |
| M-CAP-3 | Deferred | — (matches seL4 design) |
| M-DS-1 | T8 | T8-B (documentation, mitigated by KMap) |
| M-DS-2 | T8 | T8-B (documentation, safe under WF) |
| M-DS-3 | T4 | T4-I |

### MEDIUM Findings — Lifecycle & Service

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-LCS-1 | T5 | T5-E |
| M-LCS-2 | T5 | T5-K (documentation) |
| M-NEW-4 | T5 | T5-A, T5-B |
| M-NEW-5 | T5 | T5-C, T5-D |

### MEDIUM Findings — Architecture & Platform

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-ARCH-1 | T6 | T6-C, T6-D |
| M-ARCH-2 | T6 | T6-M |
| M-ARCH-3 | Deferred | — (addressed in WS-S S6-G) |
| M-ARCH-4 | T6 | T6-L |
| M-NEW-6 | T6 | T6-A, T6-B |
| M-NEW-7 | T6 | T6-E, T6-F |
| M-NEW-8 | T6 | T6-G, T6-H |
| M-CS-1 | T5 | T5-I |

### MEDIUM Findings — InformationFlow & Cross-Subsystem

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-IF-1 | T6 | T6-I, T6-J |
| M-IF-2 | Deferred | — (documented deliberate design) |
| M-IF-3 | T4 | T4-J (documentation) |

### MEDIUM Findings — Rust ABI

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-RUST-1 | T1 | → H-4 (elevated) |
| M-NEW-9 | T3 | T3-A, T3-B |
| M-NEW-10 | T3 | T3-C, T3-D |
| M-NEW-11 | T3 | T3-E, T3-F |

### MEDIUM Findings — Testing & Build

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| M-TST-1 | T1 | T1-I, T1-J |
| M-TST-2 | T7 | T7-A |
| M-TST-3 | T7 | T7-B |
| M-TST-4 | T7 | T7-C |
| M-NEW-12 | T7 | T7-G |
| M-NEW-13 | T7 | T7-H |

### LOW Findings (Selected)

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| L-NEW-1 | T5 | T5-F |
| L-NEW-2 | T5 | T5-G |
| L-NEW-3 | T5 | T5-H, T5-J |
| L-NEW-4 | T2 | T2-J |
| L-P01 | T7 | T7-D |
| L-P02 | T7 | T7-E |
| L-P03 | T7 | T7-I |
| L-P04 | Deferred | — (API completeness, future work) |
| L-P05 | Deferred | — (documentation, low priority) |
| L-P06 | T7 | T7-K |
| L-P07 | T7 | T7-K |
| L-P08 | T7 | T7-L |
| L-P09 | Deferred | — (test coverage, low priority) |
| L-P10 | T4 | T4-K |
| L-P11 | Deferred | — (documentation, low priority) |
| L-P12 | Deferred | — (documentation, low priority) |

---

## Appendix B: Deferred MEDIUM Finding Notes

### M-MOD-1 — Unbounded Nat Identifiers

Finding M-MOD-1 (unbounded `Nat` identifiers lack `isWord64` validity
predicates) is classified as Medium but represents a pervasive cross-cutting
change. Adding `isWord64` constraints to `ObjId`, `ThreadId`, `CPtr`, `Slot`,
and `DomainId` would require updating:

1. Every constructor call site (~200+ occurrences)
2. Every proof that deconstructs these types (~100+ theorems)
3. The entire test infrastructure (all fixture construction)

This is more appropriately scoped as part of the hardware binding workstream
(WS-U), where concrete 64-bit types replace `Nat` throughout the model. Adding
predicates now without enforcing them at construction time provides limited
value — the same gap exists with `isWord64` as a side predicate vs. a refined
type.

### M-MOD-2 — zeroMemoryRange Precondition

Finding M-MOD-2 (`zeroMemoryRange` lacks overflow precondition) is deferred
because the current model's `Memory := PAddr → UInt8` function type cannot
overflow — `PAddr` is `Nat`. The precondition becomes relevant only when the
model is lowered to 64-bit address arithmetic during hardware binding (WS-U).

### M-MOD-3 — Timer Wrap-Around

Finding M-MOD-3 (timer unbounded) is deferred because the RPi5's 54 MHz timer
wraps at ~10,825 years. Modeling wrap-around is correct-in-principle but has
zero practical impact for the initial hardware binding target. Defer to WS-U
if multicore or long-running server workloads are targeted.

### M-CAP-3 — cspaceCopy Full Authority

Finding M-CAP-3 (`cspaceCopy` propagates full authority without attenuation) is
deferred because this exactly matches seL4's `CNode_Copy` semantics. The
`cspaceMint` operation provides attenuation; `cspaceCopy` is intentionally
authority-preserving. This is documented in the seL4 specification and the
seLe4n spec mirrors it faithfully.

### M-IF-2 — Integrity Write-Up Direction

Finding M-IF-2 (integrity allows untrusted-to-trusted write-up) is deferred
because this is a documented, deliberate design choice. The seLe4n information
flow model provides both the write-up direction (matching seL4's integrity
policy) and a `bibaPolicy` alternative that enforces strict Biba no-write-up.
The choice is configuration-level, not a defect.

### M-ARCH-3 — BCM2712 Address Validation

Finding M-ARCH-3 (BCM2712 addresses based on partial datasheet) was addressed
in WS-S phase S6-G, which cross-referenced every address against the datasheet
and added verification comments. No additional action needed in WS-T.

---

**End of WS-T Workstream Plan**

*Author: Claude Opus 4.6 | Date: 2026-03-23 | Baseline: seLe4n v0.19.6*
*Source audits: AUDIT_COMPREHENSIVE_v0.19.6_DEEP_DIVE.md,
AUDIT_COMPREHENSIVE_v0.19.6_FULL_KERNEL_RUST.md*
