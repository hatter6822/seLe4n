# Workstream History

This document is the canonical record of all completed and planned workstreams
for the seLe4n project. It consolidates workstream information that was
previously spread across README.md, GitBook chapters, and audit plans.

## How to use this document

- **New contributors**: skim the "What's next" section to understand current
  priorities, then jump to the linked audit plans for details.
- **Returning contributors**: check "What's next" for the current slice, then
  review the completed workstream closest to your area of interest.
- **Auditors**: use the portfolio table as a traceability index linking each
  workstream to its version, scope, and evidence.

## What's next

### WS-R workstream (Comprehensive Audit Remediation) — IN PROGRESS

WS-R is the **active** workstream (v0.18.0+), addressing all 82 findings from the
comprehensive pre-release audit (`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`).
8 phases (R1–R8), 111 sub-tasks. See
[`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).

- **R1 (v0.18.0) — COMPLETE**: Pre-release blockers. Fixed Rust `Cap::downgrade()`
  rights bypass (H-01), AccessRights/PagePerms silent truncation (R-M01, R-M02),
  SyscallResponse semantic overlap (R-M03), api* wrapper capability-target bypass
  (M-04), frozen context save/restore silent failures (M-10, M-11). All 14 api*
  wrappers deprecated with validation guards.
- **R2 (v0.18.1) — COMPLETE**: Capability & CDT hardening. Fixed `processRevokeNode`
  error swallowing (M-06) — revocation now propagates `cspaceDeleteSlot` errors
  instead of silently dropping them. Fixed `streamingRevokeBFS` fuel exhaustion
  (M-05) — returns `.error .resourceExhausted` instead of `.ok`. Added
  `resourceExhausted` to `KernelError`. Updated all preservation proofs for new
  `Except` return types. Added `isAncestor` decidable predicate for CDT cycle
  detection (M-08). Existing `removeNode_parentMapConsistent` proof covers CDT
  remove consistency (M-07). Added `processRevokeNode_lenient` deprecated variant
  for backward compatibility. Added revocation error propagation test cases.
- **R3 (v0.18.2) — COMPLETE**: IPC invariant completion. Fixed `notificationSignal`
  badge delivery gap (M-16) — woken thread now receives signaled badge via
  `storeTcbIpcStateAndMessage`; badge delivery verified by chain22 test.
  Internalized `ipcInvariantFull` preservation hypotheses (M-18) — notification
  operations and `endpointReply` now have self-contained preservation theorems
  with zero externalized hypotheses. Added `notificationWaiterConsistent`
  preservation infrastructure (M-19). IpcMessage structural bounds (L-05)
  already addressed by existing `bounded` predicate. Removed
  `set_option linter.all false` from Structural.lean (L-08). Added
  `removeNode_childMapConsistent` proof closing the CDT childMap consistency gap.
- **R4–R8**: Pending. See workstream plan for details.

### WS-Q1 workstream (Service Interface Simplification)

WS-Q1 is a **completed** workstream (v0.17.7), the first phase of WS-Q (Kernel
State Architecture). It simplifies the service subsystem from a lifecycle-based
model (`serviceStart`/`serviceStop`/`serviceRestart` with `ServiceStatus` and
`ServiceConfig`) to a stateless registry model where services are registered
entries with identity, dependencies, and isolation edges — no running/stopped
state. Key changes:

- **Removed**: `ServiceStatus` enum, `ServiceConfig` structure, `ServicePolicy`
  type, `serviceStart`/`serviceStop`/`serviceRestart` transitions,
  `serviceRestartChecked` enforcement wrapper, associated NI proofs
- **Simplified**: `ServiceGraphEntry.status` field removed; `SyscallId`
  renumbered (14 valid IDs, 0..13); `projectServicePresence` replaces
  `projectServiceStatus` (returns `Bool` instead of `Option ServiceStatus`)
- **Added (WS-Q1)**: `registerServiceChecked` policy-gated enforcement wrapper,
  `ServiceRegisterArgs`/`ServiceRevokeArgs`/`ServiceQueryArgs` decode structures
  in `SyscallArgDecode.lean`, `dispatchWithCap` service syscalls use decoded MR
  arguments, SRG-001 through SRG-010 test scenarios
- **Preserved**: `serviceRegisterDependency`, `serviceHasPathTo`,
  `hasIsolationEdge`, `lookupService`, `storeServiceEntry` — all graph
  invariants and acyclicity proofs intact
- **Test migration**: All trace harnesses, negative-state tests, information
  flow tests, operation chain tests updated; fixture files synchronized
- **Proof surface**: Zero sorry, all invariant preservation theorems intact,
  enforcement boundary updated: 3 policy-gated in base, 7 in extended (WS-Q1: `registerServiceChecked` added)

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q2 workstream (Universal RHTable Migration)

WS-Q2 is a **completed** workstream (v0.17.8), the second phase of WS-Q (Kernel
State Architecture). It replaces every `Std.HashMap` and `Std.HashSet` in kernel
state with the formally verified `RHTable`/`RHSet` (Robin Hood hash table from
WS-N), establishing the builder-phase representation for the two-phase state
architecture. Scope: 16 map fields + 2 set fields across 6 structures, 30+ files
modified, 10 atomic subphases. Key changes:

- **Q2-A**: Prelude lemma foundation — `RHTable` equivalents for all 28
  `Std.HashMap` utility lemmas used by downstream proofs (re-exported from
  Bridge.lean with `[simp]` attributes)
- **Q2-B**: `RHSet` type definition — newtype wrapper around `RHTable κ Unit`
  with 14 bridge lemmas (`contains`, `insert`, `erase`, `membership`, `invExt`
  preservation), `Inhabited`/`BEq`/`Membership`/`EmptyCollection` instances,
  `ofList` constructor
- **Q2-C**: Core SystemState maps + object store (atomic group A) — `objects`,
  `objectIndexSet`, `lifecycle.objectTypes`, `lifecycle.capabilityRefs`,
  `asidTable` migrated to `RHTable`/`RHSet`; `storeObject` rewritten;
  `invExt` threading through all state-modifying operations
- **Q2-D**: Per-object maps — `VSpaceRoot.mappings` migrated to `RHTable`
- **Q2-E**: IRQ handler map — `irqHandlers` migrated to `RHTable`
- **Q2-F**: CDT maps (atomic group B) — `cdt.childMap`, `cdt.parentMap`,
  `cdtSlotNode`, `cdtNodeSlot` migrated to `RHTable`
- **Q2-G**: RunQueue internals (atomic group C) — `byPriority`,
  `threadPriority` migrated to `RHTable`; `membership` migrated to `RHSet`
- **Q2-H**: Service maps — `services`, `interfaceRegistry`, `serviceRegistry`
  migrated to `RHTable`
- **Q2-I**: Elimination verification — zero state-persistent `Std.HashMap`/
  `Std.HashSet` remaining (algorithm-local uses permitted in Acyclicity.lean,
  Projection.lean, Service/Operations.lean)
- **Q2-J**: `allTablesInvExt` predicate — global well-formedness condition
  asserting all 16 RHTable/RHSet fields satisfy `invExt`; proven for default
  state via `default_allTablesInvExt`
- **invExt threading**: Every theorem calling a state-modifying bridge lemma
  (`storeObject_*`, `storeTcbIpcState_*`, `endpointQueuePopHead_*`, etc.)
  gained an `hObjInv : st.objects.invExt` parameter, cascading across
  EndpointPreservation (~25 theorems), NotificationPreservation (~67 fixes),
  CallReplyRecv (~72 fixes), Structural (~103 fixes), Capability Preservation,
  Authority, Defs, Policy, Acyclicity, Architecture Invariant, and all
  InformationFlow invariant files
- **Proof patterns**: `HashMap_getElem?_empty` → `RHTable_get?_empty 16 (by omega)`;
  `HashMap_getElem?_insert` → `simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert]`;
  `.fold` → `.toList.foldl` (universe constraint workaround)
- **Test migration**: NegativeStateSuite, TraceSequenceProbe updated to use
  `RHTable`/`RHSet` constructors; all test suites pass
- **Proof surface**: Zero sorry, 1,459 proved declarations, 168 build jobs

### WS-Q3 workstream (IntermediateState Formalization)

WS-Q3 is a **completed** workstream (v0.17.9), the third phase of WS-Q (Kernel
State Architecture). It defines the `IntermediateState` type — a wrapper around
`SystemState` that carries four machine-checked invariant witnesses — and
implements builder operations that construct valid intermediate states during
boot. Key changes:

- **Q3-A**: `IntermediateState` type in `SeLe4n/Model/IntermediateState.lean` —
  bundles `SystemState` with `allTablesInvExt`, `perObjectSlotsInvariant`,
  `perObjectMappingsInvariant`, `lifecycleMetadataConsistent` witnesses.
  `mkEmptyIntermediateState` constructor with `mkEmptyIntermediateState_valid` proof.
  Named predicates `perObjectSlotsInvariant`, `perObjectMappingsInvariant` with
  default-state theorems.
- **Q3-B**: 7 builder operations in `SeLe4n/Model/Builder.lean`:
  `registerIrq`, `registerService`, `addServiceGraph`, `createObject`,
  `deleteObject`, `insertCap`, `mapPage`. Each carries forward all four
  invariant witnesses through machine-checked proofs. `insertCap` and `mapPage`
  delegate to `createObject` with per-object proof obligations.
  Helper theorem `insert_capacity_ge4` for capacity preservation.
- **Q3-C**: Boot sequence in `SeLe4n/Platform/Boot.lean` — `PlatformConfig`
  type with `IrqEntry` and `ObjectEntry`, `bootFromPlatform` function that
  folds IRQ entries and initial objects through builder operations.
  Master validity theorem `bootFromPlatform_valid` proves the booted state
  satisfies all four IntermediateState invariant witnesses.
  `bootFromPlatform_deterministic` and `bootFromPlatform_empty` properties.
- **Proof surface**: Zero sorry, all three modules compile independently via
  `lake build SeLe4n.Model.IntermediateState`, `lake build SeLe4n.Model.Builder`,
  `lake build SeLe4n.Platform.Boot`. All test tiers pass.

### WS-Q4 workstream (CNode Radix Tree — Verified)

WS-Q4 is a **completed** workstream (v0.17.10), the fourth phase of WS-Q (Kernel
State Architecture). It implements a verified flat radix tree (`CNodeRadix`) for
CNode capability slot lookups, matching seLe4n's existing bit-sliced addressing
semantics (guard match + radix extraction). The radix tree provides O(1) lookup
with zero hashing — pure bitwise index computation — and will serve as the
frozen-phase CNode representation in Q5. Key changes:

- **Q4-A**: Core types in `SeLe4n/Kernel/RadixTree/Core.lean` — `extractBits`
  bit extraction helper with `extractBits_lt` bound proof, `CNodeRadix` structure
  with `guardWidth`, `guardValue`, `radixWidth`, fixed-size `Array (Option Capability)`
  with `hSlotSize` size proof.
- **Q4-B**: Operations — `CNodeRadix.empty` (O(2^radixWidth) initialization),
  `lookup` (O(1) zero-hash via `extractBits` + direct array index), `insert` (O(1)
  array set), `erase` (O(1) set to `none`), `fold` (O(2^radixWidth) traversal),
  `toList`, `size`, `fanout`.
- **Q4-C**: 24 correctness proofs in `SeLe4n/Kernel/RadixTree/Invariant.lean` —
  lookup roundtrips (`lookup_empty`, `lookup_insert_self`, `lookup_insert_ne`,
  `lookup_erase_self`, `lookup_erase_ne`, `insert_idempotent`), WF preservation
  (`wf_of_mk`, `empty_wf`, `insert_wf`, `erase_wf`), `insert_erase_cancel`,
  parameter preservation (6 theorems for guard/radix width invariance across
  insert/erase), size bounds (`size_empty`, `fanout_eq_slots_size`,
  `size_insert_le`, `size_erase_le`), enumeration (`toList_complete`,
  `toList_noDup`, `fold_visits_all`).
- **Q4-D**: Builder equivalence bridge in `SeLe4n/Kernel/RadixTree/Bridge.lean` —
  `CNodeConfig` type, `buildCNodeRadix` function (RHTable → CNodeRadix via fold),
  `buildCNodeRadix_guardWidth/guardValue/radixWidth` preservation theorems,
  `buildCNodeRadix_wf` well-formedness, `buildCNodeRadix_deterministic`,
  `buildCNodeRadix_empty_lookup` (empty RHTable yields none),
  `UniqueRadixIndices` predicate (Q6-B precondition),
  `CNodeConfig.ofCNode` and `CNodeRadix.ofCNode` convenience constructors,
  `freezeCNodeSlots` with 4 preservation theorems (Q5 integration point).
- **Q4-T**: 12-scenario test suite in `tests/RadixTreeSuite.lean` (43 checks) —
  core operation tests (RT-001 to RT-008) and bridge tests (RT-009 to RT-012).
- **Re-export hub**: `SeLe4n/Kernel/RadixTree.lean` — imports Core, Invariant,
  Bridge for backward-compatible single-import usage.
- **Proof surface**: Zero admitted proofs, all 4 modules compile independently via
  `lake build SeLe4n.Kernel.RadixTree.Core`, etc. All test tiers pass.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q5 workstream (FrozenSystemState + Freeze)

WS-Q5 is a **completed** workstream (v0.17.11), the fifth phase of WS-Q (Kernel
State Architecture). It defines the frozen execution-phase state representation
and implements the `freeze` function that transforms an `IntermediateState`
(builder phase) into a `FrozenSystemState` (execution phase). Key changes:

- **Q5-A**: `FrozenMap` and `FrozenSet` types in `SeLe4n/Model/FrozenState.lean`
  — dense `Array ν` value store + `RHTable κ Nat` index mapping. Runtime
  bounds-checked `get?` (safe-by-construction), `set` (update-only), `contains`,
  `fold` operations. `FrozenSet κ` defined as `FrozenMap κ Unit`.
- **Q5-B**: Per-object frozen types — `FrozenCNode` (uses `CNodeRadix` from Q4
  for O(1) zero-hash slot lookup), `FrozenVSpaceRoot` (uses `FrozenMap` for
  page mappings), `FrozenKernelObject` inductive (6 variants), `FrozenSchedulerState`,
  `FrozenSystemState` (19 fields mirroring `SystemState`).
- **Q5-C**: Freeze functions — `freezeMap` (RHTable → FrozenMap via fold),
  `freezeCNode`, `freezeVSpaceRoot`, `freezeObject` (per-object with CNode→CNodeRadix
  via Q4 bridge), `freezeScheduler`, `freeze` (IntermediateState → FrozenSystemState).
- **Q5-D**: Capacity planning — `minObjectSize` constant, `objectCapacity`
  (current objects + potential from untyped memory).
- **Q5-T**: 15-scenario test suite in `tests/FrozenStateSuite.lean` (49 checks):
  FrozenMap core (FS-001 to FS-007), FrozenKernelObject (FS-008 to FS-010),
  freeze integration (FS-011 to FS-015) including objectIndexSet, scheduler
  freeze, FrozenMap.set size preservation, and data size round-trip.
- **Proof surface**: 20+ theorems including `freeze_deterministic`,
  `freeze_preserves_machine`, `freeze_preserves_objectIndexSet`,
  `freezeMap_empty`, `freezeMap_data_size`, `freezeObject_preserves_type`,
  `freezeObject_tcb_passthrough`, `frozenMap_set_preserves_size`,
  `objectCapacity_ge_size`. Zero admitted proofs, all modules compile independently.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q6 workstream (Freeze Correctness Proofs)

WS-Q6 is a **completed** workstream (v0.17.12), the sixth phase of WS-Q (Kernel
State Architecture). It provides machine-checked proofs that the `freeze`
function preserves lookup semantics, structural properties, and kernel
invariants across the builder→execution phase transition. Key changes:

- **Q6-A**: Core `freezeMap` lookup equivalence — `freezeMap_get?_eq` proves
  `rt.get? k = (freezeMap rt).get? k` for any key `k`. 13 per-field theorems
  (`lookup_freeze_objects`, `lookup_freeze_objectIndexSet`,
  `lookup_freeze_irqHandlers`, etc.) instantiate this
  for every `RHTable` field in `SystemState`. Helper theorems connect
  `RHTable.toList` membership to `get?` results.
- **Q6-B**: CNode radix lookup equivalence — `lookup_freeze_cnode_slots_some`
  and `lookup_freeze_cnode_slots_none` prove that `cn.slots.get? slot` agrees
  with `(freezeCNodeSlots cn).lookup slot` in both directions. Three generic
  helper theorems (`foldl_generic_preserves_lookup`, `foldl_generic_preserves_none`,
  `foldl_generic_establishes_lookup`) work around Lean 4 match compilation
  identity differences by parameterizing over the fold step function.
- **Q6-C**: Structural properties — `freeze_deterministic'` (idempotent output),
  `freezeMap_preserves_size` (data array size = toList length),
  `freezeMap_preserves_membership` (isSome agreement),
  `freezeMap_no_duplicates` (pairwise distinct keys in toList),
  `freezeMap_total_coverage` (every source key has valid data index).
- **Q6-D**: Invariant transfer — `apiInvariantBundle_frozen` (existential
  formulation), `freeze_preserves_invariants` (keystone theorem: builder-phase
  `apiInvariantBundle` → frozen `apiInvariantBundle_frozen`),
  `frozen_lookup_transfer` (enabling lemma for per-invariant transfer proofs).
- **Q6-T**: 22-scenario test suite in `tests/FreezeProofSuite.lean` (60 checks):
  freezeMap lookup (FP-001 to FP-005), per-field lookup (FP-006 to FP-009),
  CNode radix (FP-010 to FP-013), structural properties (FP-014 to FP-018),
  invariant transfer (FP-019 to FP-021).
- **Proof surface**: 30 theorems/definitions in `SeLe4n/Model/FreezeProofs.lean`,
  zero sorry/axiom, all modules compile independently.

### WS-Q7 workstream (Frozen Kernel Operations)

WS-Q7 is a **completed** workstream (v0.17.13), the seventh phase of WS-Q (Kernel
State Architecture). It delivers the execution-phase kernel operations that run
on top of the frozen (immutable key-set) state produced by WS-Q5/Q6. Key changes:

- **Q7-A**: `FrozenKernel` monad (`KernelM FrozenSystemState KernelError`) with
  lookup/store primitives for all 5 object types (TCB, Endpoint, Notification,
  CNode, VSpaceRoot). Scheduler context-switch helpers.
- **Q7-B/C**: 14 per-subsystem frozen operations across 5 subsystems: Scheduler
  (`frozenSchedule`, `frozenHandleYield`, `frozenTimerTick`), IPC
  (`frozenNotificationSignal`, `frozenNotificationWait`, `frozenEndpointSend`,
  `frozenEndpointReceive`, `frozenEndpointCall`, `frozenEndpointReply`),
  Capability (`frozenCspaceLookup`, `frozenCspaceMint`, `frozenCspaceDelete`),
  VSpace (`frozenVspaceLookup`), Service (`frozenLookupServiceByCap`).
- **Q7-D**: FrozenMap set/get? commutativity proofs and structural lemmas.
- **Q7-E**: 18 `frozenStoreObject` frame/preservation theorems.
- **Q7-T**: 15-scenario test suite in `tests/FrozenOpsSuite.lean` covering
  TPH-005 through TPH-014.
- **Proof surface**: Zero sorry/axiom, all modules compile independently.

### WS-Q8 workstream (Rust Syscall Wrappers)

WS-Q8 is a **completed** workstream (v0.17.13), absorbing WS-O (Syscall Rust
Wrappers). It delivers `libsele4n`, a `no_std` Rust userspace library with safe
syscall wrappers for all 14 seLe4n syscalls. Key changes:

- **Q8-A**: `sele4n-types` crate — 14 newtype identifiers (`ObjId`, `ThreadId`,
  `CPtr`, `Slot`, etc.), 34-variant `KernelError` enum, 5-variant `AccessRight`
  enum + `AccessRights` bitmask, 14-variant `SyscallId` enum. Zero `unsafe`,
  `#![no_std]`, zero external dependencies.
- **Q8-B**: `sele4n-abi` crate — `MessageInfo` bitfield encode/decode (seL4
  convention: 7-bit length, 2-bit extraCaps, label), `SyscallRequest`/
  `SyscallResponse` register structures, ARM64 `svc #0` inline asm (the single
  `unsafe` block), per-syscall argument structures (CSpace×4, Lifecycle×1,
  VSpace×2, Service×3), `TypeTag` enum (6 variants), `PagePerms` bitmask with
  W^X enforcement.
- **Q8-C**: `sele4n-sys` crate — safe high-level wrappers: IPC (endpoint
  send/receive/call/reply, notification signal/wait), CSpace (mint/copy/move/
  delete), Lifecycle (retype + convenience constructors), VSpace (map with W^X
  pre-check, unmap), Service (register/revoke/query). Phantom-typed capability
  handles (`Cap<Obj, Rts>`) with sealed traits, rights downgrading.
- **Q8-D**: Conformance tests (RUST-XVAL-001 through RUST-XVAL-019) validating
  register-by-register ABI encoding for all 14 syscalls, notification signal/wait,
  and IPC buffer overflow. `test_rust.sh` CI script integrated into
  `test_smoke.sh` (Tier 2). Lean trace harness extended with XVAL-001 through
  XVAL-004 cross-validation vectors.
- **Proof surface**: Lean side unchanged (zero new sorry/axiom). Rust side:
  64 unit tests + 25 conformance tests across 3 crates.

### WS-Q9 workstream (Integration Testing + Documentation)

WS-Q9 is a **completed** workstream (v0.17.14), the final phase of WS-Q (Kernel
State Architecture). It delivers comprehensive integration testing for the
two-phase builder→freeze→execution pipeline and synchronizes all documentation.
Key changes:

- **Q9-A**: `TwoPhaseArchSuite.lean` — 14 integration tests (41 checks) covering
  TPH-001 (builder pipeline), TPH-003 (freeze populated + lookup equivalence),
  TPH-005 (frozen IPC send/receive/call), TPH-006 (frozen scheduler tick with
  active thread + preemption), TPH-010 (commutativity: builder→freeze =
  freeze→frozen op), TPH-012 (pre-allocated slot retype in frozen state),
  TPH-014 (RunQueue frozen operations: schedule/yield/no-eligible).
- **Q9-B**: Rust conformance tests RUST-XVAL-001 through RUST-XVAL-019 verified
  complete (25 tests in `rust/sele4n-abi/tests/conformance.rs`).
- **Q9-C**: Service interface tests SRG-001 through SRG-010 verified complete
  in `MainTraceHarness.lean`.
- **Q9-D**: Full documentation sync across 15+ files: WORKSTREAM_HISTORY.md,
  SELE4N_SPEC.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, README.md, CLAUDE.md,
  GitBook chapters (architecture, design, spec, proofs), codebase_map.json.
- **Test infrastructure**: New `two_phase_arch_suite` executable registered in
  `lakefile.toml`, integrated into `test_tier2_negative.sh`, scenario registry
  updated with TPH-* entries, fixture file created.
- **Proof surface**: Zero sorry/axiom, all modules compile independently.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9). **WS-Q portfolio is now COMPLETE.**

### WS-N workstream (Robin Hood hashing verified implementation)

WS-N is a **completed** workstream (v0.17.0–v0.17.5), created to close the trust gap
between seLe4n's machine-checked proof surface and the unverified `Std.HashMap`
library type used across 14 production source files (114 occurrences). The
workstream delivers a formally verified Robin Hood hash table implementation
with fuel-bounded recursion (no `partial`), bounds-checked array access (no
`get!`/`set!`), and machine-checked invariant proofs.

WS-N phases N1–N3 were previously attempted and **reverted** (PRs #453–#455)
due to `partial` functions, unsafe array access, missing refinement proofs, and
incorrect cluster-ordering invariants. This re-plan addresses every failure mode
with a single-representation architecture, `Nat`-based bounded recursion, and
per-cluster modular-arithmetic ordering.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-N1** | Core types + operations: `RHEntry`, `RHTable`, `empty`, `insert`, `get?`, `erase`, `fold`, `resize`; fuel-bounded loops, bounds-checked access; `empty_wf` proof | CRITICAL — **COMPLETED** (v0.17.1) |
| **WS-N2** | Invariant proofs: `wf`/`distCorrect`/`noDupKeys`/`probeChainDominant` preservation through insert/erase/resize; lookup soundness + completeness (`get_after_insert_eq`, `get_after_insert_ne`, `get_after_erase_eq`). All 6 TPI-D items completed (D1–D6), ~4,655 LoC, zero sorry | HIGH — **COMPLETED** (v0.17.2) |
| **WS-N3** | Kernel API bridge: `Inhabited`/`BEq` instances, 12 bridge lemmas (`getElem?_*`, `size_*`, `mem_iff_isSome_getElem?`, `fold_eq_slots_foldl`, `size_filter_le_*`), `filter` + `ofList` support, `get_after_erase_ne` proof. ~307 LoC Bridge.lean + ~247 LoC Lookup.lean additions, zero sorry | MEDIUM — **COMPLETED** (v0.17.3) |
| **WS-N4** | Kernel integration (first site): replaced `CNode.slots : Std.HashMap Slot Capability` with `RHTable Slot Capability`; updated CNode operations, ~25 CNode/capability theorems, ~15 invariant proofs across Capability/InformationFlow subsystems, test fixtures; `slotsUnique` repurposed as substantive `invExt` invariant; 3 new bridge lemmas (`filter_fold_absent_by_pred`, `filter_get_pred`, `filter_filter_getElem?`); 20+ files modified | MEDIUM — **COMPLETED** (v0.17.4) |
| **WS-N5** | Test coverage + documentation: `RobinHoodSuite.lean` with 12 standalone tests (RH-001–RH-012: empty table, insert/get, erase, overwrite, multi-key, collision, Robin Hood swap, backward-shift, resize, post-resize, large-scale 200-entry stress, fold/toList) + 6 CNode integration tests (RH-INT-001–RH-INT-006: lookup/insert/remove, revokeTargetLocal, findFirstEmptySlot, slotCountBounded, CSpace resolution, BEq). Full doc sync across 8 canonical files + 4 GitBook chapters. ~300 LoC tests, zero sorry | LOW — **COMPLETED** (v0.17.5) |

See [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: N1 through N5, 122 subtasks).

**WS-N1 (v0.17.1):** Core types + operations — 379 new lines in
`SeLe4n/Kernel/RobinHood/Core.lean` plus re-export hub. Delivers:
- **N1-A:** `RHEntry` (key, value, probe distance), `RHTable` (single-
  representation `Array (Option (RHEntry α β))` with capacity-positivity and
  slots-length invariants), `idealIndex`/`nextIndex` with `@[inline]`,
  `idealIndex_lt`/`nextIndex_lt` bound proofs via `Nat.mod_lt`.
- **N1-B:** `RHTable.empty` constructor, `countOccupied` helper, 4-conjunct
  `RHTable.WF` predicate, `empty_wf` proof (zero sorry).
- **N1-C:** Fuel-bounded `insertLoop` with 5 operational branches (empty slot,
  key match, Robin Hood swap, continue probing, fuel exhausted).
  `insertLoop_preserves_len` proof by induction on fuel.
- **N1-D:** `RHTable.insert` with 75% load-factor resize trigger,
  `insertNoResize_size_le` proof. Full `insert_size_le` deferred to N2
  (requires WF preservation through resize).
- **N1-E:** Fuel-bounded `getLoop` with Robin Hood early termination,
  `RHTable.get?`, `RHTable.contains`.
- **N1-F:** `findLoop` + `backshiftLoop` (backward-shift erasure),
  `backshiftLoop_preserves_len` proof, `RHTable.erase`.
- **N1-G:** `RHTable.fold`, `RHTable.toList`, `RHTable.resize` (double
  capacity, re-insert all), `resize_preserves_len` proof (`slots.size =
  capacity * 2` via `Array.foldl_induction`), `resize_fold_capacity` proof,
  `Membership` instance, `GetElem`/`GetElem?` instances (bracket notation
  `t[k]?`).
- **N1-H:** Re-export hub `SeLe4n/Kernel/RobinHood.lean`.
- Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.

**WS-N2 (v0.17.2):** Invariant proofs — invariant definitions, WF/distCorrect
preservation, modular arithmetic helpers, and lookup correctness foundations.
Delivers:
- **Major finding:** Discovery: `robinHoodOrdered` (non-decreasing dist within
  clusters) is NOT preserved by backshift-on-erase. The `invExt` bundle was
  restructured to use `probeChainDominant` instead, which IS preserved by all
  operations.
- **N2-A:** Invariant definitions in `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`:
  `distCorrect` (probe distance accuracy), `noDupKeys` (key uniqueness),
  `robinHoodOrdered` (non-decreasing cluster distances), `probeChainDominant`
  (replaces `robinHoodOrdered` in `invExt` bundle), `RHTable.invariant`
  (restructured bundle using `probeChainDominant`).
  `empty_distCorrect`, `empty_noDupKeys`, `empty_robinHoodOrdered`,
  `empty_invariant` proofs for empty table.
- **N2-B:** WF preservation in `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`:
  `insertNoResize_preserves_wf`, `insert_preserves_wf`, `resize_preserves_wf`,
  `erase_preserves_wf`. Modular arithmetic helpers: `mod_succ_eq`,
  `dist_step_mod`. `countOccupied_le_size` bound proof.
- **N2-C:** distCorrect preservation: `insertLoop_preserves_distCorrect` (full
  induction proof with modular arithmetic), `insertNoResize_preserves_distCorrect`,
  `insert_preserves_distCorrect`, `resize_preserves_distCorrect` (via fold
  induction).
- **N2-D:** Loop count and correctness: `insertLoop_countOccupied`,
  `backshiftLoop_countOccupied`, `findLoop_lt`, `findLoop_correct`.
- **N2-E:** Bundle preservation theorems: `insert_preserves_invariant`,
  `erase_preserves_invariant`, `resize_preserves_invariant`.
- **N2-F:** Lookup correctness signatures in
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`: `get_after_insert_eq`,
  `get_after_insert_ne`, `get_after_erase_eq`.
- **N2-G:** Re-export hub `SeLe4n/Kernel/RobinHood/Invariant.lean`. Updated
  `SeLe4n/Kernel/RobinHood.lean` to import Invariant module. Changed `private`
  to `protected` for `insertNoResize`, `insertNoResize_capacity`,
  `resize_fold_capacity` in `Core.lean`.
- Files: `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant.lean` (new);
  `SeLe4n/Kernel/RobinHood/Core.lean`, `SeLe4n/Kernel/RobinHood.lean` (modified).
- **N2 additional deliverables:** `noDupKeys_after_clear`,
  `backshiftLoop_preserves_noDupKeys`, `erase_preserves_noDupKeys`,
  `displacement_backward`, `backshiftLoop_preserves_distCorrect`,
  `erase_preserves_distCorrect`.
- Preservation theorems proved: WF (all ops), distCorrect (all ops),
  noDupKeys (all ops), probeChainDominant (all ops). All 6 TPI-D items
  completed with zero sorry.
- **TPI-D1 completed:** `insertLoop_preserves_noDupKeys` — full fuel induction
  proving noDupKeys for insertLoop result (zero sorry).
- **TPI-D2 completed:** `insertLoop_preserves_pcd` — full fuel induction
  proving probeChainDominant for insertLoop result (zero sorry).
- **TPI-D3 completed:** `erase_preserves_probeChainDominant` — relaxedPCD
  framework: clear creates relaxedPCD gap, backshiftStep_relaxedPCD advances
  gap, relaxedPCD_to_pcd_at_termination recovers full PCD when loop terminates
  at empty/dist=0 slot (zero sorry).
- **TPI-D4 completed:** `get_after_insert_eq` — insert lookup correctness via
  `getLoop_finds_present` + `insertLoop_places_key` (zero sorry).
- **TPI-D5 completed:** `get_after_insert_ne` — insert non-interference via
  `insertLoop_absent_ne_key` (none case) + `insertLoop_output_source` +
  `resize_preserves_key_absence` (some case) (zero sorry).
- **TPI-D6 completed:** `get_after_erase_eq` — erase lookup correctness via
  `erase_removes_key` + `getLoop_none_of_absent` (zero sorry).
- Helper infrastructure: `offset_injective` (modular offset injectivity),
  `getElem_idx_eq` (array access proof irrelevance), `carried_key_absent`
  (key absent if probe reached empty/swap position), `getLoop_none_of_absent`
  (if key absent from all slots, getLoop returns none), `displacement_backward`
  (backshift displacement decrement), `relaxedPCD` (gap-excused PCD invariant).
- Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.
- **WS-N2 COMPLETE** — 6/6 TPI-D proofs, ~4,655 LoC across Defs/Preservation/Lookup.

**WS-N4 (v0.17.4):** Kernel integration (first site — CNode.slots) — replaced
`CNode.slots : Std.HashMap Slot Capability` with `RHTable Slot Capability`
across the entire kernel. Delivers:
- **N4-A1/A2:** Type change in `Model/Object/Types.lean` — import
  `SeLe4n.Kernel.RobinHood.Bridge`, CNode.slots field type changed to
  `Kernel.RobinHood.RHTable Slot Capability`.
- **N4-A3:** CNode operations updated in `Model/Object/Structures.lean` —
  `CNode.empty` uses `RHTable.empty 16`, `CNode.mk'` uses `RHTable.ofList`,
  `CNode.lookup`/`insert`/`remove`/`revokeTargetLocal` use RHTable operations,
  `BEq CNode` uses `RHTable.fold`, manual `DecidableEq CNode` instance added,
  `CNode.slotsUnique` repurposed from `True` to substantive invariant
  `cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity`.
- **N4-Bridge:** 3 new bridge lemmas in `Bridge.lean` — `filter_fold_absent_by_pred`
  (predicate-gated fold induction for filter absence), `filter_get_pred`
  (filter lookup implies predicate holds), `filter_filter_getElem?` (filter
  idempotence for projection proofs).
- **N4-Capability:** Invariant updates across `Capability/Invariant/Defs.lean`,
  `Authority.lean`, `Preservation.lean` — `cspaceSlotUnique` propagated as
  theorem parameter where RHTable operations require `invExt`; `remove_slots_sub`,
  `revokeTargetLocal_slots_sub` proofs updated with `change` for `[·]?`/`.get?`
  bridge; `cspaceRevoke_local_target_reduction` rewritten with `filter_get_pred`;
  `cspaceInsertSlot_lookup_eq` simplified with direct bridge lemma application.
- **N4-InformationFlow:** `projectKernelObject_idempotent` updated with
  `slotsUnique` hypothesis, using `filter_filter_getElem?`; `cspaceSlotUnique`
  propagated through `Helpers.lean`, `Operations.lean`, `Composition.lean`.
- **N4-State:** `RHTable.fold` argument-order updates in `State.lean`,
  `Lifecycle/Operations.lean`, `Testing/InvariantChecks.lean`.
- **N4-Tests:** All test files updated — `Std.HashMap.ofList` → `RHTable.ofList`,
  `slots := {}` → `RHTable.empty 16`, fold argument order fixes. Files:
  `MainTraceHarness.lean`, `OperationChainSuite.lean`, `NegativeStateSuite.lean`,
  `InformationFlowSuite.lean`, `TraceSequenceProbe.lean`.
- 20+ files modified. Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.
- **WS-N4 COMPLETE** — CNode.slots fully migrated to verified RHTable.

### WS-M workstream (Capability subsystem audit & remediation)

WS-M is a **completed** workstream portfolio (v0.16.14–v0.17.0), created from a
comprehensive end-to-end audit of the Capability subsystem (3,520 LoC, 5 files).
The audit found zero `sorry`/`axiom`, zero critical vulnerabilities, but
identified 5 performance optimization opportunities, 4 proof strengthening
opportunities, 3 test coverage gaps, and 2 previously deferred items. All 5
phases delivered. All findings resolved.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-M1** | Proof strengthening: guard-match theorem, CDT mint completeness, `addEdge_preserves_edgeWellFounded_fresh`, error-swallowing consistency, docstring updates | HIGH — **COMPLETED** (v0.16.14) |
| **WS-M2** | Performance: fused revoke fold, CDT `parentMap` index, shared reply lemma | HIGH — **COMPLETED** (v0.16.15) |
| **WS-M3** | IPC capability transfer (20 subtasks): `CapTransferResult`/`CapTransferSummary` types, `DerivationOp.ipcTransfer`, `findFirstEmptySlot`, `ipcTransferSingleCap`/`ipcUnwrapCaps`, IPC wrappers, API wiring, 2 test scenarios (resolves L-T03) | MEDIUM — **COMPLETED** (v0.16.17) |
| **WS-M4** | Test coverage (8 subtasks): multi-level resolution edge cases (guard-only, 64-bit max depth, guard mismatch at intermediate level, partial bits, single-level leaf), strict revocation stress (15+ deep chain, partial failure, BFS ordering) | MEDIUM — **COMPLETED** (v0.16.18) |
| **WS-M5** | Streaming BFS revocation (13 subtasks): `streamingRevokeBFS` interleaved BFS loop, `cspaceRevokeCdtStreaming` top-level operation, 3 preservation theorems, `SCN-REVOKE-STREAMING-BFS` test, full documentation sync; v0.17.0 optimization pass | LOW — **COMPLETED** (v0.16.19; optimized v0.17.0) |

See [`AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: M1 through M5).

**WS-M1** (v0.16.14): Proof strengthening & correctness — 10 atomic subtasks.
M1-E: updated `cspaceRevoke` docstring (removed stale scope disclaimer).
M1-A: added `resolveCapAddress_guard_match` forward-direction theorem proving
successful resolution implies guard bits match stored guardValue.
M1-B1: introduced `cdtMintCompleteness` predicate (derived nodes have parent
edges, root nodes are edge-isolated). M1-B2: transfer theorem for state
transitions preserving CDT edges and nodeSlot. M1-B3: extended invariant bundle
`capabilityInvariantBundleWithMintCompleteness` with extraction theorems.
M1-C1: proved `addEdge_preserves_edgeWellFounded_fresh` — CDT acyclicity
preserved for fresh child nodes. M1-C2: `addEdgeWouldBeSafe` runtime check.
M1-D1: `cspaceRevokeCdt_swallowed_error_consistent` — invariant preservation,
object stability, and edge-set monotonicity through error-swallowing path.
M1-D2: enriched `cspaceRevokeCdt` docstring with error-handling rationale.
7 new proved declarations; zero sorry/axiom.

**WS-M2** (v0.16.15): Performance optimization — 3 targeted improvements across
the Capability subsystem hot paths. M2-A: fused `revokeAndClearRefsState` replaces
the prior two-pass revoke pattern (one O(m) traversal to revoke children, then a
second O(m) traversal to clear parent references) with a single O(m) pass that
performs both revocation and reference clearing in one fold over the child set.
M2-B: CDT `parentMap` index added to `CSpaceState` — `parentOf` lookups are now
O(1) instead of scanning the CDT edge set; `removeNode`, `removeAsChild`, and
`removeAsParent` are updated to maintain the index with targeted updates rather
than full rebuilds. M2-C: reply lemma extraction — the proof body for
`endpointReply` preservation is factored into a shared lemma consumed by both
the direct-reply and reply-recv paths, eliminating duplicated proof obligations.
Field preservation lemmas for non-interference proofs added to cover the new
`parentMap` index field. Runtime `parentMapConsistent` check added and verified.
Zero sorry/axiom.

**WS-M3** (v0.16.17): IPC capability transfer — seL4-aligned receive-side cap
unwrapping with Grant-right gate. M3-A: `CapTransferResult`/`CapTransferSummary`
types, `DerivationOp.ipcTransfer` CDT variant. M3-B: `CNode.findFirstEmptySlot`
with structural recursion and correctness theorems. M3-C: `ipcTransferSingleCap`
single-cap transfer with CDT edge tracking and `capabilityInvariantBundle`
preservation proof. M3-D: `ipcUnwrapCaps` batch unwrap with `ipcUnwrapCapsLoop`
recursive helper and scheduler preservation proof by induction;
`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` bundle preservation
when Grant absent. M3-E: `endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
`endpointCallWithCaps` wrapper operations composing existing IPC ops with cap
transfer; IPC invariant preservation proofs for all three wrappers plus
`ipcUnwrapCaps_preserves_ipcInvariant`; `dualQueueSystemInvariant` preservation
for `ipcUnwrapCaps` and both WithCaps wrappers (`ipcUnwrapCaps_preserves_dualQueueSystemInvariant`,
`endpointSendDualWithCaps_preserves_dualQueueSystemInvariant`,
`endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant`);
`ipcUnwrapCaps_preserves_cnode_at_root` CNode type preservation. M3-F: `decodeExtraCapAddrs`,
`resolveExtraCaps`, API dispatch updated to use WithCaps wrappers with renamed
theorems (`dispatchWithCap_send_uses_withCaps`, `dispatchWithCap_call_uses_withCaps`).
M3-G: 4 test scenarios (SCN-IPC-CAP-TRANSFER-BASIC, SCN-IPC-CAP-TRANSFER-NO-GRANT,
SCN-IPC-CAP-TRANSFER-FULL-CNODE, SCN-IPC-CAP-BADGE-COMBINED). Resolves L-T03
(capability transfer during IPC). 12+ new proved declarations; zero sorry/axiom.

**WS-M4** (v0.16.18): Test coverage expansion — 8 atomic subtasks across 2 tasks,
addressing M-T01 (multi-level resolution) and M-T02 (strict revocation).
M4-A: 5 `resolveCapAddress` edge case tests in NegativeStateSuite — guard-only
CNode with zero radixWidth (SCN-RESOLVE-GUARD-ONLY), 64-bit resolution across 8
CNodes (SCN-RESOLVE-MAX-DEPTH), guard mismatch at intermediate level in a 3-level
chain (SCN-RESOLVE-GUARD-MISMATCH-MID), partial bit consumption where
bitsRemaining < guardWidth + radixWidth (SCN-RESOLVE-PARTIAL-BITS), and
single-level leaf resolution (SCN-RESOLVE-SINGLE-LEVEL). M4-B: 3
`cspaceRevokeCdtStrict` stress tests in OperationChainSuite — 15-level deep
derivation chain with full deletion verification (SCN-REVOKE-STRICT-DEEP),
partial failure mid-traversal with corrupted CNode triggering `.objectNotFound`
and `firstFailure` context verification (SCN-REVOKE-STRICT-PARTIAL-FAIL), and
branching tree BFS ordering verification with 5 descendants
(SCN-REVOKE-STRICT-ORDER). 8 new test scenarios; zero sorry/axiom (test-only
phase; no new proof declarations).

**WS-M5** (v0.16.19): Streaming revocation & documentation — 13 atomic subtasks
across 2 tasks, addressing M-P04 (streaming BFS optimization). M5-A:
`streamingRevokeBFS` interleaved BFS loop that processes CDT descendants
on-the-fly instead of materializing the full descendant list upfront, reducing
peak memory from O(N) to O(max branching factor); `cspaceRevokeCdtStreaming`
top-level operation composing `cspaceRevoke` with streaming BFS;
`streamingRevokeBFS_step_preserves` single-step invariant preservation
(same case analysis as `revokeCdtFoldBody_preserves`);
`streamingRevokeBFS_preserves` full induction proof by fuel;
`cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` top-level
preservation composing local revoke with streaming BFS preservation;
`SCN-REVOKE-STREAMING-BFS` test scenario exercising 5-node branching tree
with all descendants deleted, root preserved, CDT nodes detached.
M5-B: version bump to v0.16.19, workstream plan refinement into 13 granular
subtasks, full documentation sync across WORKSTREAM_HISTORY, DEVELOPMENT,
CLAIM_EVIDENCE_INDEX, SELE4N_SPEC, and 7 GitBook chapters; codebase map
regeneration and README metrics sync. 3 new proved declarations; 1 new test
scenario. Zero sorry/axiom. Closes M-P04. **WS-M portfolio fully completed.**

**WS-M5 optimization** (v0.17.0): Extracted `processRevokeNode` shared helper
eliminating code duplication between materialized fold and streaming BFS paths.
Added `processRevokeNode_preserves_capabilityInvariantBundle` shared theorem.
Simplified `streamingRevokeBFS_step_preserves` to one-line delegation. Added 3
new edge case tests: chain19 (empty CDT), chain20 (deep linear chain), chain21
(streaming-vs-materialized equivalence). Zero sorry/axiom.

### WS-L workstream (IPC subsystem audit & remediation)

WS-L is a **completed** workstream portfolio (v0.16.9–v0.16.13), created from a
comprehensive end-to-end audit of the IPC subsystem (9,195 LoC, 12 files). The
audit found zero critical issues, zero sorry/axiom, but identified 3 performance
optimization opportunities, 5 proof strengthening opportunities, and 5 test
coverage gaps. WS-L resolved all deferred WS-I5 items. All 5 phases delivered.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-L1** | IPC performance optimization: eliminate redundant TCB lookups in endpointReceiveDual, endpointReply, notificationWait | HIGH — **COMPLETED** (v0.16.9) |
| **WS-L2** | Code quality: HashMap.fold migration — eliminate all `.toList.foldl/foldr` anti-patterns (closes WS-I5/R-17) | MEDIUM — **COMPLETED** (v0.16.10) |
| **WS-L3** | Proof strengthening: enqueue-dequeue round-trip, queue link integrity, ipcState-queue consistency, tail preservation, reply contract preservation | MEDIUM — **COMPLETED** (v0.16.11) |
| **WS-L4** | Test coverage: ReplyRecv positive-path + rendezvous, endpoint lifecycle with queued threads, blocked thread rejection, multi-endpoint interleaving (3 endpoints) | MEDIUM — **COMPLETED** (v0.16.12) |
| **WS-L5** | Documentation: IF readers' guide, fixture update process, metrics automation, full doc sync (closes WS-I5/R-13/R-14/R-18) | LOW — **COMPLETED** (v0.16.13) |

**WS-L1** (v0.16.9): Eliminated 4 redundant TCB lookups on IPC hot paths.
L1-A: changed `endpointQueuePopHead` return type to `(ThreadId × TCB × SystemState)`,
providing pre-dequeue TCB to callers and eliminating redundant `lookupTcb` in
`endpointReceiveDual`. L1-B: added `storeTcbIpcStateAndMessage_fromTcb` with
equivalence theorem, eliminating redundant lookups in `endpointReply` and
`endpointReplyRecv`. L1-C: added `storeTcbIpcState_fromTcb` with equivalence
theorem, eliminating redundant lookup in `notificationWait`. Added
`lookupTcb_preserved_by_storeObject_notification` helper for cross-store TCB
stability. ~18 mechanical pattern-match updates across 6 invariant files. Zero
sorry/axiom; all proofs machine-checked.

**WS-L2** (v0.16.10): Eliminated all 4 `Std.HashMap.toList.foldl/foldr`
anti-patterns across the codebase. L2-A: migrated 3 fold patterns in
`Testing/InvariantChecks.lean` (`cspaceSlotCoherencyChecks`,
`capabilityRightsStructuralChecks`, `cdtChildMapConsistentCheck`) from
`.toList.foldr` to direct `HashMap.fold`. L2-B: migrated `detachCNodeSlots`
in `Kernel/Lifecycle/Operations.lean` from `.toList.foldl` to `HashMap.fold`,
updated 3 preservation proofs (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`)
using `Std.HashMap.fold_eq_foldl_toList` bridge lemma. Refined WS-L2 workstream
plan with expanded scope covering all 4 sites (original plan only covered 1).
Zero sorry/axiom; all proofs machine-checked.

**WS-L3** (v0.16.11): Proof strengthening for IPC dual-queue subsystem.
L3-A: enqueue-dequeue round-trip theorem — `endpointQueueEnqueue_empty_sets_head`
(postcondition), `endpointQueueEnqueue_empty_queueNext_none` (TCB state),
`endpointQueueEnqueue_then_popHead_succeeds` (composed round-trip).
L3-B: standalone `tcbQueueLinkIntegrity` preservation for popHead and enqueue
(extracted from bundled `dualQueueSystemInvariant`).
L3-C: `ipcStateQueueConsistent` invariant definition (blocked → endpoint exists)
plus queue-operation preservation (popHead, enqueue). Forward endpoint preservation
helpers (`storeTcbQueueLinks_endpoint_forward`, `endpointQueuePopHead_endpoint_forward`,
`endpointQueueEnqueue_endpoint_forward`).
L3-C3: high-level `ipcStateQueueConsistent` preservation for `endpointSendDual`,
`endpointReceiveDual`, `endpointReply` — plus 5 sub-operation helpers
(`ensureRunnable`, `removeRunnable`, `storeTcbIpcStateAndMessage`,
`storeTcbIpcState`, `storeTcbPendingMessage`).
L3-D: tail consistency for `endpointQueueRemoveDual` — non-tail removal preserves
tail (`_preserves_tail_of_nonTail`), tail removal characterization (`_tail_update`).
L3-E: already resolved (pre-existing in `CallReplyRecv.lean:797`).
22 new theorems, 1 new invariant definition. Zero sorry/axiom; all proofs
machine-checked.

**WS-L4** (v0.16.12): IPC test coverage expansion. Filled all 4 test coverage
gaps identified during the IPC subsystem audit: L-T01 (ReplyRecv positive-path),
L-T02 (endpoint lifecycle with queued threads), L-T04 (blocked thread rejection),
L-T05 (multi-endpoint interleaving). 9 new scenario IDs (16 total across L4
test functions), 2 new cross-state blocked-thread rejection tests (L4-C4/C5).
L4-A2: extended `runReplyRecvRoundtripTrace` with second-sender rendezvous
path (RRC-002, RRC-006). L4-B: new `runEndpointLifecycleTrace` validates
graceful-failure-by-guard model when endpoint is retyped while senders are
blocked on sendQ (ELC-001 through ELC-004). L4-D2/D3: extended
`runMultiEndpointInterleavingTrace` from 2 to 3 endpoints with out-of-order
receive and FIFO verification (MEI-004, MEI-005, MEI-006). L-T03 (cap transfer)
intentionally deferred — CSpace IPC integration not yet modeled.

**WS-L5** (v0.16.13): Documentation & workstream closeout. L5-A: added
information-flow architecture readers' guide to `docs/gitbook/12-proof-and-invariant-map.md`
documenting the 3-layer Policy → Enforcement → Invariant architecture with
cross-references to all canonical source files. L5-B/L5-C: test fixture update
process and metrics regeneration documentation delivered early in v0.16.12 (already
present in `docs/DEVELOPMENT.md` §7). L5-D: split into 6 sub-tasks (D1–D6) for
version bump, README/spec sync, DEVELOPMENT.md update, workstream history/claim
evidence, GitBook sync, and test validation. Bumped version to 0.16.13.
Regenerated `docs/codebase_map.json`. Updated metrics across README, SELE4N_SPEC,
and GitBook chapters. Added WS-L3 theorem documentation to GitBook ch.12.
All findings resolved (12/13, 1 intentionally deferred). All 4 WS-I5 deferred
items closed. WS-L portfolio complete.

See [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: L1 through L5).

### Remaining WS-H workstreams

WS-H1..H16 are all completed. No remaining WS-H workstreams.

### WS-F workstreams (F1-F8) — ALL COMPLETED

All WS-F workstreams are completed. The v0.12.2 audit remediation portfolio is
100% closed (33/33 findings). See the
[workstream plan](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium — **COMPLETED** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low — **COMPLETED** |
| **WS-F8** | Cleanup (dead code, dead type constructors, extension labeling) | Low — **COMPLETED** |

### WS-I workstreams (I1-I5) — Improvement recommendations from v0.14.9 audit

The v0.14.9 comprehensive codebase audit identified 18 non-blocking improvement
recommendations across testing, proof quality, documentation, code quality, and
coverage expansion. These are organized into 5 workstreams across 3 phases. See
the [workstream plan](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) for
full details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-I1** | Test infrastructure hardening (inter-transition assertions, determinism promotion, scenario ID traceability) | HIGH — **COMPLETED** (v0.15.0) |
| **WS-I2** | Proof & hygiene strengthening (semantic L-08 validation, Tier 3 correctness anchors, VSpace memory ownership projection) | HIGH — **COMPLETED** (v0.15.1) |
| **WS-I3** | Operations coverage expansion (multi-operation chains, scheduler stress, declassification checks) | MEDIUM — **COMPLETED** (v0.15.2) |
| **WS-I4** | Subsystem coverage expansion (VSpace multi-ASID, IPC interleaving, lifecycle cascading revoke chains) | LOW — **COMPLETED** (v0.15.3) |
| **WS-I5** | Documentation and code-quality polish (remaining low-priority recommendations) | LOW — **SUPERSEDED by WS-L** (all R-12..R-18 items resolved within WS-L) |

### WS-J1 workstream (register-indexed authoritative namespaces)

WS-J1 supersedes the WS-I5 Part A documentation-only treatment of
`RegName`/`RegValue`. A comprehensive audit revealed that bare `Nat`
abbreviations are insufficient: the syscall API bypasses the machine register
file entirely, omitting the decode path where untrusted user-space register
values become trusted kernel references. WS-J1 addresses this by:

1. Replacing `RegName`/`RegValue` with typed wrapper structures.
2. Introducing a `RegisterDecode.lean` module with total, deterministic decode
   functions from raw register words to typed kernel identifiers.
3. Adding `syscallEntry` as a register-sourced syscall dispatch path.
4. Wrapping `CdtNodeId` (secondary bare-Nat alias) for consistency.
5. Proving decode correctness, invariant preservation, and NI properties.

See [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md)
for the full workstream plan (6 phases: J1-A through J1-F).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-J1** | Replace `abbrev Nat` register types with typed wrappers, add syscall argument decode layer bridging machine registers to typed kernel operations, wrap `CdtNodeId`, prove decode correctness and NI | HIGH — **J1-A COMPLETED** (v0.15.4), **J1-B COMPLETED** (v0.15.5), **J1-C COMPLETED** (v0.15.6; audit refinements v0.15.7), **J1-D COMPLETED** (v0.15.8), **J1-E COMPLETED** (v0.15.9), **J1-F COMPLETED** (v0.15.10) — **PORTFOLIO COMPLETE** |

### WS-K workstream (full syscall dispatch completion)

WS-K completed the syscall surface that WS-J1 established. WS-J1 built the
typed register decode layer and 13-case dispatch skeleton, but 7 syscalls
returned `.illegalState` (CSpace mint/copy/move/delete, lifecycle retype,
VSpace map/unmap), 2 service syscalls used `(fun _ => true)` policy stubs,
and IPC messages carried empty register payloads. WS-K addressed all of these:

1. Extending `SyscallDecodeResult` with message register values (x2–x5).
2. Per-syscall argument structures with total decode functions.
3. Full dispatch for all 13 syscalls (zero `.illegalState` stubs).
4. Configuration-sourced service policy replacing permissive stubs.
5. IPC message body population from decoded register contents.
6. Round-trip proofs, NI integration, and deferred proof completion.

See [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md)
for the full workstream plan (8 phases: K-A through K-H).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-K** | Extend `SyscallDecodeResult` with msgRegs, implement per-syscall argument decode, wire all 13 syscalls through dispatch, replace service policy stubs, populate IPC message bodies, prove round-trip correctness and NI, comprehensive testing and documentation | CRITICAL — **K-A COMPLETED** (v0.16.0), **K-B COMPLETED** (v0.16.1), **K-C COMPLETED** (v0.16.2), **K-D COMPLETED** (v0.16.3), **K-E COMPLETED** (v0.16.4), **K-F COMPLETED** (v0.16.5), **K-G COMPLETED** (v0.16.7), **K-H COMPLETED** (v0.16.8) — **PORTFOLIO COMPLETE** |

### Raspberry Pi 5 hardware binding

After the remaining workstreams, the next major milestone is populating the RPi5
platform stubs with hardware-validated contracts:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

### Long-horizon items

- MCS scheduling contexts (budget/period/replenishments).
- Multi-core support (per-core kernel instances).
- Device memory and IOMMU modeling.
- Cryptographic attestation of kernel image.
- Side-channel analysis at hardware binding layer.

## Completed workstream portfolio

| Portfolio | Version | Scope | Workstreams |
|-----------|---------|-------|-------------|
| **WS-M** | v0.16.14–v0.17.0 | Capability subsystem audit & remediation — 5 phases, 55+ subtasks, all 14 audit findings resolved. M1: proof strengthening (guard-match, mint completeness, addEdge acyclicity, error-swallowing consistency). M2: performance optimization (fused revoke, CDT parentMap, shared reply lemma). M3: IPC capability transfer (20 subtasks, resolves L-T03). M4: test coverage expansion (8 edge-case tests). M5: streaming BFS revocation + documentation sync; v0.17.0 optimization (shared `processRevokeNode` helper, 3 new edge case tests). Zero sorry/axiom. | M1–M5 |
| **WS-M2** | v0.16.15 | Capability subsystem performance optimization. M2-A: fused `revokeAndClearRefsState` — single-pass O(m) fold replacing two O(m) passes (revoke children + clear parent references). M2-B: CDT `parentMap` index in `CSpaceState` — O(1) `parentOf` lookup; `removeNode`/`removeAsChild`/`removeAsParent` maintain the index with targeted updates. M2-C: shared reply lemma extraction — factored `endpointReply` preservation proof body consumed by both direct-reply and reply-recv paths. Field preservation lemmas for non-interference proofs added for new `parentMap` field. Runtime `parentMapConsistent` check added and verified. Zero sorry/axiom. | M2 |
| **WS-L** | v0.16.9–v0.16.13 | IPC subsystem audit & remediation — comprehensive end-to-end audit of IPC subsystem (9,195 LoC, 12 files). L1: eliminated 4 redundant TCB lookups on IPC hot paths. L2: HashMap.fold migration (4 sites). L3: 22 new theorems + `ipcStateQueueConsistent` invariant. L4: 16 test scenario IDs, 4 coverage gaps filled. L5: IF readers' guide, version bump, full doc sync. 12/13 findings resolved, 1 deferred (L-T03). All WS-I5 deferred items closed. Zero sorry/axiom. | L1–L5 |
| **WS-K-H** | v0.16.8 | Documentation sync and workstream closeout: updated `WORKSTREAM_HISTORY.md` with WS-K portfolio completion (K-A through K-H, v0.16.0–v0.16.8); updated `SELE4N_SPEC.md` current state snapshot with v0.16.8 version, updated metrics (37,139 production LoC, 4,037 test LoC, 1,198 proved declarations), and WS-K portfolio complete status; updated `DEVELOPMENT.md` active workstream to show WS-K complete, next priority as RPi5 hardware binding; updated `CLAIM_EVIDENCE_INDEX.md` WS-K claim row with comprehensive K-A through K-H deliverables and evidence commands; updated GitBook chapters: `03-architecture-and-module-map.md` (added `SyscallArgDecode.lean` module entry with 7 structures, 7 decode functions, 7 encode functions, 14 theorems), `04-project-design-deep-dive.md` (added section 1.7 documenting two-layer syscall argument decode architecture), `05-specification-and-roadmap.md` (version and roadmap update, WS-K complete, RPi5 next), `12-proof-and-invariant-map.md` (added WS-K proof surface: layer-2 round-trip proofs, delegation theorems, NI coverage extension to 34 constructors); regenerated `docs/codebase_map.json`; synced `README.md` metrics from `readme_sync`; bumped `lakefile.toml` version to 0.16.8; refined WS-K-H workstream plan from 9 flat tasks into 13 granular subtasks (K-H.1 through K-H.13) with dependency ordering, per-file change specifications, and explicit acceptance criteria; updated completion evidence checklist from 5 to 13 K-H items. Zero sorry/axiom. Closes WS-K Phase H. WS-K portfolio fully complete. | K-H |
| **WS-K-G** | v0.16.7 | Lifecycle NI proof completion and deferred proof resolution: added `cspaceRevoke_preserves_projection` standalone theorem in `InformationFlow/Invariant/Operations.lean` extracted from inline proof for compositional reuse; added `lifecycleRevokeDeleteRetype_preserves_projection` theorem chaining projection preservation across `cspaceRevoke`, `cspaceDeleteSlot`, and `lifecycleRetypeObject` sub-operations; added `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem completing the previously deferred `lifecycleRevokeDeleteRetype` NI proof using compositional projection-preservation reasoning; extended `NonInterferenceStep` inductive with `lifecycleRevokeDeleteRetype` constructor (34 constructors total, up from 33); updated `step_preserves_projection` with the new constructor case; updated `syscallNI_coverage_witness` documentation to reflect 34-constructor exhaustive match. Zero sorry/axiom. Closes WS-K Phase G | K-G |
| **WS-K-F** | v0.16.5 | Proofs: round-trip, preservation, and NI integration: added 7 encode functions in `SyscallArgDecode.lean` (`encodeCSpaceMintArgs` through `encodeVSpaceUnmapArgs`) completing encode/decode symmetry for all layer-2 structures; proved 7 round-trip theorems via structure eta reduction (`rcases + rfl`) with `decode_layer2_roundtrip_all` composed conjunction; added `extractMessageRegisters_roundtrip` in `RegisterDecode.lean` closing the layer-1 extraction round-trip gap; added `dispatchWithCap_layer2_decode_pure` proving decode functions depend only on `msgRegs` (two results with same `msgRegs` produce identical decode) and `dispatchWithCap_preservation_composition_witness` structural preservation theorem in `API.lean`; added `retypeFromUntyped_preserves_lowEquivalent` NI theorem completing the last deferred NI proof via two-stage `storeObject_at_unobservable_preserves_lowEquivalent` composition; added `syscallNI_coverage_witness` in `Composition.lean` witnessing decode-error NI step availability, step→trace composition, and `step_preserves_projection` totality over all 33 constructors; refined WS-K-F plan into 6 granular sub-phases (K-F1 through K-F6). Zero sorry/axiom. Closes WS-K Phase F | K-F |
| **WS-K-E** | v0.16.4 | Service policy and IPC message population: added `ServiceConfig` structure with `Inhabited` default (permissive `fun _ => true`) in `Model/State.lean`; extended `SystemState` with `serviceConfig : ServiceConfig := default` field; replaced `(fun _ => true)` service policy stubs in `dispatchWithCap` with `st.serviceConfig.allowStart`/`st.serviceConfig.allowStop` — service operations now read policy from system state configuration; added `extractMessageRegisters` in `RegisterDecode.lean` that converts `Array RegValue` → `Array Nat` (matching `IpcMessage.registers : Array Nat`) with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`); updated `.send`/`.call`/`.reply` IPC dispatch arms to populate message bodies from decoded message registers instead of empty arrays; proved `extractMessageRegisters_length` (result size ≤ `maxMessageRegisters`), `extractMessageRegisters_ipc_bounded` (constructed `IpcMessage` satisfies `bounded`), `extractMessageRegisters_deterministic`; 5 delegation theorems (`dispatchWithCap_serviceStart_uses_config`, `dispatchWithCap_serviceStop_uses_config`, `dispatchWithCap_send_populates_msg`, `dispatchWithCap_call_populates_msg`, `dispatchWithCap_reply_populates_msg`); all existing soundness theorems compile unchanged; `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig` combinator; 11 Tier 3 invariant surface anchors (5 `rg` + 11 `#check`). Zero `(fun _ => true)` stubs remain. Zero `registers := #[]` in IPC dispatch. Zero sorry/axiom. Closes WS-K Phase E | K-E |
| **WS-K-D** | v0.16.3 | Lifecycle and VSpace syscall dispatch: wired all 3 remaining syscall stubs (`lifecycleRetype`, `vspaceMap`, `vspaceUnmap`) through `dispatchWithCap` — zero `.illegalState` stubs remain, all 13 syscalls fully dispatch; added `objectOfTypeTag` total type-tag decoder with dedicated `invalidTypeTag` error variant, `lifecycleRetypeDirect` pre-resolved authority companion, `PagePermissions.ofNat`/`toNat` bitfield codec with round-trip theorem; 3 delegation theorems, 3 error-decomposition theorems, equivalence theorem linking `lifecycleRetypeDirect` to `lifecycleRetypeObject`; Tier 3 anchors. Zero sorry/axiom. Closes WS-K Phase D | K-D |
| **WS-K-C** | v0.16.2 | CSpace syscall dispatch: wired all 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`) through `dispatchWithCap` using decoded message register arguments from `SyscallArgDecode`; changed `dispatchWithCap` signature from `SyscallId` to `SyscallDecodeResult`; `cspaceMint` dispatch decodes srcSlot, dstSlot, rights bitmask, badge from 4 message registers with badge=0→none seL4 convention; `cspaceCopy`/`cspaceMove` dispatch decodes srcSlot and dstSlot from 2 message registers; `cspaceDelete` dispatch decodes targetSlot from 1 message register; 4 delegation theorems proved (`dispatchWithCap_cspaceMint_delegates`, `dispatchWithCap_cspaceCopy_delegates`, `dispatchWithCap_cspaceMove_delegates`, `dispatchWithCap_cspaceDelete_delegates`); all 3 existing soundness theorems compile unchanged; refined WS-K-C workstream plan with 8 detailed subtasks (K-C.1–K-C.8). Zero sorry/axiom. Closes WS-K Phase C | K-C |
| **WS-K-B** | v0.16.1 | Per-syscall argument decode layer: added `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` implementing layer 2 of the two-layer syscall decode architecture; 7 typed argument structures (`CSpaceMintArgs`, `CSpaceCopyArgs`, `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`, `VSpaceUnmapArgs`) with `DecidableEq` and `Repr`; shared `requireMsgReg` bounds-checked indexing helper; 7 total decode functions with explicit `Except KernelError` error handling via `do` notation; 7 determinism theorems (trivial `rfl`); 7 error-exclusivity theorems (`decode fails ↔ msgRegs.size < N`) using `by_cases`/`dif_pos`/`nomatch` proof strategy; helper theorems `requireMsgReg_unfold_ok` and `requireMsgReg_unfold_err` for rewriting `dite` in mpr direction; integrated into `API.lean` import graph. Zero sorry/axiom. Closes WS-K Phase B | K-B |
| **WS-K-A** | v0.16.0 | Message register extraction into SyscallDecodeResult: added `msgRegs : Array RegValue := #[]` field to `SyscallDecodeResult` in `Model/Object/Types.lean`; updated `decodeSyscallArgs` in `RegisterDecode.lean` to validate and read message registers (x2–x5) in single pass via `Array.mapM`; added `encodeMsgRegs` identity encoder; proved `decodeMsgRegs_length` (output size = layout size) via novel `list_mapM_except_length`/`array_mapM_except_size` helpers; proved `decodeMsgRegs_roundtrip`; extended `decode_components_roundtrip` to 4-conjunct; NegativeStateSuite J1-NEG-17 verifies `msgRegs.size = 4`; RDT-002 trace includes msgRegs count; 4 new Tier 3 anchors; WS-K-A plan refined into 8 detailed subtasks. Zero sorry/axiom. Closes WS-K Phase A | K-A |
| **WS-J1-F** | v0.15.10 | CdtNodeId cleanup and documentation sync: replaced `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`; added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`); fixed downstream compilation (`SystemState` defaults, monotone allocator, test literals); all documentation synchronized across canonical sources and GitBook chapters; codebase map regenerated. All 16 kernel identifiers are now typed wrappers. Zero sorry/axiom. Closes WS-J1 Phase F. **WS-J1 portfolio fully completed** | J1-F |
| **WS-J1-E** | v0.15.9 | Testing and trace evidence: 18 negative decode tests in `NegativeStateSuite.lean`; 5 register-decode trace scenarios (RDT-002 through RDT-010) in `MainTraceHarness.lean`; 2 operation-chain tests in `OperationChainSuite.lean`; fixture and scenario registry updates; 13 Tier 3 invariant surface anchors for RegisterDecode definitions and theorems. Zero sorry/axiom. Closes WS-J1 Phase E | J1-E |
| **WS-J1-D** | v0.15.8 | Invariant and information-flow integration: `registerDecodeConsistent` predicate bridging decode layer to kernel object store validity (implied by `schedulerInvariantBundleFull` via `currentThreadValid`), `syscallEntry_preserves_proofLayerInvariantBundle` compositional preservation theorem for success and error paths, `syscallEntry_error_preserves_proofLayerInvariantBundle` trivial error-path preservation, `decodeSyscallArgs_preserves_lowEquivalent` NI theorem for pure decode, `syscallEntry_preserves_projection` projection-preservation theorem, two new `NonInterferenceStep` constructors (`syscallDecodeError` for failed decode/state unchanged, `syscallDispatchHigh` for high-domain dispatch with projection preservation), `step_preserves_projection` extended with new constructor cases, `syscallEntry_error_yields_NI_step` and `syscallEntry_success_yields_NI_step` bridge theorems from API to NI composition framework. Default-state, timer, and register-write preservation theorems for `registerDecodeConsistent`. Tier 3 anchor entries for all new definitions and theorems (13 grep anchors + 7 `#check` anchors). Zero sorry/axiom. Closes WS-J1 Phase D | J1-D |
| **WS-J1-C** | v0.15.6; refinements v0.15.7 | Syscall entry point and dispatch: `syscallEntry` top-level user-space entry point reading current thread's register file and dispatching via capability-gated `syscallInvoke`, `lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing decoded arguments through `SyscallGate` to internal kernel operations, `dispatchWithCap` per-syscall routing for all 13 syscalls (IPC send/receive/call/reply, CSpace mint/copy/move/delete, lifecycle retype, VSpace map/unmap, service start/stop), `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to configurable field (default 32). Audit refinements (v0.15.7): CSpace/lifecycle/VSpace dispatch returns `illegalState` for MR-dependent ops, `syscallEntry` accepts `regCount` parameter, `syscallEntry_implies_capability_held` strengthened to full capability-resolution chain. Soundness theorems: `syscallEntry_requires_valid_decode`, `syscallEntry_implies_capability_held`, `dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`, `syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C | J1-C |
| **WS-J1-B** | v0.15.5 | Register decode layer: `SyscallId` inductive (13 modeled syscalls with injective `toNat`/total `ofNat?`, round-trip and injectivity theorems), `MessageInfo` structure (seL4 message-info word bit-field layout with `encode`/`decode`), `SyscallDecodeResult` (typed decode output), total deterministic decode functions (`decodeCapPtr`, `decodeMsgInfo`, `decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`) in new `RegisterDecode.lean` module, `SyscallRegisterLayout` with `arm64DefaultLayout` (x0–x7 convention), `MachineConfig.registerCount`, 3 new `KernelError` variants (`invalidRegister`, `invalidSyscallNumber`, `invalidMessageInfo`), round-trip lemmas (`decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`), determinism theorem, error exclusivity theorems, universal CPtr success theorem. Self-contained module with no kernel subsystem imports. Zero sorry/axiom. Closes WS-J1 Phase B | J1-B |
| **WS-J1-A** | v0.15.4 | Typed register wrappers: replaced `abbrev RegName := Nat` and `abbrev RegValue := Nat` with typed wrapper structures (`structure RegName where val : Nat` / `structure RegValue where val : Nat`) in `Machine.lean`; added full instance suites (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat`, roundtrip/injectivity proofs); updated `RegisterFile.gpr` type signature from `Nat → Nat` to `RegName → RegValue`; re-proved all 10 existing machine lemmas; fixed all downstream compilation (Architecture adapter/invariant, Platform Sim/RPi5 proof hooks, Testing trace harness); zero sorry/axiom; zero behavior change. Closes WS-J1 Phase A | J1-A |
| **WS-I1** | v0.15.0 | Critical testing infrastructure: 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation via `test_tier2_determinism.sh` (R-02), scenario ID traceability with 121 tagged trace lines in pipe-delimited format, scenario registry YAML with Tier 0 validation (R-03). Zero sorry/axiom. Closes R-01/R-02/R-03 | I1 |
| **WS-F8** | v0.14.9 | Cleanup: removed dead `ServiceStatus.failed`/`isolated` constructors (D1), labeled Service subsystem as seLe4n extension with module docstrings (D2/MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised, finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04/MED-17/F-01/F-14/F-19 | F8 |
| **WS-F5** | v0.14.9 | Model fidelity: word-bounded `Badge` with `ofNatMasked`/`bor`/validity theorems (F5-D1/CRIT-06), order-independent `AccessRightSet` bitmask replacing list-based rights (F5-D2/HIGH-04), deferred operations documented with rationale (F5-D3/MED-03), `badgeWellFormed` invariant with `notificationBadgesWellFormed`/`capabilityBadgesWellFormed` predicates and preservation proofs for `notificationSignal`/`notificationWait`/`cspaceMint`/`cspaceMutate`. Closes CRIT-06/HIGH-04/MED-03 | F5 |
| **WS-H16** | v0.14.8 | Testing, documentation & cleanup: 10 lifecycle negative tests (M-18), 13 semantic Tier 3 assertions (A-43), `objectIndexLive` liveness invariant with preservation proof (A-13), `runQueueThreadPriorityConsistent` predicate with default theorem (A-19), O(1) membership audit confirmation (A-18), documentation metrics sync (M-21/A-45). Closes M-18/A-43/A-13/A-18/A-19/M-21/A-45 | H16 |
| **WS-H15** | v0.14.7 | Platform & API hardening: InterruptBoundaryContract decidability + consistency theorems (H15a), RPi5 MMIO disjointness/boot contract hardening (H15b), syscall capability-checking wrappers with 3 soundness theorems and 13 `api*` entry points (H15c), generic timer-invariant preservation + concrete `AdapterProofHooks` for Sim and RPi5 restrictive contracts with 6 end-to-end theorems (H15d), 31 Tier 3 anchors + 5 trace scenarios + 6 negative tests (H15e). Closes A-33/A-41/A-42/M-13 | H15a-e |
| **WS-H14** | v0.14.6 | Type safety & Prelude foundations: `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal (type-safety enforcement), sentinel predicate completion. Closes A-01/A-02/A-03/A-04/A-06/M-09/M-10/M-11 | H14 |
| **Restructuring** | v0.14.5 | Module decomposition: 9 monolithic files (1K-5.8K lines) split into 24 focused submodules via re-export hub pattern. 15 private defs tightened after cross-module audit. 209 Tier 3 anchor checks updated. Zero sorry/axiom | Structural |
| **WS-H13** | v0.14.4 | CSpace/service model enrichment: multi-level CSpace resolution, backing-object verification, `serviceCountBounded` | H13 |
| **WS-H12f** | v0.14.3 | Test harness update & documentation sync: 3 new trace scenarios, fixture update, 9 new Tier 3 anchors | H12f |
| **WS-H12e** | v0.14.2 | Cross-subsystem invariant reconciliation: `coreIpcInvariantBundle` upgraded to `ipcInvariantFull` 3-conjunct, `schedulerInvariantBundleFull` extended to 5-tuple, 8 frame lemmas + 3 compound preservation theorems | H12e |
| **WS-H12d** | v0.14.1 | IPC message payload bounds: `IpcMessage` Array migration, `maxMessageRegisters`(120)/`maxExtraCaps`(3), 4 bounds theorems, `allPendingMessagesBounded` system invariant. Closes A-09 | H12d |
| **WS-H12c** | v0.14.0 | Per-TCB register context with inline context switch: `registerContext` field, `contextMatchesCurrent` invariant, IF projection stripping. Closes H-03 | H12c |
| **WS-H12b** | v0.13.9 | Dequeue-on-dispatch scheduler semantics matching seL4's `switchToThread`/`tcbSchedDequeue`, ~1800 lines re-proved. Closes H-04 | H12b |
| **WS-H12a** | v0.13.8 | Legacy endpoint field & operation removal | H12a |
| **WS-H11** | v0.13.7 | VSpace & architecture enrichment: PagePermissions with W^X enforcement, TLB/cache model, `VSpaceBackend` typeclass, 23 new theorems | H11 |
| **End-to-end audit** | v0.13.6 | Comprehensive codebase audit: zero critical issues, zero sorry/axiom, stale documentation metrics fixed | Audit |
| **WS-H10** | v0.13.6 | Security model foundations: `ObservableState`, BIBA lattice alternatives, `DeclassificationPolicy`, `InformationFlowConfigInvariant` | H10 |
| **WS-H9** | v0.13.4 | Non-interference coverage >80%: 27 new NI theorems, 28-constructor `NonInterferenceStep`, `composedNonInterference_trace`. Closes C-02/A-40 (CRITICAL) | H9 |
| **WS-H8** | v0.13.2 | Enforcement-NI bridge: 5 enforcement soundness meta-theorems, 4 `*Checked` wrappers. Closes A-35/H-07, A-36/A-37/H-11 | H8 |
| **WS-H7** | v0.12.21 | HashMap equality + state-store migration: order-independent `BEq`, closure-to-HashMap migration for 5 state fields | H7 |
| **WS-H6** | v0.13.1 | Scheduler proof completion: `timeSlicePositive` fully proven, EDF domain-aware fix, `schedulerInvariantBundleFull` 5-tuple | H6 |
| **WS-H5** | v0.12.19 | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, 13 preservation theorems. Closes C-04/A-22..A-24 | H5 |
| **WS-H4** | v0.12.18 | Capability invariant redesign: `capabilityInvariantBundle` 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity` | H4 |
| **WS-H3** | v0.12.17 | Build/CI infrastructure: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | H3 |
| **WS-H2** | v0.12.16 | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, atomic retype | H2 |
| **WS-H1** | v0.12.16 | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | H1 |
| **WS-G** | v0.12.6-v0.12.15 | Kernel performance: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | G1-G9 + refinement |
| **WS-F1..F4** | v0.12.2-v0.12.5 | Critical audit remediation: IPC message transfer (14 theorems), untyped memory (watermark tracking), info-flow completeness (15 NI theorems), proof gap closure | F1-F4 |
| **WS-E** | v0.11.0-v0.11.6 | Test/CI hardening, proof quality, kernel hardening, capability/IPC, info-flow enforcement, completeness | E1-E6 |
| **WS-D** | v0.11.0 | Test validity, info-flow enforcement, proof gaps, kernel design | D1-D4 |
| **WS-C** | v0.9.32 | Model structure, documentation, maintainability | C1-C8 |
| **WS-B** | v0.9.0 | Comprehensive audit (2026-02) | B1-B11 |

Prior audits (v0.8.0-v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](dev_history/README.md).

## Audit plans (canonical sources)

| Plan | Scope |
|------|-------|
| [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md) | **WS-N** Robin Hood hashing verified implementation (5 phases) — **active** |
| [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md) | **WS-L** IPC subsystem audit & remediation (5 phases) — **completed** (v0.16.13) |
| [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md) | WS-K full syscall dispatch completion (8 phases) — completed |
| [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md) | WS-J1 register-indexed authoritative namespaces (6 phases) — completed |
| [`AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) | WS-I portfolio (v0.14.9 improvement recommendations) — completed |
| [`AUDIT_CODEBASE_v0.13.6.md`](dev_history/audits/AUDIT_CODEBASE_v0.13.6.md) | End-to-end audit (v0.13.6) — completed |
| [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) | WS-H portfolio (v0.12.15 audit findings) — completed |
| [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) | WS-G portfolio (performance optimization) — completed |
| [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) | WS-F portfolio (v0.12.2 audit findings) — completed |
